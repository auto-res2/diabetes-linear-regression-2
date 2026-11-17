"""パーサー。claims.json を読み、検証器を呼び、Lean の値と定理のファイルを書き、Lean の出力から判定を読む。"""
import json
import re
from fractions import Fraction
from pathlib import Path

from verifiers import QUERIES

FORMAL = Path(__file__).parent
# 型ごとの、Lean での書き方
LITERAL = {
    "String": json.dumps,
    "Bool": lambda value: str(bool(value)).lower(),
    "ℕ": lambda value: str(int(value)),
    "ℚ": lambda value: f"(({Fraction(value).numerator} : ℚ) / {Fraction(value).denominator})",
}
HEADER = ["import Values", "import Claims", "open Claims"]


def lean_literal(lean_type: str, value) -> str:
    if lean_type.startswith("List "):
        return "[" + ", ".join(lean_literal(lean_type.removeprefix("List "), item) for item in value) + "]"
    return LITERAL[lean_type](value)


def read_claims() -> dict:
    record = json.loads((FORMAL / "claims.json").read_text(encoding="utf-8"))
    unknown = [item["id"] for item in record["non_claims"] + record["claims"] if item["sentence"] not in record["sentences"]]
    if unknown:
        raise ValueError(f"存在しない文を指している: {unknown}")
    return record


def write_values(repository: str, mode: str) -> tuple[dict[str, str], dict[str, str]]:
    """変数ごとに、宣言した値を読むか、検証器に問い合わせて、Values.lean を書く。(値, 取れなかった理由) を返す。"""
    values, errors = {}, {}
    for name, variable in read_claims()["variables"].items():
        try:
            if "declared" in variable:
                value = variable["declared"]
            else:
                query = QUERIES[variable["verifier"]][variable["query"]]
                value = query(repository, mode, name, **variable.get("args", {}))
            values[name] = lean_literal(variable["type"], value)
        except Exception as error:  # 取れなかった値を使う claim だけを、判定できずにする
            errors[name] = str(error)
    lines = ["import Mathlib", "/-! 検証器が返した値と、宣言した値。parse_claims.py が生成する。手で編集しない。 -/", "namespace Values"]
    lines += [f"def {name} : {read_claims()['variables'][name]['type']} := {literal}" for name, literal in values.items()]
    (FORMAL / "lean" / "Values.lean").write_text("\n".join(lines + ["end Values", ""]), encoding="utf-8")
    return values, errors


def proposition(claim: dict) -> str:
    """命題名に、値を名前付きの引数として付ける。"""
    formalization = claim["formalization"]
    return " ".join([formalization["proposition_name"]] + [f"({name} := Values.{name})" for name in formalization["arguments"]])


def candidates(claim: dict) -> list[str]:
    """命題が真である定理と、偽である（否定の）定理。通ったほうが判定になる。有理数の比較は decide では簡約が止まるので、kernel に評価させる。"""
    name, statement = claim["id"], proposition(claim)
    return [f"theorem {name}_holds : {statement} := by decide +kernel",
            f"theorem {name}_fails : ¬ ({statement}) := by decide +kernel",
            f"#print axioms {name}_holds", f"#print axioms {name}_fails"]


def write_candidates(judgeable: list[dict], formalized_non_claims: list[dict]) -> Path:
    """全 claim の定理の候補と、非claims の命題があることの確認を、1 つのファイルに書く。Lean の起動を 1 回で済ませる。"""
    lines = HEADER + [line for claim in judgeable for line in candidates(claim)]
    lines += [f"#check @{item['formalization']['proposition_name']}" for item in formalized_non_claims]
    path = FORMAL / "lean" / "Candidates.lean"
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return path


def read_axioms(lean_output: str) -> dict[str, list[str] | None]:
    """定理ごとの、依存する公理。証明が通らなかった定理は sorryAx に依存する。出力に無い定理は None。"""
    flat = re.sub(r"\s+", " ", lean_output)
    axioms = {name: [] for name in re.findall(r"'(\w+)' does not depend on any axioms", flat)}
    axioms |= {name: listed.split(", ") for name, listed in re.findall(r"'(\w+)' depends on axioms: \[([^\]]*)\]", flat)}
    return axioms


def judge(claim: dict, allowed_axioms: set[str], axioms: dict) -> dict:
    """真か偽か判定できずか。通った定理が、宣言した公理の外に依存していたら、判定できずにする。"""
    for verdict, suffix in (("真", "holds"), ("偽", "fails")):
        used = axioms.get(f"{claim['id']}_{suffix}")
        if used is not None and "sorryAx" not in used:
            if set(used) <= allowed_axioms:
                return {"verdict": verdict, "axioms": sorted(used)}
            return {"verdict": "判定できず", "reason": f"宣言した公理の外に依存している: {sorted(set(used) - allowed_axioms)}"}
    return {"verdict": "判定できず", "reason": "真の定理も偽の定理も通らなかった"}


def write_theorems(claims: list[dict], results: dict) -> None:
    """判定が付いた命題を、真なら定理、偽なら否定の定理として Theorems.lean に書く。"""
    lines = HEADER + ["/-! 各命題の判定。parse_claims.py が生成する。 -/"]
    lines += [candidates(claim)[results[claim["id"]]["verdict"] == "偽"] for claim in claims
              if results[claim["id"]]["verdict"] != "判定できず"]
    (FORMAL / "lean" / "Theorems.lean").write_text("\n".join(lines) + "\n", encoding="utf-8")
