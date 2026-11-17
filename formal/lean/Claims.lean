import Mathlib
/-!
レポートの各文の claims と仮定を、命題として書いたもの。
値はすべて引数で受ける。値を入れるのは parse_claims.py が生成する Theorems.lean。
-/
namespace Claims

/-- 報告値 reported が、値 value を unit の桁に四捨五入したものである。 -/
abbrev roundsTo (value reported unit : ℚ) : Prop :=
  reported - unit / 2 ≤ value ∧ value < reported + unit / 2

/-! ## R01 -/
abbrev R01_c2 (observedSha256 dataSha256 : String) : Prop := observedSha256 = dataSha256
abbrev R01_c3 (dataSha256 literatureSha256 : String) : Prop := dataSha256 = literatureSha256
abbrev R01_c1 (observedSha256 dataSha256 literatureSha256 : String) : Prop :=
  R01_c2 observedSha256 dataSha256 ∧ R01_c3 dataSha256 literatureSha256

/-! ## R02 -/
abbrev R02_c1 (nSamples nFeatures : ℕ) : Prop := nSamples = 442 ∧ nFeatures = 10
abbrev R02_c2 (featureColumns : List String) : Prop :=
  featureColumns = ["AGE", "SEX", "BMI", "BP", "S1", "S2", "S3", "S4", "S5", "S6"]
abbrev R02_c3 (targetColumn : String) : Prop := targetColumn = "Y"

/-! ## R03 -/
abbrev R03_c1 (observedSha256 dataSha256 : String) : Prop := observedSha256 = dataSha256
abbrev R03_c2 (dataSha256DeclaredAt firstFullRunAt : ℕ) : Prop := dataSha256DeclaredAt ≤ firstFullRunAt
/-- 仮定。一致しないファイルでは実行されない。 -/
abbrev R03_a1 (sha256Of : String → String) (runs : String → Prop) (dataSha256 : String) : Prop :=
  ∀ file, sha256Of file ≠ dataSha256 → ¬ runs file

/-! ## R04 -/
abbrev R04_c1 (modelInputXSha256 loadedXSha256 : String) : Prop := modelInputXSha256 = loadedXSha256

/-! ## R05 -/
abbrev R05_c1 (targetMean : ℚ) : Prop := roundsTo targetMean 152.1 0.1
abbrev R05_c2 (targetStd : ℚ) : Prop := roundsTo targetStd 77.0 0.1

/-! ## R06 -/
abbrev R06_c1 (nTrain nTest nSamples : ℕ) : Prop := nTrain + nTest = nSamples
abbrev R06_c2 (trainIndex testIndex : List ℕ) (nSamples : ℕ) : Prop :=
  Disjoint trainIndex.toFinset testIndex.toFinset ∧
  trainIndex.toFinset ∪ testIndex.toFinset = Finset.range nSamples
/-- 仮定。分割は、シードを入れた並べ替えの手続きで決まる。 -/
abbrev R06_a1 (shuffleSplit : ℕ → List ℕ × List ℕ) (trainIndex testIndex : List ℕ) (splitSeed : ℕ) : Prop :=
  (trainIndex, testIndex) = shuffleSplit splitSeed

/-! ## R07 -/
abbrev R07_c1 (nTest nSamples : ℕ) : Prop := (nTest : ℤ) = ⌈(0.2 : ℚ) * nSamples⌉
abbrev R07_c2 (splitSeed : ℕ) : Prop := splitSeed = 0

/-! ## R08 -/
/-- 線形回帰モデル（式 (3)）。 -/
def linearModel {p : ℕ} (β₀ : ℝ) (β : Fin p → ℝ) (x : Fin p → ℝ) : ℝ := β₀ + ∑ j, β j * x j
/-- 残差の二乗和。 -/
noncomputable def rss {n p : ℕ} (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (β₀ : ℝ) (β : Fin p → ℝ) : ℝ :=
  ∑ i, (y i - linearModel β₀ β (X i)) ^ 2
/-- 仮定。係数は、訓練データ上の残差の二乗和を最小にする。 -/
abbrev R08_a1 {n p : ℕ} (X : Fin n → Fin p → ℝ) (y : Fin n → ℝ) (β₀ : ℝ) (β : Fin p → ℝ) : Prop :=
  ∀ b₀ b, rss X y β₀ β ≤ rss X y b₀ b

/-! ## R09 -/
abbrev R09_c1 (usedFeatureCount nFeatures : ℕ) : Prop := usedFeatureCount = nFeatures
/-- 仮定。正則化の係数は 0 である。 -/
abbrev R09_a1 (penaltyWeight : ℚ) : Prop := penaltyWeight = 0

/-! ## R10 -/
abbrev R10_c1 (fitFunction : String) : Prop := fitFunction = "sklearn.linear_model.LinearRegression"

/-! ## R11、R15 -/
abbrev R11_c1 (outputKeys : List String) : Prop :=
  ["trainMse", "trainRmse", "trainMae", "trainR2", "testMse", "testRmse", "testMae", "testR2"] ⊆ outputKeys
abbrev R15_c1 (outputKeys : List String) : Prop := R11_c1 outputKeys

/-! ## R14 -/
abbrev R14_c1 (trainRmse trainMse testRmse testMse rmseSquaredTolerance : ℚ) : Prop :=
  |trainRmse ^ 2 - trainMse| ≤ rmseSquaredTolerance ∧ |testRmse ^ 2 - testMse| ≤ rmseSquaredTolerance
abbrev R14_c2 (rmseSquaredToleranceDeclaredAt firstFullRunAt : ℕ) : Prop :=
  rmseSquaredToleranceDeclaredAt ≤ firstFullRunAt

/-! ## R16、R17 -/
abbrev R16_c1 (envCpuModel : String) (envCpuLogicalCores : ℕ) (envMemoryGib : ℚ) : Prop :=
  envCpuModel = "Intel(R) Core(TM) i5-10400 CPU @ 2.90GHz" ∧ envCpuLogicalCores = 12 ∧ envMemoryGib = 7.7
/-- 仮定。使った GPU の数は 0 である。 -/
abbrev R16_a1 (gpuCount : ℕ) : Prop := gpuCount = 0
abbrev R17_c1 (envPython envNumpy envScikitLearn : String) : Prop :=
  envPython = "3.13.3" ∧ envNumpy = "2.3.4" ∧ envScikitLearn = "1.7.2"

/-! ## R18 -/
abbrev R18_c1 (repositoryPublic : Bool) (repositoryFiles : List String) : Prop :=
  repositoryPublic = true ∧ ["src/run_experiment.py", "results/metrics.json"] ⊆ repositoryFiles

/-! ## R19 -/
/-- 仮定。表 2 に、訓練とテストのそれぞれについて、4 つの指標の欄がある。 -/
abbrev R19_a1 (tableKeys : ℕ → String → List String) : Prop :=
  ∀ split ∈ ["train", "test"], ["mse", "rmse", "mae", "r2"] ⊆ tableKeys 2 split

/-! ## R20 -/
abbrev R20_c1 (testMse : ℚ) : Prop := roundsTo testMse 3424.3 0.1
abbrev R20_c2 (testRmse : ℚ) : Prop := roundsTo testRmse 58.5 0.1
abbrev R20_c3 (testR2 : ℚ) : Prop := roundsTo testR2 0.332 0.001

/-! ## R21 -/
abbrev R21_c1 (testRmse targetStd : ℚ) : Prop := testRmse < targetStd
abbrev R21_c2 (testRmse meanPredictorTestRmse : ℚ) : Prop := testRmse < meanPredictorTestRmse
abbrev R21_c3 (testRmse targetStd meanPredictorTestRmse : ℚ) : Prop :=
  R21_c1 testRmse targetStd → R21_c2 testRmse meanPredictorTestRmse

/-! ## R22 -/
abbrev R22_c1 (testR2 trainR2 margin : ℚ) : Prop := testR2 + margin ≤ trainR2
abbrev R22_c2 (trainR2 : ℚ) : Prop := roundsTo trainR2 0.554 0.001
abbrev R22_c3 (marginDeclaredAt firstFullRunAt : ℕ) : Prop := marginDeclaredAt ≤ firstFullRunAt
/-- 仮定。出力の R² は、各データに対して式 (5) のとおりに計算され、そのまま書き出されている。 -/
abbrev R22_a1 (r2ComputedAsSpecified : Bool) : Prop := r2ComputedAsSpecified = true

/-! ## R23 -/
abbrev R23_c1 (trainMse testMse : ℚ) : Prop := trainMse < testMse

/-! ## R24 -/
abbrev R24_c1 (trainR2 trainR2LowerBound : ℚ) : Prop := trainR2LowerBound ≤ trainR2
abbrev R24_c2 (testR2 testR2UpperBound : ℚ) : Prop := testR2 ≤ testR2UpperBound
abbrev R24_c3 (testR2 trainR2 margin trainMse testMse trainR2LowerBound testR2UpperBound : ℚ) : Prop :=
  R22_c1 testR2 trainR2 margin ∧ R23_c1 trainMse testMse →
    R24_c1 trainR2 trainR2LowerBound ∧ R24_c2 testR2 testR2UpperBound
abbrev R24_c4 (trainR2LowerBoundDeclaredAt testR2UpperBoundDeclaredAt firstFullRunAt : ℕ) : Prop :=
  trainR2LowerBoundDeclaredAt ≤ firstFullRunAt ∧ testR2UpperBoundDeclaredAt ≤ firstFullRunAt

/-! ## R25 -/
abbrev R25_c1 (testR2 : ℚ) : Prop := 0 < testR2 ∧ testR2 < 1

/-! ## R26 -/
abbrev R26_c1 (trainMse trainRmse trainMae trainR2 testMse testRmse testMae testR2 : ℚ) : Prop :=
  roundsTo trainMse 2734.8 0.1 ∧ roundsTo trainRmse 52.3 0.1 ∧
  roundsTo trainMae 42.6 0.1 ∧ roundsTo trainR2 0.554 0.001 ∧
  roundsTo testMse 3424.3 0.1 ∧ roundsTo testRmse 58.5 0.1 ∧
  roundsTo testMae 46.2 0.1 ∧ roundsTo testR2 0.332 0.001

end Claims
