import ThinMatrixProducts.Util.LogBounds

/-!
# Enclosures of the logarithms that the paper's constants use

Each enclosure comes from `log_mem` and is checked by `numerics`.
-/

namespace ThinMatrixProducts

lemma log_two_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
lemma log_two_lt : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring

lemma log_three_gt : (1.0986122881 : ℝ) < Real.log 3 :=
  lt_of_lt_of_le (by numerics) (log_mem 2 7 (by norm_num : (0 : ℝ) < 3)).1
lemma log_three_lt : Real.log 3 < (1.0986122892 : ℝ) :=
  lt_of_le_of_lt (log_mem 2 7 (by norm_num : (0 : ℝ) < 3)).2 (by numerics)

lemma log_five_gt : (1.6094379119 : ℝ) < Real.log 5 :=
  lt_of_lt_of_le (by numerics) (log_mem 2 7 (by norm_num : (0 : ℝ) < 5)).1
lemma log_five_lt : Real.log 5 < (1.6094379130 : ℝ) :=
  lt_of_le_of_lt (log_mem 2 7 (by norm_num : (0 : ℝ) < 5)).2 (by numerics)

lemma log_ten_eq : Real.log 10 = Real.log 2 + Real.log 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

lemma log_pos_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
lemma log_pos_five : 0 < Real.log 5 := Real.log_pos (by norm_num)

/-! ## Tight enclosures (about 20 digits), from the series at `k = 0` -/

lemma log_two_gt' : (0.6931471805599453094171 : ℝ) < Real.log 2 :=
  lt_of_lt_of_le (by numerics) (log_mem 0 32 (by norm_num : (0 : ℝ) < 2)).1
lemma log_two_lt' : Real.log 2 < (0.6931471805599453094174 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 32 (by norm_num : (0 : ℝ) < 2)).2 (by numerics)

lemma log_three_ratio_gt : (0.405465108108164381978 : ℝ) < Real.log (3 / 2) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 20 (by norm_num : (0 : ℝ) < 3 / 2)).1
lemma log_three_ratio_lt : Real.log (3 / 2) < (0.40546510810816438197803 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 20 (by norm_num : (0 : ℝ) < 3 / 2)).2 (by numerics)
lemma log_three_gt' : (1.098612288668109691394 : ℝ) < Real.log 3 := by
  rw [show (3 : ℝ) = 3 / 2 * 2 ^ 1 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_three_ratio_gt, log_three_ratio_lt, log_two_gt', log_two_lt']
lemma log_three_lt' : Real.log 3 < (1.098612288668109691397 : ℝ) := by
  rw [show (3 : ℝ) = 3 / 2 * 2 ^ 1 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_three_ratio_gt, log_three_ratio_lt, log_two_gt', log_two_lt']

lemma log_five_ratio_gt : (0.22314355131420975576628 : ℝ) < Real.log (5 / 4) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 14 (by norm_num : (0 : ℝ) < 5 / 4)).1
lemma log_five_ratio_lt : Real.log (5 / 4) < (0.22314355131420975576631 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 14 (by norm_num : (0 : ℝ) < 5 / 4)).2 (by numerics)
lemma log_five_gt' : (1.609437912434100373 : ℝ) < Real.log 5 := by
  rw [show (5 : ℝ) = 5 / 4 * 2 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_five_ratio_gt, log_five_ratio_lt, log_two_gt', log_two_lt']
lemma log_five_lt' : Real.log 5 < (1.609437912434100376 : ℝ) := by
  rw [show (5 : ℝ) = 5 / 4 * 2 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_five_ratio_gt, log_five_ratio_lt, log_two_gt', log_two_lt']

lemma log_seven_ratio_gt : (-0.13353139262452262314636 : ℝ) < Real.log (7 / 8) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 12 (by norm_num : (0 : ℝ) < 7 / 8)).1
lemma log_seven_ratio_lt : Real.log (7 / 8) < (-0.13353139262452262314633 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 12 (by norm_num : (0 : ℝ) < 7 / 8)).2 (by numerics)
lemma log_seven_gt' : (1.945910149055313304 : ℝ) < Real.log 7 := by
  rw [show (7 : ℝ) = 7 / 8 * 2 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_seven_ratio_gt, log_seven_ratio_lt, log_two_gt', log_two_lt']
lemma log_seven_lt' : Real.log 7 < (1.945910149055313307 : ℝ) := by
  rw [show (7 : ℝ) = 7 / 8 * 2 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_seven_ratio_gt, log_seven_ratio_lt, log_two_gt', log_two_lt']

lemma log_seventeen_ratio_gt : (0.06062462181643484258059 : ℝ) < Real.log (17 / 16) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 9 (by norm_num : (0 : ℝ) < 17 / 16)).1
lemma log_seventeen_ratio_lt : Real.log (17 / 16) < (0.06062462181643484258062 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 9 (by norm_num : (0 : ℝ) < 17 / 16)).2 (by numerics)
lemma log_seventeen_gt' : (2.833213344056216079 : ℝ) < Real.log 17 := by
  rw [show (17 : ℝ) = 17 / 16 * 2 ^ 4 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_seventeen_ratio_gt, log_seventeen_ratio_lt, log_two_gt', log_two_lt']
lemma log_seventeen_lt' : Real.log 17 < (2.833213344056216082 : ℝ) := by
  rw [show (17 : ℝ) = 17 / 16 * 2 ^ 4 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_seventeen_ratio_gt, log_seventeen_ratio_lt, log_two_gt', log_two_lt']

lemma log_nineteen_ratio_gt : (0.05406722127027576780129 : ℝ) < Real.log (19 / 18) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 9 (by norm_num : (0 : ℝ) < 19 / 18)).1
lemma log_nineteen_ratio_lt : Real.log (19 / 18) < (0.05406722127027576780132 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 9 (by norm_num : (0 : ℝ) < 19 / 18)).2 (by numerics)
lemma log_nineteen_gt' : (2.944438979166440459 : ℝ) < Real.log 19 := by
  rw [show (19 : ℝ) = 19 / 18 * (2 ^ 1 * 3 ^ 2) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  linarith [log_nineteen_ratio_gt, log_nineteen_ratio_lt, log_two_gt', log_two_lt', log_three_gt', log_three_lt']
lemma log_nineteen_lt' : Real.log 19 < (2.944438979166440462 : ℝ) := by
  rw [show (19 : ℝ) = 19 / 18 * (2 ^ 1 * 3 ^ 2) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  linarith [log_nineteen_ratio_gt, log_nineteen_ratio_lt, log_two_gt', log_two_lt', log_three_gt', log_three_lt']

lemma log_twentythree_ratio_gt : (-0.0425596144187959288402 : ℝ) < Real.log (23 / 24) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 8 (by norm_num : (0 : ℝ) < 23 / 24)).1
lemma log_twentythree_ratio_lt : Real.log (23 / 24) < (-0.04255961441879592884017 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 8 (by norm_num : (0 : ℝ) < 23 / 24)).2 (by numerics)
lemma log_twentythree_gt' : (3.135494215929149689 : ℝ) < Real.log 23 := by
  rw [show (23 : ℝ) = 23 / 24 * (2 ^ 3 * 3 ^ 1) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  linarith [log_twentythree_ratio_gt, log_twentythree_ratio_lt, log_two_gt', log_two_lt', log_three_gt', log_three_lt']
lemma log_twentythree_lt' : Real.log 23 < (3.135494215929149692 : ℝ) := by
  rw [show (23 : ℝ) = 23 / 24 * (2 ^ 3 * 3 ^ 1) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  push_cast
  linarith [log_twentythree_ratio_gt, log_twentythree_ratio_lt, log_two_gt', log_two_lt', log_three_gt', log_three_lt']

lemma log_twentynine_ratio_gt : (0.07145896398214495299752 : ℝ) < Real.log (29 / 27) :=
  lt_of_lt_of_le (by numerics) (log_mem 0 10 (by norm_num : (0 : ℝ) < 29 / 27)).1
lemma log_twentynine_ratio_lt : Real.log (29 / 27) < (0.07145896398214495299755 : ℝ) :=
  lt_of_le_of_lt (log_mem 0 10 (by norm_num : (0 : ℝ) < 29 / 27)).2 (by numerics)
lemma log_twentynine_gt' : (3.367295829986474026 : ℝ) < Real.log 29 := by
  rw [show (29 : ℝ) = 29 / 27 * 3 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_twentynine_ratio_gt, log_twentynine_ratio_lt, log_two_gt', log_two_lt', log_three_gt', log_three_lt']
lemma log_twentynine_lt' : Real.log 29 < (3.367295829986474029 : ℝ) := by
  rw [show (29 : ℝ) = 29 / 27 * 3 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast
  linarith [log_twentynine_ratio_gt, log_twentynine_ratio_lt, log_two_gt', log_two_lt', log_three_gt', log_three_lt']


end ThinMatrixProducts
