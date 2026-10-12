import Statements
import ThinMatrixProducts.Util.Logs

/-!
# The thresholds `ε*_5`, `ε*_10` and `1/ε` (abstract, Theorem A, Proposition 8.1)
-/

namespace ThinMatrixProducts

lemma epsStar5_eq : epsStar5 = 2 * Real.log 2 / (5 * Real.log 5) := by
  rw [epsStar5, log_four_eq]

lemma epsStar10_eq : epsStar10 = 2 * Real.log 2 / (5 * (Real.log 2 + Real.log 5)) := by
  rw [epsStar10, log_four_eq, log_ten_eq]

theorem sec1_epsStar5_value : Sec1_epsStar5_value := by
  have h2 := log_two_gt; have h2' := log_two_lt; have h5 := log_five_gt; have h5' := log_five_lt
  rw [Sec1_epsStar5_value, epsStar5_eq, lt_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
  constructor <;> nlinarith

theorem sec1_epsStar10_value : Sec1_epsStar10_value := by
  have h2 := log_two_gt; have h2' := log_two_lt; have h5 := log_five_gt; have h5' := log_five_lt
  rw [Sec1_epsStar10_value, epsStar10_eq, lt_div_iff₀ (by positivity), div_lt_iff₀ (by positivity)]
  constructor <;> nlinarith

theorem theorem_A_thresholds : Theorem_A_thresholds := by
  have h2 := log_two_gt; have h2' := log_two_lt; have h5 := log_five_gt; have h5' := log_five_lt
  have hl4 := log_four_eq; have hl10 := log_ten_eq
  have p2 := log_pos_two; have p5 := log_pos_five
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [epsStar5, one_div_div]
  · rw [hl4, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [hl4, div_lt_iff₀ (by positivity)]; nlinarith
  · rw [epsStar10, one_div_div]
  · rw [hl4, hl10, lt_div_iff₀ (by positivity)]; nlinarith
  · rw [hl4, hl10, div_lt_iff₀ (by positivity)]; nlinarith

theorem proposition_8_1_form : Proposition_8_1_form := by
  refine ⟨epsStar5_eq, ?_⟩
  rw [epsStar10, log_four_eq]; ring

end ThinMatrixProducts
