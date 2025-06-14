import Mathlib.Tactic

-- ANCHOR: proof_x_mul_x_succ_dvd_2
lemma x_mul_x_succ_dvd_2 (x : Nat) : 2 ∣ (x + 1) * x := by
  induction x with
  | zero => simp
  | succ x' hx =>
    simp [Nat.add_assoc]
    rw [Nat.add_mul, Nat.mul_comm]
    apply Nat.dvd_add
    . exact hx
    . simp
-- ANCHOR_END: proof_x_mul_x_succ_dvd_2

-- ANCHOR: proof_x_mod_3_and_x_mod_5_eq_mod_15
lemma x_mod_3_and_x_mod_5_eq_mod_15 (n : Nat) : (n % 15 == 0) = (n % 3 == 0 && n % 5 == 0) := by
  have (n : Nat) : n % 15 = 0 ↔ (n % 3 = 0 ∧ n % 5 = 0) := by omega
  by_cases h : (n % 15 = 0)
  case pos => rw [h]; have ⟨h3, h5⟩ := (this n).mp h; simp [h3, h5]
  case neg =>
    rw [beq_eq_false_iff_ne.mpr h]
    apply ((mt (this n).mpr)) at h
    cases Classical.not_and_iff_not_or_not.mp h
      <;> (rename_i h'; simp [h'])
-- ANCHOR_END: proof_x_mod_3_and_x_mod_5_eq_mod_15

theorem n_div_succ_lt_n_div (n m : ℕ) : 0 < m -> n / (m + 1) ≤ n / m := by
  intro h
  apply Nat.div_le_div_left
  . simp
  . exact h

theorem triangle_div_le_eq_zero: ∀ (n m : Nat),
  m ≤ n -> n * ((m - 1) / n + 1) * ((m - 1) / n) / 2 = 0 := by
  intro n m hm
  have: (m - 1) / n = 0 := by
    by_cases q: (m = 0)
    . simp [q]
    . apply Nat.div_eq_of_lt
      apply Nat.le_trans (m:=m)
      rw [← Nat.pred_eq_sub_one]
      apply Nat.pred_lt
      exact q
      exact hm
  simp [this]

theorem exists_ne_dvd_3 (i : Nat) (h : 0 < i % 3) : (∃ c, i = c * 3 + 1) ∨ (∃ c, i = c * 3 + 2) := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_lt h).symm
  cases k with
  | zero =>
    simp at hk
    apply Or.inl
    exists (i / 3)
    rw [← hk, Nat.div_add_mod']
  | succ k' =>
    cases k' with
    | zero =>
      simp at hk
      apply Or.inr
      exists (i / 3)
      rw [← hk]
      rw [Nat.div_add_mod']
    | succ k'' =>
      have : (i % 3) < 3 := by
        have : 3 > 0 := by simp
        exact Nat.mod_lt _ this
      rw [hk] at this
      contradiction


theorem mod_2_even {n : Nat} :  n % 2 == 0 ↔ Even n := by
  apply Iff.intro
  . intro h
    contrapose h; simp at *
    unfold Odd at h
    have ⟨k, hk⟩ := h
    rw [hk, Nat.mul_add_mod_self_left]
    simp
  . intro h
    unfold Even at h
    have ⟨k, hk,⟩ := h
    simp [hk]
    have : k + k = 2 * k := by ring
    simp [this]
