import Mathlib.Tactic
import Commonplace.Nat
import Commonplace.List

-- ANCHOR: fibs_def
def Fibs (index : Nat) : List Nat :=
  let rec impl (index a b : Nat) : List Nat :=
    match index with
    | 0 => [a]
    | 1 => [a, b]
    | (i + 1) => a :: impl i b (a + b)
  impl index 1 1
-- ANCHOR_END: fibs_def

namespace Fibs

section
variable (a b : Nat)

@[simp]
private lemma impl_0 : impl 0 a b = [a] :=
  by unfold impl; rfl

@[simp]
private lemma impl_1 : impl 1 a b = [a, b] :=
  by unfold impl; rfl

@[simp]
private lemma impl_2 : impl 2 a b = [a, b, a + b] :=
    by repeat (unfold impl; simp)

private lemma impl_neq_nil (i : Nat) : impl i a b ≠ [] :=
  by unfold impl; split <;> simp

private def impl_index (i : Nat) : Nat :=
  (impl i a b).getLast (impl_neq_nil a b i)

@[simp]
private lemma impl_index_0 : impl_index a b 0 = a :=
  by unfold impl_index; rfl

@[simp]
private lemma impl_index_1 : impl_index a b 1 = b :=
  by unfold impl_index; rfl

@[simp]
private lemma impl_index_2 : impl_index a b 2 = a + b :=
    by unfold impl_index; rfl

private theorem impl_cons {i : Nat} :
  a :: impl i b (a + b) = impl (i + 1) a b := by
  unfold impl; split
  case h_1 => rfl
  case h_2 => simp
  case h_3 => conv => rhs; unfold impl; simp

private theorem impl_succ (i : Nat):
  impl (i + 1) a b = (impl i a b) ++ [impl_index a b (i + 1)] := by
  unfold impl_index
  induction i generalizing a b with
  | zero =>  simp
  | succ i' hi =>
    conv => lhs; rw [← impl_cons]
    conv => rhs; rhs; lhs; lhs; rw [← impl_cons]
    conv => rhs; rhs; lhs; apply List.getLast_cons; apply impl_neq_nil
    conv => rhs; lhs; rw [← impl_cons]
    simp; apply hi

private lemma impl_index_add (i : Nat) :
  impl_index a b (i + 2) = impl_index a b (i + 1) + impl_index a b i := by
  unfold impl_index
  induction i generalizing a b with
  | zero => simp [Nat.add_comm]
  | succ i' ih =>
    conv => lhs; lhs; rw [← impl_cons]
    conv => lhs; apply List.getLast_cons; apply impl_neq_nil
    conv => rhs; lhs; lhs; rw [← impl_cons]
    conv => rhs; lhs; apply List.getLast_cons; apply impl_neq_nil
    conv => rhs; rhs; lhs; rw [← impl_cons]
    conv => rhs; rhs; apply List.getLast_cons; apply impl_neq_nil
    apply ih

private lemma impl_index_leq_impl_index_succ i (h : a ≤ b) :
  impl_index a b i ≤ impl_index a b (i + 1) := by
  unfold impl_index
  induction i generalizing a b with
  | zero => simp [h]
  | succ i' hi =>
    conv => rhs; lhs; rw [← impl_cons];
    conv => rhs; apply List.getLast_cons; apply impl_neq_nil
    conv => lhs; lhs; rw [← impl_cons];
    conv => lhs; apply List.getLast_cons; apply impl_neq_nil
    apply hi
    simp

end

@[simp]
lemma zero_eq : Fibs 0 = [1] :=by unfold Fibs; rfl

@[simp]
lemma one_eq : Fibs 1 = [1, 1] := by unfold Fibs; rfl

@[simp]
lemma two_eq : Fibs 2 = [1, 1, 2] := by unfold Fibs; rfl

@[simp]
lemma three_eq : Fibs 3 = [1, 1, 2, 3] := by unfold Fibs; rfl

@[simp]
lemma four_eq : Fibs 4 = [1, 1, 2, 3, 5] := by unfold Fibs; rfl

def nth (i : Nat) : Nat := impl_index 1 1 i

@[simp]
lemma nth_0 : nth 0 = 1 :=by unfold nth; rfl

@[simp]
lemma nth_1 : nth 1 = 1 := by unfold nth; rfl

@[simp]
lemma nth_2 : nth 2 = 2 := by unfold nth; rfl

@[simp]
lemma nth_3 : nth 3 = 3 := by unfold nth; rfl

@[simp]
lemma nth_4 : nth 4 = 5 := by unfold nth; rfl

lemma neq_nil {i : Nat} : Fibs i ≠ [] :=
  by unfold Fibs; apply impl_neq_nil

lemma nth_eq_getLast {i : Nat} : (Fibs i).getLast neq_nil = Fibs.nth i := by
  unfold Fibs nth; rfl

lemma succ_eq (i : Nat) : Fibs (i + 1) = (Fibs i) ++ [nth (i + 1)] := by
  unfold Fibs; apply impl_succ

lemma len_eq (i : Nat) : (Fibs i).length = i + 1 := by
  induction i with
  | zero => simp
  | succ i' ih => simp [succ_eq, List.length_append, ih]

lemma nth_succ_eq (i : Nat) : nth (i + 2) = nth (i + 1) + nth i := by
  unfold nth; apply impl_index_add

lemma nth_succ_eq' (i : Nat) (h : 0 < i) :
  nth (i + 1) = nth i + nth (i - 1) := by
  have ⟨_, hk⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_lt h).symm
  rw [hk]; apply nth_succ_eq

lemma nth_map_eq (i : Nat) : Fibs i = (List.range (i + 1)).map nth := by
  induction i with
  | zero => simp
  | succ i' hi =>
    rw [List.range_add]
    simp [← hi, succ_eq]

lemma nth_le_nth_succ i : nth i ≤ nth (i + 1) := by
  unfold nth
  apply impl_index_leq_impl_index_succ
  simp

lemma zero_lt_fibs_index i : 0 < nth i := by
  induction i with
  | zero => simp
  | succ i' hi =>
    apply Nat.le_trans hi
    apply nth_le_nth_succ


theorem even_for_3_mul (i : Nat): Even (nth (i * 3 + 2)) := by
  induction i with
  | zero => simp
  | succ i' hi =>
    have ⟨r', hr⟩ := hi
    have : (i' + 1) * 3 + 2 = i' * 3 + 5 := by ring
    rw [this, nth_succ_eq, nth_succ_eq, hr, Nat.add_comm, nth_succ_eq]
    exists (nth (i' * 3 + 1 + 1) + nth (i' * 3 + 1) + r')
    ring

theorem even_odd_succ (i : Nat) (h: Even (nth i)): Odd (nth (i + 1)) := by
  induction i with
  | zero => simp
  | succ i' hi =>
    simp [nth_succ_eq']
    apply Even.add_odd
    . exact h
    . contrapose h
      simp at *
      apply hi
      exact h

theorem odd_for_3_mul_add_1 (i : Nat): Odd (nth (i * 3 + 2 + 1)) := by
  apply even_odd_succ
  apply even_for_3_mul

theorem odd_for_3_mul_add_2 (i : Nat): Odd (nth (i * 3 + 2 + 2)) := by
  rw [nth_succ_eq]
  apply Odd.add_even
  case ha => apply even_odd_succ; apply even_for_3_mul
  case hb => apply even_for_3_mul

-- ANCHOR: proof_fibs_even
theorem even_nth {i : Nat} : 3 ∣ i ↔ Even (nth (i + 2)) := by
  apply Iff.intro
  . intro h
    rw [dvd_iff_exists_eq_mul_left] at h
    have ⟨c, hc⟩ := h; rw [hc]
    apply even_for_3_mul
  . intro h;
    contrapose h
    apply Nat.emod_pos_of_not_dvd at h
    apply exists_ne_dvd_3 at h
    cases h
    case inl h =>
      have ⟨c, ch⟩ := h
      simp [ch]; apply odd_for_3_mul_add_1
    case inr h =>
      have ⟨c, ch⟩ := h
      simp [ch]; apply odd_for_3_mul_add_2
-- ANCHOR_END: proof_fibs_even

theorem sum_eq (i : Nat) :
  (Fibs i).sum = nth (i + 2) - 1 := by
  induction i with
  | zero => simp
  | succ i' hi =>
   rw [ succ_eq
      , nth_succ_eq
      , List.sum_append
      , List.sum_singleton
      , hi]
   rw [Nat.sub_add_comm]
   apply zero_lt_fibs_index

end Fibs

-- ANCHOR: fibs_even_def
def FibsEven (index : Nat) : List Nat :=
  let rec impl (index a b: Nat) : List Nat :=
    let c := a + b
    let a' := b + c
    let b' := c + a'
    match index with
    | 0 => [c]
    | 1 => [c, a' + b']
    | (i + 1) => c :: impl i a' b'
  impl index 1 1
-- ANCHOR_END: fibs_even_def

namespace FibsEven

section
variable (a b : Nat)

@[simp]
private lemma impl_0 : impl 0 a b = [a + b] :=
  by unfold impl; rfl

@[simp]
private lemma impl_1 : impl 1 a b = [a + b, 3 * a + 5 * b] :=
  by unfold impl; simp; ring

@[simp]
private lemma impl_2 : impl 2 a b = [a + b, 3 * a + 5 * b, 13*a + 21*b] := by
    unfold impl; simp; ring_nf; simp

private lemma impl_neq_nil i : impl i a b ≠ [] :=
  by unfold impl; split <;> simp

private def impl_index (i : Nat) : Nat :=
  (impl i a b).getLast (impl_neq_nil a b i)


@[simp]
private lemma impl_index_0 : impl_index a b 0 = a + b :=
  by unfold impl_index; simp

@[simp]
private lemma impl_index_1 : impl_index a b 1 = 3 * a + 5 * b :=
  by unfold impl_index; simp;

@[simp]
private lemma impl_index_2 : impl_index a b 2 = 13*a + 21*b := by
    unfold impl_index; simp;

private theorem impl_cons (i : Nat) :
  (a + b) :: impl i (a + 2 * b) (2 * a + 3 * b) = impl (i + 1) a b := by
  unfold impl
  split
  case h_1 => ring_nf
  case h_2 => repeat (unfold impl; simp); ring_nf; simp
  case h_3 =>
    conv => rhs; unfold impl; simp
    ring_nf

private theorem impl_len_eq i : (impl i a b).length = i + 1 := by
  induction i generalizing a b with
  | zero => unfold impl; simp
  | succ i' ih =>
    unfold impl
    split
    case succ.h_1 => contradiction
    case succ.h_2 heq => simp at heq; rw [heq]; simp
    case succ.h_3 _ _ hij =>
      simp at hij; rw [← hij]
      conv => lhs; rw [List.length_cons, ih]

private theorem impl_succ (i : Nat):
  impl (i + 1) a b = (impl i a b) ++ [@impl_index a b (i + 1)] := by
  unfold impl_index
  induction i generalizing a b with
  | zero =>  repeat (unfold impl; simp)
  | succ i' hi =>
    conv => lhs; rw [← impl_cons]
    conv => rhs; rhs; lhs; lhs; rw [← impl_cons]
    conv => rhs; rhs; lhs; apply List.getLast_cons; apply impl_neq_nil
    conv => rhs; lhs; rw [← impl_cons]
    simp; apply hi

private lemma impl_index_leq_impl_index_succ i (h : a ≤ b) :
  impl_index a b i ≤ impl_index a b (i + 1) := by
  unfold impl_index
  induction i generalizing a b with
  | zero =>
    simp [h]
    apply Nat.add_le_add
    . apply Nat.le_mul_of_pos_left; simp
    . apply Nat.le_mul_of_pos_left; simp
  | succ i' hi =>
    conv => rhs; lhs; rw [← impl_cons];
    conv => rhs; apply List.getLast_cons; apply impl_neq_nil
    conv => lhs; lhs; rw [← impl_cons];
    conv => lhs; apply List.getLast_cons; apply impl_neq_nil
    apply hi
    apply Nat.add_le_add
    . apply Nat.le_mul_of_pos_left; simp
    . apply Nat.mul_le_mul_right; simp

theorem impl_even (i : Nat) (ha : Odd a) (hb : Odd b): ∀ x ∈ impl i a b, Even x := by
  intro x hx
  induction i generalizing x a b with
  | zero =>
    simp at hx;
    apply congrArg Even at hx
    rw [hx]; apply Odd.add_odd ha hb
  | succ i' hi =>
    rw [← impl_cons, List.mem_cons] at hx
    cases hx
    case succ.inl hx =>
      rw [hx]; apply Odd.add_odd ha hb
    case succ.inr hx =>
      have ha' : Odd (a + 2 *b) := by
        apply Even.odd_add
        . simp
        . exact ha
      have hb' : Odd (2 * a + 3 * b) := by
        apply Even.add_odd
        . simp
        . apply Odd.mul
          . unfold Odd; exists 1
          . exact hb
      have := hi _ _ ha' hb'
      apply this
      apply hx

-- ANCHOR: as_fibs_proof_impl
theorem impl_to_fibs (i : Nat) : Fibs.impl_index a b (i * 3 + 2) = impl_index a b i := by
  unfold Fibs.impl_index impl_index
  induction i generalizing a b with
  | zero => simp
  | succ i' hi =>
    have : (i' + 1) * 3 + 2 = i' * 3 + 2 + 3 := by ring
    rw [this]
    repeat
    conv => lhs; lhs; rw [← Fibs.impl_cons]
    conv => lhs; apply List.getLast_cons; apply Fibs.impl_neq_nil
    conv => lhs; lhs; rw [← Fibs.impl_cons]
    conv => lhs; apply List.getLast_cons; apply Fibs.impl_neq_nil
    conv => lhs; lhs; rw [← Fibs.impl_cons]
    conv => lhs; apply List.getLast_cons; apply Fibs.impl_neq_nil
    conv => rhs; lhs; rw [← impl_cons]
    conv => rhs; apply List.getLast_cons; apply impl_neq_nil
    have : b + (a + b) = a + 2*b := by ring
    rw [this]
    have : a + b + (a + 2 * b) = 2 * a + 3 * b := by ring
    rw [this]
    apply hi
-- ANCHOR_END: as_fibs_proof_impl

private theorem impl_index_add (i : Nat) :
  impl_index a b (i + 2) = 4 * (impl_index a b (i + 1)) + impl_index a b i := by
  unfold impl_index
  induction i generalizing a b with
  | zero => simp [Nat.add_comm]; ring
  | succ i' ih =>
    conv => lhs; lhs; rw [← impl_cons]
    conv => lhs; apply List.getLast_cons; apply impl_neq_nil
    conv => rhs; lhs; rhs; lhs; rw [← impl_cons]
    conv => rhs; lhs; rhs; apply List.getLast_cons; apply impl_neq_nil
    conv => rhs; rhs; lhs; rw [← impl_cons]
    conv => rhs; rhs; apply List.getLast_cons; apply impl_neq_nil
    apply ih

end

@[simp]
lemma zero_eq : FibsEven 0 = [2] := by unfold FibsEven; rfl

@[simp]
lemma one_eq : FibsEven 1 = [2, 8] := by unfold FibsEven; rfl

@[simp]
lemma two_eq : FibsEven 2 = [2, 8, 34] := by unfold FibsEven; rfl

def nth (i : Nat) : Nat := impl_index 1 1 i

@[simp]
lemma nth_0 : nth 0 = 2 := by unfold nth; rfl

@[simp]
lemma nth_1 : nth 1 = 8 := by unfold nth; rfl

@[simp]
lemma nth_2 : nth 2 = 34 := by unfold nth; rfl

lemma neq_nil {i : Nat} : FibsEven i ≠ [] :=
  by unfold FibsEven; apply impl_neq_nil

lemma nth_eq_getLast {i : Nat} : (FibsEven i).getLast neq_nil = FibsEven.nth i := rfl

lemma len_eq (i : Nat) : (FibsEven i).length = i + 1 := by
  unfold FibsEven; apply impl_len_eq

lemma succ_eq (i : Nat) : FibsEven (i + 1) = (FibsEven i) ++ [nth (i + 1)] := by
  unfold FibsEven; apply impl_succ

lemma nth_le_nth_succ i : nth i ≤ nth (i + 1) := by
  unfold nth
  apply impl_index_leq_impl_index_succ
  simp

lemma one_lt_fibs_index i : 1 < nth i := by
  induction i with
  | zero => simp;
  | succ i' hi =>
    apply Nat.le_trans hi
    apply nth_le_nth_succ

-- ANCHOR: as_fibs_proof
theorem as_fibs {i : Nat} : Fibs.nth (i * 3 + 2) = nth i := by apply impl_to_fibs
-- ANCHOR_END: as_fibs_proof

theorem is_even {i : Nat}: ∀ x ∈ FibsEven i, Even x := by apply impl_even <;> simp

theorem nth_succ_eq {i : Nat} : nth (i + 2) = 4 * nth (i + 1) + nth i := by
  unfold nth; apply impl_index_add

theorem even_fibs_in_fibs {i : Nat} : FibsEven i ⊆ Fibs (i * 3 + 2) := by
  induction i with
  | zero => simp at *
  | succ i' hi =>
    have : (i' + 1) * 3 + 2 = i' * 3 + 2 + 3 := by ring
    rw [this]
    conv => rhs; rw [Fibs.succ_eq]; lhs; rw [Fibs.succ_eq]; lhs; rw [Fibs.succ_eq]
    rw  [succ_eq, List.append_subset]
    apply And.intro
    . simp; apply List.subset_append_of_subset_left; apply hi
    . simp [← as_fibs]; apply Or.inr; apply Or.inr; apply Or.inr; ring_nf

-- ANCHOR: fibseven_sum_eq_proof
theorem sum_eq (i : Nat) :
  (FibsEven i).sum = Fibs.nth (3 * i + 4) / 2 := by
  induction i with
  | zero => simp
  | succ i' hi =>
    rw [ succ_eq
       , List.sum_append
       , List.sum_singleton
       , hi
       , ← as_fibs]
    have : 3 * (i' + 1) + 4 = 3 * i' + 4 + 3 := by ring
    rw [this]
    conv => rhs; rw [Fibs.nth_succ_eq]
    conv => rhs; lhs; lhs; rw [Fibs.nth_succ_eq]
    ring_nf
    rw [Nat.add_div_of_dvd_right]
    . simp; ring
    . simp
-- ANCHOR_END: fibseven_sum_eq_proof

end FibsEven
