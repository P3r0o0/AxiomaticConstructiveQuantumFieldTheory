import LWEBasic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace LWE

section RationalFinDist

open scoped BigOperators

lemma bitToInt_nonneg (b : Bool) : 0 ≤ bitToInt b := by
  cases b <;> simp [bitToInt]

lemma bitToInt_le_one (b : Bool) : bitToInt b ≤ 1 := by
  cases b <;> simp [bitToInt]

lemma bitToInt_not (b : Bool) : bitToInt (!b) = 1 - bitToInt b := by
  cases b <;> simp [bitToInt]

lemma uniformFinDist_totalMass (α : Type*) [Fintype α] :
    (uniformFinDist α).totalMass = Fintype.card α := by
  simp [uniformFinDist, FinDist.totalMass]

lemma uniformFinDist_totalMass_pos (α : Type*) [Fintype α] [Nonempty α] :
    0 < (uniformFinDist α).totalMass := by
  rw [uniformFinDist_totalMass]
  exact Fintype.card_pos

lemma uniformFinDist_acceptWeight (α : Type*) [Fintype α] (P : α → Bool) :
    (uniformFinDist α).acceptWeight P = ∑ x : α, bitToInt (P x) := by
  simp [uniformFinDist, FinDist.acceptWeight]

lemma FinDist.acceptWeight_nonneg {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) :
    0 ≤ dist.acceptWeight P := by
  dsimp [FinDist.acceptWeight]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (Int.natCast_nonneg _) (bitToInt_nonneg _))

lemma FinDist.acceptWeight_le_totalMass {α : Type*} [Fintype α]
    (dist : FinDist α) (P : α → Bool) :
    dist.acceptWeight P ≤ (dist.totalMass : ℤ) := by
  dsimp [FinDist.acceptWeight, FinDist.totalMass]
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_of_le_one_right (Int.natCast_nonneg _) (bitToInt_le_one _)

lemma FinDist.acceptWeight_not {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) :
    dist.acceptWeight (fun x => !(P x)) = (dist.totalMass : ℤ) - dist.acceptWeight P := by
  dsimp [FinDist.acceptWeight, FinDist.totalMass]
  simp_rw [bitToInt_not, mul_sub, mul_one, Finset.sum_sub_distrib, ← Nat.cast_sum]

def FinDist.prod {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) : FinDist (α × β) :=
  { weight := fun p => d1.weight p.1 * d2.weight p.2 }

theorem FinDist.totalMass_prod {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) :
    (d1.prod d2).totalMass = d1.totalMass * d2.totalMass := by
  dsimp [FinDist.totalMass, FinDist.prod]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

lemma FinDist.totalMass_prod_pos {α β : Type*} [Fintype α] [Fintype β]
    {d1 : FinDist α} {d2 : FinDist β}
    (h1 : 0 < d1.totalMass) (h2 : 0 < d2.totalMass) :
    0 < (d1.prod d2).totalMass := by
  rw [FinDist.totalMass_prod]
  exact Nat.mul_pos h1 h2

theorem uniformFinDist_prod (α β : Type*) [Fintype α] [Fintype β] :
    uniformFinDist (α × β) = (uniformFinDist α).prod (uniformFinDist β) := by
  dsimp [uniformFinDist, FinDist.prod]

theorem FinDist.acceptWeight_prod_left {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (P : α × β → Bool) :
    (d1.prod d2).acceptWeight P =
      ∑ a : α, (d1.weight a : ℤ) * d2.acceptWeight (fun b => P (a, b)) := by
  dsimp [FinDist.acceptWeight, FinDist.prod]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  push_cast
  ring

theorem FinDist.acceptWeight_prod_right {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (P : α × β → Bool) :
    (d1.prod d2).acceptWeight P =
      ∑ b : β, (d2.weight b : ℤ) * d1.acceptWeight (fun a => P (a, b)) := by
  dsimp [FinDist.acceptWeight, FinDist.prod]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

def FinDist.prob {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) : ℚ :=
  (dist.acceptWeight P : ℚ) / (dist.totalMass : ℚ)

def FinDist.eventProb {α : Type*} [Fintype α]
    (dist : FinDist α) (E : α → Prop) [DecidablePred E] : ℚ :=
  (dist.eventMass E : ℚ) / (dist.totalMass : ℚ)

lemma FinDist.prob_nonneg {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) :
    0 ≤ dist.prob P := by
  dsimp [FinDist.prob]
  exact div_nonneg (Int.cast_nonneg (dist.acceptWeight_nonneg P)) (Nat.cast_nonneg _)

lemma FinDist.prob_le_one {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) :
    dist.prob P ≤ 1 := by
  by_cases h0 : dist.totalMass = 0
  · simp [FinDist.prob, h0]
  · have hm : (0 : ℚ) < (dist.totalMass : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    rw [FinDist.prob, div_le_one hm]
    exact_mod_cast dist.acceptWeight_le_totalMass P

lemma FinDist.eventProb_nonneg {α : Type*} [Fintype α]
    (dist : FinDist α) (E : α → Prop) [DecidablePred E] :
    0 ≤ dist.eventProb E := by
  dsimp [FinDist.eventProb]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma FinDist.eventProb_le_one {α : Type*} [Fintype α]
    (dist : FinDist α) (E : α → Prop) [DecidablePred E] :
    dist.eventProb E ≤ 1 := by
  have hle : dist.eventMass E ≤ dist.totalMass := by
    dsimp [FinDist.eventMass, FinDist.totalMass]
    apply Finset.sum_le_sum
    intro x _
    split_ifs <;> omega
  by_cases h0 : dist.totalMass = 0
  · simp [FinDist.eventProb, h0]
  · have hm : (0 : ℚ) < (dist.totalMass : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    rw [FinDist.eventProb, div_le_one hm]
    exact_mod_cast hle

theorem FinDist.prob_eq_eventProb {α : Type*} [Fintype α]
    (dist : FinDist α) (P : α → Bool) :
    dist.prob P = dist.eventProb (fun x => P x = true) := by
  dsimp [FinDist.prob, FinDist.eventProb]
  have hw : dist.acceptWeight P = (dist.eventMass (fun x => P x = true) : ℤ) := by
    dsimp [FinDist.acceptWeight, FinDist.eventMass]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = true <;> simp [hx, bitToInt]
  rw [hw]
  push_cast
  rfl

theorem FinDist.prob_const_true {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) :
    dist.prob (fun _ => true) = 1 := by
  dsimp [FinDist.prob]
  have hw : dist.acceptWeight (fun _ => true) = (dist.totalMass : ℤ) := by
    dsimp [FinDist.acceptWeight, FinDist.totalMass, bitToInt]
    simp [Nat.cast_sum]
  rw [hw]
  push_cast
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_pos))

theorem FinDist.prob_const_false {α : Type*} [Fintype α] (dist : FinDist α) :
    dist.prob (fun _ => false) = 0 := by
  simp [FinDist.prob, FinDist.acceptWeight, bitToInt]

theorem FinDist.prob_not {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (P : α → Bool) :
    dist.prob (fun x => !(P x)) = 1 - dist.prob P := by
  dsimp [FinDist.prob]
  rw [dist.acceptWeight_not]
  push_cast
  have hne : (dist.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_pos)
  rw [sub_div, div_self hne]

theorem prob_uniform_comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : β → Bool) :
    (uniformFinDist α).prob (fun a => P (e a)) = (uniformFinDist β).prob P := by
  dsimp [FinDist.prob]
  rw [uniformFinDist_totalMass, uniformFinDist_totalMass]
  rw [uniformFinDist_acceptWeight, uniformFinDist_acceptWeight]
  rw [Fintype.card_congr e, Equiv.sum_comp e (fun b => bitToInt (P b))]

theorem prob_uniform_add_right {G : Type*} [AddGroup G] [Fintype G]
    (μ : G) (P : G → Bool) :
    (uniformFinDist G).prob (fun x => P (x + μ)) = (uniformFinDist G).prob P :=
  prob_uniform_comp_equiv (Equiv.addRight μ) P

theorem prob_uniform_bool_id : (uniformFinDist Bool).prob id = 1 / 2 := by
  norm_num [FinDist.prob, uniformFinDist, FinDist.acceptWeight, FinDist.totalMass, bitToInt]

theorem prob_uniform_pad_guess_eq_half {α G : Type*}
    [Fintype α] [AddGroup G] [Fintype G] [Nonempty G]
    (d : FinDist α) (h_pos : 0 < d.totalMass)
    (μ0 μ1 : α → G) (A : α → G → Bool) :
    ((d.prod (uniformFinDist G)).prod (uniformFinDist Bool)).prob
      (fun x => A x.1.1 (x.1.2 + if x.2 then μ1 x.1.1 else μ0 x.1.1) == x.2) = 1 / 2 := by
  have hm :
      ((d.prod (uniformFinDist G)).prod (uniformFinDist Bool)).totalMass =
        d.totalMass * Fintype.card G * 2 := by
    rw [FinDist.totalMass_prod, FinDist.totalMass_prod]
    rw [uniformFinDist_totalMass, uniformFinDist_totalMass]
    simp
  have hw :
      ((d.prod (uniformFinDist G)).prod (uniformFinDist Bool)).acceptWeight
        (fun x => A x.1.1 (x.1.2 + if x.2 then μ1 x.1.1 else μ0 x.1.1) == x.2) =
        (d.totalMass : ℤ) * (Fintype.card G : ℤ) := by
    rw [FinDist.acceptWeight_prod_right]
    have h_inner :
        ∀ b : Bool,
          (uniformFinDist Bool).weight b = 1 ∧
          (d.prod (uniformFinDist G)).acceptWeight
              (fun ag => A ag.1 (ag.2 + if b then μ1 ag.1 else μ0 ag.1) == b) =
            ∑ a : α, (d.weight a : ℤ) * ∑ g : G, bitToInt (A a g == b) := by
      intro b
      refine ⟨rfl, ?_⟩
      rw [FinDist.acceptWeight_prod_left]
      apply Finset.sum_congr rfl
      intro a _
      rw [uniformFinDist_acceptWeight]
      dsimp only
      have h_shift :
          (∑ x : G, bitToInt (A a (x + if b then μ1 a else μ0 a) == b)) =
            ∑ g : G, bitToInt (A a g == b) :=
        Equiv.sum_comp (Equiv.addRight (if b then μ1 a else μ0 a)) (fun g => bitToInt (A a g == b))
      rw [h_shift]
    have h_sum_b :
        (∑ b : Bool, ((uniformFinDist Bool).weight b : ℤ) *
          (d.prod (uniformFinDist G)).acceptWeight
            (fun ag => A ag.1 (ag.2 + if b then μ1 ag.1 else μ0 ag.1) == b)) =
          ∑ b : Bool, ∑ a : α, (d.weight a : ℤ) * ∑ g : G, bitToInt (A a g == b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [(h_inner b).1, (h_inner b).2]
      ring
    rw [h_sum_b, Finset.sum_comm]
    have h_term :
        ∀ a : α,
          (∑ b : Bool, (d.weight a : ℤ) * ∑ g : G, bitToInt (A a g == b)) =
            (d.weight a : ℤ) * (Fintype.card G : ℤ) := by
      intro a
      rw [← Finset.mul_sum, Finset.sum_comm]
      have h_g : ∀ g : G, (∑ b : Bool, bitToInt (A a g == b)) = 1 := by
        intro g
        rw [Fintype.sum_bool]
        cases A a g <;> simp [bitToInt]
      simp_rw [h_g, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [h_term, ← Finset.sum_mul, FinDist.totalMass, Nat.cast_sum]
  dsimp [FinDist.prob]
  rw [hw, hm]
  push_cast
  have h1 : (d.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_pos)
  have h2 : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  field_simp

private lemma int_natAbs_eq_abs (z : ℤ) : (z.natAbs : ℤ) = |z| := by
  rcases le_total 0 z with h | h
  · rw [abs_of_nonneg h]
    omega
  · rw [abs_of_nonpos h]
    omega

private lemma int_natAbs_rat_eq_abs (z : ℤ) : (z.natAbs : ℚ) = |(z : ℚ)| := by
  have h : ((z.natAbs : ℤ) : ℚ) = ((|z| : ℤ) : ℚ) := congrArg Int.cast (int_natAbs_eq_abs z)
  rwa [Int.cast_natCast, Int.cast_abs] at h

theorem FinDist.abs_prob_sub_le_eventProb {α : Type*} [Fintype α]
    (dist : FinDist α) (P1 P2 : α → Bool) (E : α → Prop) [DecidablePred E]
    (h_agree : ∀ x : α, ¬ E x → P1 x = P2 x) :
    |dist.prob P1 - dist.prob P2| ≤ dist.eventProb E := by
  by_cases h0 : dist.totalMass = 0
  · simp [FinDist.prob, FinDist.eventProb, h0]
  · have hm : (0 : ℚ) < (dist.totalMass : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have h_diff := FinDist.difference_lemma dist P1 P2 E h_agree
    have h_abs_rat := int_natAbs_rat_eq_abs (dist.acceptWeight P1 - dist.acceptWeight P2)
    dsimp [FinDist.prob, FinDist.eventProb]
    rw [← sub_div, abs_div, abs_of_pos hm]
    push_cast at h_abs_rat
    rw [← h_abs_rat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast h_diff) (le_of_lt hm)

theorem FinDist.prob_prod_eq_sum_left {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (P : α × β → Bool) :
    (d1.prod d2).prob P =
      (∑ a : α, (d1.weight a : ℚ) * d2.prob (fun b => P (a, b))) / (d1.totalMass : ℚ) := by
  by_cases h1 : d1.totalMass = 0
  · have h_w0 : ∀ a : α, d1.weight a = 0 := by
      dsimp [FinDist.totalMass] at h1
      intro a
      exact (Finset.sum_eq_zero_iff.mp h1) a (Finset.mem_univ a)
    simp [FinDist.prob, FinDist.totalMass_prod, h1, h_w0]
  · by_cases h2 : d2.totalMass = 0
    · simp [FinDist.prob, FinDist.totalMass_prod, h2]
    · have hm1 : (d1.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h1
      have hm2 : (d2.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h2
      dsimp [FinDist.prob]
      rw [FinDist.acceptWeight_prod_left, FinDist.totalMass_prod]
      push_cast
      rw [Finset.sum_div]
      have h_term :
          ∀ a : α,
            (d1.weight a : ℚ) * (d2.acceptWeight (fun b => P (a, b)) : ℚ) /
                ((d1.totalMass : ℚ) * (d2.totalMass : ℚ)) =
              (d1.weight a : ℚ) *
                ((d2.acceptWeight (fun b => P (a, b)) : ℚ) / (d2.totalMass : ℚ)) /
                (d1.totalMass : ℚ) := by
        intro a
        field_simp
      simp_rw [h_term, ← Finset.sum_div]

theorem FinDist.prob_prod_eq_sum_right {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (P : α × β → Bool) :
    (d1.prod d2).prob P =
      (∑ b : β, (d2.weight b : ℚ) * d1.prob (fun a => P (a, b))) / (d2.totalMass : ℚ) := by
  by_cases h2 : d2.totalMass = 0
  · have h_w0 : ∀ b : β, d2.weight b = 0 := by
      dsimp [FinDist.totalMass] at h2
      intro b
      exact (Finset.sum_eq_zero_iff.mp h2) b (Finset.mem_univ b)
    simp [FinDist.prob, FinDist.totalMass_prod, h2, h_w0]
  · by_cases h1 : d1.totalMass = 0
    · simp [FinDist.prob, FinDist.totalMass_prod, h1]
    · have hm1 : (d1.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h1
      have hm2 : (d2.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr h2
      dsimp [FinDist.prob]
      rw [FinDist.acceptWeight_prod_right, FinDist.totalMass_prod]
      push_cast
      rw [Finset.sum_div]
      have h_term :
          ∀ b : β,
            (d2.weight b : ℚ) * (d1.acceptWeight (fun a => P (a, b)) : ℚ) /
                ((d1.totalMass : ℚ) * (d2.totalMass : ℚ)) =
              (d2.weight b : ℚ) *
                ((d1.acceptWeight (fun a => P (a, b)) : ℚ) / (d1.totalMass : ℚ)) /
                (d2.totalMass : ℚ) := by
        intro b
        field_simp
      simp_rw [h_term, ← Finset.sum_div]

private lemma rat_abs_sum_le {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    |∑ i : ι, f i| ≤ ∑ i : ι, |f i| := by
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact le_trans (abs_add_le (f a) (∑ x ∈ s, f x)) (add_le_add le_rfl ih)

theorem FinDist.abs_prob_prod_sub_le_avg {γ α β : Type*}
    [Fintype γ] [Fintype α] [Fintype β]
    (d_env : FinDist γ) (d1 : FinDist α) (d2 : FinDist β)
    (F1 : γ → α → Bool) (F2 : γ → β → Bool) :
    |(d_env.prod d1).prob (fun p => F1 p.1 p.2) -
        (d_env.prod d2).prob (fun p => F2 p.1 p.2)| ≤
      (∑ c : γ, (d_env.weight c : ℚ) * |d1.prob (F1 c) - d2.prob (F2 c)|) /
        (d_env.totalMass : ℚ) := by
  by_cases h0 : d_env.totalMass = 0
  · have h_w0 : ∀ c : γ, d_env.weight c = 0 := by
      dsimp [FinDist.totalMass] at h0
      intro c
      exact (Finset.sum_eq_zero_iff.mp h0) c (Finset.mem_univ c)
    simp [FinDist.prob, FinDist.totalMass_prod, h0, h_w0]
  · have hm : (0 : ℚ) < (d_env.totalMass : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    rw [FinDist.prob_prod_eq_sum_left, FinDist.prob_prod_eq_sum_left]
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hm]
    have h_eq :
        (∑ c : γ, ((d_env.weight c : ℚ) * d1.prob (F1 c) -
            (d_env.weight c : ℚ) * d2.prob (F2 c))) =
          ∑ c : γ, (d_env.weight c : ℚ) * (d1.prob (F1 c) - d2.prob (F2 c)) := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [h_eq]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hm)
    refine le_trans (rat_abs_sum_le _) ?_
    apply Finset.sum_le_sum
    intro c _
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]

theorem FinDist.exists_coin_ge_abs_prob_prod_sub {γ α β : Type*}
    [Fintype γ] [Fintype α] [Fintype β]
    (d_env : FinDist γ) (h_pos : 0 < d_env.totalMass)
    (d1 : FinDist α) (d2 : FinDist β)
    (F1 : γ → α → Bool) (F2 : γ → β → Bool) :
    ∃ c : γ,
      |(d_env.prod d1).prob (fun p => F1 p.1 p.2) -
          (d_env.prod d2).prob (fun p => F2 p.1 p.2)| ≤
        |d1.prob (F1 c) - d2.prob (F2 c)| := by
  have h_ne : (Finset.univ : Finset γ).Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    dsimp [FinDist.totalMass] at h_pos
    rw [h_empty, Finset.sum_empty] at h_pos
    omega
  obtain ⟨c, _, hc_max⟩ := Finset.exists_max_image (Finset.univ : Finset γ)
    (fun x => |d1.prob (F1 x) - d2.prob (F2 x)|) h_ne
  refine ⟨c, le_trans (d_env.abs_prob_prod_sub_le_avg d1 d2 F1 F2) ?_⟩
  have hm : (0 : ℚ) < (d_env.totalMass : ℚ) := Nat.cast_pos.mpr h_pos
  rw [div_le_iff₀ hm]
  have h_sum_le :
      (∑ x : γ, (d_env.weight x : ℚ) * |d1.prob (F1 x) - d2.prob (F2 x)|) ≤
        ∑ x : γ, (d_env.weight x : ℚ) * |d1.prob (F1 c) - d2.prob (F2 c)| := by
    apply Finset.sum_le_sum
    intro x hx
    exact mul_le_mul_of_nonneg_left (hc_max x hx) (Nat.cast_nonneg _)
  have h_rhs :
      (∑ x : γ, (d_env.weight x : ℚ) * |d1.prob (F1 c) - d2.prob (F2 c)|) =
        |d1.prob (F1 c) - d2.prob (F2 c)| * (d_env.totalMass : ℚ) := by
    rw [← Finset.sum_mul, mul_comm]
    dsimp [FinDist.totalMass]
    rw [Nat.cast_sum]
  exact h_rhs ▸ h_sum_le

theorem eventProb_uniform_mem_finset_le {M : Type*} [Fintype M] [DecidableEq M]
    (q_bound : ℕ) (S : Finset M) (hS : S.card ≤ q_bound) :
    (uniformFinDist M).eventProb (fun m => m ∈ S) ≤ (q_bound : ℚ) / (Fintype.card M : ℚ) := by
  dsimp [FinDist.eventProb]
  rw [uniformFinDist_totalMass]
  have h_mass : (uniformFinDist M).eventMass (fun m => m ∈ S) = S.card := by
    dsimp [FinDist.eventMass, uniformFinDist]
    simp [Finset.sum_ite_mem]
  rw [h_mass]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hS) (Nat.cast_nonneg _)

theorem eventProb_prod_uniform_mem_finset_le {α M : Type*}
    [Fintype α] [Fintype M] [DecidableEq M]
    (d : FinDist α) (q_bound : ℕ)
    (S : α → Finset M) (hS : ∀ a : α, (S a).card ≤ q_bound) :
    (d.prod (uniformFinDist M)).eventProb (fun p => p.2 ∈ S p.1) ≤
      (q_bound : ℚ) / (Fintype.card M : ℚ) := by
  have h_mass_le : (d.prod (uniformFinDist M)).eventMass (fun p => p.2 ∈ S p.1) ≤
      d.totalMass * q_bound := by
    dsimp [FinDist.eventMass, FinDist.prod, uniformFinDist, FinDist.totalMass]
    rw [Fintype.sum_prod_type]
    have h_inner : ∀ a : α,
        (∑ m : M, if m ∈ S a then d.weight a * 1 else 0) = d.weight a * (S a).card := by
      intro a
      simp_rw [mul_one, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter, mul_comm]
    simp_rw [h_inner]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    exact Nat.mul_le_mul_left (d.weight a) (hS a)
  by_cases h0 : (d.prod (uniformFinDist M)).totalMass = 0
  · rw [FinDist.eventProb, h0]
    simp only [Nat.cast_zero, div_zero]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have hm : (0 : ℚ) < ((d.prod (uniformFinDist M)).totalMass : ℚ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have h_prod : (d.prod (uniformFinDist M)).totalMass = d.totalMass * Fintype.card M := by
      rw [FinDist.totalMass_prod, uniformFinDist_totalMass]
    have hd0 : d.totalMass ≠ 0 := by
      intro hd
      rw [hd, zero_mul] at h_prod
      exact h0 h_prod
    have hdm : (d.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
    rw [FinDist.eventProb, h_prod]
    push_cast
    have h_div :
        (((d.prod (uniformFinDist M)).eventMass (fun p => p.2 ∈ S p.1) : ℚ) /
            ((d.totalMass : ℚ) * (Fintype.card M : ℚ))) ≤
          ((d.totalMass : ℚ) * (q_bound : ℚ)) / ((d.totalMass : ℚ) * (Fintype.card M : ℚ)) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast h_mass_le
      · positivity
    have h_cancel :
        ((d.totalMass : ℚ) * (q_bound : ℚ)) / ((d.totalMass : ℚ) * (Fintype.card M : ℚ)) =
          (q_bound : ℚ) / (Fintype.card M : ℚ) := by
      rw [mul_div_mul_left _ _ hdm]
    exact h_cancel ▸ h_div

theorem abs_prob_dlwe_eq_div (params : LWEParams) [NeZero params.q]
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (h_mass : 0 < seDist.totalMass)
    (D_dlwe : Sample (Zq params) params.n params.m → Bool) :
    |seDist.prob (fun se => D_dlwe (mkSample (Zq params) params.n params.m A se.1 se.2)) -
        (uniformFinDist (VectorR (Zq params) params.m)).prob
          (fun u => D_dlwe { A := A, b := u })| =
      (DLWEAdvantage params A seDist D_dlwe : ℚ) /
        ((Fintype.card (VectorR (Zq params) params.m) : ℚ) * (seDist.totalMass : ℚ)) := by
  have h_card_pos : 0 < Fintype.card (VectorR (Zq params) params.m) := by
    haveI : Nonempty (VectorR (Zq params) params.m) := ⟨fun _ => 0⟩
    exact Fintype.card_pos
  have hc : (0 : ℚ) < (Fintype.card (VectorR (Zq params) params.m) : ℚ) :=
    Nat.cast_pos.mpr h_card_pos
  have hm : (0 : ℚ) < (seDist.totalMass : ℚ) := Nat.cast_pos.mpr h_mass
  dsimp [FinDist.prob, DLWEAdvantage]
  rw [uniformFinDist_totalMass, uniformFinDist_acceptWeight]
  have h_abs_rat := int_natAbs_rat_eq_abs
    ((Fintype.card (VectorR (Zq params) params.m) : ℤ) *
        seDist.acceptWeight
          (fun se => D_dlwe (mkSample (Zq params) params.n params.m A se.1 se.2)) -
      (seDist.totalMass : ℤ) *
        ∑ u : VectorR (Zq params) params.m, bitToInt (D_dlwe { A := A, b := u }))
  rw [h_abs_rat, ← abs_of_pos (mul_pos hc hm), ← abs_div]
  push_cast
  congr 1
  field_simp

theorem abs_prob_regev_ind_cpa_eq_div (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (h_mass : 0 < seDist.totalMass)
    (msg0 msg1 : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) :
    |seDist.prob
          (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2)
            msg0)) -
        seDist.prob
          (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2)
            msg1))| =
      (INDCPAAdvantage params Δ A seDist msg0 msg1 D : ℚ) /
        ((Fintype.card (VectorR (Zq params) params.m) : ℚ) * (seDist.totalMass : ℚ)) := by
  have h_card_pos : 0 < Fintype.card (VectorR (Zq params) params.m) := by
    haveI : Nonempty (VectorR (Zq params) params.m) := ⟨fun _ => 0⟩
    exact Fintype.card_pos
  have hc : (0 : ℚ) < (Fintype.card (VectorR (Zq params) params.m) : ℚ) :=
    Nat.cast_pos.mpr h_card_pos
  have hm : (0 : ℚ) < (seDist.totalMass : ℚ) := Nat.cast_pos.mpr h_mass
  dsimp [FinDist.prob, INDCPAAdvantage]
  have h_abs_rat := int_natAbs_rat_eq_abs
    ((Fintype.card (VectorR (Zq params) params.m) : ℤ) *
        seDist.acceptWeight
          (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2)
            msg0)) -
      (Fintype.card (VectorR (Zq params) params.m) : ℤ) *
        seDist.acceptWeight
          (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2)
            msg1)))
  rw [h_abs_rat, ← abs_of_pos (mul_pos hc hm), ← abs_div]
  push_cast
  congr 1
  field_simp

theorem regev_rational_ind_cpa_to_dlwe (params : LWEParams) (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (h_mass : 0 < seDist.totalMass)
    (msg0 msg1 : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) :
    |seDist.prob
          (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2)
            msg0)) -
        seDist.prob
          (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2)
            msg1))| ≤
      |seDist.prob
            (fun se => regevShiftedDistinguisher params Δ msg0 D
              (mkSample (Zq params) params.n params.m A se.1 se.2)) -
          (uniformFinDist (VectorR (Zq params) params.m)).prob
            (fun u => regevShiftedDistinguisher params Δ msg0 D { A := A, b := u })| +
        |seDist.prob
            (fun se => regevShiftedDistinguisher params Δ msg1 D
              (mkSample (Zq params) params.n params.m A se.1 se.2)) -
          (uniformFinDist (VectorR (Zq params) params.m)).prob
            (fun u => regevShiftedDistinguisher params Δ msg1 D { A := A, b := u })| := by
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h_card_pos : 0 < Fintype.card (VectorR (Zq params) params.m) := by
    haveI : Nonempty (VectorR (Zq params) params.m) := ⟨fun _ => 0⟩
    exact Fintype.card_pos
  have h_denom_pos :
      (0 : ℚ) < (Fintype.card (VectorR (Zq params) params.m) : ℚ) * (seDist.totalMass : ℚ) :=
    mul_pos (Nat.cast_pos.mpr h_card_pos) (Nat.cast_pos.mpr h_mass)
  rw [abs_prob_regev_ind_cpa_eq_div params Δ A seDist h_mass msg0 msg1 D]
  rw [abs_prob_dlwe_eq_div params A seDist h_mass (regevShiftedDistinguisher params Δ msg0 D)]
  rw [abs_prob_dlwe_eq_div params A seDist h_mass (regevShiftedDistinguisher params Δ msg1 D)]
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (le_of_lt h_denom_pos)
  exact_mod_cast regev_ind_cpa_to_dlwe_reduction params Δ A seDist msg0 msg1 D

end RationalFinDist

section ModuleLWEAndStacking

open scoped BigOperators

def FinDist.equivMap {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (d : FinDist α) : FinDist β :=
  { weight := fun b => d.weight (e.symm b) }

theorem FinDist.totalMass_equivMap {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (d : FinDist α) :
    (d.equivMap e).totalMass = d.totalMass := by
  dsimp [FinDist.totalMass, FinDist.equivMap]
  exact Equiv.sum_comp e.symm (fun a => d.weight a)

theorem FinDist.acceptWeight_equivMap {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (d : FinDist α) (P : β → Bool) :
    (d.equivMap e).acceptWeight P = d.acceptWeight (fun a => P (e a)) := by
  dsimp [FinDist.acceptWeight, FinDist.equivMap]
  have h1 := Equiv.sum_comp e (fun b => (d.weight (e.symm b) : ℤ) * bitToInt (P b))
  rw [← h1]
  apply Finset.sum_congr rfl
  intro a _
  rw [e.symm_apply_apply]

theorem FinDist.prob_equivMap {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (d : FinDist α) (P : β → Bool) :
    (d.equivMap e).prob P = d.prob (fun a => P (e a)) := by
  dsimp [FinDist.prob]
  rw [FinDist.acceptWeight_equivMap, FinDist.totalMass_equivMap]

theorem uniformFinDist_equivMap {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) :
    (uniformFinDist α).equivMap e = uniformFinDist β := rfl

theorem FinDist.prod_equivMap {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
    (e1 : α₁ ≃ β₁) (e2 : α₂ ≃ β₂) (d1 : FinDist α₁) (d2 : FinDist α₂) :
    (d1.equivMap e1).prod (d2.equivMap e2) =
      (d1.prod d2).equivMap (Equiv.prodCongr e1 e2) := rfl

theorem FinDist.equivMap_refl {α : Type*} [Fintype α] (d : FinDist α) :
    d.equivMap (Equiv.refl α) = d := rfl

theorem prob_prod_uniform_left_equiv {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (e : α ≃ β) (d : FinDist γ) (P : β × γ → Bool) :
    ((uniformFinDist α).prod d).prob (fun p => P (e p.1, p.2)) =
      ((uniformFinDist β).prod d).prob P := by
  conv_rhs =>
    rw [← uniformFinDist_equivMap e, ← FinDist.equivMap_refl d, FinDist.prod_equivMap,
      FinDist.prob_equivMap]
  rfl

def Sample.equivProd {R : Type*} {n m : ℕ} :
    Sample R n m ≃ (MatrixR R n m × VectorR R m) where
  toFun s := (s.A, s.b)
  invFun p := { A := p.1, b := p.2 }
  left_inv s := by cases s; rfl
  right_inv p := by cases p; rfl

instance instDecidableEqSample {R : Type*} {n m : ℕ} [DecidableEq R] :
    DecidableEq (Sample R n m) :=
  fun s1 s2 =>
    decidable_of_iff (Sample.equivProd s1 = Sample.equivProd s2) Sample.equivProd.injective.eq_iff

instance instFintypeSample {R : Type*} {n m : ℕ} [Fintype R] :
    Fintype (Sample R n m) :=
  Fintype.ofEquiv (MatrixR R n m × VectorR R m) Sample.equivProd.symm

def ModPKEPublicKey.equivProd {R : Type*} {k : ℕ} :
    ModPKEPublicKey R k ≃ (MatrixR R k k × VectorR R k) where
  toFun pk := (pk.A, pk.t)
  invFun p := { A := p.1, t := p.2 }
  left_inv pk := by cases pk; rfl
  right_inv p := by cases p; rfl

def ModPKEPublicKey.equivSample {R : Type*} {k : ℕ} :
    ModPKEPublicKey R k ≃ Sample R k k :=
  ModPKEPublicKey.equivProd.trans Sample.equivProd.symm

instance instDecidableEqModPKEPublicKey {R : Type*} {k : ℕ} [DecidableEq R] :
    DecidableEq (ModPKEPublicKey R k) :=
  fun pk1 pk2 =>
    decidable_of_iff (ModPKEPublicKey.equivProd pk1 = ModPKEPublicKey.equivProd pk2)
      ModPKEPublicKey.equivProd.injective.eq_iff

instance instFintypeModPKEPublicKey {R : Type*} {k : ℕ} [Fintype R] :
    Fintype (ModPKEPublicKey R k) :=
  Fintype.ofEquiv (MatrixR R k k × VectorR R k) ModPKEPublicKey.equivProd.symm

theorem modPKEKeygen_eq_equivSample_symm (R : Type*) [CommRing R] (k : ℕ)
    (A : MatrixR R k k) (s e : VectorR R k) :
    modPKEKeygen R k A s e = ModPKEPublicKey.equivSample.symm (mkSample R k k A s e) := rfl

def mlweRealDist (R : Type*) [Fintype R] (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m)) :
    FinDist (MatrixR R n m × (VectorR R n × VectorR R m)) :=
  (uniformFinDist (MatrixR R n m)).prod seDist

def mlweRealProb (R : Type*) [CommRing R] [Fintype R] (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m)) (D : Sample R n m → Bool) : ℚ :=
  (mlweRealDist R n m seDist).prob (fun p => D (mkSample R n m p.1 p.2.1 p.2.2))

def mlweUniformProb (R : Type*) [Fintype R] (n m : ℕ) (D : Sample R n m → Bool) : ℚ :=
  (uniformFinDist (Sample R n m)).prob D

theorem mlweUniformProb_eq_prod (R : Type*) [Fintype R] (n m : ℕ) (D : Sample R n m → Bool) :
    mlweUniformProb R n m D =
      ((uniformFinDist (MatrixR R n m)).prod (uniformFinDist (VectorR R m))).prob
        (fun p => D { A := p.1, b := p.2 }) := by
  dsimp [mlweUniformProb]
  have h_eq := prob_uniform_comp_equiv
    (Sample.equivProd.symm : MatrixR R n m × VectorR R m ≃ Sample R n m) D
  rw [← h_eq, uniformFinDist_prod]
  rfl

def mlweAdvantage (R : Type*) [CommRing R] [Fintype R] (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m)) (D : Sample R n m → Bool) : ℚ :=
  |mlweRealProb R n m seDist D - mlweUniformProb R n m D|

lemma mlweAdvantage_nonneg (R : Type*) [CommRing R] [Fintype R] (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m)) (D : Sample R n m → Bool) :
    0 ≤ mlweAdvantage R n m seDist D :=
  abs_nonneg _

lemma mlweAdvantage_le_one (R : Type*) [CommRing R] [Fintype R] (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m)) (D : Sample R n m → Bool) :
    mlweAdvantage R n m seDist D ≤ 1 := by
  have hr0 := FinDist.prob_nonneg (mlweRealDist R n m seDist)
    (fun p => D (mkSample R n m p.1 p.2.1 p.2.2))
  have hr1 := FinDist.prob_le_one (mlweRealDist R n m seDist)
    (fun p => D (mkSample R n m p.1 p.2.1 p.2.2))
  have hu0 := FinDist.prob_nonneg (uniformFinDist (Sample R n m)) D
  have hu1 := FinDist.prob_le_one (uniformFinDist (Sample R n m)) D
  rw [mlweAdvantage, abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add.mpr (le_add_of_le_of_nonneg hr1 hu0),
    sub_le_iff_le_add.mpr (le_add_of_le_of_nonneg hu1 hr0)⟩

theorem mlweAdvantage_zq_le_avg_dlweAdvantage (params : LWEParams) [NeZero params.q]
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (h_mass : 0 < seDist.totalMass)
    (D : Sample (Zq params) params.n params.m → Bool) :
    mlweAdvantage (Zq params) params.n params.m seDist D ≤
      (∑ A : MatrixR (Zq params) params.n params.m,
        (DLWEAdvantage params A seDist D : ℚ) /
          ((Fintype.card (VectorR (Zq params) params.m) : ℚ) * (seDist.totalMass : ℚ))) /
        (Fintype.card (MatrixR (Zq params) params.n params.m) : ℚ) := by
  dsimp [mlweAdvantage, mlweRealProb, mlweRealDist]
  rw [mlweUniformProb_eq_prod]
  have h_avg := FinDist.abs_prob_prod_sub_le_avg
    (uniformFinDist (MatrixR (Zq params) params.n params.m)) seDist
    (uniformFinDist (VectorR (Zq params) params.m))
    (fun A se => D (mkSample (Zq params) params.n params.m A se.1 se.2))
    (fun A u => D { A := A, b := u })
  refine le_trans h_avg ?_
  rw [uniformFinDist_totalMass]
  have h_sum :
      (∑ A : MatrixR (Zq params) params.n params.m,
        ((uniformFinDist (MatrixR (Zq params) params.n params.m)).weight A : ℚ) *
          |seDist.prob (fun se => D (mkSample (Zq params) params.n params.m A se.1 se.2)) -
            (uniformFinDist (VectorR (Zq params) params.m)).prob (fun u => D { A := A, b := u })|) =
        ∑ A : MatrixR (Zq params) params.n params.m,
          (DLWEAdvantage params A seDist D : ℚ) /
            ((Fintype.card (VectorR (Zq params) params.m) : ℚ) * (seDist.totalMass : ℚ)) := by
    apply Finset.sum_congr rfl
    intro A _
    have hw : ((uniformFinDist (MatrixR (Zq params) params.n params.m)).weight A : ℚ) = 1 := rfl
    rw [hw, one_mul, abs_prob_dlwe_eq_div params A seDist h_mass D]
  rw [h_sum]

def splitVecLastEquiv (R : Type*) (k : ℕ) : (VectorR R k × R) ≃ VectorR R (k + 1) where
  toFun p := Fin.snoc p.1 p.2
  invFun w := (Fin.init w, w (Fin.last k))
  left_inv p := by
    cases p
    apply Prod.ext <;> dsimp <;> simp [Fin.init_snoc, Fin.snoc_last]
  right_inv w := Fin.snoc_init_self w

def stackTransposeVecEquiv (R : Type*) (k : ℕ) :
    (MatrixR R k k × VectorR R k) ≃ MatrixR R k (k + 1) where
  toFun p := Fin.snoc (transposeMatrix R p.1) p.2
  invFun M := (transposeMatrix R (Fin.init M), M (Fin.last k))
  left_inv p := by
    cases p with
    | mk A t =>
      apply Prod.ext
      · dsimp
        ext i j
        simp [transposeMatrix, Fin.init_snoc]
      · dsimp
        simp [Fin.snoc_last]
  right_inv M := by
    change Fin.snoc (transposeMatrix R (transposeMatrix R (Fin.init M))) (M (Fin.last k)) = M
    have h_tr : transposeMatrix R (transposeMatrix R (Fin.init M)) = Fin.init M := rfl
    rw [h_tr]
    exact Fin.snoc_init_self M

theorem evaluate_stackTransposeVec (R : Type*) [CommRing R] (k : ℕ)
    (A : MatrixR R k k) (t r e1 : VectorR R k) (e2 : R) :
    evaluate R k (k + 1) (stackTransposeVecEquiv R k (A, t)) r
        (splitVecLastEquiv R k (e1, e2)) =
      splitVecLastEquiv R k
        (evaluate R k k (transposeMatrix R A) r e1, dotProductR R k t r + e2) := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [evaluate, dotProductR, stackTransposeVecEquiv, splitVecLastEquiv]
  · intro j
    simp [evaluate, stackTransposeVecEquiv, splitVecLastEquiv]

def modPKEPublicKeyOfMatrix (R : Type*) (k : ℕ) (M : MatrixR R k (k + 1)) :
    ModPKEPublicKey R k :=
  let p := (stackTransposeVecEquiv R k).symm M
  { A := p.1, t := p.2 }

lemma modPKEPublicKeyOfMatrix_stack (R : Type*) (k : ℕ)
    (A : MatrixR R k k) (t : VectorR R k) :
    modPKEPublicKeyOfMatrix R k (stackTransposeVecEquiv R k (A, t)) = { A := A, t := t } := by
  dsimp [modPKEPublicKeyOfMatrix]
  rw [Equiv.symm_apply_apply]

def modPKECiphertextOfVec (R : Type*) [Add R] (k : ℕ) (w : VectorR R (k + 1)) (μ : R) :
    ModPKECiphertext R k :=
  { u := Fin.init w, v := w (Fin.last k) + μ }

theorem modPKECiphertextOfVec_evaluate_eq_encrypt (R : Type*) [CommRing R] (k : ℕ)
    (A : MatrixR R k k) (t r e1 : VectorR R k) (e2 μ : R) :
    modPKECiphertextOfVec R k
        (mkSample R k (k + 1) (stackTransposeVecEquiv R k (A, t)) r
          (splitVecLastEquiv R k (e1, e2))).b μ =
      modPKEEncrypt R k { A := A, t := t } r e1 e2 μ := by
  dsimp [modPKECiphertextOfVec, mkSample, modPKEEncrypt]
  rw [evaluate_stackTransposeVec]
  dsimp [splitVecLastEquiv]
  rw [Fin.init_snoc, Fin.snoc_last]

lemma modPKECiphertextOfVec_split (R : Type*) [Add R] (k : ℕ)
    (u : VectorR R k) (v0 μ : R) :
    modPKECiphertextOfVec R k (splitVecLastEquiv R k (u, v0)) μ = { u := u, v := v0 + μ } := by
  dsimp [modPKECiphertextOfVec, splitVecLastEquiv]
  rw [Fin.init_snoc, Fin.snoc_last]

def modPKEEncSampleDist (R : Type*) [Fintype R] (k : ℕ)
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) :
    FinDist (VectorR R k × VectorR R (k + 1)) :=
  encDist.equivMap (Equiv.prodCongr (Equiv.refl (VectorR R k)) (splitVecLastEquiv R k))

lemma modPKEEncSampleDist_totalMass (R : Type*) [Fintype R] (k : ℕ)
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) :
    (modPKEEncSampleDist R k encDist).totalMass = encDist.totalMass :=
  FinDist.totalMass_equivMap _ encDist

def modPKEKeygenDistinguisher (R : Type*) (k : ℕ)
    (F : ModPKEPublicKey R k → Bool) (s : Sample R k k) : Bool :=
  F (ModPKEPublicKey.equivSample.symm s)

theorem prob_modPKE_keygen_eq_mlweRealProb (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (F : ModPKEPublicKey R k → Bool) :
    ((uniformFinDist (MatrixR R k k)).prod kgDist).prob
        (fun p => F (modPKEKeygen R k p.1 p.2.1 p.2.2)) =
      mlweRealProb R k k kgDist (modPKEKeygenDistinguisher R k F) := by
  dsimp [mlweRealProb, mlweRealDist, modPKEKeygenDistinguisher]
  rfl

theorem prob_modPKE_keygen_uniform_eq_mlweUniformProb (R : Type*) [Fintype R] (k : ℕ)
    (F : ModPKEPublicKey R k → Bool) :
    ((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prob
        (fun p => F { A := p.1, t := p.2 }) =
      mlweUniformProb R k k (modPKEKeygenDistinguisher R k F) := by
  rw [mlweUniformProb_eq_prod]
  rfl

def modPKEEncDistinguisher (R : Type*) [Add R] (k : ℕ) (μ : R)
    (G : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) (s : Sample R k (k + 1)) : Bool :=
  G (modPKEPublicKeyOfMatrix R k s.A) (modPKECiphertextOfVec R k s.b μ)

theorem prob_modPKE_enc_hybrid1_eq_mlweRealProb (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) (μ : R)
    (G : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod encDist).prob
        (fun p => G { A := p.1.1, t := p.1.2 }
          (modPKEEncrypt R k { A := p.1.1, t := p.1.2 } p.2.1 p.2.2.1 p.2.2.2 μ)) =
      mlweRealProb R k (k + 1) (modPKEEncSampleDist R k encDist)
        (modPKEEncDistinguisher R k μ G) := by
  let eL := stackTransposeVecEquiv R k
  let eR : (VectorR R k × (VectorR R k × R)) ≃ (VectorR R k × VectorR R (k + 1)) :=
    Equiv.prodCongr (Equiv.refl (VectorR R k)) (splitVecLastEquiv R k)
  dsimp [mlweRealProb, mlweRealDist, modPKEEncSampleDist]
  rw [← uniformFinDist_equivMap eL, FinDist.prod_equivMap eL eR]
  rw [FinDist.prob_equivMap, uniformFinDist_prod]
  refine congrArg _ ?_
  funext p
  rcases p with ⟨⟨A, t⟩, ⟨r, ⟨e1, e2⟩⟩⟩
  change G { A := A, t := t } (modPKEEncrypt R k { A := A, t := t } r e1 e2 μ) =
    G (modPKEPublicKeyOfMatrix R k (stackTransposeVecEquiv R k (A, t)))
      (modPKECiphertextOfVec R k
        (mkSample R k (k + 1) (stackTransposeVecEquiv R k (A, t)) r
          (splitVecLastEquiv R k (e1, e2))).b μ)
  rw [modPKEPublicKeyOfMatrix_stack, modPKECiphertextOfVec_evaluate_eq_encrypt]

theorem prob_modPKE_enc_hybrid2_eq_mlweUniformProb (R : Type*) [Add R] [Fintype R] (k : ℕ)
    (μ : R) (G : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
        ((uniformFinDist (VectorR R k)).prod (uniformFinDist R))).prob
        (fun p => G { A := p.1.1, t := p.1.2 } { u := p.2.1, v := p.2.2 + μ }) =
      mlweUniformProb R k (k + 1) (modPKEEncDistinguisher R k μ G) := by
  let e : ((MatrixR R k k × VectorR R k) × (VectorR R k × R)) ≃ Sample R k (k + 1) :=
    (Equiv.prodCongr (stackTransposeVecEquiv R k) (splitVecLastEquiv R k)).trans
      Sample.equivProd.symm
  dsimp [mlweUniformProb]
  rw [← prob_uniform_comp_equiv e]
  rw [uniformFinDist_prod, uniformFinDist_prod, uniformFinDist_prod]
  refine congrArg _ ?_
  funext p
  rcases p with ⟨⟨A, t⟩, ⟨u, v0⟩⟩
  change G { A := A, t := t } { u := u, v := v0 + μ } =
    G (modPKEPublicKeyOfMatrix R k (stackTransposeVecEquiv R k (A, t)))
      (modPKECiphertextOfVec R k (splitVecLastEquiv R k (u, v0)) μ)
  rw [modPKEPublicKeyOfMatrix_stack, modPKECiphertextOfVec_split]

end ModuleLWEAndStacking

section ModulePKESecurityReductions

open scoped BigOperators

private lemma FinDist.eventProb_congr {α : Type*} [Fintype α] (dist : FinDist α)
    (E1 E2 : α → Prop) [DecidablePred E1] [DecidablePred E2]
    (h_iff : ∀ x : α, E1 x ↔ E2 x) :
    dist.eventProb E1 = dist.eventProb E2 := by
  dsimp [FinDist.eventProb]
  rw [dist.eventMass_congr E1 E2 h_iff]

theorem FinDist.prod_assoc_eq {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (d1 : FinDist α) (d2 : FinDist β) (d3 : FinDist γ) :
    d1.prod (d2.prod d3) = ((d1.prod d2).prod d3).equivMap (Equiv.prodAssoc α β γ) := by
  dsimp [FinDist.prod, FinDist.equivMap, Equiv.prodAssoc]
  refine congrArg FinDist.mk ?_
  funext p
  exact (Nat.mul_assoc _ _ _).symm

theorem FinDist.prod_assoc_symm_eq {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (d1 : FinDist α) (d2 : FinDist β) (d3 : FinDist γ) :
    (d1.prod d2).prod d3 = (d1.prod (d2.prod d3)).equivMap (Equiv.prodAssoc α β γ).symm := by
  dsimp [FinDist.prod, FinDist.equivMap, Equiv.prodAssoc]
  refine congrArg FinDist.mk ?_
  funext p
  exact Nat.mul_assoc _ _ _

theorem FinDist.prob_prod_comm {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (P : α × β → Bool) :
    (d1.prod d2).prob P = (d2.prod d1).prob (fun p => P (p.2, p.1)) := by
  dsimp [FinDist.prob]
  rw [FinDist.acceptWeight_prod_left, FinDist.acceptWeight_prod_right]
  rw [FinDist.totalMass_prod, FinDist.totalMass_prod, Nat.mul_comm d1.totalMass d2.totalMass]

theorem FinDist.prob_prod_assoc {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (d1 : FinDist α) (d2 : FinDist β) (d3 : FinDist γ) (P : (α × β) × γ → Bool) :
    ((d1.prod d2).prod d3).prob P =
      (d1.prod (d2.prod d3)).prob (fun p => P ((p.1, p.2.1), p.2.2)) := by
  rw [FinDist.prod_assoc_symm_eq, FinDist.prob_equivMap]
  rfl

theorem FinDist.prob_prod_assoc_symm {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (d1 : FinDist α) (d2 : FinDist β) (d3 : FinDist γ) (P : α × (β × γ) → Bool) :
    (d1.prod (d2.prod d3)).prob P =
      ((d1.prod d2).prod d3).prob (fun p => P (p.1.1, (p.1.2, p.2))) := by
  rw [FinDist.prod_assoc_eq, FinDist.prob_equivMap]
  rfl

def modPKERealAuxProb (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R)))
    (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) : ℚ :=
  (((uniformFinDist (MatrixR R k k)).prod kgDist).prod (encDist.prod auxDist)).prob
    (fun p =>
      let pk := modPKEKeygen R k p.1.1 p.1.2.1 p.1.2.2
      Test p.2.2 pk (modPKEEncrypt R k pk p.2.1.1 p.2.1.2.1 p.2.1.2.2 (μ_of p.2.2)))

def modPKEHybrid1AuxProb (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux)
    (encDist : FinDist (VectorR R k × (VectorR R k × R)))
    (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) : ℚ :=
  (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
      (encDist.prod auxDist)).prob
    (fun p =>
      let pk : ModPKEPublicKey R k := { A := p.1.1, t := p.1.2 }
      Test p.2.2 pk (modPKEEncrypt R k pk p.2.1.1 p.2.1.2.1 p.2.1.2.2 (μ_of p.2.2)))

def modPKEHybrid2AuxProb (R : Type*) [Add R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux)
    (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) : ℚ :=
  ((((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
        ((uniformFinDist (VectorR R k)).prod (uniformFinDist R))).prod auxDist).prob
    (fun p => Test p.2 { A := p.1.1.1, t := p.1.1.2 } { u := p.1.2.1, v := p.1.2.2 + μ_of p.2 })

theorem modPKE_hybrid0_hybrid1_bound (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux) (h_aux : 0 < auxDist.totalMass)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) (h_enc : 0 < encDist.totalMass)
    (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    ∃ B_kg : Sample R k k → Bool,
      |modPKERealAuxProb R k auxDist kgDist encDist μ_of Test -
          modPKEHybrid1AuxProb R k auxDist encDist μ_of Test| ≤
        mlweAdvantage R k k kgDist B_kg := by
  dsimp [modPKERealAuxProb, modPKEHybrid1AuxProb]
  rw [FinDist.prob_prod_comm ((uniformFinDist (MatrixR R k k)).prod kgDist) (encDist.prod auxDist)]
  rw [FinDist.prob_prod_comm
    ((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))) (encDist.prod auxDist)]
  let F1 : ((VectorR R k × (VectorR R k × R)) × Aux) →
      (MatrixR R k k × (VectorR R k × VectorR R k)) → Bool := fun coin p =>
    let pk := modPKEKeygen R k p.1 p.2.1 p.2.2
    Test coin.2 pk (modPKEEncrypt R k pk coin.1.1 coin.1.2.1 coin.1.2.2 (μ_of coin.2))
  let F2 : ((VectorR R k × (VectorR R k × R)) × Aux) →
      (MatrixR R k k × VectorR R k) → Bool := fun coin p =>
    let pk : ModPKEPublicKey R k := { A := p.1, t := p.2 }
    Test coin.2 pk (modPKEEncrypt R k pk coin.1.1 coin.1.2.1 coin.1.2.2 (μ_of coin.2))
  obtain ⟨coin, h_coin⟩ := FinDist.exists_coin_ge_abs_prob_prod_sub
    (encDist.prod auxDist) (FinDist.totalMass_prod_pos h_enc h_aux)
    ((uniformFinDist (MatrixR R k k)).prod kgDist)
    ((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))) F1 F2
  let F_pk : ModPKEPublicKey R k → Bool := fun pk =>
    Test coin.2 pk (modPKEEncrypt R k pk coin.1.1 coin.1.2.1 coin.1.2.2 (μ_of coin.2))
  refine ⟨modPKEKeygenDistinguisher R k F_pk, le_trans h_coin ?_⟩
  have h1 :
      ((uniformFinDist (MatrixR R k k)).prod kgDist).prob (F1 coin) =
        mlweRealProb R k k kgDist (modPKEKeygenDistinguisher R k F_pk) :=
    prob_modPKE_keygen_eq_mlweRealProb R k kgDist F_pk
  have h2 :
      ((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prob (F2 coin) =
        mlweUniformProb R k k (modPKEKeygenDistinguisher R k F_pk) :=
    prob_modPKE_keygen_uniform_eq_mlweUniformProb R k F_pk
  rw [h1, h2]
  rfl

theorem modPKE_hybrid1_hybrid2_bound (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux) (h_aux : 0 < auxDist.totalMass)
    (encDist : FinDist (VectorR R k × (VectorR R k × R)))
    (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    ∃ B_enc : Sample R k (k + 1) → Bool,
      |modPKEHybrid1AuxProb R k auxDist encDist μ_of Test -
          modPKEHybrid2AuxProb R k auxDist μ_of Test| ≤
        mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc := by
  dsimp [modPKEHybrid1AuxProb, modPKEHybrid2AuxProb]
  rw [FinDist.prob_prod_assoc_symm]
  rw [FinDist.prob_prod_comm
    (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod encDist) auxDist]
  rw [FinDist.prob_prod_comm
    (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
      ((uniformFinDist (VectorR R k)).prod (uniformFinDist R))) auxDist]
  let F1 : Aux →
      ((MatrixR R k k × VectorR R k) × (VectorR R k × (VectorR R k × R))) → Bool := fun a p =>
    Test a { A := p.1.1, t := p.1.2 }
      (modPKEEncrypt R k { A := p.1.1, t := p.1.2 } p.2.1 p.2.2.1 p.2.2.2 (μ_of a))
  let F2 : Aux →
      ((MatrixR R k k × VectorR R k) × (VectorR R k × R)) → Bool := fun a p =>
    Test a { A := p.1.1, t := p.1.2 } { u := p.2.1, v := p.2.2 + μ_of a }
  obtain ⟨a, ha⟩ := FinDist.exists_coin_ge_abs_prob_prod_sub auxDist h_aux
    (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod encDist)
    (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
      ((uniformFinDist (VectorR R k)).prod (uniformFinDist R))) F1 F2
  refine ⟨modPKEEncDistinguisher R k (μ_of a) (Test a), le_trans ha ?_⟩
  have h1 :
      (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod encDist).prob
          (F1 a) =
        mlweRealProb R k (k + 1) (modPKEEncSampleDist R k encDist)
          (modPKEEncDistinguisher R k (μ_of a) (Test a)) :=
    prob_modPKE_enc_hybrid1_eq_mlweRealProb R k encDist (μ_of a) (Test a)
  have h2 :
      (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
          ((uniformFinDist (VectorR R k)).prod (uniformFinDist R))).prob (F2 a) =
        mlweUniformProb R k (k + 1) (modPKEEncDistinguisher R k (μ_of a) (Test a)) :=
    prob_modPKE_enc_hybrid2_eq_mlweUniformProb R k (μ_of a) (Test a)
  rw [h1, h2]
  rfl

theorem modPKE_parametric_two_hybrid (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux) (h_aux : 0 < auxDist.totalMass)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) (h_enc : 0 < encDist.totalMass)
    (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    ∃ (B_kg : Sample R k k → Bool) (B_enc : Sample R k (k + 1) → Bool),
      |modPKERealAuxProb R k auxDist kgDist encDist μ_of Test -
          modPKEHybrid2AuxProb R k auxDist μ_of Test| ≤
        mlweAdvantage R k k kgDist B_kg +
          mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc := by
  obtain ⟨B_kg, h01⟩ := modPKE_hybrid0_hybrid1_bound R k auxDist h_aux kgDist encDist h_enc
    μ_of Test
  obtain ⟨B_enc, h12⟩ := modPKE_hybrid1_hybrid2_bound R k auxDist h_aux encDist μ_of Test
  refine ⟨B_kg, B_enc,
    le_trans (abs_sub_le _ (modPKEHybrid1AuxProb R k auxDist encDist μ_of Test) _)
      (add_le_add h01 h12)⟩

theorem modPKEHybrid2_shift_invariant (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    {Aux : Type*} [Fintype Aux]
    (auxDist : FinDist Aux) (μ_of : Aux → R)
    (Test : Aux → ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    modPKEHybrid2AuxProb R k auxDist μ_of Test =
      modPKEHybrid2AuxProb R k auxDist (fun _ => 0) Test := by
  dsimp [modPKEHybrid2AuxProb]
  rw [FinDist.prob_prod_eq_sum_right, FinDist.prob_prod_eq_sum_right]
  refine congrArg (fun x : ℚ => x / (auxDist.totalMass : ℚ)) ?_
  apply Finset.sum_congr rfl
  intro a _
  refine congrArg (fun x : ℚ => (auxDist.weight a : ℚ) * x) ?_
  have h_assoc :
      ∀ sh : R,
        (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
            ((uniformFinDist (VectorR R k)).prod (uniformFinDist R))).prob
            (fun p => Test a { A := p.1.1, t := p.1.2 } { u := p.2.1, v := p.2.2 + sh }) =
          ((((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
              (uniformFinDist (VectorR R k))).prod (uniformFinDist R)).prob
            (fun p => Test a { A := p.1.1.1, t := p.1.1.2 } { u := p.1.2, v := p.2 + sh }) := by
    intro sh
    rw [FinDist.prob_prod_assoc_symm]
  rw [h_assoc (μ_of a), h_assoc 0]
  rw [FinDist.prob_prod_eq_sum_left, FinDist.prob_prod_eq_sum_left]
  refine congrArg (fun x : ℚ => x / (((((uniformFinDist (MatrixR R k k)).prod
      (uniformFinDist (VectorR R k))).prod (uniformFinDist (VectorR R k))).totalMass) : ℚ)) ?_
  apply Finset.sum_congr rfl
  intro p _
  refine congrArg (fun x : ℚ => ((((uniformFinDist (MatrixR R k k)).prod
      (uniformFinDist (VectorR R k))).prod (uniformFinDist (VectorR R k))).weight p : ℚ) * x) ?_
  dsimp only
  rw [prob_uniform_add_right (μ_of a)
    (fun v => Test a { A := p.1.1, t := p.1.2 } { u := p.2, v := v })]
  rw [prob_uniform_add_right (0 : R)
    (fun v => Test a { A := p.1.1, t := p.1.2 } { u := p.2, v := v })]

def modPKEBitINDCPAWinProb (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R)))
    (μ0 μ1 : R)
    (adv : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) : ℚ :=
  modPKERealAuxProb R k (uniformFinDist Bool) kgDist encDist
    (fun b => if b then μ1 else μ0) (fun b pk ct => adv pk ct == b)

def modPKEBitINDCPAAdvantage (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R)))
    (μ0 μ1 : R)
    (adv : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) : ℚ :=
  |modPKEBitINDCPAWinProb R k kgDist encDist μ0 μ1 adv - 1 / 2|

theorem modPKEHybrid2_bit_ind_cpa_eq_half (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (μ0 μ1 : R)
    (adv : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    modPKEHybrid2AuxProb R k (uniformFinDist Bool)
        (fun b => if b then μ1 else μ0) (fun b pk ct => adv pk ct == b) =
      1 / 2 := by
  let dPK := (uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))
  let dBase := dPK.prod (uniformFinDist (VectorR R k))
  haveI : Nonempty R := ⟨0⟩
  have h_pos : 0 < dBase.totalMass :=
    FinDist.totalMass_prod_pos
      (FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) (uniformFinDist_totalMass_pos _))
      (uniformFinDist_totalMass_pos _)
  dsimp [modPKEHybrid2AuxProb]
  rw [FinDist.prod_assoc_eq dPK (uniformFinDist (VectorR R k)) (uniformFinDist R)]
  conv_lhs =>
    rw [← FinDist.equivMap_refl (uniformFinDist Bool), FinDist.prod_equivMap,
      FinDist.prob_equivMap]
  exact prob_uniform_pad_guess_eq_half dBase h_pos (fun _ => μ0) (fun _ => μ1)
    (fun ag v => adv { A := ag.1.1, t := ag.1.2 } { u := ag.2, v := v })

theorem modPKE_bit_ind_cpa_to_mlwe (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) (h_enc : 0 < encDist.totalMass)
    (μ0 μ1 : R)
    (adv : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    ∃ (B_kg : Sample R k k → Bool) (B_enc : Sample R k (k + 1) → Bool),
      modPKEBitINDCPAAdvantage R k kgDist encDist μ0 μ1 adv ≤
        mlweAdvantage R k k kgDist B_kg +
          mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc := by
  obtain ⟨B_kg, B_enc, h_bnd⟩ := modPKE_parametric_two_hybrid R k
    (uniformFinDist Bool) (uniformFinDist_totalMass_pos Bool) kgDist encDist h_enc
    (fun b => if b then μ1 else μ0) (fun b pk ct => adv pk ct == b)
  rw [modPKEHybrid2_bit_ind_cpa_eq_half R k μ0 μ1 adv] at h_bnd
  exact ⟨B_kg, B_enc, h_bnd⟩

theorem modPKE_two_msg_ind_cpa_to_mlwe (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) (h_enc : 0 < encDist.totalMass)
    (μ0 μ1 : R)
    (adv : ModPKEPublicKey R k → ModPKECiphertext R k → Bool) :
    ∃ (B_kg0 B_kg1 : Sample R k k → Bool) (B_enc0 B_enc1 : Sample R k (k + 1) → Bool),
      |modPKERealAuxProb R k (uniformFinDist Unit) kgDist encDist (fun _ => μ0)
            (fun _ pk ct => adv pk ct) -
          modPKERealAuxProb R k (uniformFinDist Unit) kgDist encDist (fun _ => μ1)
            (fun _ pk ct => adv pk ct)| ≤
        mlweAdvantage R k k kgDist B_kg0 +
          mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc0 +
          mlweAdvantage R k k kgDist B_kg1 +
          mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc1 := by
  obtain ⟨B_kg0, B_enc0, h0⟩ := modPKE_parametric_two_hybrid R k
    (uniformFinDist Unit) (uniformFinDist_totalMass_pos Unit) kgDist encDist h_enc
    (fun _ => μ0) (fun _ pk ct => adv pk ct)
  obtain ⟨B_kg1, B_enc1, h1⟩ := modPKE_parametric_two_hybrid R k
    (uniformFinDist Unit) (uniformFinDist_totalMass_pos Unit) kgDist encDist h_enc
    (fun _ => μ1) (fun _ pk ct => adv pk ct)
  have h_hyb_eq :
      modPKEHybrid2AuxProb R k (uniformFinDist Unit) (fun _ => μ0)
          (fun _ pk ct => adv pk ct) =
        modPKEHybrid2AuxProb R k (uniformFinDist Unit) (fun _ => μ1)
          (fun _ pk ct => adv pk ct) := by
    rw [modPKEHybrid2_shift_invariant, ← modPKEHybrid2_shift_invariant]
  rw [h_hyb_eq] at h0
  rw [abs_sub_comm] at h1
  refine ⟨B_kg0, B_kg1, B_enc0, B_enc1,
    le_trans (abs_sub_le _ (modPKEHybrid2AuxProb R k (uniformFinDist Unit) (fun _ => μ1)
      (fun _ pk ct => adv pk ct)) _) ?_⟩
  rw [add_assoc (mlweAdvantage R k k kgDist B_kg0 +
    mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc0)]
  exact add_le_add h0 h1

def modPKECompressedBitINDCPAWinProb (params : LWEParams) (N k d_u d_v : ℕ) [Fact (0 < N)]
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (encDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      (VectorR (NegacyclicPoly (Zq params) N) k × NegacyclicPoly (Zq params) N)))
    (μ0 μ1 : NegacyclicPoly (Zq params) N)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKEQuantizedCiphertext N k → Bool) : ℚ :=
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  modPKEBitINDCPAWinProb (NegacyclicPoly (Zq params) N) k kgDist encDist μ0 μ1
    (fun pk ct => adv pk (modPKECompressCiphertext params N k d_u d_v ct))

def modPKECompressedBitINDCPAAdvantage (params : LWEParams) (N k d_u d_v : ℕ) [Fact (0 < N)]
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (encDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      (VectorR (NegacyclicPoly (Zq params) N) k × NegacyclicPoly (Zq params) N)))
    (μ0 μ1 : NegacyclicPoly (Zq params) N)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKEQuantizedCiphertext N k → Bool) : ℚ :=
  |modPKECompressedBitINDCPAWinProb params N k d_u d_v kgDist encDist μ0 μ1 adv - 1 / 2|

theorem modPKE_compressed_bit_ind_cpa_to_mlwe (params : LWEParams) (N k d_u d_v : ℕ)
    [Fact (0 < N)]
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (encDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      (VectorR (NegacyclicPoly (Zq params) N) k × NegacyclicPoly (Zq params) N)))
    (h_enc : 0 < encDist.totalMass)
    (μ0 μ1 : NegacyclicPoly (Zq params) N)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKEQuantizedCiphertext N k → Bool) :
    letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
    ∃ (B_kg : Sample (NegacyclicPoly (Zq params) N) k k → Bool)
      (B_enc : Sample (NegacyclicPoly (Zq params) N) k (k + 1) → Bool),
      modPKECompressedBitINDCPAAdvantage params N k d_u d_v kgDist encDist μ0 μ1 adv ≤
        mlweAdvantage (NegacyclicPoly (Zq params) N) k k kgDist B_kg +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k (k + 1)
            (modPKEEncSampleDist (NegacyclicPoly (Zq params) N) k encDist) B_enc := by
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  exact modPKE_bit_ind_cpa_to_mlwe (NegacyclicPoly (Zq params) N) k kgDist encDist h_enc μ0 μ1
    (fun pk ct => adv pk (modPKECompressCiphertext params N k d_u d_v ct))

def modPKEListOWCPAWinProb (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (M : Type*) [Fintype M] [DecidableEq M]
    (encode : M → R)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R)))
    (Q_adv : ModPKEPublicKey R k → ModPKECiphertext R k → Finset M) : ℚ :=
  modPKERealAuxProb R k (uniformFinDist M) kgDist encDist encode
    (fun m pk ct => decide (m ∈ Q_adv pk ct))

theorem modPKEHybrid2_list_ow_cpa_le (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (M : Type*) [Fintype M] [DecidableEq M]
    (q_G : ℕ) (encode : M → R)
    (Q_adv : ModPKEPublicKey R k → ModPKECiphertext R k → Finset M)
    (hQ : ∀ pk ct, (Q_adv pk ct).card ≤ q_G) :
    modPKEHybrid2AuxProb R k (uniformFinDist M) encode
        (fun m pk ct => decide (m ∈ Q_adv pk ct)) ≤
      (q_G : ℚ) / (Fintype.card M : ℚ) := by
  rw [modPKEHybrid2_shift_invariant]
  dsimp [modPKEHybrid2AuxProb]
  rw [FinDist.prob_eq_eventProb]
  let d := (((uniformFinDist (MatrixR R k k)).prod (uniformFinDist (VectorR R k))).prod
    ((uniformFinDist (VectorR R k)).prod (uniformFinDist R)))
  let S : ((MatrixR R k k × VectorR R k) × (VectorR R k × R)) → Finset M := fun x =>
    Q_adv { A := x.1.1, t := x.1.2 } { u := x.2.1, v := x.2.2 + 0 }
  have h_ev :
      (d.prod (uniformFinDist M)).eventProb
          (fun x => decide (x.2 ∈ Q_adv { A := x.1.1.1, t := x.1.1.2 }
            { u := x.1.2.1, v := x.1.2.2 + 0 }) = true) =
        (d.prod (uniformFinDist M)).eventProb (fun p => p.2 ∈ S p.1) :=
    (d.prod (uniformFinDist M)).eventProb_congr
      (fun x => decide (x.2 ∈ Q_adv { A := x.1.1.1, t := x.1.1.2 }
        { u := x.1.2.1, v := x.1.2.2 + 0 }) = true)
      (fun p => p.2 ∈ S p.1)
      (fun _ => by simp [S])
  exact le_trans (le_of_eq h_ev) (eventProb_prod_uniform_mem_finset_le d q_G S (fun _ => hQ _ _))

theorem modPKE_list_ow_cpa_to_mlwe (R : Type*) [CommRing R] [Fintype R] (k : ℕ)
    (M : Type*) [Fintype M] [DecidableEq M] [Nonempty M]
    (q_G : ℕ) (encode : M → R)
    (kgDist : FinDist (VectorR R k × VectorR R k))
    (encDist : FinDist (VectorR R k × (VectorR R k × R))) (h_enc : 0 < encDist.totalMass)
    (Q_adv : ModPKEPublicKey R k → ModPKECiphertext R k → Finset M)
    (hQ : ∀ pk ct, (Q_adv pk ct).card ≤ q_G) :
    ∃ (B_kg : Sample R k k → Bool) (B_enc : Sample R k (k + 1) → Bool),
      modPKEListOWCPAWinProb R k M encode kgDist encDist Q_adv ≤
        (q_G : ℚ) / (Fintype.card M : ℚ) +
          mlweAdvantage R k k kgDist B_kg +
          mlweAdvantage R k (k + 1) (modPKEEncSampleDist R k encDist) B_enc := by
  obtain ⟨B_kg, B_enc, h_diff⟩ := modPKE_parametric_two_hybrid R k
    (uniformFinDist M) (uniformFinDist_totalMass_pos M) kgDist encDist h_enc encode
    (fun m pk ct => decide (m ∈ Q_adv pk ct))
  have h_hyb2 := modPKEHybrid2_list_ow_cpa_le R k M q_G encode Q_adv hQ
  have h_le :
      modPKERealAuxProb R k (uniformFinDist M) kgDist encDist encode
          (fun m pk ct => decide (m ∈ Q_adv pk ct)) ≤
        modPKEHybrid2AuxProb R k (uniformFinDist M) encode
            (fun m pk ct => decide (m ∈ Q_adv pk ct)) +
          |modPKERealAuxProb R k (uniformFinDist M) kgDist encDist encode
              (fun m pk ct => decide (m ∈ Q_adv pk ct)) -
            modPKEHybrid2AuxProb R k (uniformFinDist M) encode
              (fun m pk ct => decide (m ∈ Q_adv pk ct))| :=
    le_add_of_sub_left_le (le_abs_self _)
  refine ⟨B_kg, B_enc, ?_⟩
  dsimp [modPKEListOWCPAWinProb]
  have h_comb := le_trans h_le (add_le_add h_hyb2 h_diff)
  rw [← add_assoc] at h_comb
  exact h_comb

theorem modPKE_poly_list_ow_cpa_to_mlwe (params : LWEParams) (k N Δ t q_G : ℕ)
    [Fact (0 < N)] [Fact (0 < t)]
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (encDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      (VectorR (NegacyclicPoly (Zq params) N) k × NegacyclicPoly (Zq params) N)))
    (h_enc : 0 < encDist.totalMass)
    (Q_adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Finset (Fin N → Fin t))
    (hQ : ∀ pk ct, (Q_adv pk ct).card ≤ q_G) :
    letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
    ∃ (B_kg : Sample (NegacyclicPoly (Zq params) N) k k → Bool)
      (B_enc : Sample (NegacyclicPoly (Zq params) N) k (k + 1) → Bool),
      modPKEListOWCPAWinProb (NegacyclicPoly (Zq params) N) k (Fin N → Fin t)
          (bfvEncodePolyFin params N Δ t) kgDist encDist Q_adv ≤
        (q_G : ℚ) / ((t : ℚ) ^ N) +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k k kgDist B_kg +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k (k + 1)
            (modPKEEncSampleDist (NegacyclicPoly (Zq params) N) k encDist) B_enc := by
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  haveI : Nonempty (Fin N → Fin t) := ⟨fun _ => ⟨0, Fact.out⟩⟩
  have h_card : (Fintype.card (Fin N → Fin t) : ℚ) = (t : ℚ) ^ N := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  obtain ⟨B_kg, B_enc, h_bnd⟩ := modPKE_list_ow_cpa_to_mlwe (NegacyclicPoly (Zq params) N) k
    (Fin N → Fin t) q_G (bfvEncodePolyFin params N Δ t) kgDist encDist h_enc Q_adv hQ
  rw [h_card] at h_bnd
  exact ⟨B_kg, B_enc, h_bnd⟩

theorem modPKE_poly_ow_cpa_to_mlwe (params : LWEParams) (k N Δ t : ℕ)
    [Fact (0 < N)] [Fact (0 < t)]
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (encDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      (VectorR (NegacyclicPoly (Zq params) N) k × NegacyclicPoly (Zq params) N)))
    (h_enc : 0 < encDist.totalMass)
    (adv_ow : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t)) :
    letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
    ∃ (B_kg : Sample (NegacyclicPoly (Zq params) N) k k → Bool)
      (B_enc : Sample (NegacyclicPoly (Zq params) N) k (k + 1) → Bool),
      modPKEListOWCPAWinProb (NegacyclicPoly (Zq params) N) k (Fin N → Fin t)
          (bfvEncodePolyFin params N Δ t) kgDist encDist (fun pk ct => {adv_ow pk ct}) ≤
        1 / ((t : ℚ) ^ N) +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k k kgDist B_kg +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k (k + 1)
            (modPKEEncSampleDist (NegacyclicPoly (Zq params) N) k encDist) B_enc := by
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  simpa using modPKE_poly_list_ow_cpa_to_mlwe params k N Δ t 1 kgDist encDist h_enc
    (fun pk ct => {adv_ow pk ct}) (fun _ _ => by simp)

end ModulePKESecurityReductions

section PrimeSearchToDecisionLWE

open scoped BigOperators

def FinDist.map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (dist : FinDist α) : FinDist β :=
  { weight := fun b => ∑ a : α, if f a = b then dist.weight a else 0 }

theorem FinDist.totalMass_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (dist : FinDist α) :
    (dist.map f).totalMass = dist.totalMass := by
  dsimp [FinDist.totalMass, FinDist.map]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mem_univ]

lemma FinDist.totalMass_map_pos {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) {dist : FinDist α} (h_pos : 0 < dist.totalMass) :
    0 < (dist.map f).totalMass := by
  rwa [FinDist.totalMass_map]

theorem FinDist.acceptWeight_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (dist : FinDist α) (P : β → Bool) :
    (dist.map f).acceptWeight P = dist.acceptWeight (fun a => P (f a)) := by
  dsimp [FinDist.acceptWeight, FinDist.map]
  have h1 :
      (∑ b : β,
          ((∑ a : α, if f a = b then dist.weight a else 0 : ℕ) : ℤ) * bitToInt (P b)) =
        ∑ b : β, ∑ a : α, if f a = b then (dist.weight a : ℤ) * bitToInt (P b) else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [Finset.mem_univ]

theorem FinDist.prob_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (dist : FinDist α) (P : β → Bool) :
    (dist.map f).prob P = dist.prob (fun a => P (f a)) := by
  dsimp [FinDist.prob]
  rw [FinDist.acceptWeight_map, FinDist.totalMass_map]

theorem FinDist.pos_weight_map_iff {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (dist : FinDist α) (b : β) :
    0 < (dist.map f).weight b ↔ ∃ a : α, f a = b ∧ 0 < dist.weight a := by
  dsimp [FinDist.map]
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro hne
    by_contra h_none
    apply hne
    apply Finset.sum_eq_zero
    intro a _
    by_cases hfa : f a = b
    · rw [if_pos hfa]
      by_contra ha0
      exact h_none ⟨a, hfa, Nat.pos_of_ne_zero ha0⟩
    · rw [if_neg hfa]
  · rintro ⟨a, hfa, ha⟩ hzero
    have ha0 := (Finset.sum_eq_zero_iff.mp hzero) a (Finset.mem_univ a)
    rw [if_pos hfa] at ha0
    omega

theorem FinDist.prob_prod_map_left {α₁ α₂ β : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β] [DecidableEq α₂]
    (f : α₁ → α₂) (d1 : FinDist α₁) (d2 : FinDist β) (P : α₂ × β → Bool) :
    ((d1.map f).prod d2).prob P = (d1.prod d2).prob (fun p => P (f p.1, p.2)) := by
  by_cases h2 : d2.totalMass = 0
  · have h_w0 : ∀ b : β, d2.weight b = 0 := by
      dsimp [FinDist.totalMass] at h2
      intro b
      exact (Finset.sum_eq_zero_iff.mp h2) b (Finset.mem_univ b)
    simp [FinDist.prob, FinDist.totalMass_prod, h2]
  · rw [FinDist.prob_prod_eq_sum_right, FinDist.prob_prod_eq_sum_right]
    refine congrArg (fun x : ℚ => x / (d2.totalMass : ℚ)) ?_
    apply Finset.sum_congr rfl
    intro b _
    rw [FinDist.prob_map]

theorem FinDist.prob_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (h2 : 0 < d2.totalMass) (P : α → Bool) :
    (d1.prod d2).prob (fun p => P p.1) = d1.prob P := by
  rw [FinDist.prob_prod_eq_sum_right]
  dsimp only
  rw [← Finset.sum_mul]
  have hsum : (∑ b : β, (d2.weight b : ℚ)) = (d2.totalMass : ℚ) := by
    dsimp [FinDist.totalMass]
    rw [Nat.cast_sum]
  have hne : (d2.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h2)
  rw [hsum, mul_div_cancel_left₀ _ hne]

theorem FinDist.prob_prod_snd {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (h1 : 0 < d1.totalMass) (P : β → Bool) :
    (d1.prod d2).prob (fun p => P p.2) = d2.prob P := by
  rw [FinDist.prob_prod_comm, FinDist.prob_prod_fst d2 d1 h1 P]

theorem FinDist.eventProb_eq_prob_decide {α : Type*} [Fintype α]
    (dist : FinDist α) (E : α → Prop) [DecidablePred E] :
    dist.eventProb E = dist.prob (fun x => decide (E x)) := by
  rw [FinDist.prob_eq_eventProb]
  exact dist.eventProb_congr E (fun x => decide (E x) = true)
    (fun x => decide_eq_true_iff.symm)

theorem FinDist.eventProb_prod_left {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (h2 : 0 < d2.totalMass)
    (E : α → Prop) [DecidablePred E] :
    (d1.prod d2).eventProb (fun p => E p.1) = d1.eventProb E := by
  rw [FinDist.eventProb_eq_prob_decide, FinDist.eventProb_eq_prob_decide]
  exact FinDist.prob_prod_fst d1 d2 h2 (fun a => decide (E a))

theorem FinDist.eventProb_mono {α : Type*} [Fintype α] (dist : FinDist α)
    (E1 E2 : α → Prop) [DecidablePred E1] [DecidablePred E2]
    (h_imp : ∀ x : α, E1 x → E2 x) :
    dist.eventProb E1 ≤ dist.eventProb E2 := by
  dsimp [FinDist.eventProb]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  norm_cast
  dsimp [FinDist.eventMass]
  apply Finset.sum_le_sum
  intro x _
  by_cases h1 : E1 x
  · rw [if_pos h1, if_pos (h_imp x h1)]
  · rw [if_neg h1]
    split_ifs <;> omega

theorem FinDist.eventMass_exists_le {α ι : Type*} [Fintype α] [Fintype ι]
    (dist : FinDist α) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] [DecidablePred (fun x => ∃ i : ι, E i x)] :
    dist.eventMass (fun x => ∃ i : ι, E i x) ≤ ∑ i : ι, dist.eventMass (E i) := by
  dsimp [FinDist.eventMass]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : ∃ i : ι, E i x
  · rcases hx with ⟨i0, hi0⟩
    rw [if_pos ⟨i0, hi0⟩]
    have h_term : dist.weight x = (if E i0 x then dist.weight x else 0) := by
      rw [if_pos hi0]
    conv_lhs => rw [h_term]
    exact Finset.single_le_sum (f := fun i => if E i x then dist.weight x else 0)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
  · rw [if_neg hx]
    exact Nat.zero_le _

theorem FinDist.eventProb_exists_le {α ι : Type*} [Fintype α] [Fintype ι]
    (dist : FinDist α) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] [DecidablePred (fun x => ∃ i : ι, E i x)] :
    dist.eventProb (fun x => ∃ i : ι, E i x) ≤ ∑ i : ι, dist.eventProb (E i) := by
  dsimp [FinDist.eventProb]
  rw [← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Nat.cast_sum]
  exact Nat.cast_le.mpr (dist.eventMass_exists_le E)

def FinDist.expect {α : Type*} [Fintype α] (dist : FinDist α) (X : α → ℚ) : ℚ :=
  (∑ x : α, (dist.weight x : ℚ) * X x) / (dist.totalMass : ℚ)

lemma FinDist.expect_const {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (c : ℚ) :
    dist.expect (fun _ => c) = c := by
  dsimp [FinDist.expect, FinDist.totalMass]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  have hne : ((∑ x : α, dist.weight x : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_pos)
  rw [div_eq_iff hne, mul_comm]

lemma FinDist.expect_add {α : Type*} [Fintype α] (dist : FinDist α) (X Y : α → ℚ) :
    dist.expect (fun x => X x + Y x) = dist.expect X + dist.expect Y := by
  dsimp [FinDist.expect]
  simp_rw [mul_add, Finset.sum_add_distrib, add_div]

lemma FinDist.expect_sub {α : Type*} [Fintype α] (dist : FinDist α) (X Y : α → ℚ) :
    dist.expect (fun x => X x - Y x) = dist.expect X - dist.expect Y := by
  dsimp [FinDist.expect]
  simp_rw [mul_sub, Finset.sum_sub_distrib, sub_div]

lemma FinDist.expect_smul {α : Type*} [Fintype α] (dist : FinDist α) (c : ℚ) (X : α → ℚ) :
    dist.expect (fun x => c * X x) = c * dist.expect X := by
  dsimp [FinDist.expect]
  have h_eq :
      (∑ x : α, (dist.weight x : ℚ) * (c * X x)) =
        c * ∑ x : α, (dist.weight x : ℚ) * X x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [h_eq, mul_div_assoc]

lemma FinDist.expect_sum {α ι : Type*} [Fintype α]
    (dist : FinDist α) (s : Finset ι) (X : ι → α → ℚ) :
    dist.expect (fun a => ∑ i ∈ s, X i a) = ∑ i ∈ s, dist.expect (X i) := by
  dsimp [FinDist.expect]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

lemma FinDist.expect_mono {α : Type*} [Fintype α]
    (dist : FinDist α) (X Y : α → ℚ) (h_le : ∀ x : α, X x ≤ Y x) :
    dist.expect X ≤ dist.expect Y := by
  dsimp [FinDist.expect]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h_le x) (Nat.cast_nonneg _)

lemma FinDist.expect_bitToInt_eq_prob {α : Type*} [Fintype α]
    (dist : FinDist α) (P : α → Bool) :
    dist.expect (fun x => (bitToInt (P x) : ℚ)) = dist.prob P := by
  dsimp [FinDist.expect, FinDist.prob, FinDist.acceptWeight]
  push_cast
  rfl

theorem FinDist.eventProb_le_expect_div {α : Type*} [Fintype α]
    (dist : FinDist α) (X : α → ℚ) (h_nonneg : ∀ x : α, 0 ≤ X x)
    (E : α → Prop) [DecidablePred E] (a : ℚ) (ha : 0 < a)
    (hE : ∀ x : α, E x → a ≤ X x) :
    dist.eventProb E ≤ dist.expect X / a := by
  by_cases h0 : dist.totalMass = 0
  · simp [FinDist.eventProb, FinDist.expect, h0]
  · have hm : (0 : ℚ) < (dist.totalMass : ℚ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
    have h_sum_le :
        a * (dist.eventMass E : ℚ) ≤ ∑ x : α, (dist.weight x : ℚ) * X x := by
      dsimp [FinDist.eventMass]
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : E x
      · rw [if_pos hx, mul_comm a (dist.weight x : ℚ)]
        exact mul_le_mul_of_nonneg_left (hE x hx) (Nat.cast_nonneg _)
      · rw [if_neg hx, Nat.cast_zero, mul_zero]
        exact mul_nonneg (Nat.cast_nonneg _) (h_nonneg x)
    dsimp [FinDist.eventProb, FinDist.expect]
    rw [div_div, div_le_div_iff₀ hm (mul_pos hm ha)]
    calc
      (dist.eventMass E : ℚ) * ((dist.totalMass : ℚ) * a) =
          (a * (dist.eventMass E : ℚ)) * (dist.totalMass : ℚ) := by ring
      _ ≤ (∑ x : α, (dist.weight x : ℚ) * X x) * (dist.totalMass : ℚ) :=
          mul_le_mul_of_nonneg_right h_sum_le (le_of_lt hm)

def FinDist.iid {α : Type*} [Fintype α] (dist : FinDist α) (T : ℕ) : FinDist (Fin T → α) :=
  { weight := fun v => ∏ t : Fin T, dist.weight (v t) }

theorem FinDist.totalMass_iid {α : Type*} [Fintype α] (dist : FinDist α) (T : ℕ) :
    (dist.iid T).totalMass = dist.totalMass ^ T := by
  dsimp [FinDist.totalMass, FinDist.iid]
  exact (Fintype.sum_pow (fun a => dist.weight a) T).symm

lemma FinDist.totalMass_iid_pos {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (T : ℕ) :
    0 < (dist.iid T).totalMass := by
  rw [FinDist.totalMass_iid]
  exact pow_pos h_pos T

theorem uniformFinDist_iid (α : Type*) [Fintype α] (T : ℕ) :
    (uniformFinDist α).iid T = uniformFinDist (Fin T → α) := by
  dsimp [FinDist.iid, uniformFinDist]
  simp

theorem FinDist.prod_iid_equiv {α β : Type*} [Fintype α] [Fintype β]
    (d1 : FinDist α) (d2 : FinDist β) (T : ℕ) :
    ((d1.prod d2).iid T).equivMap
        (Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => α) (fun _ => β)) =
      (d1.iid T).prod (d2.iid T) := by
  dsimp [FinDist.equivMap, FinDist.iid, FinDist.prod, Equiv.arrowProdEquivProdArrow]
  refine congrArg FinDist.mk ?_
  funext p
  exact Finset.prod_mul_distrib

theorem FinDist.expect_iid_prod {α : Type*} [Fintype α]
    (dist : FinDist α) (T : ℕ) (g : Fin T → α → ℚ) :
    (dist.iid T).expect (fun v => ∏ t : Fin T, g t (v t)) = ∏ t : Fin T, dist.expect (g t) := by
  dsimp [FinDist.expect]
  rw [FinDist.totalMass_iid, Nat.cast_pow]
  dsimp [FinDist.iid]
  have h_sum :
      (∑ v : Fin T → α, ((∏ t : Fin T, dist.weight (v t) : ℕ) : ℚ) * ∏ t : Fin T, g t (v t)) =
        ∑ v : Fin T → α, ∏ t : Fin T, (dist.weight (v t) : ℚ) * g t (v t) := by
    apply Finset.sum_congr rfl
    intro v _
    rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  have h_ps :=
    (Fintype.prod_sum (fun (t : Fin T) (a : α) => (dist.weight a : ℚ) * g t a)).symm
  have h_pow : (dist.totalMass : ℚ) ^ T = ∏ _t : Fin T, (dist.totalMass : ℚ) := by simp
  rw [h_sum, h_ps, h_pow, ← Finset.prod_div_distrib]

theorem FinDist.expect_iid_coord {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (T : ℕ) (i : Fin T) (f : α → ℚ) :
    (dist.iid T).expect (fun v => f (v i)) = dist.expect f := by
  let g : Fin T → α → ℚ := fun t a => if t = i then f a else 1
  have h_prod : ∀ v : Fin T → α, f (v i) = ∏ t : Fin T, g t (v t) := by
    intro v
    rw [← Finset.mul_prod_erase Finset.univ (fun t => g t (v t)) (Finset.mem_univ i)]
    have h_one : (∏ t ∈ Finset.univ.erase i, g t (v t)) = 1 := by
      apply Finset.prod_eq_one
      intro t ht
      have hne : t ≠ i := (Finset.mem_erase.mp ht).1
      simp [g, hne]
    rw [h_one, mul_one]
    simp [g]
  simp_rw [h_prod]
  rw [FinDist.expect_iid_prod]
  rw [← Finset.mul_prod_erase Finset.univ (fun t => dist.expect (g t)) (Finset.mem_univ i)]
  have h_one : (∏ t ∈ Finset.univ.erase i, dist.expect (g t)) = 1 := by
    apply Finset.prod_eq_one
    intro t ht
    have hne : t ≠ i := (Finset.mem_erase.mp ht).1
    have hg : g t = fun _ => 1 := funext fun _ => if_neg hne
    rw [hg, dist.expect_const h_pos]
  rw [h_one, mul_one]
  have hgi : g i = f := funext fun _ => if_pos rfl
  rw [hgi]

theorem FinDist.expect_iid_mul_of_ne {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (T : ℕ) (i j : Fin T) (hij : i ≠ j)
    (f1 f2 : α → ℚ) :
    (dist.iid T).expect (fun v => f1 (v i) * f2 (v j)) = dist.expect f1 * dist.expect f2 := by
  let g : Fin T → α → ℚ := fun t a => if t = i then f1 a else if t = j then f2 a else 1
  have h_prod : ∀ v : Fin T → α, f1 (v i) * f2 (v j) = ∏ t : Fin T, g t (v t) := by
    intro v
    rw [← Finset.mul_prod_erase Finset.univ (fun t => g t (v t)) (Finset.mem_univ i)]
    have hj_mem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun t => g t (v t)) hj_mem]
    have h_one : (∏ t ∈ (Finset.univ.erase i).erase j, g t (v t)) = 1 := by
      apply Finset.prod_eq_one
      intro t ht
      have htj : t ≠ j := (Finset.mem_erase.mp ht).1
      have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
      simp [g, hti, htj]
    rw [h_one, mul_one]
    simp [g, hij.symm]
  simp_rw [h_prod]
  rw [FinDist.expect_iid_prod]
  rw [← Finset.mul_prod_erase Finset.univ (fun t => dist.expect (g t)) (Finset.mem_univ i)]
  have hj_mem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) (fun t => dist.expect (g t)) hj_mem]
  have h_one : (∏ t ∈ (Finset.univ.erase i).erase j, dist.expect (g t)) = 1 := by
    apply Finset.prod_eq_one
    intro t ht
    have htj : t ≠ j := (Finset.mem_erase.mp ht).1
    have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    have hg : g t = fun _ => 1 := funext fun _ => by simp [g, hti, htj]
    rw [hg, dist.expect_const h_pos]
  rw [h_one, mul_one]
  have hgi : g i = f1 := funext fun _ => by simp [g]
  have hgj : g j = f2 := funext fun _ => by simp [g, hij.symm]
  rw [hgi, hgj]

theorem FinDist.chebyshev_iid_prob_le {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (T : ℕ) (hT : 0 < T)
    (P : α → Bool) (τ : ℚ) (hτ : 0 < τ) :
    (dist.iid T).eventProb
        (fun v => τ ≤ |(∑ t : Fin T, (bitToInt (P (v t)) : ℚ)) / (T : ℚ) - dist.prob P|) ≤
      1 / (4 * (T : ℚ) * τ ^ 2) := by
  let μ : ℚ := dist.prob P
  let Y : α → ℚ := fun a => (bitToInt (P a) : ℚ) - μ
  have h_exp_Y : dist.expect Y = 0 := by
    dsimp [Y]
    rw [dist.expect_sub, dist.expect_bitToInt_eq_prob, dist.expect_const h_pos]
    exact sub_self μ
  have h_var_le : dist.expect (fun a => Y a ^ 2) ≤ 1 / 4 := by
    have h_sq : ∀ a : α, Y a ^ 2 = (1 - 2 * μ) * (bitToInt (P a) : ℚ) + μ ^ 2 := by
      intro a
      dsimp [Y]
      have h_b : (bitToInt (P a) : ℚ) ^ 2 = (bitToInt (P a) : ℚ) := by
        cases P a <;> simp [bitToInt]
      ring_nf
      rw [h_b]
      ring
    simp_rw [h_sq]
    rw [dist.expect_add, dist.expect_smul, dist.expect_bitToInt_eq_prob, dist.expect_const h_pos]
    have h_id : (1 - 2 * μ) * μ + μ ^ 2 = 1 / 4 - (μ - 1 / 2) ^ 2 := by ring
    rw [h_id]
    exact sub_le_self _ (sq_nonneg _)
  let S_Y : (Fin T → α) → ℚ := fun v => (∑ t : Fin T, Y (v t)) ^ 2
  have h_exp_S : (dist.iid T).expect S_Y ≤ (T : ℚ) / 4 := by
    have h_expand : S_Y = fun v => ∑ t1 : Fin T, ∑ t2 : Fin T, Y (v t1) * Y (v t2) := by
      funext v
      dsimp [S_Y]
      rw [sq, Finset.sum_mul_sum]
    rw [h_expand, FinDist.expect_sum]
    simp_rw [FinDist.expect_sum]
    have h_row : ∀ t1 : Fin T,
        (∑ t2 : Fin T, (dist.iid T).expect (fun v => Y (v t1) * Y (v t2))) ≤ 1 / 4 := by
      intro t1
      rw [← Finset.add_sum_erase Finset.univ
        (fun t2 => (dist.iid T).expect (fun v => Y (v t1) * Y (v t2))) (Finset.mem_univ t1)]
      have h_diag : (dist.iid T).expect (fun v => Y (v t1) * Y (v t1)) ≤ 1 / 4 := by
        have h_eq : ∀ v : Fin T → α, Y (v t1) * Y (v t1) = Y (v t1) ^ 2 := fun v => (sq _).symm
        simp_rw [h_eq]
        rw [FinDist.expect_iid_coord dist h_pos T t1 (fun a => Y a ^ 2)]
        exact h_var_le
      have h_off :
          (∑ t2 ∈ Finset.univ.erase t1,
            (dist.iid T).expect (fun v => Y (v t1) * Y (v t2))) = 0 := by
        apply Finset.sum_eq_zero
        intro t2 ht2
        have hne : t1 ≠ t2 := (Finset.mem_erase.mp ht2).1.symm
        rw [FinDist.expect_iid_mul_of_ne dist h_pos T t1 t2 hne Y Y, h_exp_Y, zero_mul]
      rw [h_off, add_zero]
      exact h_diag
    have h_sum_le :
        (∑ t1 : Fin T, ∑ t2 : Fin T, (dist.iid T).expect (fun v => Y (v t1) * Y (v t2))) ≤
          ∑ _t1 : Fin T, (1 / 4 : ℚ) :=
      Finset.sum_le_sum (fun t1 _ => h_row t1)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_sum_le
    have h_t4 : (T : ℚ) * (1 / 4 : ℚ) = (T : ℚ) / 4 := by ring
    exact h_t4 ▸ h_sum_le
  have hT_pos : (0 : ℚ) < (T : ℚ) := Nat.cast_pos.mpr hT
  have h_thresh_pos : 0 < ((T : ℚ) * τ) ^ 2 := sq_pos_of_pos (mul_pos hT_pos hτ)
  have h_markov := FinDist.eventProb_le_expect_div (dist.iid T) S_Y (fun v => sq_nonneg _)
    (fun v => τ ≤ |(∑ t : Fin T, (bitToInt (P (v t)) : ℚ)) / (T : ℚ) - dist.prob P|)
    (((T : ℚ) * τ) ^ 2) h_thresh_pos
    (fun v hv => by
      have h_sub :
          (∑ t : Fin T, (bitToInt (P (v t)) : ℚ)) / (T : ℚ) - dist.prob P =
            (∑ t : Fin T, Y (v t)) / (T : ℚ) := by
        have h_sum_sub :
            ∑ t : Fin T, Y (v t) = (∑ t : Fin T, (bitToInt (P (v t)) : ℚ)) - (T : ℚ) * μ := by
          dsimp [Y]
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
        rw [h_sum_sub, sub_div, mul_div_cancel_left₀ μ (ne_of_gt hT_pos)]
      rw [h_sub, abs_div, abs_of_pos hT_pos, le_div_iff₀ hT_pos, mul_comm τ (T : ℚ)] at hv
      have h_sq_le := mul_le_mul hv hv (mul_nonneg (le_of_lt hT_pos) (le_of_lt hτ))
        (abs_nonneg _)
      rw [← sq, ← sq, sq_abs] at h_sq_le
      exact h_sq_le)
  refine le_trans h_markov ?_
  have h_div_le : (dist.iid T).expect S_Y / ((T : ℚ) * τ) ^ 2 ≤
      ((T : ℚ) / 4) / ((T : ℚ) * τ) ^ 2 :=
    div_le_div_of_nonneg_right h_exp_S (le_of_lt h_thresh_pos)
  refine le_trans h_div_le ?_
  have hT_ne : (T : ℚ) ≠ 0 := ne_of_gt hT_pos
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ
  have h_eq : ((T : ℚ) / 4) / ((T : ℚ) * τ) ^ 2 = 1 / (4 * (T : ℚ) * τ ^ 2) := by
    field_simp
  rw [h_eq]

lemma samplePhase_mkSample (R : Type*) [CommRing R] (n m : ℕ)
    (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m) :
    samplePhase R (mkSample R n m A s e) s = e := by
  ext i
  dsimp [samplePhase, mkSample, evaluate]
  ring

def oneSampleSearchWinProb (R : Type*) [CommRing R] [Fintype R] [DecidableEq R] (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m))
    (solver : Sample R n m → VectorR R n) : ℚ :=
  ((uniformFinDist (MatrixR R n m)).prod seDist).prob
    (fun p => decide (solver (mkSample R n m p.1 p.2.1 p.2.2) = p.2.1))

def decisionOfSearchDistinguisher (R : Type*) [CommRing R] [DecidableEq R] (n m : ℕ)
    (S_err : Finset (VectorR R m)) (solver : Sample R n m → VectorR R n)
    (c : Sample R n m) : Bool :=
  decide (samplePhase R c (solver c) ∈ S_err)

theorem decision_to_search_mlwe_bound (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (n m : ℕ)
    (seDist : FinDist (VectorR R n × VectorR R m))
    (S_err : Finset (VectorR R m))
    (h_supp : ∀ s e, 0 < seDist.weight (s, e) → e ∈ S_err)
    (solver : Sample R n m → VectorR R n) :
    oneSampleSearchWinProb R n m seDist solver -
        ((Fintype.card (VectorR R n) : ℚ) * (S_err.card : ℚ)) /
          (Fintype.card (VectorR R m) : ℚ) ≤
      mlweAdvantage R n m seDist (decisionOfSearchDistinguisher R n m S_err solver) := by
  let D := decisionOfSearchDistinguisher R n m S_err solver
  have h_real_le :
      oneSampleSearchWinProb R n m seDist solver ≤ mlweRealProb R n m seDist D := by
    dsimp [oneSampleSearchWinProb, mlweRealProb, mlweRealDist, FinDist.prob]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact_mod_cast Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) => by
      dsimp only [FinDist.prod]
      by_cases hw : p.2.2 ∈ S_err
      · by_cases hs : solver (mkSample R n m p.1 p.2.1 p.2.2) = p.2.1
        · have hD : D (mkSample R n m p.1 p.2.1 p.2.2) = true := by
            dsimp [D, decisionOfSearchDistinguisher]
            rw [decide_eq_true_iff, hs, samplePhase_mkSample]
            exact hw
          rw [decide_eq_true hs, hD]
        · rw [decide_eq_false hs]
          exact mul_le_mul_of_nonneg_left
            (by cases D (mkSample R n m p.1 p.2.1 p.2.2) <;> simp [bitToInt])
            (Int.natCast_nonneg _)
      · have h0 : seDist.weight p.2 = 0 := by
          by_contra hne
          exact hw (h_supp p.2.1 p.2.2 (Nat.pos_of_ne_zero hne))
        simp [h0])
  have h_unif_le :
      mlweUniformProb R n m D ≤
        ((Fintype.card (VectorR R n) : ℚ) * (S_err.card : ℚ)) /
          (Fintype.card (VectorR R m) : ℚ) := by
    rw [mlweUniformProb_eq_prod, FinDist.prob_eq_eventProb]
    let d_mat := uniformFinDist (MatrixR R n m)
    let d_vec := uniformFinDist (VectorR R m)
    let badSet : MatrixR R n m → Finset (VectorR R m) := fun A =>
      (Finset.univ : Finset (VectorR R n)).biUnion (fun s' =>
        S_err.image (fun e => evaluate R n m A s' e))
    have h_card : ∀ A : MatrixR R n m,
        (badSet A).card ≤ Fintype.card (VectorR R n) * S_err.card := by
      intro A
      refine le_trans Finset.card_biUnion_le ?_
      have h_le :
          (∑ s' : VectorR R n, (S_err.image (fun e => evaluate R n m A s' e)).card) ≤
            ∑ _s' : VectorR R n, S_err.card :=
        Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h_le
      exact h_le
    have h_ev :
        (d_mat.prod d_vec).eventProb (fun p => D { A := p.1, b := p.2 } = true) ≤
          (d_mat.prod d_vec).eventProb (fun p => p.2 ∈ badSet p.1) := by
      refine (d_mat.prod d_vec).eventProb_mono _ _ (fun p hp => ?_)
      dsimp [D, decisionOfSearchDistinguisher] at hp
      rw [decide_eq_true_iff] at hp
      refine Finset.mem_biUnion.mpr ⟨solver { A := p.1, b := p.2 }, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨samplePhase R { A := p.1, b := p.2 } (solver { A := p.1, b := p.2 }),
          hp, ?_⟩⟩
      ext i
      dsimp [evaluate, samplePhase]
      ring
    refine le_trans h_ev ?_
    have h_bd := eventProb_prod_uniform_mem_finset_le d_mat
      (Fintype.card (VectorR R n) * S_err.card) badSet h_card
    push_cast at h_bd
    exact h_bd
  have h_abs : mlweRealProb R n m seDist D - mlweUniformProb R n m D ≤
      mlweAdvantage R n m seDist D := le_abs_self _
  exact le_trans (sub_le_sub h_real_le h_unif_le) h_abs

def addColVec (R : Type*) [Add R] [Zero R] (n m : ℕ)
    (A : MatrixR R n m) (k : Fin n) (r : VectorR R m) : MatrixR R n m :=
  fun i j => A i j + if j = k then r i else 0

def rerandomizeFullCoord (R : Type*) [CommRing R] (n m : ℕ) (k : Fin n) (g : R)
    (c : Sample R n m) (r : VectorR R m) (y : VectorR R n) : Sample R n m :=
  let A' := addColVec R n m c.A k r
  { A := A',
    b := fun i => c.b i + r i * g + ∑ j : Fin n, A' i j * y j }

theorem rerandomizeFullCoord_mkSample (R : Type*) [CommRing R] (n m : ℕ) (k : Fin n) (g : R)
    (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m)
    (r : VectorR R m) (y : VectorR R n) :
    rerandomizeFullCoord R n m k g (mkSample R n m A s e) r y =
      mkSample R n m (addColVec R n m A k r) (fun j => s j + y j)
        (fun i => e i + r i * (g - s k)) := by
  dsimp [rerandomizeFullCoord, mkSample, evaluate, addColVec]
  congr 1
  ext i
  dsimp [evaluate, addColVec]
  have h_sum1 :
      (∑ j : Fin n, (A i j + if j = k then r i else 0) * (s j + y j)) =
        (∑ j : Fin n, A i j * s j) + r i * s k +
          ∑ j : Fin n, (A i j + if j = k then r i else 0) * y j := by
    have h_split :
        (∑ j : Fin n, (A i j + if j = k then r i else 0) * (s j + y j)) =
          (∑ j : Fin n, (A i j * s j + if j = k then r i * s j else 0)) +
            ∑ j : Fin n, (A i j + if j = k then r i else 0) * y j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [h_split, Finset.sum_add_distrib]
    simp
  rw [h_sum1]
  ring

theorem rerandomizeFullCoord_mkSample_eq (R : Type*) [CommRing R] (n m : ℕ) (k : Fin n)
    (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m)
    (r : VectorR R m) (y : VectorR R n) :
    rerandomizeFullCoord R n m k (s k) (mkSample R n m A s e) r y =
      mkSample R n m (addColVec R n m A k r) (fun j => s j + y j) e := by
  rw [rerandomizeFullCoord_mkSample]
  simp

theorem FinDist.prob_prod_prod_comm {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (d1 : FinDist α) (d2 : FinDist β) (d3 : FinDist γ) (d4 : FinDist δ)
    (P : (α × β) × (γ × δ) → Bool) :
    ((d1.prod d2).prod (d3.prod d4)).prob P =
      ((d1.prod d3).prod (d2.prod d4)).prob (fun q => P ((q.1.1, q.2.1), (q.1.2, q.2.2))) := by
  let e : (α × β) × (γ × δ) ≃ (α × γ) × (β × δ) :=
    { toFun := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
      invFun := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
      left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  have h_eq :
      (d1.prod d3).prod (d2.prod d4) = ((d1.prod d2).prod (d3.prod d4)).equivMap e := by
    dsimp [FinDist.prod, FinDist.equivMap, e]
    refine congrArg FinDist.mk ?_
    funext q
    exact Nat.mul_mul_mul_comm _ _ _ _
  rw [h_eq, FinDist.prob_equivMap]
  rfl

theorem prob_rerandomizeFullCoord_eq_mlweRealProb (R : Type*) [CommRing R] [Fintype R]
    (n m : ℕ) (k : Fin n) (s : VectorR R n)
    (eDist : FinDist (VectorR R m)) (D : Sample R n m → Bool) :
    (((uniformFinDist (MatrixR R n m)).prod eDist).prod
        ((uniformFinDist (VectorR R m)).prod (uniformFinDist (VectorR R n)))).prob
        (fun p => D (rerandomizeFullCoord R n m k (s k)
          (mkSample R n m p.1.1 s p.1.2) p.2.1 p.2.2)) =
      mlweRealProb R n m ((uniformFinDist (VectorR R n)).prod eDist) D := by
  let dM := uniformFinDist (MatrixR R n m)
  let dR := uniformFinDist (VectorR R m)
  let dY := uniformFinDist (VectorR R n)
  haveI : Nonempty (VectorR R m) := ⟨fun _ => 0⟩
  have h_rw :
      (((dM.prod eDist).prod (dR.prod dY)).prob
          (fun p => D (rerandomizeFullCoord R n m k (s k)
            (mkSample R n m p.1.1 s p.1.2) p.2.1 p.2.2))) =
        (dR.prod (dM.prod (dY.prod eDist))).prob
          (fun p => D (mkSample R n m (addColVec R n m p.2.1 k p.1)
            (fun j => s j + p.2.2.1 j) p.2.2.2)) := by
    let e_swap : ((MatrixR R n m × VectorR R m) × (VectorR R m × VectorR R n)) ≃
        (VectorR R m × (MatrixR R n m × (VectorR R n × VectorR R m))) :=
      { toFun := fun p => (p.2.1, (p.1.1, (p.2.2, p.1.2)))
        invFun := fun q => ((q.2.1, q.2.2.2), (q.1, q.2.2.1))
        left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
        right_inv := fun ⟨_, ⟨_, ⟨_, _⟩⟩⟩ => rfl }
    have h_dist_eq :
        dR.prod (dM.prod (dY.prod eDist)) =
          ((dM.prod eDist).prod (dR.prod dY)).equivMap e_swap := by
      dsimp [FinDist.prod, FinDist.equivMap, e_swap]
      refine congrArg FinDist.mk ?_
      funext q
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    rw [h_dist_eq, FinDist.prob_equivMap]
    refine congrArg _ ?_
    funext p
    rw [rerandomizeFullCoord_mkSample_eq]
    rfl
  rw [h_rw, FinDist.prob_prod_eq_sum_left]
  have h_const :
      ∀ r : VectorR R m,
        (dM.prod (dY.prod eDist)).prob
            (fun p => D (mkSample R n m (addColVec R n m p.1 k r)
              (fun j => s j + p.2.1 j) p.2.2)) =
          mlweRealProb R n m ((uniformFinDist (VectorR R n)).prod eDist) D := by
    intro r
    let e_mat : MatrixR R n m ≃ MatrixR R n m :=
      Equiv.addRight (fun i j => if j = k then r i else 0)
    let e_vec : VectorR R n ≃ VectorR R n := Equiv.addLeft s
    let e_all := Equiv.prodCongr e_mat (Equiv.prodCongr e_vec (Equiv.refl (VectorR R m)))
    have h_dist :
        mlweRealDist R n m ((uniformFinDist (VectorR R n)).prod eDist) =
          (dM.prod (dY.prod eDist)).equivMap e_all := by
      dsimp [mlweRealDist, e_all]
      rw [← uniformFinDist_equivMap e_mat, ← uniformFinDist_equivMap e_vec,
        ← FinDist.equivMap_refl eDist, FinDist.prod_equivMap, FinDist.prod_equivMap]
      rfl
    have h_fun :
        (fun p : MatrixR R n m × (VectorR R n × VectorR R m) =>
          D (mkSample R n m (addColVec R n m p.1 k r) (fun j => s j + p.2.1 j) p.2.2)) =
          (fun a => D (mkSample R n m (e_all a).1 (e_all a).2.1 (e_all a).2.2)) := by
      funext p
      rfl
    dsimp [mlweRealProb]
    rw [h_dist, FinDist.prob_equivMap, h_fun]
  simp_rw [h_const, ← Finset.sum_mul]
  have hsum : (∑ r : VectorR R m, (dR.weight r : ℚ)) = (dR.totalMass : ℚ) := by
    dsimp [FinDist.totalMass]
    rw [Nat.cast_sum]
  have hr_pos : 0 < dR.totalMass := uniformFinDist_totalMass_pos _
  have hne : (dR.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr_pos)
  rw [hsum, mul_div_cancel_left₀ _ hne]

def wrongGuessFieldEquiv (F : Type*) [Field F] (n m : ℕ) (k : Fin n)
    (s : VectorR F n) (g : F) (hg : g ≠ s k) (e : VectorR F m) (y : VectorR F n) :
    (MatrixR F n m × VectorR F m) ≃ Sample F n m where
  toFun p := rerandomizeFullCoord F n m k g (mkSample F n m p.1 s e) p.2 y
  invFun c :=
    let d := g - s k
    let r : VectorR F m := fun i => (c.b i - ∑ j : Fin n, c.A i j * (s j + y j) - e i) * d⁻¹
    let A : MatrixR F n m := fun i j => c.A i j - if j = k then r i else 0
    (A, r)
  left_inv p := by
    rcases p with ⟨A, r⟩
    have hd : g - s k ≠ 0 := sub_ne_zero.mpr hg
    dsimp only
    rw [rerandomizeFullCoord_mkSample]
    dsimp [mkSample, evaluate, addColVec]
    have h_r :
        ∀ i : Fin m,
          ((∑ j : Fin n, (A i j + if j = k then r i else 0) * (s j + y j)) +
              (e i + r i * (g - s k)) -
              ∑ j : Fin n, (A i j + if j = k then r i else 0) * (s j + y j) - e i) *
              (g - s k)⁻¹ =
            r i := by
      intro i
      have h_sub :
          ((∑ j : Fin n, (A i j + if j = k then r i else 0) * (s j + y j)) +
              (e i + r i * (g - s k))) -
              ∑ j : Fin n, (A i j + if j = k then r i else 0) * (s j + y j) - e i =
            r i * (g - s k) := by ring
      rw [h_sub, mul_inv_cancel_right₀ hd]
    apply Prod.ext
    · ext i j
      dsimp only
      rw [h_r i]
      ring
    · ext i
      exact h_r i
  right_inv c := by
    cases c with
    | mk cA cb =>
      have hd : g - s k ≠ 0 := sub_ne_zero.mpr hg
      dsimp only
      rw [rerandomizeFullCoord_mkSample]
      have hA :
          addColVec F n m
              (fun i j => cA i j - if j = k then
                (cb i - ∑ j1 : Fin n, cA i j1 * (s j1 + y j1) - e i) * (g - s k)⁻¹ else 0)
              k
              (fun i => (cb i - ∑ j1 : Fin n, cA i j1 * (s j1 + y j1) - e i) *
                (g - s k)⁻¹) =
            cA := by
        ext i j
        dsimp [addColVec]
        ring
      dsimp [mkSample]
      rw [hA]
      congr 1
      ext i
      dsimp [evaluate]
      rw [inv_mul_cancel_right₀ hd]
      ring

theorem prob_rerandomizeFullCoord_ne_eq_mlweUniformProb (F : Type*) [Field F] [Fintype F]
    (n m : ℕ) (k : Fin n) (s : VectorR F n) (g : F) (hg : g ≠ s k)
    (eDist : FinDist (VectorR F m)) (he : 0 < eDist.totalMass) (D : Sample F n m → Bool) :
    (((uniformFinDist (MatrixR F n m)).prod eDist).prod
        ((uniformFinDist (VectorR F m)).prod (uniformFinDist (VectorR F n)))).prob
        (fun p => D (rerandomizeFullCoord F n m k g
          (mkSample F n m p.1.1 s p.1.2) p.2.1 p.2.2)) =
      mlweUniformProb F n m D := by
  let dM := uniformFinDist (MatrixR F n m)
  let dR := uniformFinDist (VectorR F m)
  let dY := uniformFinDist (VectorR F n)
  rw [FinDist.prob_prod_prod_comm dM eDist dR dY]
  rw [FinDist.prob_prod_comm (dM.prod dR) (eDist.prod dY)]
  rw [FinDist.prob_prod_eq_sum_left (eDist.prod dY) (dM.prod dR)]
  have h_const :
      ∀ ey : VectorR F m × VectorR F n,
        (dM.prod dR).prob
            (fun mr => D (rerandomizeFullCoord F n m k g
              (mkSample F n m mr.1 s ey.1) mr.2 ey.2)) =
          mlweUniformProb F n m D := by
    intro ey
    dsimp [mlweUniformProb]
    rw [← uniformFinDist_prod]
    exact prob_uniform_comp_equiv (wrongGuessFieldEquiv F n m k s g hg ey.1 ey.2) D
  simp_rw [h_const, ← Finset.sum_mul]
  have hsum : (∑ ey : VectorR F m × VectorR F n, ((eDist.prod dY).weight ey : ℚ)) =
      ((eDist.prod dY).totalMass : ℚ) := by
    dsimp [FinDist.totalMass]
    rw [Nat.cast_sum]
  have h_ey_pos : 0 < (eDist.prod dY).totalMass :=
    FinDist.totalMass_prod_pos he (uniformFinDist_totalMass_pos _)
  have hne : ((eDist.prod dY).totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_ey_pos)
  rw [hsum, mul_div_cancel_left₀ _ hne]

def regevCoordGuess (F : Type*) [Field F] (n m : ℕ) (k : Fin n)
    (D : Sample F n m → Bool) (c : Sample F n m)
    (coins : (VectorR F m × VectorR F n) × (F × F)) : F :=
  if D (rerandomizeFullCoord F n m k coins.2.1 c coins.1.1 coins.1.2) then
    coins.2.1
  else
    coins.2.2

theorem regev_coord_search_exact_prob_field (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n m : ℕ) (k : Fin n) (s : VectorR F n)
    (eDist : FinDist (VectorR F m)) (he : 0 < eDist.totalMass) (D : Sample F n m → Bool) :
    let q : ℚ := Fintype.card F
    let d_se := (uniformFinDist (VectorR F n)).prod eDist
    let d_ry := (uniformFinDist (VectorR F m)).prod (uniformFinDist (VectorR F n))
    let d_gg := (uniformFinDist F).prod (uniformFinDist F)
    let d_all := (((uniformFinDist (MatrixR F n m)).prod eDist).prod d_ry).prod d_gg
    d_all.prob (fun p =>
      decide (regevCoordGuess F n m k D (mkSample F n m p.1.1.1 s p.1.1.2)
        (p.1.2, p.2) = s k)) =
      1 / q + ((q - 1) / q ^ 2) * (mlweRealProb F n m d_se D - mlweUniformProb F n m D) := by
  intro q d_se d_ry d_gg d_all
  let d_ae := (uniformFinDist (MatrixR F n m)).prod eDist
  let d_1 := d_ae.prod d_ry
  let dF := uniformFinDist F
  have hq_pos_nat : 0 < Fintype.card F := Fintype.card_pos
  have hq_ne : q ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq_pos_nat)
  have hq_card_pos : 1 ≤ Fintype.card F := hq_pos_nat
  have h_reassoc :
      d_all.prob (fun p =>
          decide (regevCoordGuess F n m k D (mkSample F n m p.1.1.1 s p.1.1.2)
            (p.1.2, p.2) = s k)) =
        (dF.prod (d_1.prod dF)).prob (fun p =>
          decide ((if D (rerandomizeFullCoord F n m k p.1
              (mkSample F n m p.2.1.1.1 s p.2.1.1.2) p.2.1.2.1 p.2.1.2.2)
            then p.1 else p.2.2) = s k)) := by
    let e_g0 :
        (((MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n)) × (F × F)) ≃
          (F × (((MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n)) × F)) :=
      { toFun := fun p => (p.2.1, (p.1, p.2.2))
        invFun := fun q => (q.2.1, (q.1, q.2.2))
        left_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl
        right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
    have h_dist_eq :
        dF.prod (d_1.prod dF) = d_all.equivMap e_g0 := by
      dsimp [d_all, d_gg, FinDist.prod, FinDist.equivMap, e_g0]
      refine congrArg FinDist.mk ?_
      funext q
      exact Nat.mul_left_comm _ _ _
    rw [h_dist_eq, FinDist.prob_equivMap]
    rfl
  rw [h_reassoc, FinDist.prob_prod_eq_sum_left dF (d_1.prod dF)]
  have h_for_g0 :
      ∀ g0 : F,
        (d_1.prod dF).prob (fun q0 =>
            decide ((if D (rerandomizeFullCoord F n m k g0
                (mkSample F n m q0.1.1.1 s q0.1.1.2) q0.1.2.1 q0.1.2.2)
              then g0 else q0.2) = s k)) =
          if g0 = s k then
            (1 + (q - 1) * mlweRealProb F n m d_se D) / q
          else
            (1 - mlweUniformProb F n m D) / q := by
    intro g0
    rw [FinDist.prob_prod_eq_sum_right d_1 dF]
    have h_inner_sum :
        (∑ g1 : F, (dF.weight g1 : ℚ) *
            d_1.prob (fun q1 =>
              decide ((if D (rerandomizeFullCoord F n m k g0
                  (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                then g0 else g1) = s k))) =
          if g0 = s k then
            1 + (q - 1) * mlweRealProb F n m d_se D
          else
            1 - mlweUniformProb F n m D := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (s k))]
      have hw1 : ∀ g1 : F, (dF.weight g1 : ℚ) = 1 := fun _ => rfl
      have h_d1_pos : 0 < d_1.totalMass := FinDist.totalMass_prod_pos
        (FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) he)
        (FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _)
          (uniformFinDist_totalMass_pos _))
      have h_erase_card : ((Finset.univ.erase (s k)).card : ℚ) = q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ (s k)), Finset.card_univ]
        rw [Nat.cast_sub hq_card_pos]
        simp [q]
      by_cases hg0 : g0 = s k
      · subst hg0
        rw [if_pos rfl]
        have h_term0 :
            d_1.prob (fun q1 =>
                decide ((if D (rerandomizeFullCoord F n m k (s k)
                    (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                  then s k else s k) = s k)) = 1 := by
          have h_true :
              (fun q1 : (MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n) =>
                decide ((if D (rerandomizeFullCoord F n m k (s k)
                    (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                  then s k else s k) = s k)) = (fun _ => true) := by
            funext q1
            split_ifs <;> simp
          rw [h_true, FinDist.prob_const_true d_1 h_d1_pos]
        have h_rest :
            ∀ g1 ∈ Finset.univ.erase (s k),
              (dF.weight g1 : ℚ) *
                d_1.prob (fun q1 =>
                  decide ((if D (rerandomizeFullCoord F n m k (s k)
                      (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                    then s k else g1) = s k)) =
                mlweRealProb F n m d_se D := by
          intro g1 hg1
          have hne : g1 ≠ s k := (Finset.mem_erase.mp hg1).1
          rw [hw1 g1, one_mul]
          have h_eqP :
              (fun q1 : (MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n) =>
                decide ((if D (rerandomizeFullCoord F n m k (s k)
                    (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                  then s k else g1) = s k)) =
                (fun q1 => D (rerandomizeFullCoord F n m k (s k)
                  (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)) := by
            funext q1
            cases hD : D (rerandomizeFullCoord F n m k (s k)
                (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2) <;> simp [hne]
          rw [h_eqP]
          exact prob_rerandomizeFullCoord_eq_mlweRealProb F n m k s eDist D
        rw [hw1 (s k), one_mul, h_term0, Finset.sum_congr rfl h_rest, Finset.sum_const,
          nsmul_eq_mul, h_erase_card]
      · rw [if_neg hg0]
        have h_term0 :
            d_1.prob (fun q1 =>
                decide ((if D (rerandomizeFullCoord F n m k g0
                    (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                  then g0 else s k) = s k)) =
              1 - mlweUniformProb F n m D := by
          have h_eqP :
              (fun q1 : (MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n) =>
                decide ((if D (rerandomizeFullCoord F n m k g0
                    (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                  then g0 else s k) = s k)) =
                (fun q1 => !(D (rerandomizeFullCoord F n m k g0
                  (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2))) := by
            funext q1
            cases hD : D (rerandomizeFullCoord F n m k g0
                (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2) <;> simp [hg0]
          rw [h_eqP, FinDist.prob_not d_1 h_d1_pos]
          rw [prob_rerandomizeFullCoord_ne_eq_mlweUniformProb F n m k s g0 hg0 eDist he D]
        have h_rest :
            ∀ g1 ∈ Finset.univ.erase (s k),
              (dF.weight g1 : ℚ) *
                d_1.prob (fun q1 =>
                  decide ((if D (rerandomizeFullCoord F n m k g0
                      (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                    then g0 else g1) = s k)) = 0 := by
          intro g1 hg1
          have hne : g1 ≠ s k := (Finset.mem_erase.mp hg1).1
          rw [hw1 g1, one_mul]
          have h_false :
              (fun q1 : (MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n) =>
                decide ((if D (rerandomizeFullCoord F n m k g0
                    (mkSample F n m q1.1.1 s q1.1.2) q1.2.1 q1.2.2)
                  then g0 else g1) = s k)) = (fun _ => false) := by
            funext q1
            split_ifs <;> simp [hg0, hne]
          rw [h_false, FinDist.prob_const_false]
        rw [hw1 (s k), one_mul, h_term0, Finset.sum_congr rfl h_rest, Finset.sum_const_zero,
          add_zero]
    rw [h_inner_sum, uniformFinDist_totalMass]
    by_cases hc : g0 = s k
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
  have h_outer :
      (∑ g0 : F, (dF.weight g0 : ℚ) *
          (d_1.prod dF).prob (fun q0 =>
            decide ((if D (rerandomizeFullCoord F n m k g0
                (mkSample F n m q0.1.1.1 s q0.1.1.2) q0.1.2.1 q0.1.2.2)
              then g0 else q0.2) = s k))) =
        (1 + (q - 1) * mlweRealProb F n m d_se D) / q +
          (q - 1) * ((1 - mlweUniformProb F n m D) / q) := by
    have h_congr :
        (∑ g0 : F, (dF.weight g0 : ℚ) *
            (d_1.prod dF).prob (fun q0 =>
              decide ((if D (rerandomizeFullCoord F n m k g0
                  (mkSample F n m q0.1.1.1 s q0.1.1.2) q0.1.2.1 q0.1.2.2)
                then g0 else q0.2) = s k))) =
          ∑ g0 : F, if g0 = s k then
            (1 + (q - 1) * mlweRealProb F n m d_se D) / q
          else
            (1 - mlweUniformProb F n m D) / q := by
      apply Finset.sum_congr rfl
      intro g0 _
      have hw : (dF.weight g0 : ℚ) = 1 := rfl
      rw [hw, one_mul, h_for_g0 g0]
    rw [h_congr, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (s k)), if_pos rfl]
    have h_erase :
        (∑ g0 ∈ Finset.univ.erase (s k),
          if g0 = s k then (1 + (q - 1) * mlweRealProb F n m d_se D) / q
          else (1 - mlweUniformProb F n m D) / q) =
          (q - 1) * ((1 - mlweUniformProb F n m D) / q) := by
      have h_neg :
          ∀ g0 ∈ Finset.univ.erase (s k),
            (if g0 = s k then (1 + (q - 1) * mlweRealProb F n m d_se D) / q
            else (1 - mlweUniformProb F n m D) / q) = (1 - mlweUniformProb F n m D) / q := by
        intro g0 hg0
        exact if_neg (Finset.mem_erase.mp hg0).1
      rw [Finset.sum_congr rfl h_neg, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ (s k)), Finset.card_univ,
        nsmul_eq_mul, Nat.cast_sub hq_card_pos]
      simp [q]
    rw [h_erase]
  rw [h_outer, uniformFinDist_totalMass]
  change ((1 + (q - 1) * mlweRealProb F n m d_se D) / q +
      (q - 1) * ((1 - mlweUniformProb F n m D) / q)) / q =
    1 / q + ((q - 1) / q ^ 2) * (mlweRealProb F n m d_se D - mlweUniformProb F n m D)
  field_simp
  ring

theorem regev_coord_search_to_decision_field (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n m : ℕ) (k : Fin n)
    (eDist : FinDist (VectorR F m)) (he : 0 < eDist.totalMass) (D : Sample F n m → Bool) :
    let q : ℚ := Fintype.card F
    let d_se := (uniformFinDist (VectorR F n)).prod eDist
    let d_ry := (uniformFinDist (VectorR F m)).prod (uniformFinDist (VectorR F n))
    let d_gg := (uniformFinDist F).prod (uniformFinDist F)
    let d_all := (((uniformFinDist (MatrixR F n m)).prod eDist).prod d_ry).prod d_gg
    ∃ solver_k : Sample F n m → (VectorR F m × VectorR F n) × (F × F) → F,
      ∀ s : VectorR F n,
        d_all.prob (fun p =>
          decide (solver_k (mkSample F n m p.1.1.1 s p.1.1.2) (p.1.2, p.2) = s k)) =
          1 / q + ((q - 1) / q ^ 2) * mlweAdvantage F n m d_se D := by
  intro q d_se d_ry d_gg d_all
  let D_pos : Sample F n m → Bool :=
    if mlweUniformProb F n m D ≤ mlweRealProb F n m d_se D then D else fun x => !(D x)
  refine ⟨regevCoordGuess F n m k D_pos, fun s => ?_⟩
  rw [regev_coord_search_exact_prob_field F n m k s eDist he D_pos]
  have h_adv : mlweRealProb F n m d_se D_pos - mlweUniformProb F n m D_pos =
      mlweAdvantage F n m d_se D := by
    by_cases h_le : mlweUniformProb F n m D ≤ mlweRealProb F n m d_se D
    · have h_dp : D_pos = D := if_pos h_le
      rw [h_dp, mlweAdvantage, abs_of_nonneg (sub_nonneg.mpr h_le)]
    · have h_lt : mlweRealProb F n m d_se D < mlweUniformProb F n m D := lt_of_not_ge h_le
      have h_dp : D_pos = fun x => !(D x) := if_neg h_le
      rw [h_dp]
      have h_real_pos : 0 < (mlweRealDist F n m d_se).totalMass :=
        FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _)
          (FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) he)
      haveI : Nonempty (Sample F n m) := ⟨{ A := 0, b := 0 }⟩
      have h_unif_pos : 0 < (uniformFinDist (Sample F n m)).totalMass :=
        uniformFinDist_totalMass_pos _
      have hr : mlweRealProb F n m d_se (fun x => !(D x)) = 1 - mlweRealProb F n m d_se D :=
        FinDist.prob_not (mlweRealDist F n m d_se) h_real_pos _
      have hu : mlweUniformProb F n m (fun x => !(D x)) = 1 - mlweUniformProb F n m D :=
        FinDist.prob_not (uniformFinDist (Sample F n m)) h_unif_pos D
      rw [hr, hu, mlweAdvantage, abs_of_neg (sub_neg.mpr h_lt)]
      ring
  rw [h_adv]

theorem regev_coord_search_to_decision_prime_zq (params : LWEParams) [Fact (Nat.Prime params.q)]
    (k : Fin params.n)
    (eDist : FinDist (VectorR (Zq params) params.m)) (he : 0 < eDist.totalMass)
    (D : Sample (Zq params) params.n params.m → Bool) :
    let d_se := (uniformFinDist (VectorR (Zq params) params.n)).prod eDist
    let d_ry := (uniformFinDist (VectorR (Zq params) params.m)).prod
      (uniformFinDist (VectorR (Zq params) params.n))
    let d_gg := (uniformFinDist (Zq params)).prod (uniformFinDist (Zq params))
    let d_all :=
      (((uniformFinDist (MatrixR (Zq params) params.n params.m)).prod eDist).prod d_ry).prod d_gg
    ∃ solver_k : Sample (Zq params) params.n params.m →
        (VectorR (Zq params) params.m × VectorR (Zq params) params.n) ×
          (Zq params × Zq params) → Zq params,
      ∀ s : VectorR (Zq params) params.n,
        d_all.prob (fun p =>
          decide (solver_k (mkSample (Zq params) params.n params.m p.1.1.1 s p.1.1.2)
            (p.1.2, p.2) = s k)) =
          1 / (params.q : ℚ) +
            (((params.q : ℚ) - 1) / (params.q : ℚ) ^ 2) *
              mlweAdvantage (Zq params) params.n params.m d_se D := by
  have hcard : (Fintype.card (Zq params) : ℚ) = (params.q : ℚ) := by
    rw [ZMod.card params.q]
  have h := regev_coord_search_to_decision_field (Zq params) params.n params.m k eDist he D
  simpa [hcard] using h

abbrev SearchLWECoins (R : Type*) (n m T : ℕ) :=
  Fin T → (VectorR R m × VectorR R n)

def searchLWEFixedSecretWinProb (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (n m T : ℕ) (eDist : FinDist (VectorR R m))
    (solver : (Fin T → Sample R n m) → SearchLWECoins R n m T → VectorR R n)
    (s : VectorR R n) : ℚ :=
  ((((uniformFinDist (MatrixR R n m)).prod eDist).iid T).prod
      (uniformFinDist (SearchLWECoins R n m T))).prob
    (fun p =>
      let samples : Fin T → Sample R n m := fun t => mkSample R n m (p.1 t).1 s (p.1 t).2
      decide (solver samples p.2 = s))

def searchLWEAvgWinProb (R : Type*) [CommRing R] [Fintype R] [DecidableEq R]
    (n m T : ℕ) (sDist : FinDist (VectorR R n)) (eDist : FinDist (VectorR R m))
    (solver : (Fin T → Sample R n m) → SearchLWECoins R n m T → VectorR R n) : ℚ :=
  (sDist.prod ((((uniformFinDist (MatrixR R n m)).prod eDist).iid T).prod
      (uniformFinDist (SearchLWECoins R n m T)))).prob
    (fun p =>
      let samples : Fin T → Sample R n m := fun t => mkSample R n m (p.2.1 t).1 p.1 (p.2.1 t).2
      decide (solver samples p.2.2 = p.1))

noncomputable def argmaxUniv {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) : α :=
  (Finset.univ.exists_max_image f Finset.univ_nonempty).choose

lemma le_argmaxUniv {α : Type*} [Fintype α] [Nonempty α] (f : α → ℚ) (x : α) :
    f x ≤ f (argmaxUniv f) :=
  (Finset.univ.exists_max_image f Finset.univ_nonempty).choose_spec.2 x (Finset.mem_univ x)

noncomputable def regevSearchSolver (F : Type*) [Field F] [Fintype F] (n m T : ℕ)
    (D : Sample F n m → Bool)
    (samples : Fin T → Sample F n m) (coins : SearchLWECoins F n m T) : VectorR F n :=
  fun k =>
    argmaxUniv (fun g : F =>
      (∑ t : Fin T,
        (bitToInt (D (rerandomizeFullCoord F n m k g (samples t) (coins t).1 (coins t).2)) : ℚ)) /
        (T : ℚ))

theorem regev_search_to_decision_field (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (n m T : ℕ) (hT : 0 < T)
    (eDist : FinDist (VectorR F m)) (he : 0 < eDist.totalMass)
    (D : Sample F n m → Bool) :
    let d_se := (uniformFinDist (VectorR F n)).prod eDist
    let ε := mlweAdvantage F n m d_se D
    ∃ solver : (Fin T → Sample F n m) → SearchLWECoins F n m T → VectorR F n,
      ∀ s : VectorR F n,
        (0 < ε →
          1 - ((n : ℚ) * (Fintype.card F : ℚ)) / ((T : ℚ) * ε ^ 2) ≤
            searchLWEFixedSecretWinProb F n m T eDist solver s) ∧
        ε ^ 2 ≤ ((n : ℚ) * (Fintype.card F : ℚ)) / (T : ℚ) +
          searchLWEFixedSecretWinProb F n m T eDist solver s := by
  intro d_se ε
  let D_pos : Sample F n m → Bool :=
    if mlweUniformProb F n m D ≤ mlweRealProb F n m d_se D then D else fun x => !(D x)
  have h_adv : mlweRealProb F n m d_se D_pos - mlweUniformProb F n m D_pos = ε := by
    by_cases h_le : mlweUniformProb F n m D ≤ mlweRealProb F n m d_se D
    · have h_dp : D_pos = D := if_pos h_le
      rw [h_dp]
      dsimp [ε, mlweAdvantage]
      exact (abs_of_nonneg (sub_nonneg.mpr h_le)).symm
    · have h_lt : mlweRealProb F n m d_se D < mlweUniformProb F n m D := lt_of_not_ge h_le
      have h_dp : D_pos = fun x => !(D x) := if_neg h_le
      rw [h_dp]
      have h_real_pos : 0 < (mlweRealDist F n m d_se).totalMass :=
        FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _)
          (FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) he)
      haveI : Nonempty (Sample F n m) := ⟨{ A := fun _ _ => 0, b := fun _ => 0 }⟩
      have h_unif_pos : 0 < (uniformFinDist (Sample F n m)).totalMass :=
        uniformFinDist_totalMass_pos _
      have hr : mlweRealProb F n m d_se (fun x => !(D x)) = 1 - mlweRealProb F n m d_se D :=
        FinDist.prob_not (mlweRealDist F n m d_se) h_real_pos _
      have hu : mlweUniformProb F n m (fun x => !(D x)) = 1 - mlweUniformProb F n m D :=
        FinDist.prob_not (uniformFinDist (Sample F n m)) h_unif_pos D
      rw [hr, hu]
      dsimp [ε, mlweAdvantage]
      rw [abs_of_neg (sub_neg.mpr h_lt)]
      ring
  refine ⟨regevSearchSolver F n m T D_pos, fun s => ?_⟩
  let d_ae := (uniformFinDist (MatrixR F n m)).prod eDist
  let d_c := uniformFinDist (VectorR F m × VectorR F n)
  let d_step := d_ae.prod d_c
  let d_joint := (d_ae.iid T).prod (uniformFinDist (SearchLWECoins F n m T))
  have h_ae_pos : 0 < d_ae.totalMass :=
    FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) he
  have h_c_pos : 0 < d_c.totalMass := uniformFinDist_totalMass_pos _
  have h_step_pos : 0 < d_step.totalMass := FinDist.totalMass_prod_pos h_ae_pos h_c_pos
  have h_joint_pos : 0 < d_joint.totalMass :=
    FinDist.totalMass_prod_pos (FinDist.totalMass_iid_pos d_ae h_ae_pos T)
      (uniformFinDist_totalMass_pos _)
  have h_d_joint_eq :
      d_joint = (d_step.iid T).equivMap
        (Equiv.arrowProdEquivProdArrow (Fin T)
          (fun _ => MatrixR F n m × VectorR F m)
          (fun _ => VectorR F m × VectorR F n)) := by
    dsimp [d_joint, d_step, d_c]
    rw [← uniformFinDist_iid (VectorR F m × VectorR F n) T, FinDist.prod_iid_equiv]
  have h_part1 :
      0 < ε →
        1 - ((n : ℚ) * (Fintype.card F : ℚ)) / ((T : ℚ) * ε ^ 2) ≤
          searchLWEFixedSecretWinProb F n m T eDist (regevSearchSolver F n m T D_pos) s := by
    intro hε
    let P_win : ((Fin T → MatrixR F n m × VectorR F m) × SearchLWECoins F n m T) → Bool :=
      fun p =>
        let samples : Fin T → Sample F n m := fun t => mkSample F n m (p.1 t).1 s (p.1 t).2
        decide (regevSearchSolver F n m T D_pos samples p.2 = s)
    let P_step : Fin n × F →
        ((MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n)) → Bool := fun kg x =>
      D_pos (rerandomizeFullCoord F n m kg.1 kg.2 (mkSample F n m x.1.1 s x.1.2) x.2.1 x.2.2)
    have h_step_prob :
        ∀ kg : Fin n × F,
          d_step.prob (P_step kg) =
            if kg.2 = s kg.1 then mlweRealProb F n m d_se D_pos
            else mlweUniformProb F n m D_pos := by
      intro kg
      by_cases hkg : kg.2 = s kg.1
      · rw [if_pos hkg]
        have h_eqP :
            P_step kg =
              (fun x : (MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n) =>
                D_pos (rerandomizeFullCoord F n m kg.1 (s kg.1)
                  (mkSample F n m x.1.1 s x.1.2) x.2.1 x.2.2)) := by
          funext x
          dsimp [P_step]
          rw [hkg]
        dsimp [d_step, d_ae, d_c]
        rw [h_eqP, uniformFinDist_prod]
        exact prob_rerandomizeFullCoord_eq_mlweRealProb F n m kg.1 s eDist D_pos
      · rw [if_neg hkg]
        dsimp [P_step, d_step, d_ae, d_c]
        rw [uniformFinDist_prod]
        exact prob_rerandomizeFullCoord_ne_eq_mlweUniformProb F n m kg.1 s kg.2 hkg eDist he D_pos
    have h_fail_eq :
        1 - searchLWEFixedSecretWinProb F n m T eDist (regevSearchSolver F n m T D_pos) s =
          (d_step.iid T).prob (fun v =>
            let samples : Fin T → Sample F n m := fun t => mkSample F n m (v t).1.1 s (v t).1.2
            let coins : SearchLWECoins F n m T := fun t => (v t).2
            !(decide (regevSearchSolver F n m T D_pos samples coins = s))) := by
      change 1 - d_joint.prob P_win = _
      rw [← FinDist.prob_not d_joint h_joint_pos P_win, h_d_joint_eq, FinDist.prob_equivMap]
      rfl
    let E_bad_v : (Fin T → ((MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n))) → Prop :=
      fun v =>
        let samples : Fin T → Sample F n m := fun t => mkSample F n m (v t).1.1 s (v t).1.2
        let coins : SearchLWECoins F n m T := fun t => (v t).2
        regevSearchSolver F n m T D_pos samples coins ≠ s
    let E_dev : Fin n × F →
        (Fin T → ((MatrixR F n m × VectorR F m) × (VectorR F m × VectorR F n))) → Prop :=
      fun kg v =>
        ε / 2 ≤ |(∑ t : Fin T, (bitToInt (P_step kg (v t)) : ℚ)) / (T : ℚ) -
          d_step.prob (P_step kg)|
    have h_imp :
        ∀ v, E_bad_v v → ∃ kg : Fin n × F, E_dev kg v := by
      intro v hv
      dsimp [E_bad_v] at hv
      have h_coord : ∃ k : Fin n,
          regevSearchSolver F n m T D_pos
            (fun t => mkSample F n m (v t).1.1 s (v t).1.2) (fun t => (v t).2) k ≠ s k := by
        by_contra h_all
        apply hv
        funext k
        by_contra h_ne
        exact h_all ⟨k, h_ne⟩
      rcases h_coord with ⟨k, hk⟩
      let g_hat := regevSearchSolver F n m T D_pos
        (fun t => mkSample F n m (v t).1.1 s (v t).1.2) (fun t => (v t).2) k
      have h_max :
          (∑ t : Fin T, (bitToInt (P_step (k, s k) (v t)) : ℚ)) / (T : ℚ) ≤
            (∑ t : Fin T, (bitToInt (P_step (k, g_hat) (v t)) : ℚ)) / (T : ℚ) := by
        exact le_argmaxUniv (fun g : F =>
          (∑ t : Fin T, (bitToInt (D_pos (rerandomizeFullCoord F n m k g
            (mkSample F n m (v t).1.1 s (v t).1.2) (v t).2.1 (v t).2.2)) : ℚ)) / (T : ℚ)) (s k)
      have hp1 : d_step.prob (P_step (k, s k)) = mlweRealProb F n m d_se D_pos := by
        rw [h_step_prob (k, s k), if_pos rfl]
      have hp0 : d_step.prob (P_step (k, g_hat)) = mlweUniformProb F n m D_pos := by
        rw [h_step_prob (k, g_hat), if_neg hk]
      by_cases h1 : E_dev (k, s k) v
      · exact ⟨(k, s k), h1⟩
      · refine ⟨(k, g_hat), ?_⟩
        dsimp [E_dev] at h1 ⊢
        rw [hp1] at h1
        rw [hp0]
        set m1 := (∑ t : Fin T, (bitToInt (P_step (k, s k) (v t)) : ℚ)) / (T : ℚ)
        set m0 := (∑ t : Fin T, (bitToInt (P_step (k, g_hat) (v t)) : ℚ)) / (T : ℚ)
        have h1_lt : |m1 - mlweRealProb F n m d_se D_pos| < ε / 2 := lt_of_not_ge h1
        have h_nl : mlweRealProb F n m d_se D_pos - m1 < ε / 2 :=
          lt_of_le_of_lt (by simpa [neg_sub] using neg_le_abs (m1 - mlweRealProb F n m d_se D_pos))
            h1_lt
        have h_diff_1 : mlweRealProb F n m d_se D_pos - ε / 2 < m1 :=
          sub_lt_iff_lt_add.mpr (by simpa [add_comm] using sub_lt_iff_lt_add.mp h_nl)
        have h_diff_1' : mlweRealProb F n m d_se D_pos - ε / 2 < m0 :=
          lt_of_lt_of_le h_diff_1 h_max
        have hp_eq : mlweRealProb F n m d_se D_pos = ε + mlweUniformProb F n m D_pos :=
          eq_add_of_sub_eq h_adv
        rw [hp_eq] at h_diff_1'
        have h_step_eq : ε + mlweUniformProb F n m D_pos - ε / 2 =
            mlweUniformProb F n m D_pos + ε / 2 := by ring
        rw [h_step_eq] at h_diff_1'
        have h_le_abs : ε / 2 ≤ m0 - mlweUniformProb F n m D_pos :=
          le_of_lt (lt_sub_iff_add_lt'.mpr h_diff_1')
        exact le_trans h_le_abs (le_abs_self _)
    have h_prob_bad :
        1 - searchLWEFixedSecretWinProb F n m T eDist (regevSearchSolver F n m T D_pos) s ≤
          ((n : ℚ) * (Fintype.card F : ℚ)) / ((T : ℚ) * ε ^ 2) := by
      rw [h_fail_eq, FinDist.prob_eq_eventProb]
      have h_ev_eq :
          (d_step.iid T).eventProb (fun v =>
              (!(decide (regevSearchSolver F n m T D_pos
                (fun t => mkSample F n m (v t).1.1 s (v t).1.2)
                (fun t => (v t).2) = s))) = true) =
            (d_step.iid T).eventProb E_bad_v := by
        refine (d_step.iid T).eventProb_congr _ _ (fun v => by simp [E_bad_v])
      rw [h_ev_eq]
      refine le_trans ((d_step.iid T).eventProb_mono E_bad_v (fun v => ∃ kg, E_dev kg v) h_imp) ?_
      refine le_trans ((d_step.iid T).eventProb_exists_le E_dev) ?_
      have h_half_pos : 0 < ε / 2 := half_pos hε
      have h_term : ∀ kg : Fin n × F,
          (d_step.iid T).eventProb (E_dev kg) ≤ 1 / (4 * (T : ℚ) * (ε / 2) ^ 2) :=
        fun kg => d_step.chebyshev_iid_prob_le h_step_pos T hT (P_step kg) (ε / 2) h_half_pos
      have h_sum_le :
          (∑ kg : Fin n × F, (d_step.iid T).eventProb (E_dev kg)) ≤
            ∑ _kg : Fin n × F, 1 / (4 * (T : ℚ) * (ε / 2) ^ 2) :=
        Finset.sum_le_sum (fun kg _ => h_term kg)
      refine le_trans h_sum_le ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_mul]
      have hT_ne : (T : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      have h_simp :
          ((n : ℚ) * (Fintype.card F : ℚ)) * (1 / (4 * (T : ℚ) * (ε / 2) ^ 2)) =
            ((n : ℚ) * (Fintype.card F : ℚ)) / ((T : ℚ) * ε ^ 2) := by
        field_simp
        ring
      rw [h_simp]
    exact sub_le_comm.mp h_prob_bad
  refine ⟨h_part1, ?_⟩
  by_cases hε0 : ε = 0
  · rw [hε0, zero_pow (by decide)]
    exact add_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (FinDist.prob_nonneg _ _)
  · have hε_pos : 0 < ε := lt_of_le_of_ne (mlweAdvantage_nonneg F n m d_se D) (Ne.symm hε0)
    have hp1 := h_part1 hε_pos
    have hε_le_one : ε ≤ 1 := mlweAdvantage_le_one F n m d_se D
    have hε_sq_le_one : ε ^ 2 ≤ 1 := by
      rw [sq, ← one_mul (1 : ℚ)]
      exact mul_le_mul hε_le_one hε_le_one (le_of_lt hε_pos) zero_le_one
    have hε_sq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε_pos
    have h_mul := mul_le_mul_of_nonneg_left hp1 (le_of_lt hε_sq_pos)
    have hT_ne : (T : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)
    have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
    have h_lhs :
        ε ^ 2 * (1 - ((n : ℚ) * (Fintype.card F : ℚ)) / ((T : ℚ) * ε ^ 2)) =
          ε ^ 2 - ((n : ℚ) * (Fintype.card F : ℚ)) / (T : ℚ) := by
      field_simp
    have h_rhs :
        ε ^ 2 * searchLWEFixedSecretWinProb F n m T eDist (regevSearchSolver F n m T D_pos) s ≤
          searchLWEFixedSecretWinProb F n m T eDist (regevSearchSolver F n m T D_pos) s := by
      have h_w0 : 0 ≤ searchLWEFixedSecretWinProb F n m T eDist
          (regevSearchSolver F n m T D_pos) s := FinDist.prob_nonneg _ _
      exact mul_le_of_le_one_left h_w0 hε_sq_le_one
    have h_sub :
        ε ^ 2 - ((n : ℚ) * (Fintype.card F : ℚ)) / (T : ℚ) ≤
          searchLWEFixedSecretWinProb F n m T eDist (regevSearchSolver F n m T D_pos) s :=
      le_trans (h_lhs ▸ h_mul) h_rhs
    rw [add_comm]
    exact sub_le_iff_le_add.mp h_sub

theorem regev_search_to_decision_prime_zq (params : LWEParams) [Fact (Nat.Prime params.q)]
    (T : ℕ) (hT : 0 < T)
    (eDist : FinDist (VectorR (Zq params) params.m)) (he : 0 < eDist.totalMass)
    (D : Sample (Zq params) params.n params.m → Bool) :
    let d_se := (uniformFinDist (VectorR (Zq params) params.n)).prod eDist
    let ε := mlweAdvantage (Zq params) params.n params.m d_se D
    ∃ solver : (Fin T → Sample (Zq params) params.n params.m) →
        SearchLWECoins (Zq params) params.n params.m T → VectorR (Zq params) params.n,
      ∀ s : VectorR (Zq params) params.n,
        (0 < ε →
          1 - ((params.n : ℚ) * (params.q : ℚ)) / ((T : ℚ) * ε ^ 2) ≤
            searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist solver s) ∧
        ε ^ 2 ≤ ((params.n : ℚ) * (params.q : ℚ)) / (T : ℚ) +
          searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist solver s := by
  have hcard : (Fintype.card (Zq params) : ℚ) = (params.q : ℚ) := by
    rw [ZMod.card params.q]
  have h := regev_search_to_decision_field (Zq params) params.n params.m T hT eDist he D
  simpa [hcard] using h

theorem regev_avg_search_to_decision_prime_zq (params : LWEParams) [Fact (Nat.Prime params.q)]
    (T : ℕ) (hT : 0 < T)
    (sDist : FinDist (VectorR (Zq params) params.n)) (hs : 0 < sDist.totalMass)
    (eDist : FinDist (VectorR (Zq params) params.m)) (he : 0 < eDist.totalMass)
    (D : Sample (Zq params) params.n params.m → Bool) :
    let d_se := (uniformFinDist (VectorR (Zq params) params.n)).prod eDist
    let ε := mlweAdvantage (Zq params) params.n params.m d_se D
    ∃ solver : (Fin T → Sample (Zq params) params.n params.m) →
        SearchLWECoins (Zq params) params.n params.m T → VectorR (Zq params) params.n,
      (0 < ε →
        1 - ((params.n : ℚ) * (params.q : ℚ)) / ((T : ℚ) * ε ^ 2) ≤
          searchLWEAvgWinProb (Zq params) params.n params.m T sDist eDist solver) ∧
      ε ^ 2 ≤ ((params.n : ℚ) * (params.q : ℚ)) / (T : ℚ) +
        searchLWEAvgWinProb (Zq params) params.n params.m T sDist eDist solver := by
  obtain ⟨solver, h_fixed⟩ := regev_search_to_decision_prime_zq params T hT eDist he D
  refine ⟨solver, ?_, ?_⟩
  · intro hε
    dsimp [searchLWEAvgWinProb]
    rw [FinDist.prob_prod_eq_sum_left]
    have h_term :
        ∀ s : VectorR (Zq params) params.n,
          (sDist.weight s : ℚ) *
              (1 - ((params.n : ℚ) * (params.q : ℚ)) /
                ((T : ℚ) * (mlweAdvantage (Zq params) params.n params.m
                  ((uniformFinDist (VectorR (Zq params) params.n)).prod eDist) D) ^ 2)) ≤
            (sDist.weight s : ℚ) *
              searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist solver s :=
      fun s => mul_le_mul_of_nonneg_left ((h_fixed s).1 hε) (Nat.cast_nonneg _)
    have h_sum_le :
        (∑ s : VectorR (Zq params) params.n,
          (sDist.weight s : ℚ) *
            (1 - ((params.n : ℚ) * (params.q : ℚ)) /
              ((T : ℚ) * (mlweAdvantage (Zq params) params.n params.m
                ((uniformFinDist (VectorR (Zq params) params.n)).prod eDist) D) ^ 2))) ≤
          ∑ s : VectorR (Zq params) params.n,
            (sDist.weight s : ℚ) *
              searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist solver s :=
      Finset.sum_le_sum (fun s _ => h_term s)
    rw [← Finset.sum_mul] at h_sum_le
    have hs_pos : (0 : ℚ) < (sDist.totalMass : ℚ) := Nat.cast_pos.mpr hs
    have h_div := div_le_div_of_nonneg_right h_sum_le (le_of_lt hs_pos)
    have hsum : (∑ s : VectorR (Zq params) params.n, (sDist.weight s : ℚ)) =
        (sDist.totalMass : ℚ) := by
      dsimp [FinDist.totalMass]
      rw [Nat.cast_sum]
    rw [hsum, mul_div_cancel_left₀ _ (ne_of_gt hs_pos)] at h_div
    exact h_div
  · dsimp [searchLWEAvgWinProb]
    rw [FinDist.prob_prod_eq_sum_left]
    have hs_pos : (0 : ℚ) < (sDist.totalMass : ℚ) := Nat.cast_pos.mpr hs
    let err : ℚ := ((params.n : ℚ) * (params.q : ℚ)) / (T : ℚ)
    let ε := mlweAdvantage (Zq params) params.n params.m
      ((uniformFinDist (VectorR (Zq params) params.n)).prod eDist) D
    have h_term :
        ∀ s : VectorR (Zq params) params.n,
          (sDist.weight s : ℚ) * (ε ^ 2 - err) ≤
            (sDist.weight s : ℚ) *
              searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist solver s := by
      intro s
      have hs2 := (h_fixed s).2
      have h_sub : ε ^ 2 - err ≤ searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist
          solver s := by
        refine sub_le_iff_le_add.mpr ?_
        rw [add_comm _ err]
        exact hs2
      exact mul_le_mul_of_nonneg_left h_sub (Nat.cast_nonneg _)
    have h_sum_le :
        (∑ s : VectorR (Zq params) params.n, (sDist.weight s : ℚ) * (ε ^ 2 - err)) ≤
          ∑ s : VectorR (Zq params) params.n,
            (sDist.weight s : ℚ) *
              searchLWEFixedSecretWinProb (Zq params) params.n params.m T eDist solver s :=
      Finset.sum_le_sum (fun s _ => h_term s)
    rw [← Finset.sum_mul] at h_sum_le
    have h_div := div_le_div_of_nonneg_right h_sum_le (le_of_lt hs_pos)
    have hsum : (∑ s : VectorR (Zq params) params.n, (sDist.weight s : ℚ)) =
        (sDist.totalMass : ℚ) := by
      dsimp [FinDist.totalMass]
      rw [Nat.cast_sum]
    rw [hsum, mul_div_cancel_left₀ _ (ne_of_gt hs_pos)] at h_div
    rw [add_comm err _]
    exact sub_le_iff_le_add.mp h_div

end PrimeSearchToDecisionLWE

section ConcreteSecurityAndMaster

open scoped BigOperators

def foReprogramFull {PK Msg Coins Key : Type*} [DecidableEq Msg]
    (G : PK → Msg → Key × Coins) (m_star : Msg) (k_new : Key) (c_new : Coins) :
    PK → Msg → Key × Coins :=
  fun pk m => if m = m_star then (k_new, c_new) else G pk m

theorem foEncDet_reprogramFull_self {PK Msg Coins Key CT : Type*} [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (G : PK → Msg → Key × Coins) (m_star : Msg) (k_new : Key) (c_new : Coins) (pk : PK) :
    foEncDet encPKE (foReprogramFull G m_star k_new c_new) pk m_star = encPKE pk m_star c_new := by
  simp [foEncDet, foReprogramFull]

theorem foDecapsSim_reprogramFull_eq_of_not_mem {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (m_star : Msg) (k_new : Key) (c_new : Coins)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT)
    (h_not_mem : m_star ∉ Q_G) :
    foDecapsSim encPKE decPKE (foReprogramFull G m_star k_new c_new) J Q_G pk sk z ct =
      foDecapsSim encPKE decPKE G J Q_G pk sk z ct := by
  dsimp [foDecapsSim, foEncDet, foReprogramFull]
  by_cases hm_in : decPKE sk ct ∈ Q_G
  · have h_ne : decPKE sk ct ≠ m_star := fun h_eq => h_not_mem (h_eq ▸ hm_in)
    have h_ite : (if decPKE sk ct = m_star then (k_new, c_new) else G pk (decPKE sk ct)) =
        G pk (decPKE sk ct) := if_neg h_ne
    simp only [h_ite]
    by_cases h_enc : encPKE pk (decPKE sk ct) (G pk (decPKE sk ct)).2 = ct
    · rw [if_pos ⟨hm_in, h_enc⟩, if_pos ⟨hm_in, h_enc⟩]
    · have h_n1 : ¬ (decPKE sk ct ∈ Q_G ∧
          encPKE pk (decPKE sk ct) (G pk (decPKE sk ct)).2 = ct) :=
        fun h => h_enc h.2
      rw [if_neg h_n1, if_neg h_n1]
  · have h_n1 : ¬ (decPKE sk ct ∈ Q_G ∧
        encPKE pk (decPKE sk ct)
          (if decPKE sk ct = m_star then (k_new, c_new) else G pk (decPKE sk ct)).2 = ct) :=
      fun h => hm_in h.1
    have h_n2 : ¬ (decPKE sk ct ∈ Q_G ∧
        encPKE pk (decPKE sk ct) (G pk (decPKE sk ct)).2 = ct) :=
      fun h => hm_in h.1
    rw [if_neg h_n1, if_neg h_n2]

theorem foBadDecapsEvent_reprogramFull_imp {PK SK Msg Coins Key CT : Type*}
    [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (m_star : Msg) (k_new : Key) (c_new : Coins)
    (pk : PK) (sk : SK) (ct : CT)
    (h_ne_chal : ct ≠ encPKE pk m_star c_new)
    (h_bad : foBadDecapsEvent encPKE decPKE (foReprogramFull G m_star k_new c_new) Q_G pk sk ct) :
    foBadDecapsEvent encPKE decPKE G Q_G pk sk ct := by
  dsimp [foBadDecapsEvent, foEncDet, foReprogramFull] at h_bad ⊢
  rcases h_bad with ⟨h_notin, h_enc⟩
  refine ⟨h_notin, ?_⟩
  by_cases h_eq : decPKE sk ct = m_star
  · rw [h_eq, if_pos rfl] at h_enc
    exact False.elim (h_ne_chal h_enc.symm)
  · rwa [if_neg h_eq] at h_enc

theorem prob_uniform_key_pair_guess_eq_half {α Key : Type*}
    [Fintype α] [Fintype Key] [Nonempty Key]
    (d : FinDist α) (h_pos : 0 < d.totalMass) (f : α → Key → Bool) :
    ((d.prod ((uniformFinDist Key).prod (uniformFinDist Key))).prod (uniformFinDist Bool)).prob
      (fun x => f x.1.1 (if x.2 then x.1.2.2 else x.1.2.1) == x.2) = 1 / 2 := by
  let dK := uniformFinDist Key
  let dK2 := dK.prod dK
  have hm :
      ((d.prod dK2).prod (uniformFinDist Bool)).totalMass =
        d.totalMass * (Fintype.card Key * Fintype.card Key) * 2 := by
    rw [FinDist.totalMass_prod, FinDist.totalMass_prod, FinDist.totalMass_prod]
    simp only [dK, uniformFinDist_totalMass, Fintype.card_bool]
  have hw :
      ((d.prod dK2).prod (uniformFinDist Bool)).acceptWeight
        (fun x => f x.1.1 (if x.2 then x.1.2.2 else x.1.2.1) == x.2) =
        (d.totalMass : ℤ) * ((Fintype.card Key : ℤ) * (Fintype.card Key : ℤ)) := by
    rw [FinDist.acceptWeight_prod_right]
    have h_inner :
        ∀ b : Bool,
          (uniformFinDist Bool).weight b = 1 ∧
          (d.prod dK2).acceptWeight
              (fun ak => f ak.1 (if b then ak.2.2 else ak.2.1) == b) =
            ∑ a : α, (d.weight a : ℤ) *
              ((Fintype.card Key : ℤ) * ∑ k : Key, bitToInt (f a k == b)) := by
      intro b
      refine ⟨rfl, ?_⟩
      rw [FinDist.acceptWeight_prod_left]
      apply Finset.sum_congr rfl
      intro a _
      have hk :
          dK2.acceptWeight (fun kk => f a (if b then kk.2 else kk.1) == b) =
            (Fintype.card Key : ℤ) * ∑ k : Key, bitToInt (f a k == b) := by
        dsimp [dK2, dK]
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [FinDist.acceptWeight_prod_left]
          have h_f : ∀ k0 : Key,
              (dK.weight k0 : ℤ) * dK.acceptWeight (fun _k1 : Key => f a k0 == false) =
                (Fintype.card Key : ℤ) * bitToInt (f a k0 == false) := by
            intro k0
            rw [uniformFinDist_acceptWeight]
            have hw0 : (dK.weight k0 : ℤ) = 1 := rfl
            rw [hw0, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp [dK] at h_f ⊢
          simp_rw [h_f, ← Finset.mul_sum]
        · simp only [↓reduceIte]
          rw [FinDist.acceptWeight_prod_right]
          have h_t : ∀ k1 : Key,
              (dK.weight k1 : ℤ) * dK.acceptWeight (fun _k0 : Key => f a k1 == true) =
                (Fintype.card Key : ℤ) * bitToInt (f a k1 == true) := by
            intro k1
            rw [uniformFinDist_acceptWeight]
            have hw1 : (dK.weight k1 : ℤ) = 1 := rfl
            rw [hw1, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          dsimp [dK] at h_t ⊢
          simp_rw [h_t, ← Finset.mul_sum]
      rw [hk]
    have h_sum_b :
        (∑ b : Bool, ((uniformFinDist Bool).weight b : ℤ) *
          (d.prod dK2).acceptWeight (fun ak => f ak.1 (if b then ak.2.2 else ak.2.1) == b)) =
          ∑ b : Bool, ∑ a : α, (d.weight a : ℤ) *
            ((Fintype.card Key : ℤ) * ∑ k : Key, bitToInt (f a k == b)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [(h_inner b).1, (h_inner b).2]
      push_cast
      rw [one_mul]
    rw [h_sum_b, Finset.sum_comm]
    have h_term :
        ∀ a : α,
          (∑ b : Bool, (d.weight a : ℤ) *
            ((Fintype.card Key : ℤ) * ∑ k : Key, bitToInt (f a k == b))) =
            (d.weight a : ℤ) * ((Fintype.card Key : ℤ) * (Fintype.card Key : ℤ)) := by
      intro a
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
      have h_k : ∀ k : Key, (∑ b : Bool, bitToInt (f a k == b)) = 1 := by
        intro k
        rw [Fintype.sum_bool]
        cases f a k <;> simp [bitToInt]
      simp_rw [h_k, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    simp_rw [h_term, ← Finset.sum_mul, FinDist.totalMass, Nat.cast_sum]
  dsimp [FinDist.prob]
  rw [hw, hm]
  push_cast
  have h1 : (d.totalMass : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_pos)
  have h2 : (Fintype.card Key : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt Fintype.card_pos)
  field_simp

theorem fo_rational_bit_ind_cca2_reduction
    {PK SK Msg Coins Key Seed CT Base : Type*}
    [Fintype Msg] [Fintype Coins] [Fintype Key] [Fintype Base]
    [DecidableEq Msg] [DecidableEq CT]
    [Nonempty Msg] [Nonempty Key]
    (pk_of : Base → PK) (sk_of : Base → SK) (z_of : Base → Seed)
    (encPKE : PK → Msg → Coins → CT) (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins) (J : Seed → CT → Key)
    (baseDist : FinDist Base) (h_base : 0 < baseDist.totalMass)
    (coinDist : FinDist Coins) (h_coin : 0 < coinDist.totalMass)
    {q_D : ℕ}
    (Q_G : PK → CT → Finset Msg)
    (ct_queries : PK → CT → Fin q_D → CT)
    (adv : PK → CT → Key → (Fin q_D → Key) → Bool)
    (h_non_chal : ∀ (pk : PK) (ct : CT) (i : Fin q_D), ct_queries pk ct i ≠ ct) :
    let d_base := baseDist.prod ((uniformFinDist Msg).prod coinDist)
    let d_fo := (d_base.prod ((uniformFinDist Key).prod (uniformFinDist Key))).prod
      (uniformFinDist Bool)
    let WinPred : ((Base × (Msg × Coins)) × (Key × Key)) × Bool → Bool := fun ω =>
      let base := ω.1.1.1
      let m_star := ω.1.1.2.1
      let c_star := ω.1.1.2.2
      let k0 := ω.1.2.1
      let k1 := ω.1.2.2
      let b := ω.2
      let pk := pk_of base
      let sk := sk_of base
      let z := z_of base
      let G' := foReprogramFull G m_star k0 c_star
      let ct_star := foEncDet encPKE G' pk m_star
      adv pk ct_star (if b then k1 else k0)
        (fun i => foDecapsReal encPKE decPKE G' J pk sk z (ct_queries pk ct_star i)) == b
    let BadDecapsBase : Base × (Msg × Coins) → Prop := fun w =>
      let pk := pk_of w.1
      let sk := sk_of w.1
      let ct_star := encPKE pk w.2.1 w.2.2
      ∃ i : Fin q_D, foBadDecapsEvent encPKE decPKE G (Q_G pk ct_star) pk sk
        (ct_queries pk ct_star i)
    let QueryChallengeBase : Base × (Msg × Coins) → Prop := fun w =>
      w.2.1 ∈ Q_G (pk_of w.1) (encPKE (pk_of w.1) w.2.1 w.2.2)
    |d_fo.prob WinPred - 1 / 2| ≤
      d_base.eventProb BadDecapsBase + d_base.eventProb QueryChallengeBase := by
  intro d_base d_fo WinPred BadDecapsBase QueryChallengeBase
  have h_db_pos : 0 < d_base.totalMass :=
    FinDist.totalMass_prod_pos h_base
      (FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) h_coin)
  let dK2 := (uniformFinDist Key).prod (uniformFinDist Key)
  have h_dk2_pos : 0 < dK2.totalMass :=
    FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) (uniformFinDist_totalMass_pos _)
  let SimPred : ((Base × (Msg × Coins)) × (Key × Key)) × Bool → Bool := fun ω =>
    let base := ω.1.1.1
    let m_star := ω.1.1.2.1
    let c_star := ω.1.1.2.2
    let k0 := ω.1.2.1
    let k1 := ω.1.2.2
    let b := ω.2
    let pk := pk_of base
    let sk := sk_of base
    let z := z_of base
    let G' := foReprogramFull G m_star k0 c_star
    let ct_star := encPKE pk m_star c_star
    adv pk ct_star (if b then k1 else k0)
      (fun i => foDecapsSim encPKE decPKE G' J (Q_G pk ct_star) pk sk z
        (ct_queries pk ct_star i)) == b
  let IdealPred : ((Base × (Msg × Coins)) × (Key × Key)) × Bool → Bool := fun ω =>
    let base := ω.1.1.1
    let m_star := ω.1.1.2.1
    let c_star := ω.1.1.2.2
    let k0 := ω.1.2.1
    let k1 := ω.1.2.2
    let b := ω.2
    let pk := pk_of base
    let sk := sk_of base
    let z := z_of base
    let ct_star := encPKE pk m_star c_star
    adv pk ct_star (if b then k1 else k0)
      (fun i => foDecapsSim encPKE decPKE G J (Q_G pk ct_star) pk sk z
        (ct_queries pk ct_star i)) == b
  let BadDecapsFull : ((Base × (Msg × Coins)) × (Key × Key)) × Bool → Prop :=
    fun ω => BadDecapsBase ω.1.1
  let QueryChallengeFull : ((Base × (Msg × Coins)) × (Key × Key)) × Bool → Prop :=
    fun ω => QueryChallengeBase ω.1.1
  have h_hop1 : ∀ ω, ¬ BadDecapsFull ω → WinPred ω = SimPred ω := by
    intro ω h_nbad
    rcases ω with ⟨⟨⟨base, m_star, c_star⟩, ⟨k0, k1⟩⟩, b⟩
    dsimp [WinPred, SimPred]
    have h_ct : foEncDet encPKE (foReprogramFull G m_star k0 c_star) (pk_of base) m_star =
        encPKE (pk_of base) m_star c_star :=
      foEncDet_reprogramFull_self encPKE G m_star k0 c_star (pk_of base)
    rw [h_ct]
    have h_no_bad_G' : ∀ i : Fin q_D,
        ¬ foBadDecapsEvent encPKE decPKE (foReprogramFull G m_star k0 c_star)
          (Q_G (pk_of base) (encPKE (pk_of base) m_star c_star))
          (pk_of base) (sk_of base)
          (ct_queries (pk_of base) (encPKE (pk_of base) m_star c_star) i) :=
      fun i h_bad => h_nbad ⟨i, foBadDecapsEvent_reprogramFull_imp encPKE decPKE G
        (Q_G (pk_of base) (encPKE (pk_of base) m_star c_star)) m_star k0 c_star
        (pk_of base) (sk_of base) (ct_queries (pk_of base) (encPKE (pk_of base) m_star c_star) i)
        (h_non_chal (pk_of base) (encPKE (pk_of base) m_star c_star) i) h_bad⟩
    have h_tr := foDecapsTranscript_eq_of_no_bad encPKE decPKE
      (foReprogramFull G m_star k0 c_star) J
      (Q_G (pk_of base) (encPKE (pk_of base) m_star c_star))
      (pk_of base) (sk_of base) (z_of base)
      (ct_queries (pk_of base) (encPKE (pk_of base) m_star c_star)) h_no_bad_G'
    rw [h_tr]
  have h_hop2 : ∀ ω, ¬ QueryChallengeFull ω → SimPred ω = IdealPred ω := by
    intro ω h_nq
    rcases ω with ⟨⟨⟨base, m_star, c_star⟩, ⟨k0, k1⟩⟩, b⟩
    dsimp [SimPred, IdealPred]
    have h_tr :
        (fun i : Fin q_D => foDecapsSim encPKE decPKE (foReprogramFull G m_star k0 c_star) J
          (Q_G (pk_of base) (encPKE (pk_of base) m_star c_star)) (pk_of base) (sk_of base)
          (z_of base) (ct_queries (pk_of base) (encPKE (pk_of base) m_star c_star) i)) =
          (fun i : Fin q_D => foDecapsSim encPKE decPKE G J
            (Q_G (pk_of base) (encPKE (pk_of base) m_star c_star)) (pk_of base) (sk_of base)
            (z_of base) (ct_queries (pk_of base) (encPKE (pk_of base) m_star c_star) i)) := by
      ext i
      exact foDecapsSim_reprogramFull_eq_of_not_mem encPKE decPKE G J
        (Q_G (pk_of base) (encPKE (pk_of base) m_star c_star)) m_star k0 c_star
        (pk_of base) (sk_of base) (z_of base)
        (ct_queries (pk_of base) (encPKE (pk_of base) m_star c_star) i) h_nq
    rw [h_tr]
  have h_ideal : d_fo.prob IdealPred = 1 / 2 := by
    let f_ideal : (Base × (Msg × Coins)) → Key → Bool := fun w key =>
      let pk := pk_of w.1
      let sk := sk_of w.1
      let z := z_of w.1
      let ct_star := encPKE pk w.2.1 w.2.2
      adv pk ct_star key
        (fun i => foDecapsSim encPKE decPKE G J (Q_G pk ct_star) pk sk z (ct_queries pk ct_star i))
    exact prob_uniform_key_pair_guess_eq_half d_base h_db_pos f_ideal
  have h_b1 := d_fo.abs_prob_sub_le_eventProb WinPred SimPred BadDecapsFull h_hop1
  have h_b2 := d_fo.abs_prob_sub_le_eventProb SimPred IdealPred QueryChallengeFull h_hop2
  have h_ev1 : d_fo.eventProb BadDecapsFull = d_base.eventProb BadDecapsBase := by
    dsimp [d_fo, BadDecapsFull]
    rw [FinDist.eventProb_prod_left (d_base.prod dK2) (uniformFinDist Bool)
      (uniformFinDist_totalMass_pos Bool) (fun p => BadDecapsBase p.1)]
    exact FinDist.eventProb_prod_left d_base dK2 h_dk2_pos BadDecapsBase
  have h_ev2 : d_fo.eventProb QueryChallengeFull = d_base.eventProb QueryChallengeBase := by
    dsimp [d_fo, QueryChallengeFull]
    rw [FinDist.eventProb_prod_left (d_base.prod dK2) (uniformFinDist Bool)
      (uniformFinDist_totalMass_pos Bool) (fun p => QueryChallengeBase p.1)]
    exact FinDist.eventProb_prod_left d_base dK2 h_dk2_pos QueryChallengeBase
  rw [← h_ideal]
  rw [h_ev1] at h_b1
  rw [h_ev2] at h_b2
  exact le_trans (abs_sub_le _ (d_fo.prob SimPred) _) (add_le_add h_b1 h_b2)

def modFOEncNoiseDist (params : LWEParams) (k N : ℕ) {Coins : Type*} [Fintype Coins]
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (coinDist : FinDist Coins) :
    FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      (VectorR (NegacyclicPoly (Zq params) N) k × NegacyclicPoly (Zq params) N)) :=
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  coinDist.map (fun c => (expandR c, (expandE1 c, expandE2 c)))

def modKEMFOINDCPAWinProb {Coins Key Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    [Fintype Coins] [Fintype Key] [Fintype Seed]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (coinDist : FinDist Coins) (seedDist : FinDist Seed)
    {q_D : ℕ}
    (ct_queries : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k →
      Fin q_D → ModPKECiphertext (NegacyclicPoly (Zq params) N) k)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key → (Fin q_D → Key) → Bool) : ℚ :=
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  let d_kg_full := (uniformFinDist (MatrixR (NegacyclicPoly (Zq params) N) k k)).prod kgDist
  let d_base := (d_kg_full.prod seedDist).prod ((uniformFinDist (Fin N → Fin t)).prod coinDist)
  let d_fo := (d_base.prod ((uniformFinDist Key).prod (uniformFinDist Key))).prod
    (uniformFinDist Bool)
  d_fo.prob (fun ω =>
    let base := ω.1.1.1
    let A := base.1.1
    let s := base.1.2.1
    let e := base.1.2.2
    let z := base.2
    let m_star := ω.1.1.2.1
    let c_star := ω.1.1.2.2
    let k0 := ω.1.2.1
    let k1 := ω.1.2.2
    let b := ω.2
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let G' := foReprogramFull G m_star k0 c_star
    let ct_star := (modKEMEncapsFin params k N Δ t G' expandR expandE1 expandE2 pk m_star).1
    adv pk ct_star (if b then k1 else k0)
      (fun i => modKEMDecapsFin params k N Δ t G' expandR expandE1 expandE2 J pk s z
        (ct_queries pk ct_star i)) == b)

def modKEMFOINDCPAAdvantage {Coins Key Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    [Fintype Coins] [Fintype Key] [Fintype Seed]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (coinDist : FinDist Coins) (seedDist : FinDist Seed)
    {q_D : ℕ}
    (ct_queries : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k →
      Fin q_D → ModPKECiphertext (NegacyclicPoly (Zq params) N) k)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key → (Fin q_D → Key) → Bool) : ℚ :=
  |modKEMFOINDCPAWinProb params k N Δ t G expandR expandE1 expandE2 J kgDist coinDist seedDist
    ct_queries adv - 1 / 2|

def modKEMBadDecapsProb {Coins Key Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    [Fintype Coins] [Fintype Seed]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (coinDist : FinDist Coins) (seedDist : FinDist Seed)
    {q_D : ℕ}
    (Q_G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Finset (Fin N → Fin t))
    (ct_queries : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k →
      Fin q_D → ModPKECiphertext (NegacyclicPoly (Zq params) N) k) : ℚ :=
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  let d_kg_full := (uniformFinDist (MatrixR (NegacyclicPoly (Zq params) N) k k)).prod kgDist
  let d_base := (d_kg_full.prod seedDist).prod ((uniformFinDist (Fin N → Fin t)).prod coinDist)
  let encPKE := modFOEncPKE params k N Δ t expandR expandE1 expandE2
  let decPKE := modFODecPKE params k N Δ t
  d_base.eventProb (fun w =>
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k w.1.1.1 w.1.1.2.1 w.1.1.2.2
    let ct_star := encPKE pk w.2.1 w.2.2
    ∃ i : Fin q_D, foBadDecapsEvent encPKE decPKE G (Q_G pk ct_star) pk w.1.1.2.1
      (ct_queries pk ct_star i))

theorem modKEM_fo_ind_cca2_to_mlwe {Coins Key Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    [Fintype Coins] [Fintype Key] [Nonempty Key] [Fintype Seed]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (kgDist : FinDist (VectorR (NegacyclicPoly (Zq params) N) k ×
      VectorR (NegacyclicPoly (Zq params) N) k))
    (h_kg : 0 < kgDist.totalMass)
    (coinDist : FinDist Coins) (h_coin : 0 < coinDist.totalMass)
    (seedDist : FinDist Seed) (h_seed : 0 < seedDist.totalMass)
    {q_D q_G : ℕ}
    (Q_G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Finset (Fin N → Fin t))
    (hQ : ∀ pk ct, (Q_G pk ct).card ≤ q_G)
    (ct_queries : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k →
      Fin q_D → ModPKECiphertext (NegacyclicPoly (Zq params) N) k)
    (h_non_chal : ∀ pk ct i, ct_queries pk ct i ≠ ct)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k →
      ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key → (Fin q_D → Key) → Bool) :
    letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
    let encNoiseDist := modFOEncNoiseDist params k N expandR expandE1 expandE2 coinDist
    ∃ (B_kg : Sample (NegacyclicPoly (Zq params) N) k k → Bool)
      (B_enc : Sample (NegacyclicPoly (Zq params) N) k (k + 1) → Bool),
      modKEMFOINDCPAAdvantage params k N Δ t G expandR expandE1 expandE2 J kgDist coinDist seedDist
          ct_queries adv ≤
        modKEMBadDecapsProb params k N Δ t G expandR expandE1 expandE2 kgDist coinDist seedDist
            Q_G ct_queries +
          (q_G : ℚ) / ((t : ℚ) ^ N) +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k k kgDist B_kg +
          mlweAdvantage (NegacyclicPoly (Zq params) N) k (k + 1)
            (modPKEEncSampleDist (NegacyclicPoly (Zq params) N) k encNoiseDist) B_enc := by
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  let R := NegacyclicPoly (Zq params) N
  let encPKE := modFOEncPKE params k N Δ t expandR expandE1 expandE2
  let decPKE := modFODecPKE params k N Δ t
  let d_kg_full := (uniformFinDist (MatrixR R k k)).prod kgDist
  let baseDist := d_kg_full.prod seedDist
  let d_base := baseDist.prod ((uniformFinDist (Fin N → Fin t)).prod coinDist)
  have h_kg_full_pos : 0 < d_kg_full.totalMass :=
    FinDist.totalMass_prod_pos (uniformFinDist_totalMass_pos _) h_kg
  have h_base_pos : 0 < baseDist.totalMass := FinDist.totalMass_prod_pos h_kg_full_pos h_seed
  haveI : Nonempty (Fin N → Fin t) := ⟨fun _ => ⟨0, Fact.out⟩⟩
  let pk_of : ((MatrixR R k k × (VectorR R k × VectorR R k)) × Seed) → ModPKEPublicKey R k :=
    fun base => modPKEKeygen R k base.1.1 base.1.2.1 base.1.2.2
  let sk_of : ((MatrixR R k k × (VectorR R k × VectorR R k)) × Seed) → VectorR R k :=
    fun base => base.1.2.1
  let z_of : ((MatrixR R k k × (VectorR R k × VectorR R k)) × Seed) → Seed := fun base => base.2
  have h_fo := fo_rational_bit_ind_cca2_reduction pk_of sk_of z_of encPKE decPKE G J
    baseDist h_base_pos coinDist h_coin Q_G ct_queries adv h_non_chal
  have h_win_eq :
      modKEMFOINDCPAWinProb params k N Δ t G expandR expandE1 expandE2 J kgDist coinDist seedDist
          ct_queries adv =
        ((d_base.prod ((uniformFinDist Key).prod (uniformFinDist Key))).prod
            (uniformFinDist Bool)).prob (fun ω =>
          let base := ω.1.1.1
          let m_star := ω.1.1.2.1
          let c_star := ω.1.1.2.2
          let k0 := ω.1.2.1
          let k1 := ω.1.2.2
          let b := ω.2
          let pk := pk_of base
          let sk := sk_of base
          let z := z_of base
          let G' := foReprogramFull G m_star k0 c_star
          let ct_star := foEncDet encPKE G' pk m_star
          adv pk ct_star (if b then k1 else k0)
            (fun i => foDecapsReal encPKE decPKE G' J pk sk z (ct_queries pk ct_star i)) ==
              b) := by
    dsimp [modKEMFOINDCPAWinProb, modKEMEncapsFin, foEncDet, encPKE, pk_of, sk_of, z_of]
    refine congrArg _ ?_
    funext ω
    simp_rw [modKEMDecapsFin_eq_foDecapsReal]
    rfl
  dsimp only at h_fo
  rw [← h_win_eq] at h_fo
  change modKEMFOINDCPAAdvantage params k N Δ t G expandR expandE1 expandE2 J kgDist coinDist
      seedDist ct_queries adv ≤
    modKEMBadDecapsProb params k N Δ t G expandR expandE1 expandE2 kgDist coinDist seedDist
      Q_G ct_queries +
      d_base.eventProb (fun w => w.2.1 ∈ Q_G (pk_of w.1) (encPKE (pk_of w.1) w.2.1 w.2.2)) at h_fo
  let encNoiseDist := modFOEncNoiseDist params k N expandR expandE1 expandE2 coinDist
  have h_enc_pos : 0 < encNoiseDist.totalMass := FinDist.totalMass_map_pos _ h_coin
  let f_noise : Coins → VectorR R k × (VectorR R k × R) :=
    fun c => (expandR c, (expandE1 c, expandE2 c))
  have h_q_eq :
      d_base.eventProb (fun w => w.2.1 ∈ Q_G (pk_of w.1) (encPKE (pk_of w.1) w.2.1 w.2.2)) =
        modPKEListOWCPAWinProb R k (Fin N → Fin t) (bfvEncodePolyFin params N Δ t) kgDist
          encNoiseDist Q_G := by
    rw [FinDist.eventProb_eq_prob_decide]
    let e_sd :
        (((MatrixR R k k × (VectorR R k × VectorR R k)) × Seed) × ((Fin N → Fin t) × Coins)) ≃
          (((MatrixR R k k × (VectorR R k × VectorR R k)) × ((Fin N → Fin t) × Coins)) × Seed) :=
      { toFun := fun w => ((w.1.1, w.2), w.1.2)
        invFun := fun q => ((q.1.1, q.2), q.1.2)
        left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
        right_inv := fun ⟨⟨_, ⟨_, _⟩⟩, _⟩ => rfl }
    let d_mc := (uniformFinDist (Fin N → Fin t)).prod coinDist
    have h_drop_seed :
        d_base.prob (fun w =>
            decide (w.2.1 ∈ Q_G (pk_of w.1) (encPKE (pk_of w.1) w.2.1 w.2.2))) =
          (d_kg_full.prod d_mc).prob (fun w =>
            let pk := modPKEKeygen R k w.1.1 w.1.2.1 w.1.2.2
            decide (w.2.1 ∈ Q_G pk (encPKE pk w.2.1 w.2.2))) := by
      have h_eq :
          (d_kg_full.prod d_mc).prod seedDist = d_base.equivMap e_sd := by
        dsimp [d_base, baseDist, d_mc, FinDist.prod, FinDist.equivMap, e_sd]
        refine congrArg FinDist.mk ?_
        funext q
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have h_fst := FinDist.prob_prod_fst (d_kg_full.prod d_mc) seedDist h_seed
        (fun w =>
          let pk := modPKEKeygen R k w.1.1 w.1.2.1 w.1.2.2
          decide (w.2.1 ∈ Q_G pk (encPKE pk w.2.1 w.2.2)))
      rw [← h_fst, h_eq, FinDist.prob_equivMap]
      rfl
    rw [h_drop_seed, FinDist.prob_prod_eq_sum_left]
    dsimp [modPKEListOWCPAWinProb, modPKERealAuxProb]
    rw [FinDist.prob_prod_eq_sum_left]
    refine congrArg (fun x : ℚ => x / (d_kg_full.totalMass : ℚ)) ?_
    apply Finset.sum_congr rfl
    intro kg _
    refine congrArg (fun x : ℚ => (d_kg_full.weight kg : ℚ) * x) ?_
    let pk := modPKEKeygen R k kg.1 kg.2.1 kg.2.2
    rw [FinDist.prob_prod_comm (uniformFinDist (Fin N → Fin t)) coinDist]
    dsimp [encNoiseDist, modFOEncNoiseDist]
    rw [FinDist.prob_prod_map_left f_noise coinDist (uniformFinDist (Fin N → Fin t))]
    rfl
  obtain ⟨B_kg, B_enc, h_ow⟩ := modPKE_poly_list_ow_cpa_to_mlwe params k N Δ t q_G kgDist
    encNoiseDist h_enc_pos Q_G hQ
  refine ⟨B_kg, B_enc, le_trans h_fo ?_⟩
  rw [h_q_eq, add_assoc, add_assoc]
  exact add_le_add le_rfl (by simpa [add_assoc] using h_ow)

def cbd1Elem (R : Type*) [Ring R] (ab : Bool × Bool) : R :=
  (if ab.1 then 1 else 0) - (if ab.2 then 1 else 0)

lemma cbd1Elem_isTernaryElem (R : Type*) [Ring R] (ab : Bool × Bool) :
    IsTernaryElem (cbd1Elem R ab) := by
  rcases ab with ⟨a, b⟩
  cases a <;> cases b <;> simp [cbd1Elem, IsTernaryElem]

def cbd1Poly (R : Type*) [Ring R] (N : ℕ) (bits : Fin N → Bool × Bool) : NegacyclicPoly R N :=
  ⟨fun i => cbd1Elem R (bits i)⟩

def cbd1PolyDist (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N : ℕ) :
    FinDist (NegacyclicPoly R N) :=
  ((uniformFinDist (Bool × Bool)).iid N).map (cbd1Poly R N)

def cbd1VecDist (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N k : ℕ) :
    FinDist (VectorR (NegacyclicPoly R N) k) :=
  (cbd1PolyDist R N).iid k

def cbd1KeygenDist (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N k : ℕ) :
    FinDist (VectorR (NegacyclicPoly R N) k × VectorR (NegacyclicPoly R N) k) :=
  (cbd1VecDist R N k).prod (cbd1VecDist R N k)

def cbd1EncDist (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N k : ℕ) :
    FinDist (VectorR (NegacyclicPoly R N) k ×
      (VectorR (NegacyclicPoly R N) k × NegacyclicPoly R N)) :=
  (cbd1VecDist R N k).prod ((cbd1VecDist R N k).prod (cbd1PolyDist R N))

lemma cbd1PolyDist_totalMass_pos (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N : ℕ) :
    0 < (cbd1PolyDist R N).totalMass :=
  FinDist.totalMass_map_pos _
    (FinDist.totalMass_iid_pos _ (uniformFinDist_totalMass_pos (Bool × Bool)) N)

lemma cbd1VecDist_totalMass_pos (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N k : ℕ) :
    0 < (cbd1VecDist R N k).totalMass :=
  FinDist.totalMass_iid_pos _ (cbd1PolyDist_totalMass_pos R N) k

lemma cbd1KeygenDist_totalMass_pos (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N k : ℕ) :
    0 < (cbd1KeygenDist R N k).totalMass :=
  FinDist.totalMass_prod_pos (cbd1VecDist_totalMass_pos R N k) (cbd1VecDist_totalMass_pos R N k)

lemma cbd1EncDist_totalMass_pos (R : Type*) [Ring R] [Fintype R] [DecidableEq R] (N k : ℕ) :
    0 < (cbd1EncDist R N k).totalMass :=
  FinDist.totalMass_prod_pos (cbd1VecDist_totalMass_pos R N k)
    (FinDist.totalMass_prod_pos (cbd1VecDist_totalMass_pos R N k) (cbd1PolyDist_totalMass_pos R N))

theorem cbd1PolyDist_pos_isTernaryPoly (R : Type*) [Ring R] [Fintype R] [DecidableEq R]
    (N : ℕ) (p : NegacyclicPoly R N) (hp : 0 < (cbd1PolyDist R N).weight p) :
    NegacyclicPoly.IsTernaryPoly p := by
  rw [cbd1PolyDist, FinDist.pos_weight_map_iff] at hp
  rcases hp with ⟨bits, h_eq, _⟩
  subst h_eq
  intro i
  exact cbd1Elem_isTernaryElem R (bits i)

theorem cbd1VecDist_pos_isTernaryPoly (R : Type*) [Ring R] [Fintype R] [DecidableEq R]
    (N k : ℕ) (v : VectorR (NegacyclicPoly R N) k)
    (hv : 0 < (cbd1VecDist R N k).weight v) :
    ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (v i) := by
  intro i
  apply cbd1PolyDist_pos_isTernaryPoly
  dsimp [cbd1VecDist, FinDist.iid] at hv
  by_contra h0
  have hzi : (cbd1PolyDist R N).weight (v i) = 0 := by omega
  have h_prod0 : (∏ t : Fin k, (cbd1PolyDist R N).weight (v t)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hzi
  omega

theorem cbd1KeygenDist_pos_ternary_and_norm (params : LWEParams) (N k : ℕ)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (h_pos : 0 < (cbd1KeygenDist (Zq params) N k).weight (s, e)) :
    (∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i)) ∧
      (∀ i : Fin k, normInf params (e i).coeffs ≤ 1) := by
  dsimp [cbd1KeygenDist, FinDist.prod] at h_pos
  have hs_pos : 0 < (cbd1VecDist (Zq params) N k).weight s :=
    Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at h_pos; omega)
  have he_pos : 0 < (cbd1VecDist (Zq params) N k).weight e :=
    Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at h_pos; omega)
  refine ⟨cbd1VecDist_pos_isTernaryPoly _ N k s hs_pos, fun i => ?_⟩
  exact NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N (e i)
    (cbd1VecDist_pos_isTernaryPoly _ N k e he_pos i)

theorem cbd1EncDist_pos_ternary_and_norm (params : LWEParams) (N k : ℕ)
    (r e1 : VectorR (NegacyclicPoly (Zq params) N) k) (e2 : NegacyclicPoly (Zq params) N)
    (h_pos : 0 < (cbd1EncDist (Zq params) N k).weight (r, (e1, e2))) :
    (∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (r i)) ∧
      (∀ i : Fin k, normInf params (e1 i).coeffs ≤ 1) ∧
      normInf params e2.coeffs ≤ 1 := by
  dsimp [cbd1EncDist, FinDist.prod] at h_pos
  have hr_pos : 0 < (cbd1VecDist (Zq params) N k).weight r :=
    Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at h_pos; omega)
  have he12_pos :
      0 < (cbd1VecDist (Zq params) N k).weight e1 * (cbd1PolyDist (Zq params) N).weight e2 :=
    Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at h_pos; omega)
  have he1_pos : 0 < (cbd1VecDist (Zq params) N k).weight e1 :=
    Nat.pos_of_ne_zero (fun h => by rw [h, zero_mul] at he12_pos; omega)
  have he2_pos : 0 < (cbd1PolyDist (Zq params) N).weight e2 :=
    Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at he12_pos; omega)
  refine ⟨cbd1VecDist_pos_isTernaryPoly _ N k r hr_pos, fun i => ?_, ?_⟩
  · exact NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N (e1 i)
      (cbd1VecDist_pos_isTernaryPoly _ N k e1 he1_pos i)
  · exact NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N e2
      (cbd1PolyDist_pos_isTernaryPoly _ N e2 he2_pos)

theorem FinDist.map_prod {α₁ α₂ β₁ β₂ : Type*}
    [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂] [DecidableEq β₁] [DecidableEq β₂]
    (f1 : α₁ → β₁) (f2 : α₂ → β₂) (d1 : FinDist α₁) (d2 : FinDist α₂) :
    (d1.prod d2).map (fun p => (f1 p.1, f2 p.2)) = (d1.map f1).prod (d2.map f2) := by
  dsimp [FinDist.map, FinDist.prod]
  refine congrArg FinDist.mk ?_
  funext ⟨b1, b2⟩
  rw [Fintype.sum_prod_type]
  have h_term : ∀ a1 : α₁,
      (∑ a2 : α₂, if (f1 a1, f2 a2) = (b1, b2) then d1.weight a1 * d2.weight a2 else 0) =
        (if f1 a1 = b1 then d1.weight a1 else 0) *
          (∑ a2 : α₂, if f2 a2 = b2 then d2.weight a2 else 0) := by
    intro a1
    by_cases h1 : f1 a1 = b1
    · rw [if_pos h1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a2 _
      by_cases h2 : f2 a2 = b2 <;> simp [h1, h2]
    · rw [if_neg h1, zero_mul]
      apply Finset.sum_eq_zero
      intro a2 _
      have hne : (f1 a1, f2 a2) ≠ (b1, b2) := fun h => h1 (congrArg Prod.fst h)
      rw [if_neg hne]
  simp_rw [h_term, ← Finset.sum_mul]

theorem FinDist.map_iid {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (d : FinDist α) (k : ℕ) :
    (d.iid k).map (fun v i => f (v i)) = (d.map f).iid k := by
  dsimp [FinDist.map, FinDist.iid]
  refine congrArg FinDist.mk ?_
  funext w
  have h_term : ∀ v : Fin k → α,
      (if (fun i => f (v i)) = w then ∏ i : Fin k, d.weight (v i) else 0) =
        ∏ i : Fin k, if f (v i) = w i then d.weight (v i) else 0 := by
    intro v
    by_cases hv : (fun i => f (v i)) = w
    · rw [if_pos hv]
      exact (Finset.prod_congr rfl fun i _ => if_pos (congrFun hv i)).symm
    · rw [if_neg hv]
      have h_ex : ∃ i : Fin k, f (v i) ≠ w i := by
        by_contra h_all
        apply hv
        funext i
        by_contra hne
        exact h_all ⟨i, hne⟩
      rcases h_ex with ⟨i0, hi0⟩
      exact (Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg hi0)).symm
  simp_rw [h_term]
  exact (Fintype.prod_sum
    (fun (i : Fin k) (a : α) => if f a = w i then d.weight a else 0)).symm

abbrev CBD1EncCoins (N k : ℕ) :=
  (Fin k → Fin N → Bool × Bool) × ((Fin k → Fin N → Bool × Bool) × (Fin N → Bool × Bool))

def cbd1ExpandR (params : LWEParams) (N k : ℕ) (c : CBD1EncCoins N k) :
    VectorR (NegacyclicPoly (Zq params) N) k :=
  fun i => cbd1Poly (Zq params) N (c.1 i)

def cbd1ExpandE1 (params : LWEParams) (N k : ℕ) (c : CBD1EncCoins N k) :
    VectorR (NegacyclicPoly (Zq params) N) k :=
  fun i => cbd1Poly (Zq params) N (c.2.1 i)

def cbd1ExpandE2 (params : LWEParams) (N k : ℕ) (c : CBD1EncCoins N k) :
    NegacyclicPoly (Zq params) N :=
  cbd1Poly (Zq params) N c.2.2

lemma cbd1ExpandR_isTernary (params : LWEParams) (N k : ℕ) (c : CBD1EncCoins N k)
    (i : Fin k) : NegacyclicPoly.IsTernaryPoly (cbd1ExpandR params N k c i) :=
  fun j => cbd1Elem_isTernaryElem (Zq params) (c.1 i j)

lemma cbd1ExpandE1_normInf (params : LWEParams) (N k : ℕ) (c : CBD1EncCoins N k)
    (i : Fin k) : normInf params (cbd1ExpandE1 params N k c i).coeffs ≤ 1 :=
  NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N _
    (fun j => cbd1Elem_isTernaryElem (Zq params) (c.2.1 i j))

lemma cbd1ExpandE2_normInf (params : LWEParams) (N k : ℕ) (c : CBD1EncCoins N k) :
    normInf params (cbd1ExpandE2 params N k c).coeffs ≤ 1 :=
  NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N _
    (fun j => cbd1Elem_isTernaryElem (Zq params) (c.2.2 j))

theorem modFOEncNoiseDist_cbd1Coins_eq (params : LWEParams) (k N : ℕ) :
    letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
    modFOEncNoiseDist params k N (cbd1ExpandR params N k) (cbd1ExpandE1 params N k)
        (cbd1ExpandE2 params N k) (uniformFinDist (CBD1EncCoins N k)) =
      cbd1EncDist (Zq params) N k := by
  letI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  let dB := (uniformFinDist (Bool × Bool)).iid N
  let dK := dB.iid k
  have h_dB : uniformFinDist (Fin N → Bool × Bool) = dB := (uniformFinDist_iid _ N).symm
  have h_dK : uniformFinDist (Fin k → Fin N → Bool × Bool) = dK := by
    dsimp [dK, dB]
    rw [uniformFinDist_iid, uniformFinDist_iid]
  have h_unif :
      uniformFinDist (CBD1EncCoins N k) = dK.prod (dK.prod dB) := by
    rw [uniformFinDist_prod, uniformFinDist_prod, h_dK, h_dB]
  dsimp [modFOEncNoiseDist]
  rw [h_unif]
  have h_e2 : dB.map (cbd1Poly (Zq params) N) = cbd1PolyDist (Zq params) N := rfl
  have h_vec : dK.map (fun (v : Fin k → Fin N → Bool × Bool) i => cbd1Poly (Zq params) N (v i)) =
      cbd1VecDist (Zq params) N k := by
    dsimp [dK, dB, cbd1VecDist, cbd1PolyDist]
    exact FinDist.map_iid (cbd1Poly (Zq params) N) dB k
  dsimp [cbd1EncDist]
  have h_map1 :
      (dK.prod (dK.prod dB)).map (fun c =>
          (cbd1ExpandR params N k c, (cbd1ExpandE1 params N k c, cbd1ExpandE2 params N k c))) =
        (dK.map (fun v i => cbd1Poly (Zq params) N (v i))).prod
          ((dK.prod dB).map (fun p =>
            ((fun v i => cbd1Poly (Zq params) N (v i)) p.1, cbd1Poly (Zq params) N p.2))) := by
    rw [← FinDist.map_prod]
    rfl
  have h_map2 :
      (dK.prod dB).map (fun p =>
          ((fun v i => cbd1Poly (Zq params) N (v i)) p.1, cbd1Poly (Zq params) N p.2)) =
        (dK.map (fun v i => cbd1Poly (Zq params) N (v i))).prod
          (dB.map (cbd1Poly (Zq params) N)) :=
    FinDist.map_prod (fun v i => cbd1Poly (Zq params) N (v i)) (cbd1Poly (Zq params) N) dK dB
  rw [h_map1, h_map2, h_vec, h_e2]

theorem FinDist.prob_eq_one_of_support {α : Type*} [Fintype α]
    (dist : FinDist α) (h_pos : 0 < dist.totalMass) (P : α → Bool)
    (h_supp : ∀ x : α, 0 < dist.weight x → P x = true) :
    dist.prob P = 1 := by
  dsimp [FinDist.prob]
  have hw : dist.acceptWeight P = (dist.totalMass : ℤ) := by
    dsimp [FinDist.acceptWeight, FinDist.totalMass]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : 0 < dist.weight x
    · rw [h_supp x hx]
      simp [bitToInt]
    · have hx0 : dist.weight x = 0 := by omega
      simp [hx0]
  rw [hw]
  push_cast
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt h_pos))

local instance : Fact (0 < 2) := ⟨by decide⟩
local instance : Fact (0 < 256) := ⟨by decide⟩

theorem standardZeroFailure_cbd1_kem_correct_prob_eq_one
    {Coins Key Seed : Type*} [DecidableEq Key]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      (Fin 256 → Fin 2) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (expandE2 : Coins → NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 → Key)
    (z : Seed)
    (hr_tern : ∀ c : Coins, ∀ i : Fin 4, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin 4,
      normInf standardZeroFailureParams (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf standardZeroFailureParams (expandE2 c).coeffs ≤ 1) :
    let p := standardZeroFailureParams
    let d_kg := (uniformFinDist (MatrixR (NegacyclicPoly (Zq p) 256) 4 4)).prod
      (cbd1KeygenDist (Zq p) 256 4)
    d_kg.prob (fun aes =>
      let pk := modPKEKeygen (NegacyclicPoly (Zq p) 256) 4 aes.1 aes.2.1 aes.2.2
      decide (∀ m : Fin 256 → Fin 2,
        let enc := modKEMEncapsFin p 4 256 6144 2 G expandR expandE1 expandE2 pk m
        modKEMDecapsFin p 4 256 6144 2 G expandR expandE1 expandE2 J pk aes.2.1 z enc.1 =
          enc.2)) = 1 := by
  intro p d_kg
  have h_pos : 0 < d_kg.totalMass := FinDist.totalMass_prod_pos
    (uniformFinDist_totalMass_pos _) (cbd1KeygenDist_totalMass_pos _ 256 4)
  refine FinDist.prob_eq_one_of_support d_kg h_pos _ (fun aes h_wt => ?_)
  dsimp [d_kg, FinDist.prod] at h_wt
  have hw_se : 0 < (cbd1KeygenDist (Zq p) 256 4).weight aes.2 :=
    Nat.pos_of_ne_zero (fun h => by rw [h, mul_zero] at h_wt; omega)
  obtain ⟨hs_tern, he_norm⟩ := cbd1KeygenDist_pos_ternary_and_norm p 256 4 aes.2.1 aes.2.2 hw_se
  rw [decide_eq_true_iff]
  have h_corr := modPKE_instIsCorrectFOPKE p 4 256 6144 2 G expandR expandE1 expandE2
    aes.1 aes.2.1 aes.2.2 (by dsimp only [p]; decide) hs_tern he_norm hr_tern he1_norm he2_norm
    (by decide)
  intro m enc
  have hm := h_corr m
  change modKEMDecapsFin p 4 256 6144 2 G expandR expandE1 expandE2 J
    (modPKEKeygen (NegacyclicPoly (Zq p) 256) 4 aes.1 aes.2.1 aes.2.2) aes.2.1 z
    (foEncDet (modFOEncPKE p 4 256 6144 2 expandR expandE1 expandE2) G
      (modPKEKeygen (NegacyclicPoly (Zq p) 256) 4 aes.1 aes.2.1 aes.2.2) m) =
    (G (modPKEKeygen (NegacyclicPoly (Zq p) 256) 4 aes.1 aes.2.1 aes.2.2) m).1
  rw [modKEMDecapsFin_eq_foDecapsReal]
  dsimp [foDecapsReal]
  have hm' :
      modFODecPKE p 4 256 6144 2 aes.2.1
          (foEncDet (modFOEncPKE p 4 256 6144 2 expandR expandE1 expandE2) G
            (modPKEKeygen (NegacyclicPoly (Zq p) 256) 4 aes.1 aes.2.1 aes.2.2) m) = m := hm
  rw [hm', if_pos rfl]

instance instFactPrimeToyZeroFailure : Fact (Nat.Prime toyZeroFailureParams.q) :=
  ⟨by decide⟩

instance instFactPrimeMLKEM : Fact (Nat.Prime mlkemPrimeParams.q) :=
  ⟨mlkemPrimeParams_prime⟩

instance instFactPrimeStandardZeroFailure : Fact (Nat.Prime standardZeroFailureParams.q) :=
  ⟨standardZeroFailureParams_prime⟩

theorem mlkem_prime_search_to_decision
    (T : ℕ) (hT : 0 < T)
    (eDist : FinDist (VectorR (Zq mlkemPrimeParams) mlkemPrimeParams.m))
    (he : 0 < eDist.totalMass)
    (D : Sample (Zq mlkemPrimeParams) mlkemPrimeParams.n mlkemPrimeParams.m → Bool)
    (μ0 μ1 : NegacyclicPoly (Zq mlkemPrimeParams) 256)
    (adv : ModPKEPublicKey (NegacyclicPoly (Zq mlkemPrimeParams) 256) 3 →
      ModPKEQuantizedCiphertext 256 3 → Bool) :
    let R768 := NegacyclicPoly (Zq mlkemPrimeParams) 256
    let d_se := (uniformFinDist (VectorR (Zq mlkemPrimeParams) mlkemPrimeParams.n)).prod eDist
    let ε := mlweAdvantage (Zq mlkemPrimeParams) mlkemPrimeParams.n mlkemPrimeParams.m d_se D
    (∃ solver : (Fin T → Sample (Zq mlkemPrimeParams) mlkemPrimeParams.n mlkemPrimeParams.m) →
        SearchLWECoins (Zq mlkemPrimeParams) mlkemPrimeParams.n mlkemPrimeParams.m T →
        VectorR (Zq mlkemPrimeParams) mlkemPrimeParams.n,
      ∀ s : VectorR (Zq mlkemPrimeParams) mlkemPrimeParams.n,
        (0 < ε →
          1 - ((mlkemPrimeParams.n : ℚ) * (mlkemPrimeParams.q : ℚ)) / ((T : ℚ) * ε ^ 2) ≤
            searchLWEFixedSecretWinProb (Zq mlkemPrimeParams)
              mlkemPrimeParams.n mlkemPrimeParams.m T eDist solver s) ∧
        ε ^ 2 ≤ ((mlkemPrimeParams.n : ℚ) * (mlkemPrimeParams.q : ℚ)) / (T : ℚ) +
          searchLWEFixedSecretWinProb (Zq mlkemPrimeParams)
            mlkemPrimeParams.n mlkemPrimeParams.m T eDist solver s) ∧
    (∃ (B_kg : Sample R768 3 3 → Bool) (B_enc : Sample R768 3 4 → Bool),
      modPKECompressedBitINDCPAAdvantage mlkemPrimeParams 256 3 10 4
          (cbd1KeygenDist (Zq mlkemPrimeParams) 256 3)
          (cbd1EncDist (Zq mlkemPrimeParams) 256 3) μ0 μ1 adv ≤
        mlweAdvantage R768 3 3 (cbd1KeygenDist (Zq mlkemPrimeParams) 256 3) B_kg +
          mlweAdvantage R768 3 4
            (modPKEEncSampleDist R768 3 (cbd1EncDist (Zq mlkemPrimeParams) 256 3)) B_enc) :=
  ⟨regev_search_to_decision_prime_zq mlkemPrimeParams T hT eDist he D,
    modPKE_compressed_bit_ind_cpa_to_mlwe mlkemPrimeParams 256 3 10 4
      (cbd1KeygenDist _ 256 3) (cbd1EncDist _ 256 3) (cbd1EncDist_totalMass_pos _ 256 3)
      μ0 μ1 adv⟩

theorem standardZeroFailure_fo_cca2_and_s2d_master
    {Key Seed : Type*} [Fintype Key] [Nonempty Key] [DecidableEq Key] [Fintype Seed]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      (Fin 256 → Fin 2) → Key × CBD1EncCoins 256 4)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 → Key)
    (seedDist : FinDist Seed) (h_seed : 0 < seedDist.totalMass) (z_corr : Seed)
    {q_D q_G : ℕ}
    (Q_G : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      Finset (Fin 256 → Fin 2))
    (hQ : ∀ pk ct, (Q_G pk ct).card ≤ q_G)
    (ct_queries : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      Fin q_D → ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (h_non_chal : ∀ pk ct i, ct_queries pk ct i ≠ ct)
    (adv_cca : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      Key → (Fin q_D → Key) → Bool)
    (μ0 μ1 : NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (adv_cpa : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      ModPKEQuantizedCiphertext 256 4 → Bool)
    (T : ℕ) (hT : 0 < T)
    (eDist_s2d : FinDist (VectorR (Zq standardZeroFailureParams) standardZeroFailureParams.m))
    (he_s2d : 0 < eDist_s2d.totalMass)
    (D_s2d : Sample (Zq standardZeroFailureParams)
      standardZeroFailureParams.n standardZeroFailureParams.m → Bool) :
    let p := standardZeroFailureParams
    let R := NegacyclicPoly (Zq p) 256
    let kgDist := cbd1KeygenDist (Zq p) 256 4
    let encDist := cbd1EncDist (Zq p) 256 4
    let d_kg := (uniformFinDist (MatrixR R 4 4)).prod kgDist
    let expR := cbd1ExpandR p 256 4
    let expE1 := cbd1ExpandE1 p 256 4
    let expE2 := cbd1ExpandE2 p 256 4
    d_kg.prob (fun aes =>
      let pk := modPKEKeygen R 4 aes.1 aes.2.1 aes.2.2
      decide (∀ m : Fin 256 → Fin 2,
        let enc := modKEMEncapsFin p 4 256 6144 2 G expR expE1 expE2 pk m
        modKEMDecapsFin p 4 256 6144 2 G expR expE1 expE2 J pk aes.2.1 z_corr enc.1 =
          enc.2)) = 1 ∧
    (∃ (B_kg : Sample R 4 4 → Bool) (B_enc : Sample R 4 5 → Bool),
      modPKECompressedBitINDCPAAdvantage p 256 4 12 5 kgDist encDist μ0 μ1 adv_cpa ≤
        mlweAdvantage R 4 4 kgDist B_kg +
          mlweAdvantage R 4 5 (modPKEEncSampleDist R 4 encDist) B_enc) ∧
    (∃ (B_kg : Sample R 4 4 → Bool) (B_enc : Sample R 4 5 → Bool),
      modKEMFOINDCPAAdvantage p 4 256 6144 2 G expR expE1 expE2 J kgDist
          (uniformFinDist (CBD1EncCoins 256 4)) seedDist ct_queries adv_cca ≤
        modKEMBadDecapsProb p 4 256 6144 2 G expR expE1 expE2 kgDist
            (uniformFinDist (CBD1EncCoins 256 4)) seedDist Q_G ct_queries +
          (q_G : ℚ) / ((2 : ℚ) ^ 256) +
          mlweAdvantage R 4 4 kgDist B_kg +
          mlweAdvantage R 4 5 (modPKEEncSampleDist R 4 encDist) B_enc) ∧
    (let d_se := (uniformFinDist (VectorR (Zq p) p.n)).prod eDist_s2d
     let ε := mlweAdvantage (Zq p) p.n p.m d_se D_s2d
     ∃ solver : (Fin T → Sample (Zq p) p.n p.m) →
         SearchLWECoins (Zq p) p.n p.m T → VectorR (Zq p) p.n,
       ∀ s : VectorR (Zq p) p.n,
         (0 < ε →
           1 - ((p.n : ℚ) * (p.q : ℚ)) / ((T : ℚ) * ε ^ 2) ≤
             searchLWEFixedSecretWinProb (Zq p) p.n p.m T eDist_s2d solver s) ∧
         ε ^ 2 ≤ ((p.n : ℚ) * (p.q : ℚ)) / (T : ℚ) +
           searchLWEFixedSecretWinProb (Zq p) p.n p.m T eDist_s2d solver s) := by
  intro p R kgDist encDist d_kg expR expE1 expE2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact standardZeroFailure_cbd1_kem_correct_prob_eq_one G expR expE1 expE2 J z_corr
      (fun c i => cbd1ExpandR_isTernary p 256 4 c i)
      (fun c i => cbd1ExpandE1_normInf p 256 4 c i)
      (fun c => cbd1ExpandE2_normInf p 256 4 c)
  · exact modPKE_compressed_bit_ind_cpa_to_mlwe p 256 4 12 5 kgDist encDist
      (cbd1EncDist_totalMass_pos _ 256 4) μ0 μ1 adv_cpa
  · obtain ⟨B_kg, B_enc, h_cca⟩ := modKEM_fo_ind_cca2_to_mlwe p 4 256 6144 2
      G expR expE1 expE2 J kgDist (cbd1KeygenDist_totalMass_pos _ 256 4)
      (uniformFinDist (CBD1EncCoins 256 4)) (uniformFinDist_totalMass_pos _)
      seedDist h_seed Q_G hQ ct_queries h_non_chal adv_cca
    rw [modFOEncNoiseDist_cbd1Coins_eq p 4 256] at h_cca
    exact ⟨B_kg, B_enc, h_cca⟩
  · exact regev_search_to_decision_prime_zq p T hT eDist_s2d he_s2d D_s2d

end ConcreteSecurityAndMaster

end LWE
