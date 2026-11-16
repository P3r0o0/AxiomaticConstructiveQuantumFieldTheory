import Mathlib.MeasureTheory.Integral.Pi
import WickCombinatorics
import VacuumTheory

open scoped ComplexConjugate Topology BigOperators Matrix
open Geometry Geometry.MatrixAnalysis Geometry.PolarDecomposition MeasureTheory Filter Complex
  Matrix

namespace QFT

noncomputable section

lemma forward_light_cone_add {x y : Fin 4 → ℝ}
    (hx : x ∈ forward_light_cone) (hy : y ∈ forward_light_cone) :
    x + y ∈ forward_light_cone := by
  have hx_cl : x ∈ closed_forward_light_cone := ⟨hx.1.le, hx.2.le⟩
  have hy_cl : y ∈ closed_forward_light_cone := ⟨hy.1.le, hy.2.le⟩
  have hxy : 0 ≤ minkowskiInner x y := closed_forward_light_cone_inner_nonneg hx_cl hy_cl
  refine ⟨add_pos hx.1 hy.1, ?_⟩
  have h_eq : minkowskiInner (x + y) (x + y) =
      minkowskiInner x x + minkowskiInner y y + 2 * minkowskiInner x y := by
    simp only [minkowskiInner_explicit, Pi.add_apply]
    ring
  rw [h_eq]
  linarith [hx.2, hy.2]

lemma add_mem_closure_forward_light_cone {x y : Fin 4 → ℝ}
    (hx : x ∈ closure forward_light_cone) (hy : y ∈ closure forward_light_cone) :
    x + y ∈ closure forward_light_cone := by
  rw [closure_forward_light_cone_eq] at hx hy ⊢
  have hxy : 0 ≤ minkowskiInner x y := closed_forward_light_cone_inner_nonneg hx hy
  refine ⟨add_nonneg hx.1 hy.1, ?_⟩
  have h_eq : minkowskiInner (x + y) (x + y) =
      minkowskiInner x x + minkowskiInner y y + 2 * minkowskiInner x y := by
    simp only [minkowskiInner_explicit, Pi.add_apply]
    ring
  rw [h_eq]
  linarith [hx.2, hy.2]

lemma sum_mem_closure_forward_light_cone {α : Type*} (s : Finset α) (f : α → Fin 4 → ℝ)
    (hf : ∀ a ∈ s, f a ∈ closure forward_light_cone) :
    (∑ a ∈ s, f a) ∈ closure forward_light_cone := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact zero_mem_closure_forward_light_cone
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add_mem_closure_forward_light_cone
        (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma add_mem_forwardConeSpectralRegion {n : ℕ} {p₁ p₂ : Fin n → Fin 4 → ℝ}
    (hp₁ : p₁ ∈ forwardConeSpectralRegion n) (hp₂ : p₂ ∈ forwardConeSpectralRegion n) :
    p₁ + p₂ ∈ forwardConeSpectralRegion n := by
  refine ⟨?_, fun k => ?_⟩
  · simp only [Pi.add_apply, Finset.sum_add_distrib, hp₁.1, hp₂.1, add_zero]
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact add_mem_closure_forward_light_cone (hp₁.2 k) (hp₂.2 k)

lemma sum_mem_forwardConeSpectralRegion {α : Type*} {n : ℕ} (s : Finset α)
    (f : α → Fin n → Fin 4 → ℝ)
    (hf : ∀ a ∈ s, f a ∈ forwardConeSpectralRegion n) :
    (∑ a ∈ s, f a) ∈ forwardConeSpectralRegion n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact zero_mem_forwardConeSpectralRegion n
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact add_mem_forwardConeSpectralRegion
        (hf a (Finset.mem_insert_self a s))
        (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma im_sub_mem_forward_light_cone_aux {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) :
    ∀ (d u : ℕ) (hv : u + (d + 1) < n),
      (fun μ => (z ⟨u + (d + 1), hv⟩ μ).im - (z ⟨u, by omega⟩ μ).im) ∈ forward_light_cone
  | 0, u, hv => by
      have h0 := diff_im_mem_forward_cone n z hz ⟨u, by omega⟩ hv
      convert h0 using 1
      ext μ
      simp [diff_im, diff_z]
  | d + 1, u, hv => by
      have h1 := im_sub_mem_forward_light_cone_aux hz d u (by omega)
      have h2 := diff_im_mem_forward_cone n z hz ⟨u + (d + 1), by omega⟩ hv
      have h_eq :
          (fun μ => (z ⟨u + (d + 1 + 1), hv⟩ μ).im - (z ⟨u, by omega⟩ μ).im) =
          (fun μ => (z ⟨u + (d + 1), by omega⟩ μ).im - (z ⟨u, by omega⟩ μ).im) +
            diff_im n z ⟨u + (d + 1), by omega⟩ hv := by
        ext μ
        have hidx : (⟨u + (d + 1 + 1), hv⟩ : Fin n) = ⟨u + (d + 1) + 1, hv⟩ := rfl
        rw [hidx]
        dsimp only [diff_im, diff_z, Pi.add_apply]
        rw [Pi.sub_apply, sub_im]
        ring
      rw [h_eq]
      exact forward_light_cone_add h1 h2

lemma pair_mem_forward_tube_two {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) {u v : Fin n} (huv : u < v) :
    ![z u, z v] ∈ forward_tube_n 2 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hv_eq : u.val + ((v.val - u.val - 1) + 1) = v.val := by
    have hlt : u.val < v.val := huv
    omega
  have hv_lt : u.val + ((v.val - u.val - 1) + 1) < n := by
    rw [hv_eq]
    exact v.isLt
  have h_cone := im_sub_mem_forward_light_cone_aux hz (v.val - u.val - 1) u.val hv_lt
  have hu_fin : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
  have hv_fin : (⟨u.val + ((v.val - u.val - 1) + 1), hv_lt⟩ : Fin n) = v := Fin.ext hv_eq
  convert h_cone using 1
  ext μ
  simp [hu_fin, hv_fin]

def pairProjCLM {n : ℕ} (u v : Fin n) :
    (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin 2 → Fin 4 → ℂ) :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin 4 → ℂ) u,
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => Fin 4 → ℂ) v]

@[simp]
lemma pairProjCLM_apply {n : ℕ} (u v : Fin n) (z : Fin n → Fin 4 → ℂ) :
    pairProjCLM u v z = ![z u, z v] := by
  ext s μ
  fin_cases s <;> rfl

def chordTwoPointMomentum {n : ℕ} (P : ChordPairing n) (c : P.Chord) (q : Fin 4 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun i => if i = c.1 then q else if i = P.mate c.1 then -q else 0

lemma sum_chordTwoPointMomentum {n : ℕ} (P : ChordPairing n) (c : P.Chord) (q : Fin 4 → ℝ) :
    ∑ i : Fin n, chordTwoPointMomentum P c q i = 0 := by
  have hne : c.1 ≠ P.mate c.1 := ne_of_lt c.2
  rw [P.sum_univ_eq_sum_chord]
  have h_term : ∀ c' : P.Chord,
      chordTwoPointMomentum P c q c'.1 + chordTwoPointMomentum P c q (P.mate c'.1) = 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      dsimp [chordTwoPointMomentum]
      rw [if_pos rfl, if_neg hne.symm, if_pos rfl, add_neg_cancel]
    · have h1 : c'.1 ≠ c.1 := fun h => hcc (Subtype.ext h)
      have h2 : c'.1 ≠ P.mate c.1 := by
        intro h
        have hlt : P.mate c.1 < P.mate (P.mate c.1) := by simpa [h] using c'.2
        rw [P.mate_mate] at hlt
        exact not_lt_of_gt c.2 hlt
      have h3 : P.mate c'.1 ≠ c.1 := by
        intro h
        have hm := congrArg P.mate h
        rw [P.mate_mate] at hm
        exact h2 hm
      have h4 : P.mate c'.1 ≠ P.mate c.1 := fun h => h1 (P.mate.injective h)
      dsimp [chordTwoPointMomentum]
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, add_zero]
  simp_rw [h_term, Finset.sum_const_zero]

lemma partial_sum_chordTwoPointMomentum {n : ℕ} (P : ChordPairing n) (c : P.Chord)
    (q : Fin 4 → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.univ.filter (· ≤ k), chordTwoPointMomentum P c q i) =
      if c.1 ≤ k ∧ k < P.mate c.1 then q else 0 := by
  have hne : c.1 ≠ P.mate c.1 := ne_of_lt c.2
  have h_split :
      ∀ i : Fin n, chordTwoPointMomentum P c q i =
        (if i = c.1 then q else 0) + (if i = P.mate c.1 then -q else 0) := by
    intro i
    dsimp only [chordTwoPointMomentum]
    by_cases h1 : i = c.1
    · subst h1
      simp [hne]
    · simp [h1]
  simp_rw [h_split]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : c.1 ≤ k
  · by_cases h2 : P.mate c.1 ≤ k
    · have hnot : ¬ k < P.mate c.1 := not_lt_of_ge h2
      simp [h1, h2, hnot]
    · have hlt : k < P.mate c.1 := lt_of_not_ge h2
      simp [h1, h2, hlt]
  · have h2 : ¬ P.mate c.1 ≤ k := fun hm => h1 (c.2.le.trans hm)
    simp [h1, h2]

lemma chordTwoPointMomentum_mem_forwardConeSpectralRegion {n : ℕ} (P : ChordPairing n)
    (c : P.Chord) {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    chordTwoPointMomentum P c q ∈ forwardConeSpectralRegion n := by
  refine ⟨sum_chordTwoPointMomentum P c q, fun k => ?_⟩
  rw [partial_sum_chordTwoPointMomentum]
  split_ifs
  · exact hq
  · exact zero_mem_closure_forward_light_cone

namespace ChordPairing

noncomputable def momentum {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => ∑ c : P.Chord, chordTwoPointMomentum P c (massShellVec m (p c)) i

lemma momentum_eq_sum {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) :
    P.momentum m p = ∑ c : P.Chord, chordTwoPointMomentum P c (massShellVec m (p c)) := by
  ext i μ
  simp [momentum, Finset.sum_apply]

@[simp]
lemma momentum_apply_fst {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) (c : P.Chord) :
    P.momentum m p c.1 = massShellVec m (p c) := by
  dsimp [momentum]
  have h_eq : ∀ c' : P.Chord,
      chordTwoPointMomentum P c' (massShellVec m (p c')) c.1 =
        if c' = c then massShellVec m (p c) else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      simp [chordTwoPointMomentum]
    · have h1 : c.1 ≠ c'.1 := fun h => hcc (Subtype.ext h.symm)
      have h2 : c.1 ≠ P.mate c'.1 := by
        intro h
        have hlt : P.mate c'.1 < P.mate (P.mate c'.1) := by simpa [h] using c.2
        rw [P.mate_mate] at hlt
        exact not_lt_of_gt c'.2 hlt
      simp [chordTwoPointMomentum, h1, h2, hcc]
  simp_rw [h_eq]
  simp

@[simp]
lemma momentum_apply_mate {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) (c : P.Chord) :
    P.momentum m p (P.mate c.1) = -massShellVec m (p c) := by
  dsimp [momentum]
  have h_eq : ∀ c' : P.Chord,
      chordTwoPointMomentum P c' (massShellVec m (p c')) (P.mate c.1) =
        if c' = c then -massShellVec m (p c) else 0 := by
    intro c'
    by_cases hcc : c' = c
    · subst hcc
      have hne : P.mate c'.1 ≠ c'.1 := (ne_of_lt c'.2).symm
      simp [chordTwoPointMomentum, hne]
    · have h1 : P.mate c.1 ≠ c'.1 := by
        intro h
        have hlt : P.mate c.1 < P.mate (P.mate c.1) := by simpa [← h] using c'.2
        rw [P.mate_mate] at hlt
        exact not_lt_of_gt c.2 hlt
      have h2 : P.mate c.1 ≠ P.mate c'.1 := fun h => hcc (Subtype.ext (P.mate.injective h.symm))
      simp [chordTwoPointMomentum, h1, h2, hcc]
  simp_rw [h_eq]
  simp

lemma momentum_mem_forwardConeSpectralRegion {n : ℕ} {m : ℝ} (hm : 0 < m)
    (P : ChordPairing n) (p : P.Chord → Fin 3 → ℝ) :
    P.momentum m p ∈ forwardConeSpectralRegion n := by
  rw [P.momentum_eq_sum]
  exact sum_mem_forwardConeSpectralRegion Finset.univ _ (fun c _ =>
    chordTwoPointMomentum_mem_forwardConeSpectralRegion P c
      (massShellVec_mem_closure_forward_light_cone hm (p c)))

lemma continuous_momentum {n : ℕ} (m : ℝ) (P : ChordPairing n) :
    Continuous (P.momentum m) := by
  refine continuous_pi (fun i => continuous_finsetSum Finset.univ (fun c _ => ?_))
  dsimp [chordTwoPointMomentum]
  split_ifs
  · exact (continuous_massShellVec m).comp (continuous_apply c)
  · exact ((continuous_massShellVec m).comp (continuous_apply c)).neg
  · exact continuous_const

lemma measurable_momentum {n : ℕ} (m : ℝ) (P : ChordPairing n) :
    Measurable (P.momentum m) :=
  (P.continuous_momentum m).measurable

lemma vladimirov_kernel_momentum {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (z : Fin n → Fin 4 → ℂ) (p : P.Chord → Fin 3 → ℝ) :
    vladimirov_kernel n z (P.momentum m p) =
      ∏ c : P.Chord, vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
        (twoPointMomentum (massShellVec m (p c))) := by
  unfold vladimirov_kernel
  rw [P.sum_univ_eq_sum_chord, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  congr 1
  rw [Fin.sum_univ_two, P.momentum_apply_fst, P.momentum_apply_mate]
  simp only [Fin.isValue, twoPointMomentum_zero, twoPointMomentum_one,
    Matrix.cons_val_zero, Matrix.cons_val_one]

lemma one_add_norm_chord_le_momentumToEuclid {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (p : P.Chord → Fin 3 → ℝ) (c : P.Chord) :
    1 + ‖p c‖ ≤
      (2 * Real.pi) * (1 + ‖momentumToEuclidCLMN n (P.momentum m p)‖) := by
  let u := momentumToEuclidCLMN n (P.momentum m p)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖p c‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (c.1, j.succ) = (2 * Real.pi)⁻¹ * p c j := by
      have hm := P.momentum_apply_fst m p c
      have hu_app : u (c.1, j.succ) = (2 * Real.pi)⁻¹ * P.momentum m p c.1 j.succ := by
        dsimp only [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
          piSpaceEquiv, finCurryEquiv, finEuclidEquiv]
        simp
      rw [hu_app, hm]
      fin_cases j <;> simp [massShellVec]
    have hpj : p c j = (2 * Real.pi) * u (c.1, j.succ) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖p c j‖ = ‖(2 * Real.pi) * u (c.1, j.succ)‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (c.1, j.succ)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (c.1, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

theorem norm_schwartz_momentumToEuclid_chord_le {n : ℕ} (m : ℝ) (P : ChordPairing n)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) (p : P.Chord → Fin 3 → ℝ) :
    ‖g (momentumToEuclidCLMN n (P.momentum m p))‖ ≤
      ((4 * Real.pi) ^ (4 * Fintype.card P.Chord) *
        ((Finset.Iic (4 * Fintype.card P.Chord, 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g)) *
        ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by
  let k := Fintype.card P.Chord
  let u := momentumToEuclidCLMN n (P.momentum m p)
  let S : ℝ := (Finset.Iic (4 * k, 0)).sup
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
  have h_sch : (1 + ‖u‖) ^ (4 * k) * ‖g u‖ ≤ 2 ^ (4 * k) * S := by
    have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (4 * k, 0)) (k := 4 * k) (n := 0) le_rfl le_rfl g u
    have h_fam :
        (fun m : ℕ × ℕ =>
          SchwartzMap.seminorm (E := EuclideanSpace ℝ (Fin n × Fin 4)) (F := ℂ) ℂ m.1 m.2) =
        schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ := rfl
    simpa [norm_iteratedFDeriv_zero, h_fam, S] using h0
  have h_prod_p :
      (∏ c : P.Chord, (1 + ‖p c‖) ^ 4) ≤ (2 * Real.pi) ^ (4 * k) * (1 + ‖u‖) ^ (4 * k) := by
    have h_each : ∀ c : P.Chord, (1 + ‖p c‖) ^ 4 ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
      fun c => pow_le_pow_left₀ (by positivity)
        (P.one_add_norm_chord_le_momentumToEuclid m p c) 4
    calc (∏ c : P.Chord, (1 + ‖p c‖) ^ 4)
        ≤ ∏ _c : P.Chord, ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => by positivity) (fun c _ => h_each c)
      _ = (((2 * Real.pi) * (1 + ‖u‖)) ^ 4) ^ k := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * k) := (pow_mul _ 4 k).symm
      _ = (2 * Real.pi) ^ (4 * k) * (1 + ‖u‖) ^ (4 * k) := mul_pow _ _ (4 * k)
  have h_prod :
      (∏ c : P.Chord, (1 + ‖p c‖) ^ 4) * ‖g u‖ ≤ (4 * Real.pi) ^ (4 * k) * S := by
    calc (∏ c : P.Chord, (1 + ‖p c‖) ^ 4) * ‖g u‖
        ≤ ((2 * Real.pi) ^ (4 * k) * (1 + ‖u‖) ^ (4 * k)) * ‖g u‖ :=
          mul_le_mul_of_nonneg_right h_prod_p (norm_nonneg _)
      _ = (2 * Real.pi) ^ (4 * k) * ((1 + ‖u‖) ^ (4 * k) * ‖g u‖) := by ring
      _ ≤ (2 * Real.pi) ^ (4 * k) * (2 ^ (4 * k) * S) :=
          mul_le_mul_of_nonneg_left h_sch (by positivity)
      _ = ((2 * Real.pi) * 2) ^ (4 * k) * S := by rw [← mul_assoc, ← mul_pow]
      _ = (4 * Real.pi) ^ (4 * k) * S := by
          congr 2
          ring
  have h_pos : 0 < ∏ c : P.Chord, (1 + ‖p c‖) ^ 4 :=
    Finset.prod_pos (fun _ _ => by positivity)
  rw [Finset.prod_inv_distrib]
  exact (le_mul_inv_iff₀' h_pos).mpr h_prod

end ChordPairing

noncomputable def wickChordWeight {κ : Type*} {n : ℕ} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (P : ChordPairing n) (α : Fin n → κ)
    (p : P.Chord → Fin 3 → ℝ) : ℂ :=
  ∏ c : P.Chord, massShellWeight m C ![α c.1, α (P.mate c.1)] (p c)

lemma measurable_wickChordWeight {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) :
    Measurable (wickChordWeight m C P α) :=
  Finset.measurable_prod Finset.univ (fun c _ =>
    (measurable_massShellWeight hC ![α c.1, α (P.mate c.1)]).comp (measurable_pi_apply c))

lemma exists_norm_wickChordWeight_le {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : P.Chord → Fin 3 → ℝ, ‖wickChordWeight m C P α p‖ ≤ B := by
  let Bc : P.Chord → ℝ := fun c => Classical.choose (hC.2 ![α c.1, α (P.mate c.1)])
  have hBc : ∀ c : P.Chord,
      0 ≤ Bc c ∧ ∀ q : Fin 3 → ℝ, ‖massShellWeight m C ![α c.1, α (P.mate c.1)] q‖ ≤ Bc c :=
    fun c => Classical.choose_spec (hC.2 ![α c.1, α (P.mate c.1)])
  refine ⟨∏ c : P.Chord, Bc c, Finset.prod_nonneg (fun c _ => (hBc c).1), fun p => ?_⟩
  unfold wickChordWeight
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun c _ => (hBc c).2 (p c))

lemma integrable_chordDecay {n : ℕ} (P : ChordPairing n) :
    Integrable (fun p : P.Chord → Fin 3 → ℝ => ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) volume :=
  Integrable.fintype_prod (f := fun _ : P.Chord => fun q : Fin 3 → ℝ => ((1 + ‖q‖) ^ 4)⁻¹)
    (fun _ => integrable_massShellDecay)

theorem integrable_wickChordWeight_mul_schwartz {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) :
    Integrable (fun p : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))) volume := by
  rcases exists_norm_wickChordWeight_le hC P α with ⟨B, hB_nn, hB⟩
  let Kg : ℝ := (4 * Real.pi) ^ (4 * Fintype.card P.Chord) *
    ((Finset.Iic (4 * Fintype.card P.Chord, 0)).sup
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g)
  have h_meas_g : Measurable (fun p : P.Chord → Fin 3 → ℝ =>
      g (momentumToEuclidCLMN n (P.momentum m p))) :=
    (g.continuous.comp (momentumToEuclidCLMN n).continuous).measurable.comp
      (P.measurable_momentum m)
  refine Integrable.mono' ((integrable_chordDecay P).const_mul (B * Kg))
    ((measurable_wickChordWeight hC P α).mul h_meas_g).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => ?_))
  rw [norm_mul]
  calc ‖wickChordWeight m C P α p‖ * ‖g (momentumToEuclidCLMN n (P.momentum m p))‖
      ≤ B * (Kg * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) :=
        mul_le_mul (hB p) (P.norm_schwartz_momentumToEuclid_chord_le m g p)
          (norm_nonneg _) hB_nn
    _ = (B * Kg) * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by ring

noncomputable def wickChordEuclidCLM {κ : Type*} {n : ℕ} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) :
    SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun g => ∫ p : P.Chord → Fin 3 → ℝ,
      wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p)))
    (fun g₁ g₂ => by
      have h_add :
          (fun p : P.Chord → Fin 3 → ℝ =>
            wickChordWeight m C P α p *
              (g₁ + g₂) (momentumToEuclidCLMN n (P.momentum m p))) =
          fun p =>
            wickChordWeight m C P α p * g₁ (momentumToEuclidCLMN n (P.momentum m p)) +
            wickChordWeight m C P α p * g₂ (momentumToEuclidCLMN n (P.momentum m p)) := by
        ext p
        simp [mul_add]
      rw [h_add]
      exact integral_add (integrable_wickChordWeight_mul_schwartz hC P α g₁)
        (integrable_wickChordWeight_mul_schwartz hC P α g₂))
    (fun c g => by
      have h_smul :
          (fun p : P.Chord → Fin 3 → ℝ =>
            wickChordWeight m C P α p *
              (c • g) (momentumToEuclidCLMN n (P.momentum m p))) =
          fun p =>
            c * (wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))) := by
        ext p
        simp [smul_eq_mul, mul_left_comm]
      rw [h_smul, RingHom.id_apply, smul_eq_mul, integral_const_mul])
    (by
      let B : ℝ := Classical.choose (exists_norm_wickChordWeight_le hC P α)
      have hB_spec := Classical.choose_spec (exists_norm_wickChordWeight_le hC P α)
      have hB_nn : 0 ≤ B := hB_spec.1
      have hB : ∀ p : P.Chord → Fin 3 → ℝ, ‖wickChordWeight m C P α p‖ ≤ B := hB_spec.2
      let k := Fintype.card P.Chord
      let I_dec : ℝ := ∫ p : P.Chord → Fin 3 → ℝ, ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹
      have hI_nn : 0 ≤ I_dec :=
        integral_nonneg (fun p => Finset.prod_nonneg (fun _ _ => by positivity))
      refine ⟨Finset.Iic (4 * k, 0), B * (4 * Real.pi) ^ (4 * k) * I_dec, by positivity,
        fun g => ?_⟩
      let S : ℝ := (Finset.Iic (4 * k, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
      calc ‖∫ p : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))‖
          ≤ ∫ p : P.Chord → Fin 3 → ℝ,
              ‖wickChordWeight m C P α p * g (momentumToEuclidCLMN n (P.momentum m p))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ p : P.Chord → Fin 3 → ℝ,
              (B * ((4 * Real.pi) ^ (4 * k) * S)) *
                ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
              ((integrable_chordDecay P).const_mul (B * ((4 * Real.pi) ^ (4 * k) * S)))
              (Filter.Eventually.of_forall (fun p => ?_))
            dsimp only
            rw [norm_mul]
            calc ‖wickChordWeight m C P α p‖ *
                  ‖g (momentumToEuclidCLMN n (P.momentum m p))‖
                ≤ B * (((4 * Real.pi) ^ (4 * k) * S) *
                    ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) :=
                  mul_le_mul (hB p) (P.norm_schwartz_momentumToEuclid_chord_le m g p)
                    (norm_nonneg _) hB_nn
              _ = (B * ((4 * Real.pi) ^ (4 * k) * S)) *
                    ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by ring
        _ = (B * (4 * Real.pi) ^ (4 * k) * I_dec) * S := by
            rw [integral_const_mul]
            dsimp [I_dec]
            ring)

noncomputable def wickMassShellEuclidCLM {κ : Type*} {n : ℕ} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) (α : Fin n → κ) :
    SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ →L[ℂ] ℂ :=
  ∑ P : ChordPairing n, (η ^ P.cross) • wickChordEuclidCLM m C hC P α

noncomputable def wickMassShellW {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    WightmanFamily κ :=
  fun n α =>
    PointwiseConvergenceCLM.precomp ℂ (minkowskiFourierSchwartzCLM n)
      (ContinuousLinearMap.toPointwiseConvergenceCLM _ _ _ _
        (wickMassShellEuclidCLM m η C hC α))

theorem integrable_wickChordWeight_mul_minkowskiFourier {κ : Type*} {n : ℕ} {m : ℝ}
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Integrable (fun p : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) volume := by
  have h_eq :
      (fun p : P.Chord → Fin 3 → ℝ =>
        wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) =
      fun p =>
        wickChordWeight m C P α p *
          (minkowskiFourierSchwartzCLM n f) (momentumToEuclidCLMN n (P.momentum m p)) := by
    ext p
    rw [minkowskiFourier_eq_minkowskiFourierSchwartzCLM n f]
  rw [h_eq]
  exact integrable_wickChordWeight_mul_schwartz hC P α (minkowskiFourierSchwartzCLM n f)

theorem wickMassShellW_apply {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wickMassShellW m η C hC n α f =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p) := by
  change (wickMassShellEuclidCLM m η C hC α) (minkowskiFourierSchwartzCLM n f) = _
  simp only [wickMassShellEuclidCLM, FunLike.coe_sum,
    FunLike.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  change ∫ p : P.Chord → Fin 3 → ℝ,
    wickChordWeight m C P α p *
      (minkowskiFourierSchwartzCLM n f) (momentumToEuclidCLMN n (P.momentum m p)) = _
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [← minkowskiFourier_eq_minkowskiFourierSchwartzCLM n f (P.momentum m p)]

noncomputable def wickMassShellH {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (n : ℕ) (α : Fin n → κ)
    (z : Fin n → Fin 4 → ℂ) : ℂ :=
  ∑ P : ChordPairing n, η ^ P.cross *
    ∏ c : P.Chord,
      massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]

theorem wickMassShellH_eq_sum_integral {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (n : ℕ) (α : Fin n → κ)
    (z : Fin n → Fin 4 → ℂ) :
    wickMassShellH m η C n α z =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p * vladimirov_kernel n z (P.momentum m p) := by
  unfold wickMassShellH
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  have h_prod := (MeasureTheory.integral_fintype_prod_volume_eq_prod
    (E := fun _ : P.Chord => Fin 3 → ℝ)
    (f := fun (c : P.Chord) (q : Fin 3 → ℝ) =>
      massShellWeight m C ![α c.1, α (P.mate c.1)] q *
        vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
          (twoPointMomentum (massShellVec m q)))).symm
  simp only [massShellTwoPointH_two]
  rw [h_prod]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only [wickChordWeight]
  rw [Finset.prod_mul_distrib, ← P.vladimirov_kernel_momentum m z p]

theorem analyticOn_wickMassShellH {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) :
    AnalyticOn ℂ (wickMassShellH m η C n α) (forward_tube_n n) := by
  rw [(forward_tube_n_isOpen n).analyticOn_iff_analyticOnNhd]
  intro z hz
  unfold wickMassShellH
  have h_prod_an : ∀ P : ChordPairing n,
      ∀ s : Finset P.Chord, AnalyticAt ℂ
        (fun w : Fin n → Fin 4 → ℂ =>
          ∏ c ∈ s, massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)])
        z := by
    intro P s
    induction s using Finset.induction_on with
    | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ => (1 : ℂ)) z)
    | insert c s hc ih =>
        have h_eq :
            (fun w : Fin n → Fin 4 → ℂ =>
              ∏ c' ∈ insert c s,
                massShellTwoPointH m C 2 ![α c'.1, α (P.mate c'.1)]
                  ![w c'.1, w (P.mate c'.1)]) =
            fun w =>
              massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)] *
                ∏ c' ∈ s,
                  massShellTwoPointH m C 2 ![α c'.1, α (P.mate c'.1)]
                    ![w c'.1, w (P.mate c'.1)] := by
          ext w
          exact Finset.prod_insert hc
        rw [h_eq]
        have hz_pair : pairProjCLM c.1 (P.mate c.1) z ∈ forward_tube_n 2 := by
          rw [pairProjCLM_apply]
          exact pair_mem_forward_tube_two hz c.2
        have h_an2 := ((forward_tube_n_isOpen 2).analyticOn_iff_analyticOnNhd.mp
          (analyticOn_massShellTwoPointH hm hC 2 ![α c.1, α (P.mate c.1)]))
          (pairProjCLM c.1 (P.mate c.1) z) hz_pair
        exact (h_an2.comp_of_eq ((pairProjCLM c.1 (P.mate c.1)).analyticAt z) rfl).mul ih
  have h_sum_an : ∀ s : Finset (ChordPairing n),
      AnalyticAt ℂ
        (fun w : Fin n → Fin 4 → ℂ =>
          ∑ P ∈ s, η ^ P.cross *
            ∏ c : P.Chord,
              massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)])
        z := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ => (0 : ℂ)) z)
    | insert P s hP ih =>
        have h_eq :
            (fun w : Fin n → Fin 4 → ℂ =>
              ∑ Q ∈ insert P s, η ^ Q.cross *
                ∏ c : Q.Chord,
                  massShellTwoPointH m C 2 ![α c.1, α (Q.mate c.1)] ![w c.1, w (Q.mate c.1)]) =
            fun w =>
              η ^ P.cross *
                (∏ c : P.Chord,
                  massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![w c.1, w (P.mate c.1)]) +
              ∑ Q ∈ s, η ^ Q.cross *
                ∏ c : Q.Chord,
                  massShellTwoPointH m C 2 ![α c.1, α (Q.mate c.1)] ![w c.1, w (Q.mate c.1)] := by
          ext w
          exact Finset.sum_insert hP
        rw [h_eq]
        exact (analyticAt_const.mul (h_prod_an P Finset.univ)).add ih
  exact h_sum_an Finset.univ

lemma integrable_prod_wickChordWeight_line_mul_f {κ : Type*} {n : ℕ} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) {t : ℝ} (ht : 0 < t) :
    Integrable
      (Function.uncurry (fun (p : P.Chord → Fin 3 → ℝ) (x : Fin n → Fin 4 → ℝ) =>
        wickChordWeight m C P α p *
          (vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p) * f x)))
      (volume.prod volume) := by
  let Bc : P.Chord → ℝ := fun c => Classical.choose (hC.2 ![α c.1, α (P.mate c.1)])
  have hBc : ∀ c : P.Chord,
      0 ≤ Bc c ∧ ∀ q : Fin 3 → ℝ, ‖massShellWeight m C ![α c.1, α (P.mate c.1)] q‖ ≤ Bc c :=
    fun c => Classical.choose_spec (hC.2 ![α c.1, α (P.mate c.1)])
  let c₀ : ℝ := t * coneGap v
  have hc₀ : 0 < c₀ := mul_pos ht (coneGap_pos v hv)
  have h_dom_p : Integrable
      (fun p : P.Chord → Fin 3 → ℝ =>
        ∏ c : P.Chord, (Bc c * Real.exp (-(c₀ * massShellEnergy m (p c))))) volume :=
    Integrable.fintype_prod
      (f := fun c : P.Chord => fun q : Fin 3 → ℝ =>
        Bc c * Real.exp (-(c₀ * massShellEnergy m q)))
      (fun c => (integrable_exp_neg_massShellEnergy hm hc₀).const_mul (Bc c))
  have h_dom : Integrable
      (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
        (∏ c : P.Chord, (Bc c * Real.exp (-(c₀ * massShellEnergy m (px.1 c))))) * ‖f px.2‖)
      (volume.prod volume) :=
    h_dom_p.mul_prod f.integrable.norm
  have h_meas_ker : Measurable
      (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
        vladimirov_kernel n (tubeBoundaryLine n px.2 v t) (P.momentum m px.1)) := by
    have h_phase : Measurable
        (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
          -Complex.I * ∑ k : Fin n,
            minkowskiInnerC
              (fun μ => (P.momentum m px.1 k μ : ℂ))
              (tubeBoundaryLine n px.2 v t k)) := by
      refine measurable_const.mul (Finset.measurable_sum Finset.univ (fun k _ => ?_))
      have hk1 : Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) => P.momentum m px.1 k) :=
        (measurable_pi_apply k).comp ((P.measurable_momentum m).comp measurable_fst)
      have hk2 : Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) => px.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      have hm1 : ∀ μ : Fin 4, Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
            (P.momentum m px.1 k μ : ℂ)) :=
        fun μ => Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply μ).comp hk1)
      have hm2 : ∀ μ : Fin 4, Measurable
          (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
            tubeBoundaryLine n px.2 v t k μ) :=
        fun μ => (Complex.continuous_ofReal.measurable.comp
          ((measurable_pi_apply μ).comp hk2)).add measurable_const
      exact (((hm1 0).mul (hm2 0)).sub ((hm1 1).mul (hm2 1))).sub
        ((hm1 2).mul (hm2 2)) |>.sub ((hm1 3).mul (hm2 3))
    exact Complex.continuous_exp.measurable.comp h_phase
  have h_meas : AEStronglyMeasurable
      (fun px : (P.Chord → Fin 3 → ℝ) × (Fin n → Fin 4 → ℝ) =>
        wickChordWeight m C P α px.1 *
          (vladimirov_kernel n (tubeBoundaryLine n px.2 v t) (P.momentum m px.1) * f px.2))
      (volume.prod volume) :=
    (((measurable_wickChordWeight hC P α).comp measurable_fst).aestronglyMeasurable).mul
      (h_meas_ker.aestronglyMeasurable.mul f.integrable.aestronglyMeasurable.comp_snd)
  refine Integrable.mono' h_dom h_meas (Filter.Eventually.of_forall (fun px => ?_))
  dsimp only [Function.uncurry]
  rw [norm_mul, norm_mul, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (f px.2))
  rw [P.vladimirov_kernel_momentum m (tubeBoundaryLine n px.2 v t) px.1]
  unfold wickChordWeight
  rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun c _ => ?_)
  let zc : Fin 2 → Fin 4 → ℂ :=
    ![tubeBoundaryLine n px.2 v t c.1, tubeBoundaryLine n px.2 v t (P.mate c.1)]
  have hzc : zc ∈ forward_tube_n 2 :=
    pair_mem_forward_tube_two (line_mem_forward_tube n px.2 v hv t ht) c.2
  have hd_ge_one : (1 : ℝ) ≤ ((P.mate c.1 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ) := by
    have hlt : (c.1 : ℕ) + 1 ≤ (P.mate c.1 : ℕ) := c.2
    have hlt_r : ((c.1 : ℕ) : ℝ) + 1 ≤ ((P.mate c.1 : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  let s_c : ℝ := t * (((P.mate c.1 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ))
  have hs_pos : 0 < s_c := mul_pos ht (by linarith)
  have h_diff_zc : diff_im 2 zc 0 (by decide) = s_c • v := by
    ext μ
    change -((zc 0 - zc 1) μ).im = s_c * v μ
    have hz0 : zc 0 μ = tubeBoundaryLine n px.2 v t c.1 μ := rfl
    have hz1 : zc 1 μ = tubeBoundaryLine n px.2 v t (P.mate c.1) μ := rfl
    rw [Pi.sub_apply, hz0, hz1]
    dsimp only [tubeBoundaryLine, s_c]
    rw [sub_im, add_im, add_im, ofReal_im, ofReal_im, mul_im, mul_im,
      ofReal_re, ofReal_re, I_re, I_im]
    ring
  have h_gap_zc : coneGap (diff_im 2 zc 0 (by decide)) = s_c * coneGap v := by
    rw [h_diff_zc]
    dsimp [coneGap]
    have h_sq : ((s_c * v 1) ^ 2 + (s_c * v 2) ^ 2 + (s_c * v 3) ^ 2) =
        s_c ^ 2 * ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by ring
    rw [h_sq, Real.sqrt_mul (sq_nonneg s_c), Real.sqrt_sq hs_pos.le]
    ring
  have h_c0_le : c₀ ≤ coneGap (diff_im 2 zc 0 (by decide)) := by
    rw [h_gap_zc]
    dsimp [c₀, s_c]
    have hcg : 0 ≤ coneGap v := (coneGap_pos v hv).le
    have ht_le : t ≤ t * (((P.mate c.1 : ℕ) : ℝ) - ((c.1 : ℕ) : ℝ)) :=
      le_mul_of_one_le_right ht.le hd_ge_one
    exact mul_le_mul_of_nonneg_right ht_le hcg
  have h_ker_le :
      ‖vladimirov_kernel 2 zc (twoPointMomentum (massShellVec m (px.1 c)))‖ ≤
        Real.exp (-(c₀ * massShellEnergy m (px.1 c))) := by
    refine (norm_vladimirov_kernel_twoPoint_le_exp hm hzc (px.1 c)).trans ?_
    apply Real.exp_le_exp.mpr
    have hω_nn : 0 ≤ massShellEnergy m (px.1 c) := (massShellEnergy_pos hm (px.1 c)).le
    nlinarith [mul_le_mul_of_nonneg_right h_c0_le hω_nn]
  exact mul_le_mul ((hBc c).2 (px.1 c)) h_ker_le (norm_nonneg _) (hBc c).1

theorem tendsto_wickMassShellH_boundary {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        wickMassShellH m η C n α (tubeBoundaryLine n x v t) * f x)
      (𝓝[>] 0)
      (𝓝 (wickMassShellW m η C hC n α f)) := by
  rw [wickMassShellW_apply]
  have h_sum_eq :
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        wickMassShellH m η C n α (tubeBoundaryLine n x v t) * f x) =ᶠ[𝓝[>] 0]
      fun t : ℝ => ∑ P : ChordPairing n, η ^ P.cross *
        ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p *
            (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
              minkowskiInner (P.momentum m p k) v : ℂ) *
              minkowskiFourier f (P.momentum m p)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h_int_x : ∀ P : ChordPairing n,
        Integrable (fun x : Fin n → Fin 4 → ℝ =>
          η ^ P.cross *
            ((∫ p : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α p *
                vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x))
          volume := by
      intro P
      have h_fub :=
        (integrable_prod_wickChordWeight_line_mul_f hm hC P α f hv ht).integral_prod_right
      have h_eq_fn : ∀ x : Fin n → Fin 4 → ℝ,
          (∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x =
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              (vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p) * f x) := by
        intro x
        rw [← integral_mul_const]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_assoc _ _ _))
      simp_rw [h_eq_fn]
      exact h_fub.const_mul (η ^ P.cross)
    have h_expand :
        (fun x : Fin n → Fin 4 → ℝ =>
          wickMassShellH m η C n α (tubeBoundaryLine n x v t) * f x) =
        fun x => ∑ P : ChordPairing n, η ^ P.cross *
          ((∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x) := by
      ext x
      rw [wickMassShellH_eq_sum_integral, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
    rw [h_expand, integral_finsetSum Finset.univ (fun P _ => h_int_x P)]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [integral_const_mul]
    congr 1
    have h_lhs :
        (fun x : Fin n → Fin 4 → ℝ =>
          (∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α p *
              vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p)) * f x) =
        fun x => ∫ p : P.Chord → Fin 3 → ℝ,
          wickChordWeight m C P α p *
            (vladimirov_kernel n (tubeBoundaryLine n x v t) (P.momentum m p) * f x) := by
      ext x
      rw [← integral_mul_const]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_assoc _ _ _))
    rw [h_lhs,
        (MeasureTheory.integral_integral_swap
          (integrable_prod_wickChordWeight_line_mul_f hm hC P α f hv ht)).symm]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    dsimp only
    rw [integral_const_mul, integral_vladimirov_kernel_line_mul_f n f (P.momentum m p) v t]
  rw [tendsto_congr' h_sum_eq]
  refine tendsto_finsetSum Finset.univ (fun P _ => Tendsto.const_mul (η ^ P.cross) ?_)
  rcases exists_norm_wickChordWeight_le hC P α with ⟨B, hB_nn, hB⟩
  let g_hat := minkowskiFourierSchwartzCLM n f
  let Kf : ℝ := (4 * Real.pi) ^ (4 * Fintype.card P.Chord) *
    ((Finset.Iic (4 * Fintype.card P.Chord, 0)).sup
      (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g_hat)
  let G : ℝ → (P.Chord → Fin 3 → ℝ) → ℂ := fun t p =>
    wickChordWeight m C P α p *
      (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (P.momentum m p k) v : ℂ) *
        minkowskiFourier f (P.momentum m p))
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun p => (B * Kf) * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) ?_ ?_
    ((integrable_chordDecay P).const_mul (B * Kf)) ?_
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have h_cont_q : Continuous (fun q : Fin n → Fin 4 → ℝ =>
        Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ) *
          minkowskiFourier f q) := by
      have h_lin : Continuous (fun q : Fin n → Fin 4 → ℝ =>
          (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ)) := by
        have h_real : Continuous (fun q : Fin n → Fin 4 → ℝ =>
            t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v) := by
          refine continuous_const.mul (continuous_finsetSum Finset.univ (fun k _ => ?_))
          refine continuous_const.mul ?_
          simp only [minkowskiInner_explicit]
          have hc : ∀ μ : Fin 4, Continuous (fun q : Fin n → Fin 4 → ℝ => q k μ) :=
            fun μ => (continuous_apply μ).comp (continuous_apply k)
          exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
            ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
        have h_eq_c : (fun q : Fin n → Fin 4 → ℝ =>
            (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (q k) v : ℂ)) =
            fun q => ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
              minkowskiInner (q k) v : ℝ) : ℂ) := by
          ext q
          push_cast
          rfl
        rw [h_eq_c]
        exact Complex.continuous_ofReal.comp h_real
      exact (Complex.continuous_exp.comp h_lin).mul (continuous_minkowskiFourier n f)
    exact ((measurable_wickChordWeight hC P α).mul
      (h_cont_q.measurable.comp (P.measurable_momentum m))).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [norm_mul, norm_mul]
    have hp_cone := P.momentum_mem_forwardConeSpectralRegion hm p
    have h_exp_le :
        ‖Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
          minkowskiInner (P.momentum m p k) v : ℂ)‖ ≤ 1 := by
      have h_cast :
          (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (P.momentum m p k) v : ℂ) =
          ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (P.momentum m p k) v : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [h_cast, Complex.norm_exp_ofReal]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le
        (sum_k_minkowskiInner_le_zero_of_forwardConeSpectralRegion n hp_cone hv))
    have h_four_le :
        ‖minkowskiFourier f (P.momentum m p)‖ ≤
          Kf * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by
      rw [minkowskiFourier_eq_minkowskiFourierSchwartzCLM n f]
      exact P.norm_schwartz_momentumToEuclid_chord_le m g_hat p
    calc ‖wickChordWeight m C P α p‖ *
          (‖Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) *
            minkowskiInner (P.momentum m p k) v : ℂ)‖ *
            ‖minkowskiFourier f (P.momentum m p)‖)
        ≤ B * (Kf * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹) :=
          mul_le_mul (hB p)
            ((mul_le_of_le_one_left (norm_nonneg _) h_exp_le).trans h_four_le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hB_nn
      _ = (B * Kf) * ∏ c : P.Chord, ((1 + ‖p c‖) ^ 4)⁻¹ := by ring
  · refine Filter.Eventually.of_forall (fun p => ?_)
    have h_cont_t : Continuous (fun t : ℝ => G t p) :=
      continuous_const.mul
        ((Complex.continuous_exp.comp
          (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const)
    have h0 : G 0 p = wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p) := by
      dsimp [G]
      simp
    rw [← h0]
    exact (h_cont_t.tendsto 0).mono_left nhdsWithin_le_nhds

noncomputable def wickMassShellTubeExtension {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    TubeExtension (wickMassShellW m η C hC) where
  H := wickMassShellH m η C
  analytic n α := analyticOn_wickMassShellH hm η hC n α
  boundary n α f _v hv := tendsto_wickMassShellH_boundary hm η hC n α f hv

@[simp]
theorem wickMassShellTubeExtension_H {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    (wickMassShellTubeExtension m hm η C hC).H = wickMassShellH m η C := rfl

noncomputable def wickMassShellS {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    SchwingerFamily κ :=
  schwingerFromTube (wickMassShellTubeExtension m hm η C hC)

theorem wickMassShellS_apply {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → κ) (x : Fin n → Fin 4 → ℝ) :
    wickMassShellS m hm η C hC n α x =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∏ c : P.Chord,
          massShellTwoPointS m hm C hC 2 ![α c.1, α (P.mate c.1)] ![x c.1, x (P.mate c.1)] := by
  change wickMassShellH m η C n α (wickEmbedN n x) = _
  unfold wickMassShellH
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_emb : ![wickEmbedN n x c.1, wickEmbedN n x (P.mate c.1)] =
      wickEmbedN 2 ![x c.1, x (P.mate c.1)] := by
    ext s μ
    fin_cases s <;> rfl
  rw [h_emb]
  rfl

@[simp]
theorem wickMassShellH_zero {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (α : Fin 0 → κ) (z : Fin 0 → Fin 4 → ℂ) :
    wickMassShellH m η C 0 α z = 1 := by
  unfold wickMassShellH
  rw [Fintype.sum_unique]
  haveI : IsEmpty (default : ChordPairing 0).Chord := ⟨fun c => Fin.elim0 c.1⟩
  have hcross : (default : ChordPairing 0).cross = 0 := rfl
  simp [hcross]

@[simp]
theorem wickMassShellS_zero {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 0 → κ) (x : Fin 0 → Fin 4 → ℝ) :
    wickMassShellS m hm η C hC 0 α x = 1 :=
  wickMassShellH_zero m η C α (wickEmbedN 0 x)

@[simp]
theorem wickMassShellS_vacuumNormalized {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    OSVacuumNormalized (wickMassShellS m hm η C hC) :=
  wickMassShellS_zero m hm η C hC Fin.elim0 0

@[simp]
theorem wickMassShellW_zero_apply {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 0 → κ) (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    wickMassShellW m η C hC 0 α f = f 0 := by
  rw [wickMassShellW_apply, Fintype.sum_unique]
  haveI : IsEmpty (default : ChordPairing 0).Chord := ⟨fun c => Fin.elim0 c.1⟩
  haveI : Unique ((default : ChordPairing 0).Chord → Fin 3 → ℝ) := Pi.uniqueOfIsEmpty _
  have hcross : (default : ChordPairing 0).cross = 0 := rfl
  have hm0 : (default : ChordPairing 0).momentum m default = 0 := by
    ext i
    exact Fin.elim0 i
  have hw0 : wickChordWeight m C (default : ChordPairing 0) α default = 1 := by
    simp [wickChordWeight]
  rw [hcross, pow_zero, one_mul]
  have h_vol : (volume : Measure ((default : ChordPairing 0).Chord → Fin 3 → ℝ)) =
      Measure.dirac default := by
    change Measure.pi (fun _ => volume) = Measure.dirac default
    exact Measure.pi_of_empty _ default
  rw [h_vol, integral_dirac, hw0, one_mul, hm0, minkowskiFourier_eval_zero_n, integral_fin0]

theorem wickMassShellH_eq_zero_of_odd {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) {n : ℕ} (hn : Odd n)
    (α : Fin n → κ) (z : Fin n → Fin 4 → ℂ) :
    wickMassShellH m η C n α z = 0 := by
  haveI := ChordPairing.isEmpty_of_odd hn
  simp [wickMassShellH]

theorem wickMassShellS_eq_zero_of_odd {κ : Type*} (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    {n : ℕ} (hn : Odd n) (α : Fin n → κ) (x : Fin n → Fin 4 → ℝ) :
    wickMassShellS m hm η C hC n α x = 0 :=
  wickMassShellH_eq_zero_of_odd m η C hn α (wickEmbedN n x)

theorem wickMassShellW_eq_zero_of_odd {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    {n : ℕ} (hn : Odd n) (α : Fin n → κ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wickMassShellW m η C hC n α f = 0 := by
  rw [wickMassShellW_apply]
  haveI := ChordPairing.isEmpty_of_odd hn
  simp

@[simp]
theorem wickMassShellH_two {κ : Type*} (m : ℝ) (η : ℂ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ)
    (α : Fin 2 → κ) (z : Fin 2 → Fin 4 → ℂ) :
    wickMassShellH m η C 2 α z = massShellTwoPointH m C 2 α z := by
  unfold wickMassShellH
  rw [Fintype.sum_unique]
  change η ^ ChordPairing.twoPairing.cross *
    (∏ c ∈ (Finset.univ : Finset ChordPairing.twoPairing.Chord),
      massShellTwoPointH m C 2
        ![α c.1, α (ChordPairing.twoPairing.mate c.1)]
        ![z c.1, z (ChordPairing.twoPairing.mate c.1)]) = _
  rw [ChordPairing.cross_two, pow_zero, one_mul, ChordPairing.unique_twoPairing_chord,
      Finset.prod_singleton]
  change massShellTwoPointH m C 2 ![α 0, α 1] ![z 0, z 1] = _
  rw [(finTwo_eq_vecCons α).symm, (finTwo_eq_vecCons z).symm]

theorem wickMassShellW_two {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) :
    wickMassShellW m η C hC 2 α = massShellTwoPointW m C hC 2 α := by
  ext f
  have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  have hb1 := tendsto_wickMassShellH_boundary hm η hC 2 α f hv
  have hb2 := tendsto_massShellTwoPointH_boundary hm hC 2 α f hv
  have h_eq :
      (fun t : ℝ => ∫ x : Fin 2 → Fin 4 → ℝ,
        wickMassShellH m η C 2 α (tubeBoundaryLine 2 x unit_time_vector t) * f x) =
      fun t : ℝ => ∫ x : Fin 2 → Fin 4 → ℝ,
        massShellTwoPointH m C 2 α (tubeBoundaryLine 2 x unit_time_vector t) * f x := by
    ext t
    simp only [wickMassShellH_two]
  rw [h_eq] at hb1
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique hb1 hb2

theorem wickMassShell_forwardConeSpectrumCondition {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    ForwardConeSpectrumCondition (wickMassShellW m η C hC) := by
  intro n α f ⟨U, _hU_open, hU_sub, hU_zero⟩
  rw [wickMassShellW_apply]
  refine Finset.sum_eq_zero (fun P _ => ?_)
  have h_zero :
      (fun p : P.Chord → Fin 3 → ℝ =>
        wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) =
      fun _ => 0 := by
    ext p
    rw [hU_zero (P.momentum m p) (hU_sub (P.momentum_mem_forwardConeSpectralRegion hm p)),
        mul_zero]
  rw [h_zero, integral_zero, mul_zero]

theorem wickMassShell_nondeg_and_not_zeroMomentum {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) {r : (Fin 3 → ℝ) → ℝ}
    (hr_cont : Continuous r) (hr_pos : ∀ p : Fin 3 → ℝ, 0 < r p)
    (hr_eq : ∀ p : Fin 3 → ℝ, C α (massShellVec m p) = (r p : ℂ)) :
    wickMassShellW m η C hC 2 α ≠ 0 ∧
      ¬ ZeroMomentumSpectrumCondition (wickMassShellW m η C hC) := by
  rcases massShellTwoPoint_nondeg_and_not_zeroMomentum hm hC α hr_cont hr_pos hr_eq with
    ⟨hne, hnot⟩
  refine ⟨by rwa [wickMassShellW_two hm η hC α], fun hspec => hnot ?_⟩
  intro n β f hf0
  match n with
  | 0 =>
      rw [minkowskiFourier_eval_zero_n, integral_fin0] at hf0
      rw [massShellTwoPointW_zero_apply, hf0]
  | 1 => rfl
  | _ + 3 => rfl
  | 2 =>
      rw [← wickMassShellW_two hm η hC β]
      exact hspec 2 β f hf0

theorem wickMassShellTubeTranslationInvariant {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    TubeTranslationInvariant (wickMassShellTubeExtension m hm η C hC) := by
  intro n α z a hz
  change wickMassShellH m η C n α (fun i => z i + a) = wickMassShellH m η C n α z
  unfold wickMassShellH
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_pair : ![z c.1 + a, z (P.mate c.1) + a] =
      fun k : Fin 2 => ![z c.1, z (P.mate c.1)] k + a := by
    ext k μ
    fin_cases k <;> rfl
  rw [h_pair]
  exact massShellTwoPointTubeTranslationInvariant hm hC 2
    ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)] a
    (pair_mem_forward_tube_two hz c.2)

theorem wickMassShellOSTranslationInvariant {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    OSTranslationInvariant (wickMassShellS m hm η C hC) :=
  schwingerFromTube_translation_invariant
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeTranslationInvariant hm η hC)

theorem wickMassShellTubeCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    TubeCovariant R (wickMassShellTubeExtension m hm η C hC) := by
  intro n A z hz hAz α
  change wickMassShellH m η C n α (spinorPhi (A, sl2c_conj A) • z) =
    ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) * wickMassShellH m η C n β z
  unfold wickMassShellH
  have h_rhs_swap :
      (∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) *
        ∑ P : ChordPairing n, η ^ P.cross *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 ![β c.1, β (P.mate c.1)] ![z c.1, z (P.mate c.1)]) =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 ![β c.1, β (P.mate c.1)] ![z c.1, z (P.mate c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    exact Finset.sum_congr rfl (fun β _ => by ring)
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  rw [P.sum_prod_chord_factor (fun i b => R.rep A (α i) b)
    (fun c γ => massShellTwoPointH m C 2 γ ![z c.1, z (P.mate c.1)])]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_smul_pair :
      ![(spinorPhi (A, sl2c_conj A) • z) c.1,
        (spinorPhi (A, sl2c_conj A) • z) (P.mate c.1)] =
      spinorPhi (A, sl2c_conj A) • ![z c.1, z (P.mate c.1)] := by
    ext k μ
    fin_cases k <;> rfl
  have hz_pair := pair_mem_forward_tube_two hz c.2
  have hAz_pair : spinorPhi (A, sl2c_conj A) • ![z c.1, z (P.mate c.1)] ∈ forward_tube_n 2 := by
    rw [← h_smul_pair]
    exact pair_mem_forward_tube_two hAz c.2
  have h2 := massShellTwoPointTubeCovariant R hm hC hC_cov 2 A
    ![z c.1, z (P.mate c.1)] hz_pair hAz_pair ![α c.1, α (P.mate c.1)]
  change massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)]
      (spinorPhi (A, sl2c_conj A) • ![z c.1, z (P.mate c.1)]) =
    ∑ γ : Fin 2 → ι, (∏ i : Fin 2, R.rep A (![α c.1, α (P.mate c.1)] i) (γ i)) *
      massShellTwoPointH m C 2 γ ![z c.1, z (P.mate c.1)] at h2
  rw [h_smul_pair, h2]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

theorem wickMassShellPoincareCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    PoincareCovariant R (wickMassShellW m η C hC) :=
  poincareCovariant_of_tubeCovariant_general R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeCovariant R hm η hC hC_cov)
    (wickMassShellTubeTranslationInvariant hm η hC)

theorem wickMassShellEuclidRotCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    EuclidRotCovariant R (wickMassShellS m hm η C hC) :=
  schwingerFromTube_euclidCovariant R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeCovariant R hm η hC hC_cov)

theorem wickMassShellTubeWickHermiticity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubeWickHermiticity S (wickMassShellTubeExtension m hm η C hC) := by
  intro n α z hz hz_rev
  let z_rev : Fin n → Fin 4 → ℂ := fun i μ => star (z (Fin.rev i) μ)
  change star (wickMassShellH m η C n α z) =
    ∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) * wickMassShellH m η C n (β ∘ Fin.rev) z_rev
  unfold wickMassShellH
  rw [star_sum]
  have h_rhs_swap :
      (∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) *
        ∑ Q : ChordPairing n, η ^ Q.cross *
          ∏ c' : Q.Chord,
            massShellTwoPointH m C 2
              ![(β ∘ Fin.rev) c'.1, (β ∘ Fin.rev) (Q.mate c'.1)]
              ![z_rev c'.1, z_rev (Q.mate c'.1)]) =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∑ β : Fin n → ι, (∏ i : Fin n, S.C (α i) (β i)) *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
              ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← (ChordPairing.revEquiv n).sum_comp]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    have hrevP : ChordPairing.revEquiv n P = P.rev := rfl
    rw [hrevP, P.cross_rev]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← P.revChordEquiv.prod_comp]
    have h_prod_eq :
        (∏ c : P.Chord,
          massShellTwoPointH m C 2
            ![(β ∘ Fin.rev) (P.revChordEquiv c).1,
              (β ∘ Fin.rev) (P.rev.mate (P.revChordEquiv c).1)]
            ![z_rev (P.revChordEquiv c).1, z_rev (P.rev.mate (P.revChordEquiv c).1)]) =
        ∏ c : P.Chord,
          massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
            ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)] := by
      refine Finset.prod_congr rfl (fun c _ => ?_)
      have hm_eq : P.rev.mate (P.revChordEquiv c).1 = Fin.rev c.1 := by
        change Fin.rev (P.mate (Fin.rev (Fin.rev (P.mate c.1)))) = Fin.rev c.1
        rw [Fin.rev_rev, P.mate_mate]
      have h1 : (P.revChordEquiv c).1 = Fin.rev (P.mate c.1) := rfl
      have hβ : ![(β ∘ Fin.rev) (Fin.rev (P.mate c.1)), (β ∘ Fin.rev) (Fin.rev c.1)] =
          ![β c.1, β (P.mate c.1)] ∘ Fin.rev := by
        ext k
        fin_cases k <;> simp [Fin.rev_rev]
      rw [hm_eq, h1, hβ]
    rw [h_prod_eq]
    ring
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [star_mul', star_eta_pow hη]
  congr 1
  rw [Complex.star_def, map_prod]
  simp_rw [← Complex.star_def]
  rw [P.sum_prod_chord_factor (fun i b => S.C (α i) b)
    (fun c γ => massShellTwoPointH m C 2 (γ ∘ Fin.rev)
      ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)])]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have hz_pair := pair_mem_forward_tube_two hz c.2
  have hz_rev_pair_eq :
      (fun k μ => star (![z c.1, z (P.mate c.1)] (Fin.rev k) μ)) =
      ![z_rev (Fin.rev (P.mate c.1)), z_rev (Fin.rev c.1)] := by
    ext k μ
    fin_cases k <;> simp [z_rev, Fin.rev_rev]
  have hz_rev_pair : (fun k μ => star (![z c.1, z (P.mate c.1)] (Fin.rev k) μ)) ∈
      forward_tube_n 2 := by
    rw [hz_rev_pair_eq]
    exact pair_mem_forward_tube_two hz_rev (Fin.rev_lt_rev.mpr c.2)
  have h2 := massShellTwoPointTubeWickHermiticity S hm hC hC_herm 2
    ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)] hz_pair hz_rev_pair
  change star (massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]) =
    ∑ γ : Fin 2 → ι, (∏ i : Fin 2, S.C (![α c.1, α (P.mate c.1)] i) (γ i)) *
      massShellTwoPointH m C 2 (γ ∘ Fin.rev)
        (fun k μ => star (![z c.1, z (P.mate c.1)] (Fin.rev k) μ)) at h2
  rw [h2, hz_rev_pair_eq]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

theorem wickMassShellOSHermiticity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSHermiticity S (wickMassShellS m hm η C hC) :=
  schwingerFromTube_os_hermiticity S (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeWickHermiticity S hm hη hC hC_herm)

theorem wickMassShellTubePCT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubePCT η R (wickMassShellTubeExtension m hm η C hC) := by
  intro n α z hz
  change wickMassShellH m η C n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) *
      ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
        wickMassShellH m η C n (β ∘ Fin.rev) z
  unfold wickMassShellH
  have h_rhs_swap :
      η ^ (n * (n - 1) / 2) *
        (∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
          ∑ Q : ChordPairing n, η ^ Q.cross *
            ∏ c' : Q.Chord,
              massShellTwoPointH m C 2
                ![(β ∘ Fin.rev) c'.1, (β ∘ Fin.rev) (Q.mate c'.1)]
                ![z c'.1, z (Q.mate c'.1)]) =
      ∑ P : ChordPairing n, (η ^ (n * (n - 1) / 2) * η ^ P.rev.cross) *
        ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
          ∏ c : P.Chord,
            massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
              ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← (ChordPairing.revEquiv n).sum_comp]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    have hrevP : ChordPairing.revEquiv n P = P.rev := rfl
    rw [hrevP]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [← P.revChordEquiv.prod_comp]
    have h_prod_eq :
        (∏ c : P.Chord,
          massShellTwoPointH m C 2
            ![(β ∘ Fin.rev) (P.revChordEquiv c).1,
              (β ∘ Fin.rev) (P.rev.mate (P.revChordEquiv c).1)]
            ![z (P.revChordEquiv c).1, z (P.rev.mate (P.revChordEquiv c).1)]) =
        ∏ c : P.Chord,
          massShellTwoPointH m C 2 (![β c.1, β (P.mate c.1)] ∘ Fin.rev)
            ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)] := by
      refine Finset.prod_congr rfl (fun c _ => ?_)
      have hm_eq : P.rev.mate (P.revChordEquiv c).1 = Fin.rev c.1 := by
        change Fin.rev (P.mate (Fin.rev (Fin.rev (P.mate c.1)))) = Fin.rev c.1
        rw [Fin.rev_rev, P.mate_mate]
      have h1 : (P.revChordEquiv c).1 = Fin.rev (P.mate c.1) := rfl
      have hβ : ![(β ∘ Fin.rev) (Fin.rev (P.mate c.1)), (β ∘ Fin.rev) (Fin.rev c.1)] =
          ![β c.1, β (P.mate c.1)] ∘ Fin.rev := by
        ext k
        fin_cases k <;> simp [Fin.rev_rev]
      rw [hm_eq, h1, hβ]
    rw [h_prod_eq]
    ring
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  rw [← P.eta_pow_card_chord_mul_cross hη,
      P.sum_prod_chord_factor (fun i b => R.σ (-1, 1) (α i) b)
        (fun c γ => massShellTwoPointH m C 2 (γ ∘ Fin.rev)
          ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)])]
  have h_each : ∀ c : P.Chord,
      massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)]
        ![(-(z ∘ Fin.rev)) c.1, (-(z ∘ Fin.rev)) (P.mate c.1)] =
      η * ∑ γ : Fin 2 → ι,
        (R.σ (-1, 1) (α c.1) (γ 0) * R.σ (-1, 1) (α (P.mate c.1)) (γ 1)) *
          massShellTwoPointH m C 2 (γ ∘ Fin.rev)
            ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)] := by
    intro c
    let w : Fin 2 → Fin 4 → ℂ := ![z (Fin.rev (P.mate c.1)), z (Fin.rev c.1)]
    have hw : w ∈ forward_tube_n 2 := pair_mem_forward_tube_two hz (Fin.rev_lt_rev.mpr c.2)
    have h_neg_w : ![(-(z ∘ Fin.rev)) c.1, (-(z ∘ Fin.rev)) (P.mate c.1)] = -(w ∘ Fin.rev) := by
      ext k μ
      fin_cases k <;> rfl
    have h2 := massShellTwoPointTubePCT R hm hC hC_pct 2 ![α c.1, α (P.mate c.1)] w hw
    rw [two_mul_two_sub_one_div_two, pow_one] at h2
    change massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] (-(w ∘ Fin.rev)) =
      η * ∑ γ : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (![α c.1, α (P.mate c.1)] i) (γ i)) *
          massShellTwoPointH m C 2 (γ ∘ Fin.rev) w at h2
    rw [h_neg_w, h2]
    congr 1
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Fin.prod_univ_two]
    rfl
  simp_rw [h_each, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

theorem wickMassShellWightmanPCT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanPCT η R (wickMassShellW m η C hC) :=
  wightman_pct_of_tubePCT_general R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubePCT R hm hη hC hC_pct)
    (wickMassShellTubeTranslationInvariant hm η hC)

theorem wickMassShellWeakLocality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WeakLocality η (wickMassShellW m η C hC) :=
  weakLocality_of_tubePCT R (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeCovariant R hm η hC hC_cov)
    (wickMassShellTubePCT R hm hη hC hC_pct)

lemma minkowskiFourier_perm_symm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (x ∘ σ) = f x)
    (q : Fin n → Fin 4 → ℝ) :
    minkowskiFourier f' q = minkowskiFourier f (q ∘ σ.symm) := by
  unfold minkowskiFourier
  let e : (Fin n → Fin 4 → ℝ) ≃ᵐ (Fin n → Fin 4 → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Fin 4 → ℝ) σ.symm
  have hmp : MeasurePreserving e volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin n => Fin 4 → ℝ) σ.symm
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  dsimp only [Function.comp_apply]
  have he : e x = x ∘ σ := by
    ext j μ
    have hj : j = σ.symm (σ j) := (σ.symm_apply_apply j).symm
    conv_lhs => rw [hj]
    simp only [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply,
      Function.comp_apply]
  rw [he, hf' x]
  congr 2
  have hsum :
      (∑ k : Fin n, minkowskiInner (q k) (x (σ k))) =
        ∑ r : Fin n, minkowskiInner (q (σ.symm r)) (x r) :=
    Fintype.sum_equiv σ
      (fun k => minkowskiInner (q k) (x (σ k)))
      (fun r => minkowskiInner (q (σ.symm r)) (x r))
      (fun k => by simp)
  dsimp only [Function.comp_apply]
  rw [hsum]

abbrev adjRestIdx (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) : Type :=
  { k : Fin n // ¬ (k = i ∨ k = ⟨i.val + 1, hi⟩) }

def adjPairEquiv {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    Fin 2 ≃ { k : Fin n // k = i ∨ k = ⟨i.val + 1, hi⟩ } where
  toFun b := if b = 0 then ⟨i, Or.inl rfl⟩ else ⟨⟨i.val + 1, hi⟩, Or.inr rfl⟩
  invFun k := if k.1 = i then 0 else 1
  left_inv b := by
    have hii' : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      dsimp at hv
      omega
    fin_cases b <;> simp [hii']
  right_inv k := by
    rcases k with ⟨k, rfl | rfl⟩
    · simp
    · have hii' : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp at hv
        omega
      simp [hii']

def adjEmbedTwoLI {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (Fin 2 → Fin 4 → ℝ) →ₗᵢ[ℝ] (Fin n → Fin 4 → ℝ) where
  toFun y k := if k = i then y 0 else if k = ⟨i.val + 1, hi⟩ then y 1 else 0
  map_add' y₁ y₂ := by
    ext k μ
    dsimp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c y := by
    ext k μ
    dsimp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
  norm_map' y := by
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr (fun k => ?_)
      change ‖(if k = i then y 0 else if k = ⟨i.val + 1, hi⟩ then y 1 else 0)‖ ≤ ‖y‖
      split_ifs
      · exact norm_le_pi_norm y 0
      · exact norm_le_pi_norm y 1
      · simp [norm_nonneg y]
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun b => ?_)
      have hii' : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        dsimp at hv
        omega
      rcases b with ⟨_ | _ | b, hb⟩
      · simpa using norm_le_pi_norm
          (fun k : Fin n => if k = i then y 0 else if k = ⟨i.val + 1, hi⟩ then y 1 else 0) i
      · simpa [hii'] using norm_le_pi_norm
          (fun k : Fin n => if k = i then y 0 else if k = ⟨i.val + 1, hi⟩ then y 1 else 0)
          ⟨i.val + 1, hi⟩
      · omega

def adjEmbedRest {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun k => if hk : k = i ∨ k = ⟨i.val + 1, hi⟩ then 0 else z ⟨k, hk⟩

def adjMerge {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  adjEmbedTwoLI i hi y + adjEmbedRest i hi z

lemma adjMerge_apply_left {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    adjMerge i hi y z i = y 0 := by
  change (if i = i then y 0 else if i = ⟨i.val + 1, hi⟩ then y 1 else 0) +
      (if hk : i = i ∨ i = ⟨i.val + 1, hi⟩ then 0 else z ⟨i, hk⟩) = y 0
  rw [if_pos rfl, dif_pos (Or.inl rfl), add_zero]

lemma adjMerge_apply_right {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    adjMerge i hi y z ⟨i.val + 1, hi⟩ = y 1 := by
  have hii' : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  change (if (⟨i.val + 1, hi⟩ : Fin n) = i then y 0
      else if (⟨i.val + 1, hi⟩ : Fin n) = ⟨i.val + 1, hi⟩ then y 1 else 0) +
      (if hk : (⟨i.val + 1, hi⟩ : Fin n) = i ∨
        (⟨i.val + 1, hi⟩ : Fin n) = ⟨i.val + 1, hi⟩ then 0 else z ⟨⟨i.val + 1, hi⟩, hk⟩) = y 1
  rw [if_neg hii', if_pos rfl, dif_pos (Or.inr rfl), add_zero]

lemma adjMerge_apply_rest {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ)
    (r : adjRestIdx n i hi) :
    adjMerge i hi y z r.1 = z r := by
  have h1 : r.1 ≠ i := fun h => r.2 (Or.inl h)
  have h2 : r.1 ≠ ⟨i.val + 1, hi⟩ := fun h => r.2 (Or.inr h)
  change (if r.1 = i then y 0 else if r.1 = ⟨i.val + 1, hi⟩ then y 1 else 0) +
      (if hk : r.1 = i ∨ r.1 = ⟨i.val + 1, hi⟩ then 0 else z ⟨r.1, hk⟩) = z r
  rw [if_neg h1, if_neg h2, dif_neg r.2, zero_add]

lemma norm_le_adjMerge_left {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    ‖y‖ ≤ ‖adjMerge i hi y z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun b => ?_)
  rcases b with ⟨_ | _ | b, hb⟩
  · change ‖y 0‖ ≤ ‖adjMerge i hi y z‖
    rw [← adjMerge_apply_left i hi y z]
    exact norm_le_pi_norm (adjMerge i hi y z) i
  · change ‖y 1‖ ≤ ‖adjMerge i hi y z‖
    rw [← adjMerge_apply_right i hi y z]
    exact norm_le_pi_norm (adjMerge i hi y z) ⟨i.val + 1, hi⟩
  · omega

lemma norm_le_adjMerge_right {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    ‖z‖ ≤ ‖adjMerge i hi y z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun r => ?_)
  rw [← adjMerge_apply_rest i hi y z r]
  exact norm_le_pi_norm (adjMerge i hi y z) r.1

lemma adjMerge_comp_adjSwap {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    (adjMerge i hi y z) ∘ ChordPairing.adjSwap i hi =
      adjMerge i hi (y ∘ Fin.rev) z := by
  let i' : Fin n := ⟨i.val + 1, hi⟩
  ext k μ
  by_cases hki : k = i
  · rw [hki]
    change adjMerge i hi y z (Equiv.swap i i' i) μ =
      adjMerge i hi (y ∘ Fin.rev) z i μ
    rw [Equiv.swap_apply_left, adjMerge_apply_right, adjMerge_apply_left]
    rfl
  · by_cases hki' : k = i'
    · rw [hki']
      change adjMerge i hi y z (Equiv.swap i i' i') μ =
        adjMerge i hi (y ∘ Fin.rev) z i' μ
      rw [Equiv.swap_apply_right, adjMerge_apply_left, adjMerge_apply_right]
      rfl
    · have hk_not : ¬ (k = i ∨ k = i') := not_or.mpr ⟨hki, hki'⟩
      change adjMerge i hi y z (Equiv.swap i i' k) μ =
        adjMerge i hi (y ∘ Fin.rev) z k μ
      rw [Equiv.swap_apply_of_ne_of_ne hki hki',
          adjMerge_apply_rest i hi y z ⟨k, hk_not⟩,
          adjMerge_apply_rest i hi (y ∘ Fin.rev) z ⟨k, hk_not⟩]

def adjSplitMeasEquiv {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    (Fin n → Fin 4 → ℝ) ≃ᵐ
      (Fin 2 → Fin 4 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Fin 4 → ℝ)
    (fun k => k = i ∨ k = ⟨i.val + 1, hi⟩)).trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Fin 4 → ℝ)
      (adjPairEquiv i hi).symm).prodCongr (MeasurableEquiv.refl _))

lemma measurePreserving_adjSplitMeasEquiv {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    MeasurePreserving (adjSplitMeasEquiv i hi) volume (volume.prod volume) :=
  (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin n => Fin 4 → ℝ)
    (fun k => k = i ∨ k = ⟨i.val + 1, hi⟩)).trans
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => Fin 4 → ℝ)
      (adjPairEquiv i hi).symm).prod (MeasurePreserving.id volume))

lemma adjSplitMeasEquiv_symm_apply {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (y : Fin 2 → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    (adjSplitMeasEquiv i hi).symm (y, z) = adjMerge i hi y z := by
  apply (adjSplitMeasEquiv i hi).injective
  rw [(adjSplitMeasEquiv i hi).apply_symm_apply]
  apply Prod.ext
  · ext b μ
    have hb : b = (adjPairEquiv i hi).symm (adjPairEquiv i hi b) :=
      ((adjPairEquiv i hi).symm_apply_apply b).symm
    change y b μ =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => Fin 4 → ℝ) (adjPairEquiv i hi).symm
        (fun u : { k : Fin n // k = i ∨ k = ⟨i.val + 1, hi⟩ } => adjMerge i hi y z u.1)) b μ
    conv_rhs => rw [hb]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rcases b with ⟨_ | _ | b, hb_lt⟩
    · change y 0 μ = adjMerge i hi y z (adjPairEquiv i hi 0).1 μ
      have hp0 : (adjPairEquiv i hi 0).1 = i := rfl
      rw [hp0, adjMerge_apply_left]
    · change y 1 μ = adjMerge i hi y z (adjPairEquiv i hi 1).1 μ
      have hp1 : (adjPairEquiv i hi 1).1 = ⟨i.val + 1, hi⟩ := rfl
      rw [hp1, adjMerge_apply_right]
    · omega
  · ext r μ
    change z r μ = adjMerge i hi y z r.1 μ
    rw [adjMerge_apply_rest]

lemma hasTemperateGrowth_adjMerge {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    Function.HasTemperateGrowth (fun y : Fin 2 → Fin 4 → ℝ => adjMerge i hi y z) :=
  (adjEmbedTwoLI i hi).toContinuousLinearMap.hasTemperateGrowth.add
    (Function.HasTemperateGrowth.const (adjEmbedRest i hi z))

lemma antilipschitzWith_adjMerge {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    AntilipschitzWith 1 (fun y : Fin 2 → Fin 4 → ℝ => adjMerge i hi y z) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro y₁ y₂
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hsub : adjMerge i hi y₁ z - adjMerge i hi y₂ z = adjEmbedTwoLI i hi (y₁ - y₂) := by
    dsimp [adjMerge]
    rw [add_sub_add_right_eq_sub, ← map_sub]
  rw [hsub, (adjEmbedTwoLI i hi).norm_map]

noncomputable def adjSliceSchwartz {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_adjMerge i hi z)
    (antilipschitzWith_adjMerge i hi z)

@[simp]
lemma adjSliceSchwartz_apply {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (y : Fin 2 → Fin 4 → ℝ) :
    adjSliceSchwartz i hi z f y = f (adjMerge i hi y z) := rfl

lemma tsupport_adjSliceSchwartz_subset_jost_two {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
      { x | is_spacelike (x i - x ⟨i.val + 1, hi⟩) }) :
    tsupport (adjSliceSchwartz i hi z f : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n 2 := by
  have h_cont : Continuous (fun y : Fin 2 → Fin 4 → ℝ => adjMerge i hi y z) :=
    (adjEmbedTwoLI i hi).continuous.add continuous_const
  have h_pre : tsupport (adjSliceSchwartz i hi z f : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆
      (fun y => adjMerge i hi y z) ⁻¹' tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) := by
    refine closure_minimal ?_ ((isClosed_tsupport _).preimage h_cont)
    intro y hy
    exact subset_tsupport _ hy
  intro y hy
  have hsl := hf (h_pre hy)
  dsimp only [Set.mem_setOf_eq] at hsl
  rw [adjMerge_apply_left, adjMerge_apply_right] at hsl
  exact mem_jost_points_two_of_minkowskiInner_sub_lt_zero hsl

lemma seminorm_adjSliceSchwartz_le {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (z : adjRestIdx n i hi → Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (M k l : ℕ) :
    SchwartzMap.seminorm ℝ k l (adjSliceSchwartz i hi z f) ≤
      (2 ^ (M + k) * ((Finset.Iic (M + k, l)).sup
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ) f)) *
        ((1 + ‖z‖) ^ M)⁻¹ := by
  let S : ℝ := (Finset.Iic (M + k, l)).sup
    (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ) f
  have hS_nn : 0 ≤ S := apply_nonneg _ f
  have hz_pos : 0 < (1 + ‖z‖) ^ M := by positivity
  refine SchwartzMap.seminorm_le_bound ℝ k l (adjSliceSchwartz i hi z f)
    (by positivity) (fun y => ?_)
  refine (le_mul_inv_iff₀' hz_pos).mpr ?_
  let L₁ := (adjEmbedTwoLI i hi).toContinuousLinearMap
  have h_fn : ((adjSliceSchwartz i hi z f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
      (Fin 2 → Fin 4 → ℝ) → ℂ) =
      (fun x : Fin n → Fin 4 → ℝ => f (x + adjEmbedRest i hi z)) ∘ L₁ := rfl
  have h_sm : ContDiff ℝ (l : ℕ∞)
      (fun x : Fin n → Fin 4 → ℝ => (f : (Fin n → Fin 4 → ℝ) → ℂ) (x + adjEmbedRest i hi z)) :=
    (f.smooth l).comp (contDiff_id.add contDiff_const)
  have h_ifd :
      iteratedFDeriv ℝ l (adjSliceSchwartz i hi z f : (Fin 2 → Fin 4 → ℝ) → ℂ) y =
        (iteratedFDeriv ℝ l (f : (Fin n → Fin 4 → ℝ) → ℂ)
          (adjMerge i hi y z)).compContinuousLinearMap (fun _ => L₁) := by
    rw [h_fn, L₁.iteratedFDeriv_comp_right h_sm y le_rfl,
        iteratedFDeriv_comp_add_right l (adjEmbedRest i hi z) (L₁ y)]
    rfl
  have h_norm_ifd :
      ‖iteratedFDeriv ℝ l (adjSliceSchwartz i hi z f : (Fin 2 → Fin 4 → ℝ) → ℂ) y‖ ≤
        ‖iteratedFDeriv ℝ l (f : (Fin n → Fin 4 → ℝ) → ℂ) (adjMerge i hi y z)‖ := by
    rw [h_ifd]
    exact ContinuousMultilinearMap.norm_compContinuous_linearIsometry_le _
      (fun _ => adjEmbedTwoLI i hi)
  have hy_le : ‖y‖ ^ k ≤ (1 + ‖adjMerge i hi y z‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg y)
      (by linarith [norm_le_adjMerge_left i hi y z]) k
  have hz_le : (1 + ‖z‖) ^ M ≤ (1 + ‖adjMerge i hi y z‖) ^ M :=
    pow_le_pow_left₀ (by positivity)
      (by linarith [norm_le_adjMerge_right i hi y z]) M
  have h_sch :
      (1 + ‖adjMerge i hi y z‖) ^ (M + k) *
        ‖iteratedFDeriv ℝ l (f : (Fin n → Fin 4 → ℝ) → ℂ) (adjMerge i hi y z)‖ ≤
      2 ^ (M + k) * S := by
    have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℝ) (m := (M + k, l)) (k := M + k) (n := l) le_rfl le_rfl f (adjMerge i hi y z)
    have h_fam :
        (fun m : ℕ × ℕ => SchwartzMap.seminorm (E := Fin n → Fin 4 → ℝ) (F := ℂ) ℝ m.1 m.2) =
        schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ := rfl
    simpa [h_fam, S] using h0
  calc (1 + ‖z‖) ^ M * (‖y‖ ^ k *
          ‖iteratedFDeriv ℝ l (adjSliceSchwartz i hi z f : (Fin 2 → Fin 4 → ℝ) → ℂ) y‖)
      ≤ (1 + ‖adjMerge i hi y z‖) ^ M * ((1 + ‖adjMerge i hi y z‖) ^ k *
          ‖iteratedFDeriv ℝ l (f : (Fin n → Fin 4 → ℝ) → ℂ) (adjMerge i hi y z)‖) := by
        refine mul_le_mul hz_le
          (mul_le_mul hy_le h_norm_ifd (norm_nonneg _) (by positivity))
          (by positivity) (by positivity)
    _ = (1 + ‖adjMerge i hi y z‖) ^ (M + k) *
          ‖iteratedFDeriv ℝ l (f : (Fin n → Fin 4 → ℝ) → ℂ) (adjMerge i hi y z)‖ := by
        rw [← mul_assoc, ← pow_add]
    _ ≤ 2 ^ (M + k) * S := h_sch

lemma fourier_twoPoint_sup_seminorm_bound :
    ∃ (s : Finset (ℕ × ℕ)) (K : ℝ), 0 ≤ K ∧
      ∀ h : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ,
        ((Finset.Iic (4, 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ)
          (minkowskiFourierSchwartzCLM 2 h)) ≤
          K * ∑ kl ∈ s, SchwartzMap.seminorm ℝ kl.1 kl.2 h := by
  let F_lin : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ →ₗ[ℝ]
      SchwartzMap (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ :=
    (minkowskiFourierSchwartzCLM 2).toLinearMap.restrictScalars ℝ
  let q : Seminorm ℝ (SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :=
    ∑ ij ∈ Finset.Iic (4, 0),
      (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ ij).comp F_lin
  have hq_cont : Continuous q := by
    change Continuous (fun h => ∑ ij ∈ Finset.Iic (4, 0),
      schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ ij
        (minkowskiFourierSchwartzCLM 2 h))
    exact continuous_finsetSum _ (fun ij _ =>
      ((schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ).continuous_seminorm ij).comp
        (minkowskiFourierSchwartzCLM 2).continuous)
  obtain ⟨s, C, _, hq_le⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (Fin 2 → Fin 4 → ℝ) ℂ) q hq_cont
  refine ⟨s, (C : ℝ), NNReal.coe_nonneg C, fun h => ?_⟩
  have hq_apply : q h = ∑ ij ∈ Finset.Iic (4, 0),
      schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ ij
        (minkowskiFourierSchwartzCLM 2 h) := by
    change FunLike.coeAddMonoidHom _ _ _ q h = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have h1 :
      ((Finset.Iic (4, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ)
        (minkowskiFourierSchwartzCLM 2 h)) ≤ q h := by
    rw [hq_apply]
    refine Seminorm.finset_sup_apply_le
      (Finset.sum_nonneg (fun ij _ => apply_nonneg
        (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ ij)
        (minkowskiFourierSchwartzCLM 2 h)))
      (fun ij hij => Finset.single_le_sum (fun m _ => apply_nonneg
        (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ m)
        (minkowskiFourierSchwartzCLM 2 h)) hij)
  have h2 :
      ((s.sup (schwartzSeminormFamily ℝ (Fin 2 → Fin 4 → ℝ) ℂ)) h) ≤
        ∑ kl ∈ s, SchwartzMap.seminorm ℝ kl.1 kl.2 h :=
    Seminorm.finset_sup_apply_le
      (Finset.sum_nonneg (fun kl _ => apply_nonneg (SchwartzMap.seminorm ℝ kl.1 kl.2) h))
      (fun kl hkl => Finset.single_le_sum
        (fun m _ => apply_nonneg (SchwartzMap.seminorm ℝ m.1 m.2) h) hkl)
  exact h1.trans ((hq_le h).trans (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg C)))

def adjEmbedMomentum {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (q : Fin 4 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun k => if k = i then q else if k = ⟨i.val + 1, hi⟩ then -q else 0

noncomputable def adjRestPhase {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (Q_rest : Fin n → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) : ℂ :=
  Complex.exp (-(Complex.I *
    ((∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r) : ℝ) : ℂ)))

lemma norm_adjRestPhase {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (Q_rest : Fin n → Fin 4 → ℝ) (z : adjRestIdx n i hi → Fin 4 → ℝ) :
    ‖adjRestPhase i hi Q_rest z‖ = 1 := by
  unfold adjRestPhase
  have h_eq :
      -(Complex.I * ((∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r) : ℝ) : ℂ)) =
        ((-(∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r)) : ℝ) : ℂ) *
          Complex.I := by
    push_cast
    ring
  rw [h_eq, Complex.norm_exp_ofReal_mul_I]

lemma continuous_adjRestPhase {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (Q_rest : Fin n → Fin 4 → ℝ) :
    Continuous (adjRestPhase i hi Q_rest) := by
  unfold adjRestPhase
  refine Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul ?_))
  refine Complex.continuous_ofReal.comp (continuous_finsetSum Finset.univ (fun r _ => ?_))
  have h_lin :
      (fun z : adjRestIdx n i hi → Fin 4 → ℝ => minkowskiInner (Q_rest r.1) (z r)) =
        fun z => Q_rest r.1 0 * z r 0 - Q_rest r.1 1 * z r 1 -
          Q_rest r.1 2 * z r 2 - Q_rest r.1 3 * z r 3 := by
    ext z
    simp [minkowskiInner_explicit]
  rw [h_lin]
  have hc : ∀ μ : Fin 4, Continuous (fun z : adjRestIdx n i hi → Fin 4 → ℝ => z r μ) :=
    fun μ => (continuous_apply μ).comp (continuous_apply r)
  exact ((((continuous_const.mul (hc 0)).sub (continuous_const.mul (hc 1))).sub
    (continuous_const.mul (hc 2))).sub (continuous_const.mul (hc 3)))

lemma minkowskiFourier_eq_integral_adjSlice {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {Q_rest : Fin n → Fin 4 → ℝ} (hQi : Q_rest i = 0) (hQi' : Q_rest ⟨i.val + 1, hi⟩ = 0)
    (q : Fin 4 → ℝ) :
    minkowskiFourier f (adjEmbedMomentum i hi q + Q_rest) =
      ∫ z : adjRestIdx n i hi → Fin 4 → ℝ,
        adjRestPhase i hi Q_rest z *
          minkowskiFourier (adjSliceSchwartz i hi z f) (twoPointMomentum q) := by
  let Q := adjEmbedMomentum i hi q + Q_rest
  have hmp := (measurePreserving_adjSplitMeasEquiv i hi).symm
  have hint := integrable_f_mul_exp_phase n f Q
  have hint_prod : Integrable
      (fun yz : (Fin 2 → Fin 4 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ) =>
        f ((adjSplitMeasEquiv i hi).symm yz) *
          Complex.exp (-(Complex.I *
            ((∑ k : Fin n, minkowskiInner (Q k) ((adjSplitMeasEquiv i hi).symm yz k) : ℝ) : ℂ))))
      (volume.prod volume) :=
    hmp.integrable_comp_of_integrable hint
  unfold minkowskiFourier
  rw [← hmp.integral_comp', MeasureTheory.integral_prod_symm _ hint_prod]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  dsimp only
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  rw [adjSplitMeasEquiv_symm_apply, adjSliceSchwartz_apply]
  have hii' : (⟨i.val + 1, hi⟩ : Fin n) ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  have hQ_i : Q i = q := by simp [Q, adjEmbedMomentum, hQi]
  have hQ_i' : Q ⟨i.val + 1, hi⟩ = -q := by simp [Q, adjEmbedMomentum, hii', hQi']
  have hQ_rest : ∀ r : adjRestIdx n i hi, Q r.1 = Q_rest r.1 := by
    intro r
    have h1 : r.1 ≠ i := fun h => r.2 (Or.inl h)
    have h2 : r.1 ≠ ⟨i.val + 1, hi⟩ := fun h => r.2 (Or.inr h)
    simp [Q, adjEmbedMomentum, h1, h2]
  have h_sum_split :
      (∑ k : Fin n, minkowskiInner (Q k) (adjMerge i hi y z k)) =
        (∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r)) +
          ∑ b : Fin 2, minkowskiInner (twoPointMomentum q b) (y b) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => k = i ∨ k = ⟨i.val + 1, hi⟩)]
    have h_left :
        (∑ k : { k : Fin n // k = i ∨ k = ⟨i.val + 1, hi⟩ },
          minkowskiInner (Q k.1) (adjMerge i hi y z k.1)) =
        ∑ b : Fin 2, minkowskiInner (twoPointMomentum q b) (y b) := by
      rw [← (adjPairEquiv i hi).sum_comp, Fin.sum_univ_two, Fin.sum_univ_two]
      have hp0 : (adjPairEquiv i hi 0).1 = i := rfl
      have hp1 : (adjPairEquiv i hi 1).1 = ⟨i.val + 1, hi⟩ := rfl
      rw [hp0, hp1, hQ_i, hQ_i', adjMerge_apply_left, adjMerge_apply_right,
          twoPointMomentum_zero, twoPointMomentum_one]
    have h_right :
        (∑ r : adjRestIdx n i hi, minkowskiInner (Q r.1) (adjMerge i hi y z r.1)) =
        ∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r) := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [hQ_rest r, adjMerge_apply_rest]
    rw [h_left, h_right, add_comm]
  unfold adjRestPhase
  rw [h_sum_split]
  have h_exp :
      -(Complex.I *
        ((((∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r)) +
          ∑ b : Fin 2, minkowskiInner (twoPointMomentum q b) (y b)) : ℝ) : ℂ)) =
      (-(Complex.I *
        ((∑ r : adjRestIdx n i hi, minkowskiInner (Q_rest r.1) (z r) : ℝ) : ℂ))) +
      (-(Complex.I *
        ((∑ b : Fin 2, minkowskiInner (twoPointMomentum q b) (y b) : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [h_exp, Complex.exp_add]
  ring

lemma integrable_adjRestDecay (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    Integrable (fun z : adjRestIdx n i hi → Fin 4 → ℝ =>
      ((1 + ‖z‖) ^ (Module.finrank ℝ (adjRestIdx n i hi → Fin 4 → ℝ) + 1))⁻¹) volume := by
  let M : ℕ := Module.finrank ℝ (adjRestIdx n i hi → Fin 4 → ℝ) + 1
  have hlt : (Module.finrank ℝ (adjRestIdx n i hi → Fin 4 → ℝ) : ℝ) < (M : ℝ) := by
    exact_mod_cast Nat.lt_succ_self _
  have h := integrable_one_add_norm
    (E := adjRestIdx n i hi → Fin 4 → ℝ) (μ := volume) (r := (M : ℝ)) hlt
  refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
  dsimp only
  have hz : 0 < 1 + ‖z‖ := by positivity
  rw [Real.rpow_neg hz.le]
  norm_cast

theorem integrable_adjSlice_twoPoint_prod {κ : Type*} {n : ℕ} (i : Fin n) (hi : i.val + 1 < n)
    {m : ℝ} {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (β : Fin 2 → κ) (Q_rest : Fin n → Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Integrable
      (fun qz : (Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ) =>
        massShellWeight m C β qz.1 *
          (adjRestPhase i hi Q_rest qz.2 *
            minkowskiFourier (adjSliceSchwartz i hi qz.2 f)
              (twoPointMomentum (massShellVec m qz.1))))
      (volume.prod volume) := by
  rcases hC.2 β with ⟨B, hB_nn, hB⟩
  rcases fourier_twoPoint_sup_seminorm_bound with ⟨s, K, hK_nn, hK⟩
  let M : ℕ := Module.finrank ℝ (adjRestIdx n i hi → Fin 4 → ℝ) + 1
  let Cf : ℝ := ∑ kl ∈ s,
    2 ^ (M + kl.1) *
      ((Finset.Iic (M + kl.1, kl.2)).sup
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ) f)
  have hCf_nn : 0 ≤ Cf := Finset.sum_nonneg (fun kl _ =>
    mul_nonneg (by positivity) (apply_nonneg _ f))
  let C_tot : ℝ := B * (4 * Real.pi) ^ 4 * K * Cf
  have h_dom : Integrable
      (fun qz : (Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ) =>
        (C_tot * ((1 + ‖qz.1‖) ^ 4)⁻¹) * ((1 + ‖qz.2‖) ^ M)⁻¹)
      (volume.prod volume) :=
    (integrable_massShellDecay.const_mul C_tot).mul_prod (integrable_adjRestDecay n i hi)
  have h_inner_cont : Continuous
      (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
        f (adjMerge i hi p.2 p.1.2) *
          Complex.exp (-(Complex.I *
            ((∑ b : Fin 2,
              minkowskiInner (twoPointMomentum (massShellVec m p.1.1) b) (p.2 b) : ℝ) : ℂ)))) := by
    have h_merge_cont : Continuous
        (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
          adjMerge i hi p.2 p.1.2) := by
      have h1 : Continuous
          (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
            adjEmbedTwoLI i hi p.2) :=
        (adjEmbedTwoLI i hi).continuous.comp continuous_snd
      have h2 : Continuous
          (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
            adjEmbedRest i hi p.1.2) := by
        refine continuous_pi (fun k => ?_)
        dsimp [adjEmbedRest]
        split_ifs with hk
        · exact continuous_const
        · exact (continuous_apply (⟨k, hk⟩ : adjRestIdx n i hi)).comp
            (continuous_snd.comp continuous_fst)
      exact h1.add h2
    refine (f.continuous.comp h_merge_cont).mul
      (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul ?_)))
    refine Complex.continuous_ofReal.comp (continuous_finsetSum Finset.univ (fun b _ => ?_))
    have hq_cont : Continuous
        (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
          twoPointMomentum (massShellVec m p.1.1) b) := by
      fin_cases b
      · exact (continuous_massShellVec m).comp (continuous_fst.comp continuous_fst)
      · exact ((continuous_massShellVec m).comp (continuous_fst.comp continuous_fst)).neg
    have hy_cont : Continuous
        (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
          p.2 b) :=
      (continuous_apply b).comp continuous_snd
    have h_mink :
        (fun p : ((Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ)) × (Fin 2 → Fin 4 → ℝ) =>
          minkowskiInner (twoPointMomentum (massShellVec m p.1.1) b) (p.2 b)) =
        fun p =>
          twoPointMomentum (massShellVec m p.1.1) b 0 * p.2 b 0 -
            twoPointMomentum (massShellVec m p.1.1) b 1 * p.2 b 1 -
            twoPointMomentum (massShellVec m p.1.1) b 2 * p.2 b 2 -
            twoPointMomentum (massShellVec m p.1.1) b 3 * p.2 b 3 := by
      ext p
      simp [minkowskiInner_explicit]
    rw [h_mink]
    exact ((((((continuous_apply 0).comp hq_cont).mul ((continuous_apply 0).comp hy_cont)).sub
      (((continuous_apply 1).comp hq_cont).mul ((continuous_apply 1).comp hy_cont))).sub
      (((continuous_apply 2).comp hq_cont).mul ((continuous_apply 2).comp hy_cont))).sub
      (((continuous_apply 3).comp hq_cont).mul ((continuous_apply 3).comp hy_cont)))
  have h_mf_sm : StronglyMeasurable
      (fun qz : (Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ) =>
        minkowskiFourier (adjSliceSchwartz i hi qz.2 f)
          (twoPointMomentum (massShellVec m qz.1))) :=
    h_inner_cont.stronglyMeasurable.integral_prod_right'
  have h_aesm : AEStronglyMeasurable
      (fun qz : (Fin 3 → ℝ) × (adjRestIdx n i hi → Fin 4 → ℝ) =>
        massShellWeight m C β qz.1 *
          (adjRestPhase i hi Q_rest qz.2 *
            minkowskiFourier (adjSliceSchwartz i hi qz.2 f)
              (twoPointMomentum (massShellVec m qz.1))))
      (volume.prod volume) :=
    (((measurable_massShellWeight hC β).comp measurable_fst).stronglyMeasurable.mul
      (((continuous_adjRestPhase i hi Q_rest).comp continuous_snd).stronglyMeasurable.mul
        h_mf_sm)).aestronglyMeasurable
  refine h_dom.mono' h_aesm (Filter.Eventually.of_forall (fun ⟨q, z⟩ => ?_))
  dsimp only
  rw [norm_mul, norm_mul, norm_adjRestPhase, one_mul]
  let h_z := adjSliceSchwartz i hi z f
  let g_z := minkowskiFourierSchwartzCLM 2 h_z
  have h_mf_eq :
      minkowskiFourier h_z (twoPointMomentum (massShellVec m q)) =
        g_z (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m q))) :=
    minkowskiFourier_eq_minkowskiFourierSchwartzCLM 2 h_z (twoPointMomentum (massShellVec m q))
  rw [h_mf_eq]
  have h_q_bd := norm_schwartz_momentumToEuclid_massShell_le m g_z q
  have h_sum_z :
      (∑ kl ∈ s, SchwartzMap.seminorm ℝ kl.1 kl.2 h_z) ≤ Cf * ((1 + ‖z‖) ^ M)⁻¹ := by
    dsimp [Cf]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun kl _ => seminorm_adjSliceSchwartz_le i hi z f M kl.1 kl.2)
  have h_sup_z :
      ((Finset.Iic (4, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g_z) ≤
        K * (Cf * ((1 + ‖z‖) ^ M)⁻¹) :=
    (hK h_z).trans (mul_le_mul_of_nonneg_left h_sum_z hK_nn)
  calc ‖massShellWeight m C β q‖ *
        ‖g_z (momentumToEuclidCLMN 2 (twoPointMomentum (massShellVec m q)))‖
      ≤ B * (((4 * Real.pi) ^ 4 *
          ((Finset.Iic (4, 0)).sup
            (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2 × Fin 4)) ℂ) g_z)) *
          ((1 + ‖q‖) ^ 4)⁻¹) :=
        mul_le_mul (hB q) h_q_bd (norm_nonneg _) hB_nn
    _ ≤ B * (((4 * Real.pi) ^ 4 * (K * (Cf * ((1 + ‖z‖) ^ M)⁻¹))) *
          ((1 + ‖q‖) ^ 4)⁻¹) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_sup_z (by positivity))
            (by positivity))
          hB_nn
    _ = (C_tot * ((1 + ‖q‖) ^ 4)⁻¹) * ((1 + ‖z‖) ^ M)⁻¹ := by
        dsimp [C_tot]
        ring

theorem adjacentTwoPoint_massShell_swap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q)
    {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) (β : Fin 2 → ι)
    {Q_rest : Fin n → Fin 4 → ℝ} (hQi : Q_rest i = 0) (hQi' : Q_rest ⟨i.val + 1, hi⟩ = 0)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
      { x | is_spacelike (x i - x ⟨i.val + 1, hi⟩) })
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (x ∘ Equiv.swap i ⟨i.val + 1, hi⟩) = f x) :
    (∫ q : Fin 3 → ℝ, massShellWeight m C β q *
      minkowskiFourier f (adjEmbedMomentum i hi (massShellVec m q) + Q_rest)) =
    η * ∫ q : Fin 3 → ℝ, massShellWeight m C (β ∘ Fin.rev) q *
      minkowskiFourier f' (adjEmbedMomentum i hi (massShellVec m q) + Q_rest) := by
  have hloc2 := massShellTwoPointWeakLocality (η := η) R hm hC hC_cov hC_pct
  have h_lhs_fub :
      (∫ q : Fin 3 → ℝ, massShellWeight m C β q *
        minkowskiFourier f (adjEmbedMomentum i hi (massShellVec m q) + Q_rest)) =
      ∫ z : adjRestIdx n i hi → Fin 4 → ℝ,
        adjRestPhase i hi Q_rest z *
          massShellTwoPointW m C hC 2 β (adjSliceSchwartz i hi z f) := by
    have h1 :
        (fun q : Fin 3 → ℝ => massShellWeight m C β q *
          minkowskiFourier f (adjEmbedMomentum i hi (massShellVec m q) + Q_rest)) =
        fun q : Fin 3 → ℝ =>
          ∫ z : adjRestIdx n i hi → Fin 4 → ℝ,
            massShellWeight m C β q *
              (adjRestPhase i hi Q_rest z *
                minkowskiFourier (adjSliceSchwartz i hi z f)
                  (twoPointMomentum (massShellVec m q))) := by
      ext q
      rw [minkowskiFourier_eq_integral_adjSlice i hi f hQi hQi' (massShellVec m q),
          ← MeasureTheory.integral_const_mul]
    rw [h1, MeasureTheory.integral_integral_swap
      (integrable_adjSlice_twoPoint_prod i hi hC β Q_rest f)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [massShellTwoPointW_two_apply, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => by ring))
  have h_rhs_fub :
      (∫ q : Fin 3 → ℝ, massShellWeight m C (β ∘ Fin.rev) q *
        minkowskiFourier f' (adjEmbedMomentum i hi (massShellVec m q) + Q_rest)) =
      ∫ z : adjRestIdx n i hi → Fin 4 → ℝ,
        adjRestPhase i hi Q_rest z *
          massShellTwoPointW m C hC 2 (β ∘ Fin.rev) (adjSliceSchwartz i hi z f') := by
    have h1 :
        (fun q : Fin 3 → ℝ => massShellWeight m C (β ∘ Fin.rev) q *
          minkowskiFourier f' (adjEmbedMomentum i hi (massShellVec m q) + Q_rest)) =
        fun q : Fin 3 → ℝ =>
          ∫ z : adjRestIdx n i hi → Fin 4 → ℝ,
            massShellWeight m C (β ∘ Fin.rev) q *
              (adjRestPhase i hi Q_rest z *
                minkowskiFourier (adjSliceSchwartz i hi z f')
                  (twoPointMomentum (massShellVec m q))) := by
      ext q
      rw [minkowskiFourier_eq_integral_adjSlice i hi f' hQi hQi' (massShellVec m q),
          ← MeasureTheory.integral_const_mul]
    rw [h1, MeasureTheory.integral_integral_swap
      (integrable_adjSlice_twoPoint_prod i hi hC (β ∘ Fin.rev) Q_rest f')]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [massShellTwoPointW_two_apply, ← MeasureTheory.integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => by ring))
  rw [h_lhs_fub, h_rhs_fub, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  dsimp only
  have hz_jost := tsupport_adjSliceSchwartz_subset_jost_two i hi z f hf
  have hz_rev : ∀ y : Fin 2 → Fin 4 → ℝ,
      adjSliceSchwartz i hi z f' (fun b => y (Fin.rev b)) = adjSliceSchwartz i hi z f y := by
    intro y
    change f' (adjMerge i hi (y ∘ Fin.rev) z) = f (adjMerge i hi y z)
    rw [← adjMerge_comp_adjSwap i hi y z]
    exact hf' (adjMerge i hi y z)
  have h2 := hloc2 2 β (adjSliceSchwartz i hi z f) (adjSliceSchwartz i hi z f') hz_jost hz_rev
  rw [two_mul_two_sub_one_div_two, pow_one] at h2
  rw [h2]
  ring

lemma wickChord_integral_conjSwap_of_mate_ne {κ : Type*} {n : ℕ} (m : ℝ)
    (C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ) (P : ChordPairing n)
    (i : Fin n) (hi : i.val + 1 < n) (h_ne : P.mate i ≠ ⟨i.val + 1, hi⟩)
    (α : Fin n → κ) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (x ∘ Equiv.swap i ⟨i.val + 1, hi⟩) = f x) :
    (∫ p' : (P.conjSwap i hi).Chord → Fin 3 → ℝ,
      wickChordWeight m C (P.conjSwap i hi) α p' *
        minkowskiFourier f ((P.conjSwap i hi).momentum m p')) =
    ∫ p : P.Chord → Fin 3 → ℝ,
      wickChordWeight m C P (α ∘ Equiv.swap i ⟨i.val + 1, hi⟩) p *
        minkowskiFourier f' (P.momentum m p) := by
  let s : Equiv.Perm (Fin n) := ChordPairing.adjSwap i hi
  let ec := P.conjSwapChordEquiv i hi h_ne
  let ep : (P.Chord → Fin 3 → ℝ) ≃ᵐ ((P.conjSwap i hi).Chord → Fin 3 → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : (P.conjSwap i hi).Chord => Fin 3 → ℝ) ec
  have hmp : MeasurePreserving ep volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : (P.conjSwap i hi).Chord => Fin 3 → ℝ) ec
  rw [← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only [Function.comp_apply]
  have hep_apply : ∀ c : P.Chord, ep p (ec c) = p c := by
    intro c
    simp only [ep, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  have h_wt :
      wickChordWeight m C (P.conjSwap i hi) α (ep p) =
        wickChordWeight m C P (α ∘ s) p := by
    unfold wickChordWeight
    rw [← ec.prod_comp]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    have hc1 : (ec c).1 = s c.1 := rfl
    have hcm : (P.conjSwap i hi).mate (ec c).1 = s (P.mate c.1) := by
      rw [hc1, P.conjSwap_mate_apply, ChordPairing.adjSwap_apply_self]
    have hα : ![α (ec c).1, α ((P.conjSwap i hi).mate (ec c).1)] =
        ![(α ∘ s) c.1, (α ∘ s) (P.mate c.1)] := by
      rw [hcm, hc1]
      rfl
    rw [hα, hep_apply c]
  have hs_symm : s.symm = s := Equiv.ext (fun k => Equiv.swap_apply_def _ _ _)
  have h_mom : (P.conjSwap i hi).momentum m (ep p) = (P.momentum m p) ∘ s.symm := by
    rw [hs_symm]
    ext k μ
    have hk_s : k = s (s k) := (ChordPairing.adjSwap_apply_self i hi k).symm
    change (∑ c' : (P.conjSwap i hi).Chord,
        chordTwoPointMomentum (P.conjSwap i hi) c' (massShellVec m (ep p c')) k) μ =
      (∑ c : P.Chord, chordTwoPointMomentum P c (massShellVec m (p c)) (s k)) μ
    rw [← ec.sum_comp]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hc1 : (ec c).1 = s c.1 := rfl
    have hcm : (P.conjSwap i hi).mate (ec c).1 = s (P.mate c.1) := by
      rw [hc1, P.conjSwap_mate_apply, ChordPairing.adjSwap_apply_self]
    have h_chord :
        chordTwoPointMomentum (P.conjSwap i hi) (ec c) (massShellVec m (ep p (ec c))) k =
          chordTwoPointMomentum P c (massShellVec m (p c)) (s k) := by
      unfold chordTwoPointMomentum
      rw [hcm, hc1, hep_apply c]
      conv_lhs => rw [hk_s]
      simp only [s.injective.eq_iff]
    rw [h_chord]
  have hf'_fourier := (minkowskiFourier_perm_symm s f f' hf' (P.momentum m p)).symm
  rw [h_wt, h_mom, hf'_fourier]
  rfl

lemma wickChord_integral_of_mate_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q)
    {n : ℕ} (P : ChordPairing n) (i : Fin n) (hi : i.val + 1 < n)
    (h_eq : P.mate i = ⟨i.val + 1, hi⟩) (α : Fin n → ι)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
      { x | is_spacelike (x i - x ⟨i.val + 1, hi⟩) })
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (x ∘ Equiv.swap i ⟨i.val + 1, hi⟩) = f x) :
    (∫ p : P.Chord → Fin 3 → ℝ,
      wickChordWeight m C P α p * minkowskiFourier f (P.momentum m p)) =
    η * ∫ p : P.Chord → Fin 3 → ℝ,
      wickChordWeight m C P (α ∘ Equiv.swap i ⟨i.val + 1, hi⟩) p *
        minkowskiFourier f' (P.momentum m p) := by
  let i' : Fin n := ⟨i.val + 1, hi⟩
  let s : Equiv.Perm (Fin n) := Equiv.swap i i'
  let c₀ : P.Chord := ⟨i, by rw [h_eq]; exact Fin.lt_def.mpr (Nat.lt_succ_self i.val)⟩
  let e_unit : Unit ≃ { c : P.Chord // c.1 = i } :=
    { toFun := fun _ => ⟨c₀, rfl⟩
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun ⟨_, hc⟩ => Subtype.ext (Subtype.ext hc.symm) }
  let ep : (P.Chord → Fin 3 → ℝ) ≃ᵐ
      (Fin 3 → ℝ) × ({ c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ) :=
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : P.Chord => Fin 3 → ℝ) (fun c => c.1 = i)).trans
      (((MeasurableEquiv.piCongrLeft (fun _ : Unit => Fin 3 → ℝ) e_unit.symm).trans
        (MeasurableEquiv.piUnique (fun _ : Unit => Fin 3 → ℝ))).prodCongr
        (MeasurableEquiv.refl _))
  have hmp : MeasurePreserving ep volume (volume.prod volume) :=
    (volume_preserving_piEquivPiSubtypeProd
      (fun _ : P.Chord => Fin 3 → ℝ) (fun c => c.1 = i)).trans
      (((volume_measurePreserving_piCongrLeft (fun _ : Unit => Fin 3 → ℝ) e_unit.symm).trans
        (volume_preserving_piUnique (fun _ : Unit => Fin 3 → ℝ))).prod
        (MeasurePreserving.id volume))
  let p_mk :
      (Fin 3 → ℝ) → ({ c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ) → (P.Chord → Fin 3 → ℝ) :=
    fun q pr c => if hc : c.1 = i then q else pr ⟨c, hc⟩
  have hep_symm_eq : ∀ (q : Fin 3 → ℝ) (pr : { c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ),
      ep.symm (q, pr) = p_mk q pr := by
    intro q pr
    apply ep.injective
    rw [ep.apply_symm_apply]
    apply Prod.ext
    · have hu : (() : Unit) = e_unit.symm ⟨c₀, rfl⟩ := rfl
      change q =
        (MeasurableEquiv.piCongrLeft (fun _ : Unit => Fin 3 → ℝ) e_unit.symm
          (fun u : { c : P.Chord // c.1 = i } => p_mk q pr u.1)) ()
      conv_rhs => rw [hu]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
      dsimp only [p_mk]
      rw [dif_pos (rfl : c₀.1 = i)]
    · ext c μ
      change pr c μ = p_mk q pr c.1 μ
      rw [show p_mk q pr c.1 = pr c from dif_neg c.2]
  have hep_symm_c0 : ∀ (q : Fin 3 → ℝ) (pr : { c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ),
      ep.symm (q, pr) c₀ = q := by
    intro q pr
    rw [hep_symm_eq]
    exact dif_pos rfl
  have hep_symm_ne : ∀ (q : Fin 3 → ℝ) (pr : { c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ)
      (c : { c : P.Chord // ¬ c.1 = i }),
      ep.symm (q, pr) c.1 = pr c := by
    intro q pr c
    rw [hep_symm_eq]
    exact dif_neg c.2
  let Q_rest_fn : ({ c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ) → (Fin n → Fin 4 → ℝ) :=
    fun pr k => ∑ c : { c : P.Chord // ¬ c.1 = i },
      chordTwoPointMomentum P c.1 (massShellVec m (pr c)) k
  have h_not_adj_of_ne : ∀ c : { c : P.Chord // ¬ c.1 = i },
      c.1.1 ≠ i ∧ c.1.1 ≠ i' ∧ P.mate c.1.1 ≠ i ∧ P.mate c.1.1 ≠ i' := by
    intro c
    have hc1 : c.1.1 ≠ i := c.2
    have hc2 : c.1.1 ≠ i' := by
      intro h
      have hlt : i' < P.mate i' := h ▸ c.1.2
      have hm' : P.mate i' = i := by
        have h1 := congrArg P.mate h_eq
        rw [P.mate_mate] at h1
        exact h1.symm
      rw [hm', Fin.lt_def] at hlt
      dsimp [i'] at hlt
      omega
    have hm1 : P.mate c.1.1 ≠ i := by
      intro h
      have h1 := congrArg P.mate h
      rw [P.mate_mate, h_eq] at h1
      exact hc2 h1
    have hm2 : P.mate c.1.1 ≠ i' := fun h => hc1 (P.mate.injective (h.trans h_eq.symm))
    exact ⟨hc1, hc2, hm1, hm2⟩
  have hQ_i : ∀ pr, Q_rest_fn pr i = 0 := by
    intro pr
    dsimp [Q_rest_fn]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rcases h_not_adj_of_ne c with ⟨h1, _, h3, _⟩
    simp [chordTwoPointMomentum, h1.symm, h3.symm]
  have hQ_i' : ∀ pr, Q_rest_fn pr i' = 0 := by
    intro pr
    dsimp [Q_rest_fn]
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rcases h_not_adj_of_ne c with ⟨_, h2, _, h4⟩
    simp [chordTwoPointMomentum, h2.symm, h4.symm]
  have h_mom_split : ∀ (q : Fin 3 → ℝ) (pr : { c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ),
      P.momentum m (ep.symm (q, pr)) =
        adjEmbedMomentum i hi (massShellVec m q) + Q_rest_fn pr := by
    intro q pr
    rw [P.momentum_eq_sum]
    funext k
    rw [Finset.sum_apply, Pi.add_apply,
        ← Fintype.sum_subtype_add_sum_subtype (fun c : P.Chord => c.1 = i)]
    have h_left :
        (∑ c : { c : P.Chord // c.1 = i },
          chordTwoPointMomentum P c.1 (massShellVec m (ep.symm (q, pr) c.1)) k) =
        adjEmbedMomentum i hi (massShellVec m q) k := by
      rw [← e_unit.sum_comp, Fintype.sum_unique]
      change chordTwoPointMomentum P c₀ (massShellVec m (ep.symm (q, pr) c₀)) k = _
      rw [hep_symm_c0]
      dsimp only [chordTwoPointMomentum, adjEmbedMomentum]
      simp only [show c₀.1 = i from rfl, h_eq]
    have h_right :
        (∑ c : { c : P.Chord // ¬ c.1 = i },
          chordTwoPointMomentum P c.1 (massShellVec m (ep.symm (q, pr) c.1)) k) =
        Q_rest_fn pr k := by
      dsimp [Q_rest_fn]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [hep_symm_ne]
    rw [h_left, h_right]
  let W_rest : (Fin n → ι) → ({ c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ) → ℂ :=
    fun γ pr => ∏ c : { c : P.Chord // ¬ c.1 = i },
      massShellWeight m C ![γ c.1.1, γ (P.mate c.1.1)] (pr c)
  have hW_rest_swap : ∀ pr, W_rest (α ∘ s) pr = W_rest α pr := by
    intro pr
    dsimp [W_rest]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rcases h_not_adj_of_ne c with ⟨h1, h2, h3, h4⟩
    have hs1 : α (s c.1.1) = α c.1.1 :=
      congrArg α (Equiv.swap_apply_of_ne_of_ne h1 h2)
    have hs2 : α (s (P.mate c.1.1)) = α (P.mate c.1.1) :=
      congrArg α (Equiv.swap_apply_of_ne_of_ne h3 h4)
    rw [hs1, hs2]
  have hW_split : ∀ (γ : Fin n → ι) (q : Fin 3 → ℝ)
      (pr : { c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ),
      wickChordWeight m C P γ (ep.symm (q, pr)) =
        W_rest γ pr * massShellWeight m C ![γ i, γ i'] q := by
    intro γ q pr
    unfold wickChordWeight
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun c : P.Chord => c.1 = i)]
    have h_left :
        (∏ c : { c : P.Chord // c.1 = i },
          massShellWeight m C ![γ c.1.1, γ (P.mate c.1.1)] (ep.symm (q, pr) c.1)) =
        massShellWeight m C ![γ i, γ i'] q := by
      rw [← e_unit.prod_comp, Fintype.prod_unique]
      change massShellWeight m C ![γ c₀.1, γ (P.mate c₀.1)] (ep.symm (q, pr) c₀) = _
      rw [hep_symm_c0]
      dsimp [c₀]
      rw [h_eq]
    have h_right :
        (∏ c : { c : P.Chord // ¬ c.1 = i },
          massShellWeight m C ![γ c.1.1, γ (P.mate c.1.1)] (ep.symm (q, pr) c.1)) =
        W_rest γ pr := by
      dsimp [W_rest]
      refine Finset.prod_congr rfl (fun c _ => ?_)
      rw [hep_symm_ne]
    rw [h_left, h_right, mul_comm]
  have hint_lhs : Integrable
      (fun qp : (Fin 3 → ℝ) × ({ c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ) =>
        wickChordWeight m C P α (ep.symm qp) *
          minkowskiFourier f (P.momentum m (ep.symm qp)))
      (volume.prod volume) :=
    hmp.symm.integrable_comp_of_integrable
      (integrable_wickChordWeight_mul_minkowskiFourier hC P α f)
  have hint_rhs : Integrable
      (fun qp : (Fin 3 → ℝ) × ({ c : P.Chord // ¬ c.1 = i } → Fin 3 → ℝ) =>
        wickChordWeight m C P (α ∘ s) (ep.symm qp) *
          minkowskiFourier f' (P.momentum m (ep.symm qp)))
      (volume.prod volume) :=
    hmp.symm.integrable_comp_of_integrable
      (integrable_wickChordWeight_mul_minkowskiFourier hC P (α ∘ s) f')
  rw [← hmp.symm.integral_comp', MeasureTheory.integral_prod_symm _ hint_lhs,
      ← hmp.symm.integral_comp', MeasureTheory.integral_prod_symm _ hint_rhs,
      ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun pr => ?_))
  dsimp only [Function.comp_apply]
  have h_lhs_pr :
      (∫ q : Fin 3 → ℝ, wickChordWeight m C P α (ep.symm (q, pr)) *
        minkowskiFourier f (P.momentum m (ep.symm (q, pr)))) =
      W_rest α pr * ∫ q : Fin 3 → ℝ, massShellWeight m C ![α i, α i'] q *
        minkowskiFourier f (adjEmbedMomentum i hi (massShellVec m q) + Q_rest_fn pr) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    dsimp only
    rw [hW_split α q pr, h_mom_split q pr, mul_assoc]
  have hα_rev : ![(α ∘ s) i, (α ∘ s) i'] = ![α i, α i'] ∘ Fin.rev := by
    ext b
    fin_cases b
    · change α (Equiv.swap i i' i) = α i'
      rw [Equiv.swap_apply_left]
    · change α (Equiv.swap i i' i') = α i
      rw [Equiv.swap_apply_right]
  have h_rhs_pr :
      (∫ q : Fin 3 → ℝ, wickChordWeight m C P (α ∘ s) (ep.symm (q, pr)) *
        minkowskiFourier f' (P.momentum m (ep.symm (q, pr)))) =
      W_rest α pr * ∫ q : Fin 3 → ℝ, massShellWeight m C (![α i, α i'] ∘ Fin.rev) q *
        minkowskiFourier f' (adjEmbedMomentum i hi (massShellVec m q) + Q_rest_fn pr) := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
    dsimp only
    rw [hW_split (α ∘ s) q pr, hW_rest_swap pr, hα_rev, h_mom_split q pr, mul_assoc]
  rw [h_lhs_pr, h_rhs_pr,
      adjacentTwoPoint_massShell_swap R hm hC hC_cov hC_pct i hi ![α i, α i']
        (hQ_i pr) (hQ_i' pr) f f' hf hf']
  ring

theorem wickMassShellLocalCommutativity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    LocalCommutativity η (wickMassShellW m η C hC) := by
  intro n i hi α f f' hf hf'
  let s : Equiv.Perm (Fin n) := Equiv.swap i ⟨i.val + 1, hi⟩
  rw [wickMassShellW_apply, wickMassShellW_apply,
      ← (ChordPairing.conjSwapEquiv i hi).sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  have hQ : ChordPairing.conjSwapEquiv i hi P = P.conjSwap i hi := rfl
  rw [hQ]
  by_cases h_eq : P.mate i = ⟨i.val + 1, hi⟩
  · rw [P.conjSwap_eq_self_of_mate_eq i hi h_eq,
        wickChord_integral_of_mate_eq R hm hC hC_cov hC_pct P i hi h_eq α f f' hf hf']
    ring
  · rw [wickChord_integral_conjSwap_of_mate_ne m C P i hi h_eq α f f' hf',
        P.eta_pow_cross_conjSwap hη i hi h_eq, mul_assoc]

theorem wickMassShellPermSpacelikeLocality {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    PermSpacelikeLocality η (wickMassShellW m η C hC) :=
  PermSpacelikeLocality.of_localCommutativity
    (wickMassShellLocalCommutativity R hm hη hC hC_cov hC_pct)

def pairProjRealCLM {n : ℕ} (u v : Fin n) :
    (Fin n → Fin 4 → ℝ) →L[ℝ] (Fin 2 → Fin 4 → ℝ) :=
  ContinuousLinearMap.pi
    ![ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin 4 → ℝ) u,
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin 4 → ℝ) v]

@[simp]
lemma pairProjRealCLM_apply {n : ℕ} (u v : Fin n) (x : Fin n → Fin 4 → ℝ) :
    pairProjRealCLM u v x = ![x u, x v] := by
  ext b μ
  fin_cases b <;> rfl

lemma pair_mem_nonCoincidentEuclidN_two {n : ℕ} {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ nonCoincidentEuclidN n) {u v : Fin n} (huv : u ≠ v) :
    ![x u, x v] ∈ nonCoincidentEuclidN 2 := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · exact hx u v huv
  · exact hx v u huv.symm
  · exact False.elim (hab rfl)

noncomputable def wickMassShellFullS {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    SchwingerFamily ι :=
  fun n α x =>
    wickPairingSum η
      (fun p q : ι × (Fin 4 → ℝ) =>
        twoPointFullEuclidS R (massShellTwoPointW m C hC)
          (massShellTwoPointTubeExtension m hm C hC) ![p.1, q.1] ![p.2, q.2])
      n (fun r => (α r, x r))

theorem wickMassShellFullS_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    wickMassShellFullS R m hm η C hC n α x =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∏ c : P.Chord,
          twoPointFullEuclidS R (massShellTwoPointW m C hC)
            (massShellTwoPointTubeExtension m hm C hC)
            ![α c.1, α (P.mate c.1)] ![x c.1, x (P.mate c.1)] := rfl

theorem wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (n : ℕ) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    wickMassShellFullS R m hm η C hC n α x = wickMassShellS m hm η C hC n α x := by
  rw [wickMassShellFullS_apply, wickMassShellS_apply]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have hx_pair : ![x c.1, x (P.mate c.1)] ∈ orderedEuclidN 2 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    change x c.1 0 < x (P.mate c.1) 0
    exact orderedEuclidN_lt_time hx c.2
  exact twoPointFullEuclidS_eq_schwingerFromTube_on_orderedEuclidN R
    (massShellTwoPointW m C hC) (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubeCovariant R hm hC hC_cov)
    ![α c.1, α (P.mate c.1)] hx_pair

@[simp]
theorem wickMassShellFullS_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ) :
    wickMassShellFullS R m hm η C hC 0 α x = 1 := by
  rw [wickMassShellFullS_apply, Fintype.sum_unique]
  haveI : IsEmpty (default : ChordPairing 0).Chord := ⟨fun c => Fin.elim0 c.1⟩
  have hcross : (default : ChordPairing 0).cross = 0 := rfl
  simp [hcross]

@[simp]
theorem wickMassShellFullS_vacuumNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    OSVacuumNormalized (wickMassShellFullS R m hm η C hC) :=
  wickMassShellFullS_zero R m hm η C hC Fin.elim0 0

theorem wickMassShellFullS_eq_zero_of_odd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    {n : ℕ} (hn : Odd n) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    wickMassShellFullS R m hm η C hC n α x = 0 := by
  rw [wickMassShellFullS_apply]
  haveI := ChordPairing.isEmpty_of_odd hn
  simp

theorem wickMassShellFullS_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (m : ℝ) (hm : 0 < m) (η : ℂ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C)
    (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ) :
    wickMassShellFullS R m hm η C hC 2 α x =
      twoPointFullEuclidS R (massShellTwoPointW m C hC)
        (massShellTwoPointTubeExtension m hm C hC) α x := by
  rw [wickMassShellFullS_apply, Fintype.sum_unique]
  change η ^ ChordPairing.twoPairing.cross *
    (∏ c ∈ (Finset.univ : Finset ChordPairing.twoPairing.Chord),
      twoPointFullEuclidS R (massShellTwoPointW m C hC)
        (massShellTwoPointTubeExtension m hm C hC)
        ![α c.1, α (ChordPairing.twoPairing.mate c.1)]
        ![x c.1, x (ChordPairing.twoPairing.mate c.1)]) = _
  rw [ChordPairing.cross_two, pow_zero, one_mul, ChordPairing.unique_twoPairing_chord,
      Finset.prod_singleton]
  change twoPointFullEuclidS R (massShellTwoPointW m C hC)
      (massShellTwoPointTubeExtension m hm C hC) ![α 0, α 1] ![x 0, x 1] = _
  rw [(finTwo_eq_vecCons α).symm, (finTwo_eq_vecCons x).symm]

theorem wickMassShellFullS_contDiffOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (n : ℕ) (α : Fin n → ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (wickMassShellFullS R m hm η C hC n α) (nonCoincidentEuclidN n) := by
  have h_cov2 := massShellTwoPointTubeCovariant R hm hC hC_cov
  have h_fn :
      wickMassShellFullS R m hm η C hC n α =
        fun x => ∑ P : ChordPairing n, η ^ P.cross *
          ∏ c : P.Chord,
            twoPointFullEuclidS R (massShellTwoPointW m C hC)
              (massShellTwoPointTubeExtension m hm C hC)
              ![α c.1, α (P.mate c.1)] (pairProjRealCLM c.1 (P.mate c.1) x) := by
    ext x
    simp [wickMassShellFullS_apply]
  rw [h_fn]
  refine ContDiffOn.sum (fun P _ => contDiffOn_const.mul ?_)
  refine contDiffOn_prod (fun c _ => ?_)
  have h_maps : Set.MapsTo (pairProjRealCLM c.1 (P.mate c.1))
      (nonCoincidentEuclidN n) (nonCoincidentEuclidN 2) := by
    intro x hx
    rw [pairProjRealCLM_apply]
    exact pair_mem_nonCoincidentEuclidN_two hx (ne_of_lt c.2)
  exact (twoPointFullEuclidS_contDiffOn R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC) h_cov2
    ![α c.1, α (P.mate c.1)]).comp
      (pairProjRealCLM c.1 (P.mate c.1)).contDiff.contDiffOn h_maps

theorem wickMassShellFullS_translation_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    FullEuclidTranslationInvariant (wickMassShellFullS R m hm η C hC) := by
  intro n α x hx a
  rw [wickMassShellFullS_apply, wickMassShellFullS_apply]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_pair : ![x c.1 + a, x (P.mate c.1) + a] =
      fun k : Fin 2 => ![x c.1, x (P.mate c.1)] k + a := by
    ext k μ
    fin_cases k <;> rfl
  rw [h_pair]
  exact twoPointFullEuclidS_translation_invariant R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC)
    (massShellTwoPointTubeCovariant R hm hC hC_cov)
    (massShellTwoPointTubeTranslationInvariant hm hC)
    ![α c.1, α (P.mate c.1)]
    (pair_mem_nonCoincidentEuclidN_two hx (ne_of_lt c.2)) a

theorem wickMassShellFullS_rotCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    FullEuclidRotCovariant R (wickMassShellFullS R m hm η C hC) := by
  intro n A B α x _hx
  let S₂ := twoPointFullEuclidS R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC)
  have h_cov2 := massShellTwoPointTubeCovariant R hm hC hC_cov
  change (∑ P : ChordPairing n, η ^ P.cross *
      ∏ c : P.Chord,
        S₂ ![α c.1, α (P.mate c.1)]
          ![(euclidRotN n A B x) c.1, (euclidRotN n A B x) (P.mate c.1)]) =
    ∑ β : Fin n → ι,
      (∏ i : Fin n, R.σ (su2ToSL2C A, su2ToSL2C B) (α i) (β i)) *
        ∑ P : ChordPairing n, η ^ P.cross *
          ∏ c : P.Chord, S₂ ![β c.1, β (P.mate c.1)] ![x c.1, x (P.mate c.1)]
  have h_rhs_swap :
      (∑ β : Fin n → ι,
        (∏ i : Fin n, R.σ (su2ToSL2C A, su2ToSL2C B) (α i) (β i)) *
          ∑ P : ChordPairing n, η ^ P.cross *
            ∏ c : P.Chord, S₂ ![β c.1, β (P.mate c.1)] ![x c.1, x (P.mate c.1)]) =
      ∑ P : ChordPairing n, η ^ P.cross *
        ∑ β : Fin n → ι,
          (∏ i : Fin n, R.σ (su2ToSL2C A, su2ToSL2C B) (α i) (β i)) *
            ∏ c : P.Chord, S₂ ![β c.1, β (P.mate c.1)] ![x c.1, x (P.mate c.1)] := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    exact Finset.sum_congr rfl (fun β _ => by ring)
  rw [h_rhs_swap]
  refine Finset.sum_congr rfl (fun P _ => congrArg (η ^ P.cross * ·) ?_)
  rw [P.sum_prod_chord_factor (fun i b => R.σ (su2ToSL2C A, su2ToSL2C B) (α i) b)
    (fun c γ => S₂ γ ![x c.1, x (P.mate c.1)])]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  have h_rot_pair :
      ![(euclidRotN n A B x) c.1, (euclidRotN n A B x) (P.mate c.1)] =
        euclidRotN 2 A B ![x c.1, x (P.mate c.1)] := by
    ext k μ
    fin_cases k <;> rfl
  rw [h_rot_pair]
  refine (twoPointFullEuclidS_euclidRotN R (massShellTwoPointW m C hC)
    (massShellTwoPointTubeExtension m hm C hC) h_cov2 A B
    ![α c.1, α (P.mate c.1)] ![x c.1, x (P.mate c.1)]).trans ?_
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  rfl

theorem wickMassShellFullS_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSPermutationSymmetry η (wickMassShellFullS R m hm η C hC) := by
  intro n π α x hx
  unfold wickMassShellFullS
  have h_comp :
      (fun r : Fin n => ((α ∘ π) r, (x ∘ π) r)) =
        (fun r : Fin n => (α r, x r)) ∘ π := rfl
  rw [h_comp]
  exact wickPairingSum_perm hη
    (fun p q : ι × (Fin 4 → ℝ) =>
      twoPointFullEuclidS R (massShellTwoPointW m C hC)
        (massShellTwoPointTubeExtension m hm C hC) ![p.1, q.1] ![p.2, q.2])
    (fun r => (α r, x r))
    (fun r t hrt =>
      twoPointFullEuclidS_pair_swap R (massShellTwoPointW m C hC)
        (massShellTwoPointTubeExtension m hm C hC)
        (massShellTwoPointTubeCovariant R hm hC hC_cov)
        (massShellTwoPointTubePCT R hm hC hC_pct)
        (α r) (α t) (hx r t hrt))
    π

def equalTimeTwoPoint (r : ℝ) : Fin 2 → Fin 4 → ℝ :=
  ![0, ![0, r, 0, 0]]

lemma equalTimeTwoPoint_mem_nonCoincidentEuclidN {r : ℝ} (hr : r ≠ 0) :
    equalTimeTwoPoint r ∈ nonCoincidentEuclidN 2 := by
  intro a b hab heq
  fin_cases a <;> fin_cases b
  · exact hab rfl
  · have h1 := congrFun heq 1
    dsimp [equalTimeTwoPoint] at h1
    exact hr h1.symm
  · have h1 := congrFun heq 1
    dsimp [equalTimeTwoPoint] at h1
    exact hr h1
  · exact hab rfl

lemma equalTimeTwoPoint_not_mem_orderedEuclidN (r : ℝ) :
    equalTimeTwoPoint r ∉ orderedEuclidN 2 := by
  intro hord
  have h01 := hord 0 (by decide)
  dsimp [equalTimeTwoPoint] at h01
  exact lt_irrefl 0 h01

lemma euclidRotN_alignPosTime_equalTimeTwoPoint {r : ℝ} (hr : 0 < r) :
    euclidRotN 2 (alignPosTimeSU2 ![0, r, 0, 0]) 1 (equalTimeTwoPoint r) =
      ![0, ![r, 0, 0, 0]] := by
  have h_norm : Real.sqrt (euclidInner ![0, r, 0, 0] ![0, r, 0, 0]) = r := by
    have h_in : euclidInner ![0, r, 0, 0] ![0, r, 0, 0] = r ^ 2 := by
      simp [euclidInner_explicit]
      ring
    rw [h_in, Real.sqrt_sq hr.le]
  have h1 := euclidRotApply_alignPosTimeSU2 ![0, r, 0, 0]
  rw [h_norm] at h1
  ext b μ
  fin_cases b
  · change ((euclidRotOfSU2 (alignPosTimeSU2 ![0, r, 0, 0]) 1).mulVec (0 : Fin 4 → ℝ)) μ = 0
    simp
  · change ((euclidRotOfSU2 (alignPosTimeSU2 ![0, r, 0, 0]) 1).mulVec ![0, r, 0, 0]) μ =
      (![r, 0, 0, 0] : Fin 4 → ℝ) μ
    rw [euclidRotOfSU2_mulVec, h1]

lemma posTimeTwoPoint_mem_orderedEuclidN {r : ℝ} (hr : 0 < r) :
    (![(0 : Fin 4 → ℝ), ![r, 0, 0, 0]] : Fin 2 → Fin 4 → ℝ) ∈ orderedEuclidN 2 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simpa using hr

theorem massShellTwoPointS_posTime_re_pos_and_ne_zero {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (α : Fin 2 → κ) {f_pos : (Fin 3 → ℝ) → ℝ}
    (hf_cont : Continuous f_pos) (hf_pos : ∀ p : Fin 3 → ℝ, 0 < f_pos p)
    (hf_eq : ∀ p : Fin 3 → ℝ, C α (massShellVec m p) = (f_pos p : ℂ))
    {r : ℝ} (hr : 0 < r) :
    0 < (massShellTwoPointS m hm C hC 2 α ![0, ![r, 0, 0, 0]]).re ∧
      massShellTwoPointS m hm C hC 2 α ![0, ![r, 0, 0, 0]] ≠ 0 := by
  let y : Fin 2 → Fin 4 → ℝ := ![0, ![r, 0, 0, 0]]
  have hy_ord : y ∈ orderedEuclidN 2 := posTimeTwoPoint_mem_orderedEuclidN hr
  have hz_ft : wickEmbedN 2 y ∈ forward_tube_n 2 := wickEmbedN_mem_forward_tube_n 2 hy_ord
  let F_real : (Fin 3 → ℝ) → ℝ := fun p =>
    (2 * massShellEnergy m p)⁻¹ * f_pos p * Real.exp (-(r * massShellEnergy m p))
  have h_ker : ∀ p : Fin 3 → ℝ,
      vladimirov_kernel 2 (wickEmbedN 2 y) (twoPointMomentum (massShellVec m p)) =
        ((Real.exp (-(r * massShellEnergy m p)) : ℝ) : ℂ) := by
    intro p
    unfold vladimirov_kernel
    rw [Complex.ofReal_exp]
    congr 1
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, y, wickEmbedN, wickEmbed, twoPointMomentum_zero, twoPointMomentum_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons,
      Pi.zero_apply, Pi.neg_apply, Complex.ofReal_zero, Complex.ofReal_neg, zero_mul, ↓reduceIte,
      Fin.reduceEq, minkowskiInnerC, massShellVec]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have h_integrand : ∀ p : Fin 3 → ℝ,
      massShellWeight m C α p *
        vladimirov_kernel 2 (wickEmbedN 2 y) (twoPointMomentum (massShellVec m p)) =
      ((F_real p : ℝ) : ℂ) := by
    intro p
    dsimp [massShellWeight, F_real]
    rw [hf_eq p, h_ker p]
    push_cast
    ring
  have hF_cont : Continuous F_real := by
    dsimp [F_real]
    have h_inv_cont : Continuous (fun p : Fin 3 → ℝ => (2 * massShellEnergy m p)⁻¹) :=
      (continuous_const.mul (continuous_massShellEnergy m)).inv₀
        (fun p => (mul_pos zero_lt_two (massShellEnergy_pos hm p)).ne')
    exact (h_inv_cont.mul hf_cont).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_massShellEnergy m)).neg)
  have hF_int : Integrable F_real volume := by
    have h_re := Complex.reCLM.integrable_comp
      (integrable_massShellWeight_mul_kernel hm hC α hz_ft)
    refine h_re.congr (Filter.Eventually.of_forall (fun p => ?_))
    change (massShellWeight m C α p *
      vladimirov_kernel 2 (wickEmbedN 2 y) (twoPointMomentum (massShellVec m p))).re = F_real p
    rw [h_integrand p, Complex.ofReal_re]
  have hF_nn : 0 ≤ F_real := by
    intro p
    dsimp [F_real]
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm p)).le)
        (hf_pos p).le)
      (Real.exp_pos _).le
  have hF_0_ne : F_real 0 ≠ 0 := by
    dsimp [F_real]
    exact (mul_pos
      (mul_pos (inv_pos.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm 0))) (hf_pos 0))
      (Real.exp_pos _)).ne'
  have h_pos : 0 < ∫ p : Fin 3 → ℝ, F_real p :=
    MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hF_cont hF_int hF_nn hF_0_ne
  have hS_eq :
      massShellTwoPointS m hm C hC 2 α y = ((∫ p : Fin 3 → ℝ, F_real p : ℝ) : ℂ) := by
    change massShellTwoPointH m C 2 α (wickEmbedN 2 y) = _
    rw [massShellTwoPointH_two]
    have h_fn :
        (fun p : Fin 3 → ℝ =>
          massShellWeight m C α p *
            vladimirov_kernel 2 (wickEmbedN 2 y) (twoPointMomentum (massShellVec m p))) =
        fun p => ((F_real p : ℝ) : ℂ) := funext h_integrand
    rw [h_fn, integral_complex_ofReal]
  rw [hS_eq, Complex.ofReal_re]
  exact ⟨h_pos, Complex.ofReal_ne_zero.mpr h_pos.ne'⟩

noncomputable def freeKGW (m : ℝ) (hm : 0 < m) : WightmanFamily Unit :=
  wickMassShellW m 1 massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def freeKGTubeExtension (m : ℝ) (hm : 0 < m) :
    TubeExtension (freeKGW m hm) :=
  wickMassShellTubeExtension m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def freeKGS (m : ℝ) (hm : 0 < m) : SchwingerFamily Unit :=
  wickMassShellS m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

theorem freeKG_forwardConeSpectrumCondition {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (freeKGW m hm) :=
  wickMassShell_forwardConeSpectrumCondition hm 1 (massiveKGCoeff_data hm)

theorem freeKGW_twoPoint_ne_zero {m : ℝ} (hm : 0 < m) :
    freeKGW m hm 2 default ≠ 0 :=
  (wickMassShell_nondeg_and_not_zeroMomentum hm 1 (massiveKGCoeff_data hm) default
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm)).1

theorem not_zeroMomentumSpectrumCondition_freeKGW {m : ℝ} (hm : 0 < m) :
    ¬ ZeroMomentumSpectrumCondition (freeKGW m hm) :=
  (wickMassShell_nondeg_and_not_zeroMomentum hm 1 (massiveKGCoeff_data hm) default
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm)).2

theorem freeKGTubeTranslationInvariant {m : ℝ} (hm : 0 < m) :
    TubeTranslationInvariant (freeKGTubeExtension m hm) :=
  wickMassShellTubeTranslationInvariant hm 1 (massiveKGCoeff_data hm)

theorem freeKGOSTranslationInvariant {m : ℝ} (hm : 0 < m) :
    OSTranslationInvariant (freeKGS m hm) :=
  wickMassShellOSTranslationInvariant hm 1 (massiveKGCoeff_data hm)

theorem freeKGTubeCovariant {m : ℝ} (hm : 0 < m) :
    TubeCovariant trivialRep (freeKGTubeExtension m hm) :=
  wickMassShellTubeCovariant trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGPoincareCovariant {m : ℝ} (hm : 0 < m) :
    PoincareCovariant trivialRep (freeKGW m hm) :=
  wickMassShellPoincareCovariant trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGTubeWickHermiticity {m : ℝ} (hm : 0 < m) :
    TubeWickHermiticity trivialStarStructure (freeKGTubeExtension m hm) :=
  wickMassShellTubeWickHermiticity trivialStarStructure hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGOSHermiticity {m : ℝ} (hm : 0 < m) :
    OSHermiticity trivialStarStructure (freeKGS m hm) :=
  wickMassShellOSHermiticity trivialStarStructure hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGTubePCT {m : ℝ} (hm : 0 < m) :
    TubePCT 1 trivialRep (freeKGTubeExtension m hm) :=
  wickMassShellTubePCT trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKGWightmanPCT {m : ℝ} (hm : 0 < m) :
    WightmanPCT 1 trivialRep (freeKGW m hm) :=
  wickMassShellWightmanPCT trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKGWeakLocality {m : ℝ} (hm : 0 < m) :
    WeakLocality 1 (freeKGW m hm) :=
  wickMassShellWeakLocality trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKG_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hloc : WeakLocality η (freeKGW m hm)) :
    η = 1 :=
  spin_statistics_of_tubePCT_and_weakLocality trivialRep (freeKGW m hm)
    (freeKGTubeExtension m hm) (freeKGTubeCovariant hm) (freeKGTubePCT hm)
    hloc ⟨default, freeKGW_twoPoint_ne_zero hm⟩

theorem freeKG_localCommutativity {m : ℝ} (hm : 0 < m) :
    LocalCommutativity 1 (freeKGW m hm) :=
  wickMassShellLocalCommutativity trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKG_permSpacelikeLocality {m : ℝ} (hm : 0 < m) :
    PermSpacelikeLocality 1 (freeKGW m hm) :=
  PermSpacelikeLocality.of_localCommutativity (freeKG_localCommutativity hm)

noncomputable def freeKGFullS (m : ℝ) (hm : 0 < m) : SchwingerFamily Unit :=
  wickMassShellFullS trivialRep m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

theorem freeKGFullS_eq_freeKGS_on_orderedEuclidN {m : ℝ} (hm : 0 < m)
    (n : ℕ) (α : Fin n → Unit) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    freeKGFullS m hm n α x = freeKGS m hm n α x :=
  wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN trivialRep hm 1
    (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    n α hx

@[simp]
theorem freeKGFullS_vacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (freeKGFullS m hm) :=
  wickMassShellFullS_vacuumNormalized trivialRep m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

theorem freeKGFullS_contDiffOn {m : ℝ} (hm : 0 < m) (n : ℕ) (α : Fin n → Unit) :
    ContDiffOn ℝ (⊤ : ℕ∞) (freeKGFullS m hm n α) (nonCoincidentEuclidN n) :=
  wickMassShellFullS_contDiffOn trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply]) n α

theorem freeKGFullS_translation_invariant {m : ℝ} (hm : 0 < m) :
    FullEuclidTranslationInvariant (freeKGFullS m hm) :=
  wickMassShellFullS_translation_invariant trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGFullS_rotCovariant {m : ℝ} (hm : 0 < m) :
    FullEuclidRotCovariant trivialRep (freeKGFullS m hm) :=
  wickMassShellFullS_rotCovariant trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGFullS_permutation {m : ℝ} (hm : 0 < m) :
    OSPermutationSymmetry 1 (freeKGFullS m hm) :=
  wickMassShellFullS_permutation trivialRep hm (Or.inl rfl) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKGFullS_equalTime_re_pos_and_ne_zero {m : ℝ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    0 < (freeKGFullS m hm 2 default (equalTimeTwoPoint r)).re ∧
      freeKGFullS m hm 2 default (equalTimeTwoPoint r) ≠ 0 := by
  let U := alignPosTimeSU2 ![0, r, 0, 0]
  have hx_nc : equalTimeTwoPoint r ∈ nonCoincidentEuclidN 2 :=
    equalTimeTwoPoint_mem_nonCoincidentEuclidN hr.ne'
  have h_def : (default : Fin 2 → Unit) = fun _ => () := Subsingleton.elim _ _
  rw [h_def]
  have hrot := freeKGFullS_rotCovariant hm 2 U 1 (fun _ => ()) (equalTimeTwoPoint r) hx_nc
  rw [euclidRotN_alignPosTime_equalTimeTwoPoint hr, Fintype.sum_unique] at hrot
  have h_prod :
      (∏ i : Fin 2,
        trivialRep.σ (su2ToSL2C U, su2ToSL2C 1) ((fun _ : Fin 2 => ()) i)
          ((default : Fin 2 → Unit) i)) = 1 := by
    simp [trivialRep]
  change freeKGFullS m hm 2 (fun _ => ()) ![0, ![r, 0, 0, 0]] =
    (∏ i : Fin 2,
      trivialRep.σ (su2ToSL2C U, su2ToSL2C 1) ((fun _ : Fin 2 => ()) i)
        ((default : Fin 2 → Unit) i)) *
      freeKGFullS m hm 2 default (equalTimeTwoPoint r) at hrot
  rw [h_prod, one_mul, h_def] at hrot
  rw [← hrot,
      freeKGFullS_eq_freeKGS_on_orderedEuclidN hm 2 _ (posTimeTwoPoint_mem_orderedEuclidN hr)]
  have h_two : freeKGS m hm 2 (fun _ => ()) ![0, ![r, 0, 0, 0]] =
      massShellTwoPointS m hm massiveKGCoeff (massiveKGCoeff_data hm) 2
        (fun _ => ()) ![0, ![r, 0, 0, 0]] := by
    change wickMassShellH m 1 massiveKGCoeff 2 (fun _ => ()) (wickEmbedN 2 ![0, ![r, 0, 0, 0]]) = _
    rw [wickMassShellH_two]
    rfl
  rw [h_two]
  exact massShellTwoPointS_posTime_re_pos_and_ne_zero hm (massiveKGCoeff_data hm) (fun _ => ())
    continuous_const (fun _ => zero_lt_one) (fun _ => Complex.ofReal_one.symm) hr

theorem freeKGFullS_equalTime_ne_zero {m : ℝ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    freeKGFullS m hm 2 default (equalTimeTwoPoint r) ≠ 0 :=
  (freeKGFullS_equalTime_re_pos_and_ne_zero hm hr).2

noncomputable def freeDiracW (m : ℝ) (hm : 0 < m) :
    WightmanFamily (Fin 2 ⊕ Fin 2) :=
  wickMassShellW m (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

noncomputable def freeDiracTubeExtension (m : ℝ) (hm : 0 < m) :
    TubeExtension (freeDiracW m hm) :=
  wickMassShellTubeExtension m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

noncomputable def freeDiracS (m : ℝ) (hm : 0 < m) :
    SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  wickMassShellS m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem freeDirac_forwardConeSpectrumCondition {m : ℝ} (hm : 0 < m) :
    ForwardConeSpectrumCondition (freeDiracW m hm) :=
  wickMassShell_forwardConeSpectrumCondition hm (-1) (diracMassShellCoeff_data hm)

theorem freeDiracW_twoPoint_inl_inr_zero_ne_zero {m : ℝ} (hm : 0 < m) :
    freeDiracW m hm 2 ![Sum.inl 0, Sum.inr 0] ≠ 0 := by
  refine (wickMassShell_nondeg_and_not_zeroMomentum hm (-1)
    (diracMassShellCoeff_data hm) ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_)).1
  simp [diracMassShellCoeff, massShellVec]

theorem freeDiracW_twoPoint_nondegenerate {m : ℝ} (hm : 0 < m) :
    ∃ β : Fin 2 → Fin 2 ⊕ Fin 2, freeDiracW m hm 2 β ≠ 0 :=
  ⟨![Sum.inl 0, Sum.inr 0], freeDiracW_twoPoint_inl_inr_zero_ne_zero hm⟩

theorem not_zeroMomentumSpectrumCondition_freeDiracW {m : ℝ} (hm : 0 < m) :
    ¬ ZeroMomentumSpectrumCondition (freeDiracW m hm) := by
  refine (wickMassShell_nondeg_and_not_zeroMomentum hm (-1)
    (diracMassShellCoeff_data hm) ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_)).2
  simp [diracMassShellCoeff, massShellVec]

theorem freeDiracTubeTranslationInvariant {m : ℝ} (hm : 0 < m) :
    TubeTranslationInvariant (freeDiracTubeExtension m hm) :=
  wickMassShellTubeTranslationInvariant hm (-1) (diracMassShellCoeff_data hm)

theorem freeDiracOSTranslationInvariant {m : ℝ} (hm : 0 < m) :
    OSTranslationInvariant (freeDiracS m hm) :=
  wickMassShellOSTranslationInvariant hm (-1) (diracMassShellCoeff_data hm)

theorem freeDiracTubeCovariant {m : ℝ} (hm : 0 < m) :
    TubeCovariant diracRep (freeDiracTubeExtension m hm) :=
  wickMassShellTubeCovariant diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem freeDiracPoincareCovariant {m : ℝ} (hm : 0 < m) :
    PoincareCovariant diracRep (freeDiracW m hm) :=
  wickMassShellPoincareCovariant diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem freeDiracTubeWickHermiticity {m : ℝ} (hm : 0 < m) :
    TubeWickHermiticity diracStarStructure (freeDiracTubeExtension m hm) :=
  wickMassShellTubeWickHermiticity diracStarStructure hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_herm m)

theorem freeDiracOSHermiticity {m : ℝ} (hm : 0 < m) :
    OSHermiticity diracStarStructure (freeDiracS m hm) :=
  wickMassShellOSHermiticity diracStarStructure hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_herm m)

theorem freeDiracTubePCT {m : ℝ} (hm : 0 < m) :
    TubePCT (-1) diracRep (freeDiracTubeExtension m hm) :=
  wickMassShellTubePCT diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_pct m)

theorem freeDiracWightmanPCT {m : ℝ} (hm : 0 < m) :
    WightmanPCT (-1) diracRep (freeDiracW m hm) :=
  wickMassShellWightmanPCT diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_pct m)

theorem freeDiracWeakLocality {m : ℝ} (hm : 0 < m) :
    WeakLocality (-1) (freeDiracW m hm) :=
  wickMassShellWeakLocality diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_pct m)

theorem freeDirac_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hloc : WeakLocality η (freeDiracW m hm)) :
    η = -1 :=
  spin_statistics_of_tubePCT_and_weakLocality diracRep (freeDiracW m hm)
    (freeDiracTubeExtension m hm) (freeDiracTubeCovariant hm) (freeDiracTubePCT hm)
    hloc (freeDiracW_twoPoint_nondegenerate hm)

theorem freeDirac_localCommutativity {m : ℝ} (hm : 0 < m) :
    LocalCommutativity (-1) (freeDiracW m hm) :=
  wickMassShellLocalCommutativity diracRep hm (Or.inr rfl) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_pct m)

theorem freeDirac_permSpacelikeLocality {m : ℝ} (hm : 0 < m) :
    PermSpacelikeLocality (-1) (freeDiracW m hm) :=
  PermSpacelikeLocality.of_localCommutativity (freeDirac_localCommutativity hm)

noncomputable def freeDiracFullS (m : ℝ) (hm : 0 < m) :
    SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  wickMassShellFullS diracRep m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem freeDiracFullS_eq_freeDiracS_on_orderedEuclidN {m : ℝ} (hm : 0 < m)
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    freeDiracFullS m hm n α x = freeDiracS m hm n α x :=
  wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN diracRep hm (-1)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m) n α hx

@[simp]
theorem freeDiracFullS_vacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (freeDiracFullS m hm) :=
  wickMassShellFullS_vacuumNormalized diracRep m hm (-1)
    (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem freeDiracFullS_contDiffOn {m : ℝ} (hm : 0 < m) (n : ℕ)
    (α : Fin n → Fin 2 ⊕ Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (freeDiracFullS m hm n α) (nonCoincidentEuclidN n) :=
  wickMassShellFullS_contDiffOn diracRep hm (-1)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m) n α

theorem freeDiracFullS_translation_invariant {m : ℝ} (hm : 0 < m) :
    FullEuclidTranslationInvariant (freeDiracFullS m hm) :=
  wickMassShellFullS_translation_invariant diracRep hm (-1)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m)

theorem freeDiracFullS_rotCovariant {m : ℝ} (hm : 0 < m) :
    FullEuclidRotCovariant diracRep (freeDiracFullS m hm) :=
  wickMassShellFullS_rotCovariant diracRep hm (-1)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m)

theorem freeDiracFullS_permutation {m : ℝ} (hm : 0 < m) :
    OSPermutationSymmetry (-1) (freeDiracFullS m hm) :=
  wickMassShellFullS_permutation diracRep hm (Or.inr rfl)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_pct m)

theorem freeDiracFullS_posTime_inl_inr_zero_ne_zero {m : ℝ} (hm : 0 < m)
    {r : ℝ} (hr : 0 < r) :
    freeDiracFullS m hm 2 ![Sum.inl 0, Sum.inr 0] ![0, ![r, 0, 0, 0]] ≠ 0 := by
  rw [freeDiracFullS_eq_freeDiracS_on_orderedEuclidN hm 2 _
    (posTimeTwoPoint_mem_orderedEuclidN hr)]
  have h_two :
      freeDiracS m hm 2 ![Sum.inl 0, Sum.inr 0] ![0, ![r, 0, 0, 0]] =
        massShellTwoPointS m hm (diracMassShellCoeff m) (diracMassShellCoeff_data hm) 2
          ![Sum.inl 0, Sum.inr 0] ![0, ![r, 0, 0, 0]] := by
    change wickMassShellH m (-1) (diracMassShellCoeff m) 2 ![Sum.inl 0, Sum.inr 0]
      (wickEmbedN 2 ![0, ![r, 0, 0, 0]]) = _
    rw [wickMassShellH_two]
    rfl
  rw [h_two]
  refine (massShellTwoPointS_posTime_re_pos_and_ne_zero hm (diracMassShellCoeff_data hm)
    ![Sum.inl 0, Sum.inr 0]
    ((continuous_massShellEnergy m).add (continuous_apply 2))
    (massShellEnergy_add_third_pos hm) (fun p => ?_) hr).2
  simp [diracMassShellCoeff, massShellVec]

theorem freeDiracFullS_equalTime_exists_ne_zero {m : ℝ} (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    ∃ α : Fin 2 → Fin 2 ⊕ Fin 2, freeDiracFullS m hm 2 α (equalTimeTwoPoint r) ≠ 0 := by
  by_contra h_all
  push Not at h_all
  let U := alignPosTimeSU2 ![0, r, 0, 0]
  have hx_nc : equalTimeTwoPoint r ∈ nonCoincidentEuclidN 2 :=
    equalTimeTwoPoint_mem_nonCoincidentEuclidN hr.ne'
  have hrot := freeDiracFullS_rotCovariant hm 2 U 1 ![Sum.inl 0, Sum.inr 0]
    (equalTimeTwoPoint r) hx_nc
  rw [euclidRotN_alignPosTime_equalTimeTwoPoint hr] at hrot
  have h_zero :
      (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
        (∏ i : Fin 2, diracRep.σ (su2ToSL2C U, su2ToSL2C 1) (![Sum.inl 0, Sum.inr 0] i) (β i)) *
          freeDiracFullS m hm 2 β (equalTimeTwoPoint r)) = 0 :=
    Finset.sum_eq_zero (fun β _ => by rw [h_all β, mul_zero])
  rw [h_zero] at hrot
  exact freeDiracFullS_posTime_inl_inr_zero_ne_zero hm hr hrot

end

end QFT
