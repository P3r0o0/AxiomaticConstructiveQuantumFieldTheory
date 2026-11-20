import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import FreeFieldWick
import WightmanBridge

open scoped ComplexConjugate Topology BigOperators Matrix InnerProductSpace
open Geometry Geometry.MatrixAnalysis MeasureTheory Filter Complex Matrix

namespace QFT

noncomputable section

structure MassShellModeData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (m : ℝ) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) where
  ν : ℕ
  hη : η = 1 ∨ η = -1
  w : Fin ν → (Fin 3 → ℝ) → ι → ℂ
  measurable_w : ∀ (s : Fin ν) (α : ι), Measurable (fun p : Fin 3 → ℝ => w s p α)
  M : ℝ
  hM : 0 ≤ M
  norm_w_le : ∀ (s : Fin ν) (p : Fin 3 → ℝ) (α : ι), ‖w s p α‖ ≤ M
  factor_weight : ∀ (p : Fin 3 → ℝ) (α β : ι),
    ∑ γ : ι, S.C α γ * massShellWeight m C ![γ, β] p =
      ∑ s : Fin ν, star (w s p α) * w s p β

noncomputable def kgModeData {m : ℝ} (hm : 0 < m) :
    MassShellModeData trivialRep trivialStarStructure m 1 massiveKGCoeff where
  ν := 1
  hη := Or.inl rfl
  w _ p _ := (((Real.sqrt (2 * massShellEnergy m p))⁻¹ : ℝ) : ℂ)
  measurable_w _ _ :=
    Complex.continuous_ofReal.measurable.comp
      (((continuous_const.mul (continuous_massShellEnergy m)).sqrt).inv₀
        (fun p => by
          change Real.sqrt (2 * massShellEnergy m p) ≠ 0
          exact Real.sqrt_ne_zero'.mpr (by linarith [massShellEnergy_pos hm p]))).measurable
  M := (Real.sqrt (2 * m))⁻¹
  hM := inv_nonneg.mpr (Real.sqrt_nonneg _)
  norm_w_le _ p _ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith))
      (Real.sqrt_le_sqrt (by linarith [massShellEnergy_ge_mass hm p]))
  factor_weight p α β := by
    cases α
    cases β
    simp only [Fin.sum_univ_one, Fintype.univ_punit, Finset.sum_singleton,
      trivialStarStructure, Matrix.one_apply_eq, one_mul,
      massShellWeight, massiveKGCoeff, mul_one]
    have hpos : 0 ≤ 2 * massShellEnergy m p := by linarith [massShellEnergy_pos hm p]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← mul_inv, Real.mul_self_sqrt hpos]
    push_cast
    rfl

def diracModeRaw (m : ℝ) : Fin 2 → (Fin 3 → ℝ) → (Fin 2 ⊕ Fin 2) → ℂ
  | 0, _, Sum.inl 0 => 0
  | 0, _, Sum.inl 1 => (m : ℂ) * Complex.I
  | 0, p, Sum.inr 0 => ((massShellEnergy m p : ℂ) + (p 2 : ℂ))
  | 0, p, Sum.inr 1 => ((p 0 : ℂ) - (p 1 : ℂ) * Complex.I)
  | 1, p, Sum.inl 0 => -Complex.I * ((massShellEnergy m p : ℂ) + (p 2 : ℂ))
  | 1, p, Sum.inl 1 => -Complex.I * ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I)
  | 1, _, Sum.inr 0 => 0
  | 1, _, Sum.inr 1 => (m : ℂ)

lemma continuous_diracModeRaw (m : ℝ) (s : Fin 2) (α : Fin 2 ⊕ Fin 2) :
    Continuous (fun p : Fin 3 → ℝ => diracModeRaw m s p α) := by
  fin_cases s <;>
    rcases α with i | i <;>
    fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact (Complex.continuous_ofReal.comp (continuous_massShellEnergy m)).add
      (Complex.continuous_ofReal.comp (continuous_apply 2))
  · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).sub
      ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul continuous_const)
  · exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (continuous_massShellEnergy m)).add
        (Complex.continuous_ofReal.comp (continuous_apply 2)))
  · exact continuous_const.mul
      ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
        ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul continuous_const))
  · exact continuous_const
  · exact continuous_const

noncomputable def diracModeScale (m : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  (Real.sqrt (2 * massShellEnergy m p * (massShellEnergy m p + p 2)))⁻¹

lemma diracModeDenom_pos {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    0 < 2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
  mul_pos (mul_pos zero_lt_two (massShellEnergy_pos hm p))
    (massShellEnergy_add_third_pos hm p)

lemma continuous_diracModeScale {m : ℝ} (hm : 0 < m) :
    Continuous (diracModeScale m) := by
  unfold diracModeScale
  refine Continuous.inv₀ ?_ (fun p => Real.sqrt_ne_zero'.mpr (diracModeDenom_pos hm p))
  exact ((continuous_const.mul (continuous_massShellEnergy m)).mul
    ((continuous_massShellEnergy m).add (continuous_apply 2))).sqrt

lemma normSq_diracModeRaw_le {m : ℝ} (hm : 0 < m) (s : Fin 2)
    (p : Fin 3 → ℝ) (α : Fin 2 ⊕ Fin 2) :
    Complex.normSq (diracModeRaw m s p α) ≤
      2 * massShellEnergy m p * (massShellEnergy m p + p 2) := by
  have he_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
  have hp_add_pos : 0 < massShellEnergy m p + p 2 := massShellEnergy_add_third_pos hm p
  have h_msq : m ^ 2 + (p 0) ^ 2 + (p 1) ^ 2 =
      (massShellEnergy m p - p 2) * (massShellEnergy m p + p 2) := by
    have hsq := massShellEnergy_sq m p
    unfold massShellSpatialSq at hsq
    linarith
  have hp2_bounds : -massShellEnergy m p ≤ p 2 ∧ p 2 ≤ massShellEnergy m p := by
    have hsq : (p 2) ^ 2 ≤ (massShellEnergy m p) ^ 2 := by
      have h1 := massShellEnergy_sq m p
      unfold massShellSpatialSq at h1
      nlinarith [sq_nonneg m, sq_nonneg (p 0), sq_nonneg (p 1)]
    exact abs_le_of_sq_le_sq' hsq he_pos.le
  have h_sub_le : massShellEnergy m p - p 2 ≤ 2 * massShellEnergy m p := by
    linarith [hp2_bounds.1]
  have h_add_le : massShellEnergy m p + p 2 ≤ 2 * massShellEnergy m p := by
    linarith [hp2_bounds.2]
  have h_prod1 : (massShellEnergy m p - p 2) * (massShellEnergy m p + p 2) ≤
      2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
    mul_le_mul_of_nonneg_right h_sub_le hp_add_pos.le
  have h_prod2 : (massShellEnergy m p + p 2) ^ 2 ≤
      2 * massShellEnergy m p * (massShellEnergy m p + p 2) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_right h_add_le hp_add_pos.le
  fin_cases s <;>
    rcases α with i | i <;>
    fin_cases i
  · simp only [diracModeRaw, map_zero, ge_iff_le]
    exact (diracModeDenom_pos hm p).le
  · simp only [diracModeRaw, map_mul, Complex.normSq_ofReal, Complex.normSq_I, mul_one]
    nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), h_msq, h_prod1]
  · have h_eq : ((massShellEnergy m p : ℂ) + (p 2 : ℂ)) =
        ((massShellEnergy m p + p 2 : ℝ) : ℂ) := by push_cast; rfl
    change Complex.normSq ((massShellEnergy m p : ℂ) + (p 2 : ℂ)) ≤ _
    rw [h_eq, Complex.normSq_ofReal]
    nlinarith [h_prod2]
  · have h_re_im : Complex.normSq ((p 0 : ℂ) - (p 1 : ℂ) * Complex.I) =
        (p 0) ^ 2 + (p 1) ^ 2 := by
      have hz : (p 0 : ℂ) - (p 1 : ℂ) * Complex.I = ⟨p 0, -(p 1)⟩ := by
        apply Complex.ext <;> simp
      rw [hz, Complex.normSq_mk]
      ring
    change Complex.normSq ((p 0 : ℂ) - (p 1 : ℂ) * Complex.I) ≤ _
    rw [h_re_im]
    nlinarith [sq_nonneg m, h_msq, h_prod1]
  · have h_eq : ((massShellEnergy m p : ℂ) + (p 2 : ℂ)) =
        ((massShellEnergy m p + p 2 : ℝ) : ℂ) := by push_cast; rfl
    change Complex.normSq (-Complex.I * ((massShellEnergy m p : ℂ) + (p 2 : ℂ))) ≤ _
    rw [map_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, h_eq, Complex.normSq_ofReal]
    nlinarith [h_prod2]
  · have h_re_im : Complex.normSq ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I) =
        (p 0) ^ 2 + (p 1) ^ 2 := by
      have hz : (p 0 : ℂ) + (p 1 : ℂ) * Complex.I = ⟨p 0, p 1⟩ := by
        apply Complex.ext <;> simp
      rw [hz, Complex.normSq_mk]
      ring
    change Complex.normSq (-Complex.I * ((p 0 : ℂ) + (p 1 : ℂ) * Complex.I)) ≤ _
    rw [map_mul, Complex.normSq_neg, Complex.normSq_I, one_mul, h_re_im]
    nlinarith [sq_nonneg m, h_msq, h_prod1]
  · simp only [diracModeRaw, map_zero, ge_iff_le]
    exact (diracModeDenom_pos hm p).le
  · simp only [diracModeRaw, Complex.normSq_ofReal]
    nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), h_msq, h_prod1]

lemma diracModeRaw_sos (m : ℝ) (p : Fin 3 → ℝ) (α β : Fin 2 ⊕ Fin 2) :
    ((massShellEnergy m p + p 2 : ℝ) : ℂ) *
      diracMassShellCoeff m ![Sum.swap α, β] (massShellVec m p) =
    ∑ s : Fin 2, star (diracModeRaw m s p α) * diracModeRaw m s p β := by
  let q := massShellVec m p
  have h_msq : (m : ℂ) ^ 2 =
      (q 0 : ℂ) ^ 2 - (q 1 : ℂ) ^ 2 - (q 2 : ℂ) ^ 2 - (q 3 : ℂ) ^ 2 := by
    have hr : m ^ 2 = (q 0) ^ 2 - (q 1) ^ 2 - (q 2) ^ 2 - (q 3) ^ 2 := by
      dsimp [q, massShellVec]
      rw [massShellEnergy_sq]
      unfold massShellSpatialSq
      ring
    exact_mod_cast hr
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  have hI4 : Complex.I ^ 4 = 1 := by
    have h4 : (4 : ℕ) = 2 + 2 := rfl
    rw [h4, pow_add, Complex.I_sq]
    ring
  have h_bilin : ∀ (ξ ζ : Fin 2 ⊕ Fin 2 → ℂ),
      ((q 0 : ℂ) + (q 3 : ℂ)) *
        (∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
          (starRingEnd ℂ) (ξ γ) * diracMassShellCoeff m ![Sum.swap γ, γ'] q * ζ γ') =
      ∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
        (starRingEnd ℂ) (ξ γ) *
          (∑ s : Fin 2, (starRingEnd ℂ) (diracModeRaw m s p γ) * diracModeRaw m s p γ') *
          ζ γ' := by
    intro ξ ζ
    have hL :
        (∑ γ : Fin 2 ⊕ Fin 2, ∑ γ' : Fin 2 ⊕ Fin 2,
          (starRingEnd ℂ) (ξ γ) * diracMassShellCoeff m ![Sum.swap γ, γ'] q * ζ γ') =
        (starRingEnd ℂ) (ξ (Sum.inl 0)) *
          (((q 0 : ℂ) + (q 3 : ℂ)) * ζ (Sum.inl 0) +
            ((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * ζ (Sum.inl 1)) +
        (starRingEnd ℂ) (ξ (Sum.inl 1)) *
          (((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * ζ (Sum.inl 0) +
            ((q 0 : ℂ) - (q 3 : ℂ)) * ζ (Sum.inl 1)) +
        (starRingEnd ℂ) (ξ (Sum.inr 0)) *
          (((q 0 : ℂ) + (q 3 : ℂ)) * ζ (Sum.inr 0) +
            ((q 1 : ℂ) - (q 2 : ℂ) * Complex.I) * ζ (Sum.inr 1)) +
        (starRingEnd ℂ) (ξ (Sum.inr 1)) *
          (((q 1 : ℂ) + (q 2 : ℂ) * Complex.I) * ζ (Sum.inr 0) +
            ((q 0 : ℂ) - (q 3 : ℂ)) * ζ (Sum.inr 1)) +
        (m : ℂ) * Complex.I *
          ((starRingEnd ℂ) (ξ (Sum.inl 0)) * ζ (Sum.inr 1) -
            (starRingEnd ℂ) (ξ (Sum.inl 1)) * ζ (Sum.inr 0) +
            (starRingEnd ℂ) (ξ (Sum.inr 0)) * ζ (Sum.inl 1) -
            (starRingEnd ℂ) (ξ (Sum.inr 1)) * ζ (Sum.inl 0)) := by
      simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, Sum.swap_inl,
        Sum.swap_inr, diracMassShellCoeff, diracEpsilon_inl_inl, diracEpsilon_inr_inr,
        diracEpsilon_inl_inr, diracEpsilon_inr_inl, diracSlashCoeff_inl_inl,
        diracSlashCoeff_inr_inr, diracSlashCoeff_inl_inr, diracSlashCoeff_inr_inl,
        weylEpsilon_zero_zero, weylEpsilon_zero_one, weylEpsilon_one_zero,
        weylEpsilon_one_one, vec_to_spinor_apply_00, vec_to_spinor_apply_01,
        vec_to_spinor_apply_10, vec_to_spinor_apply_11]
      ring
    have hq0 : massShellEnergy m p = q 0 := rfl
    have hp0 : p 0 = q 1 := rfl
    have hp1 : p 1 = q 2 := rfl
    have hp2 : p 2 = q 3 := rfl
    rw [hL]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.isValue, diracModeRaw,
      hq0, hp0, hp1, hp2, map_mul, map_add, map_sub, map_neg, map_zero,
      Complex.conj_ofReal, Complex.conj_I]
    ring_nf
    simp only [Complex.I_sq, hI3, hI4, h_msq]
    ring
  have h_eval := h_bilin (fun γ => if γ = α then 1 else 0) (fun γ' => if γ' = β then 1 else 0)
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h_eval
  have hq03 : ((massShellEnergy m p + p 2 : ℝ) : ℂ) = (q 0 : ℂ) + (q 3 : ℂ) := by
    dsimp [q, massShellVec]
    push_cast
    rfl
  rw [hq03]
  simpa only [Complex.star_def] using h_eval

noncomputable def diracModeData {m : ℝ} (hm : 0 < m) :
    MassShellModeData diracRep diracStarStructure m (-1) (diracMassShellCoeff m) where
  ν := 2
  hη := Or.inr rfl
  w s p α := (diracModeScale m p : ℂ) * diracModeRaw m s p α
  measurable_w s α :=
    (Complex.continuous_ofReal.comp (continuous_diracModeScale hm)).measurable.mul
      (continuous_diracModeRaw m s α).measurable
  M := 1
  hM := zero_le_one
  norm_w_le s p α := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hden : 0 < 2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
      diracModeDenom_pos hm p
    have hsc_nn : 0 ≤ diracModeScale m p := inv_nonneg.mpr (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hsc_nn, Complex.norm_def]
    have hle := Real.sqrt_le_sqrt (normSq_diracModeRaw_le hm s p α)
    calc diracModeScale m p * Real.sqrt (Complex.normSq (diracModeRaw m s p α))
        ≤ diracModeScale m p *
            Real.sqrt (2 * massShellEnergy m p * (massShellEnergy m p + p 2)) :=
          mul_le_mul_of_nonneg_left hle hsc_nn
      _ = 1 := inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hden)
  factor_weight p α β := by
    have hC_sum : ∑ γ : Fin 2 ⊕ Fin 2,
        diracStarStructure.C α γ * massShellWeight m (diracMassShellCoeff m) ![γ, β] p =
        massShellWeight m (diracMassShellCoeff m) ![Sum.swap α, β] p := by
      have h_entry : ∀ γ : Fin 2 ⊕ Fin 2, diracStarStructure.C α γ =
          if γ = Sum.swap α then 1 else 0 := by
        intro γ
        rcases α with i | i <;> rcases γ with j | j <;> fin_cases i <;> fin_cases j <;>
          simp [diracStarStructure, chiralDoubleStarStructure, Matrix.fromBlocks]
      simp_rw [h_entry, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [hC_sum]
    have hden_pos : 0 < 2 * massShellEnergy m p * (massShellEnergy m p + p 2) :=
      diracModeDenom_pos hm p
    have hsc_sq : (diracModeScale m p : ℂ) * (diracModeScale m p : ℂ) =
        (((2 * massShellEnergy m p * (massShellEnergy m p + p 2))⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      dsimp [diracModeScale]
      rw [← mul_inv, Real.mul_self_sqrt hden_pos.le]
    have hrhs :
        (∑ s : Fin 2,
          star ((diracModeScale m p : ℂ) * diracModeRaw m s p α) *
            ((diracModeScale m p : ℂ) * diracModeRaw m s p β)) =
        (((2 * massShellEnergy m p * (massShellEnergy m p + p 2))⁻¹ : ℝ) : ℂ) *
          ∑ s : Fin 2, star (diracModeRaw m s p α) * diracModeRaw m s p β := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [star_mul']
      have hstar_sc : star (diracModeScale m p : ℂ) = (diracModeScale m p : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]
      rw [hstar_sc]
      calc (diracModeScale m p : ℂ) * star (diracModeRaw m s p α) *
            ((diracModeScale m p : ℂ) * diracModeRaw m s p β)
          = ((diracModeScale m p : ℂ) * (diracModeScale m p : ℂ)) *
              (star (diracModeRaw m s p α) * diracModeRaw m s p β) := by ring
        _ = (((2 * massShellEnergy m p * (massShellEnergy m p + p 2))⁻¹ : ℝ) : ℂ) *
              (star (diracModeRaw m s p α) * diracModeRaw m s p β) := by rw [hsc_sq]
    rw [hrhs, ← diracModeRaw_sos m p α β]
    unfold massShellWeight
    have he_ne : ((massShellEnergy m p : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (massShellEnergy_pos hm p).ne'
    have hp_ne : ((massShellEnergy m p : ℝ) : ℂ) + (p 2 : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (massShellEnergy_add_third_pos hm p).ne'
    push_cast
    field_simp [he_ne, hp_ne]

abbrev FockSectorDom (ν r : ℕ) : Type :=
  (Fin r → Fin 3 → ℝ) × (Fin r → Fin ν)

noncomputable def fockSectorMeasure (ν r : ℕ) : Measure (FockSectorDom ν r) :=
  volume.prod Measure.count

instance instSigmaFiniteFockSectorMeasure (ν r : ℕ) :
    SigmaFinite (fockSectorMeasure ν r) := by
  unfold fockSectorMeasure
  infer_instance

abbrev FockOmega (ν : ℕ) : Type :=
  Σ r : ℕ, FockSectorDom ν r

lemma measurable_fockSigmaMk (ν r : ℕ) :
    Measurable (Sigma.mk r : FockSectorDom ν r → FockOmega ν) := by
  intro U hU
  exact (MeasurableSpace.measurableSet_iInf.mp hU) r

lemma measurableSet_fockOmega_iff (ν : ℕ) (S : Set (FockOmega ν)) :
    MeasurableSet S ↔ ∀ r : ℕ, MeasurableSet (Sigma.mk r ⁻¹' S) :=
  MeasurableSpace.measurableSet_iInf

noncomputable def fockMeasure (ν : ℕ) : Measure (FockOmega ν) :=
  Measure.sum (fun r : ℕ => (fockSectorMeasure ν r).map (Sigma.mk r))

abbrev FockHilbert (ν : ℕ) : Type :=
  MeasureTheory.Lp ℂ 2 (fockMeasure ν)

def sectorToOmega (ν r : ℕ) (g : FockSectorDom ν r → ℂ) : FockOmega ν → ℂ :=
  fun a => if h : a.1 = r then g (h ▸ a.2) else 0

@[simp]
lemma sectorToOmega_sigmaMk_eq (ν r : ℕ) (g : FockSectorDom ν r → ℂ)
    (x : FockSectorDom ν r) :
    sectorToOmega ν r g ⟨r, x⟩ = g x := by
  simp [sectorToOmega]

lemma sectorToOmega_sigmaMk_ne (ν : ℕ) {r r' : ℕ} (hne : r' ≠ r)
    (g : FockSectorDom ν r → ℂ) (x : FockSectorDom ν r') :
    sectorToOmega ν r g ⟨r', x⟩ = 0 := by
  simp [sectorToOmega, hne]

lemma sectorToOmega_mul_ne (ν : ℕ) {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    (g₁ : FockSectorDom ν r₁ → ℂ) (g₂ : FockSectorDom ν r₂ → ℂ) (a : FockOmega ν) :
    star (sectorToOmega ν r₁ g₁ a) * sectorToOmega ν r₂ g₂ a = 0 := by
  rcases a with ⟨r', x⟩
  by_cases h1 : r' = r₁
  · subst h1
    rw [sectorToOmega_sigmaMk_ne ν hne g₂ x, mul_zero]
  · rw [sectorToOmega_sigmaMk_ne ν h1 g₁ x, star_zero, zero_mul]

lemma measurable_sectorToOmega {ν r : ℕ} {g : FockSectorDom ν r → ℂ} (hg : Measurable g) :
    Measurable (sectorToOmega ν r g) := by
  intro U hU
  rw [measurableSet_fockOmega_iff]
  intro r'
  by_cases h : r' = r
  · subst h
    have hpre : Sigma.mk r' ⁻¹' (sectorToOmega ν r' g ⁻¹' U) = g ⁻¹' U := by
      ext x
      simp [sectorToOmega]
    rw [hpre]
    exact hg hU
  · by_cases h0 : (0 : ℂ) ∈ U
    · have hpre : Sigma.mk r' ⁻¹' (sectorToOmega ν r g ⁻¹' U) = Set.univ := by
        ext x
        simp [sectorToOmega, h, h0]
      rw [hpre]
      exact MeasurableSet.univ
    · have hpre : Sigma.mk r' ⁻¹' (sectorToOmega ν r g ⁻¹' U) = ∅ := by
        ext x
        simp [sectorToOmega, h, h0]
      rw [hpre]
      exact MeasurableSet.empty

lemma memLp_sectorToOmega {ν r : ℕ} {g : FockSectorDom ν r → ℂ} (hg_meas : Measurable g)
    (hg : MemLp g 2 (fockSectorMeasure ν r)) :
    MemLp (sectorToOmega ν r g) 2 (fockMeasure ν) := by
  refine ⟨(measurable_sectorToOmega hg_meas).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  have h_sum :
      ∫⁻ a : FockOmega ν, (‖sectorToOmega ν r g a‖ₑ) ^ (2 : ℝ) ∂(fockMeasure ν) =
      ∫⁻ x : FockSectorDom ν r, (‖g x‖ₑ) ^ (2 : ℝ) ∂(fockSectorMeasure ν r) := by
    unfold fockMeasure
    have h_meas_nn : Measurable (fun a : FockOmega ν =>
        (‖sectorToOmega ν r g a‖ₑ) ^ (2 : ℝ)) :=
      ((measurable_sectorToOmega hg_meas).enorm).pow_const (2 : ℝ)
    rw [lintegral_sum_measure, tsum_eq_single r]
    · rw [lintegral_map h_meas_nn (measurable_fockSigmaMk ν r)]
      simp [sectorToOmega]
    · intro r' hne
      rw [lintegral_map h_meas_nn (measurable_fockSigmaMk ν r')]
      simp [sectorToOmega, hne]
  have hg_norm := hg.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at hg_norm
  rwa [h2, h_sum, ← h2]

noncomputable def liftSectorToFock (ν r : ℕ) (g : FockSectorDom ν r → ℂ)
    (hg_meas : Measurable g) (hg : MemLp g 2 (fockSectorMeasure ν r)) : FockHilbert ν :=
  (memLp_sectorToOmega hg_meas hg).toLp (sectorToOmega ν r g)

lemma integral_fockMeasure_mul_sectorToOmega_eq {ν r : ℕ}
    {g₁ g₂ : FockSectorDom ν r → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r))
    (hg₂_meas : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r)) :
    (∫ a : FockOmega ν,
      star (sectorToOmega ν r g₁ a) * sectorToOmega ν r g₂ a ∂(fockMeasure ν)) =
    ∫ x : FockSectorDom ν r, star (g₁ x) * g₂ x ∂(fockSectorMeasure ν r) := by
  let F : FockOmega ν → ℂ := fun a => star (sectorToOmega ν r g₁ a) * sectorToOmega ν r g₂ a
  have hF_meas : Measurable F :=
    (continuous_star.measurable.comp (measurable_sectorToOmega hg₁_meas)).mul
      (measurable_sectorToOmega hg₂_meas)
  have hF_int : Integrable F (fockMeasure ν) := by
    have h1 := memLp_sectorToOmega hg₁_meas hg₁
    have h2 := memLp_sectorToOmega hg₂_meas hg₂
    have h_inner := L2.integrable_inner (𝕜 := ℂ) (h1.toLp _) (h2.toLp _)
    refine h_inner.congr ?_
    filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with a ha1 ha2
    simp [F, RCLike.inner_apply, ha1, ha2, mul_comm]
  change ∫ a : FockOmega ν, F a ∂(fockMeasure ν) = _
  unfold fockMeasure
  rw [integral_sum_measure hF_int, tsum_eq_single r]
  · rw [integral_map (measurable_fockSigmaMk ν r).aemeasurable hF_meas.aestronglyMeasurable]
    simp [F, sectorToOmega]
  · intro r' hne
    rw [integral_map (measurable_fockSigmaMk ν r').aemeasurable hF_meas.aestronglyMeasurable]
    simp [F, sectorToOmega, hne]

theorem inner_liftSectorToFock_eq {ν r : ℕ}
    {g₁ g₂ : FockSectorDom ν r → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r))
    (hg₂_meas : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r)) :
    ⟪liftSectorToFock ν r g₁ hg₁_meas hg₁, liftSectorToFock ν r g₂ hg₂_meas hg₂⟫_ℂ =
      ∫ x : FockSectorDom ν r, star (g₁ x) * g₂ x ∂(fockSectorMeasure ν r) := by
  rw [L2.inner_def]
  have h_congr :
      (∫ a : FockOmega ν,
        ⟪(liftSectorToFock ν r g₁ hg₁_meas hg₁ : FockOmega ν → ℂ) a,
          (liftSectorToFock ν r g₂ hg₂_meas hg₂ : FockOmega ν → ℂ) a⟫_ℂ ∂(fockMeasure ν)) =
      ∫ a : FockOmega ν,
        star (sectorToOmega ν r g₁ a) * sectorToOmega ν r g₂ a ∂(fockMeasure ν) := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_sectorToOmega hg₁_meas hg₁).coeFn_toLp,
      (memLp_sectorToOmega hg₂_meas hg₂).coeFn_toLp] with a ha1 ha2
    unfold liftSectorToFock
    rw [ha1, ha2]
    simp [RCLike.inner_apply, mul_comm]
  rw [h_congr, integral_fockMeasure_mul_sectorToOmega_eq hg₁_meas hg₁ hg₂_meas hg₂]

theorem inner_liftSectorToFock_ne {ν r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    {g₁ : FockSectorDom ν r₁ → ℂ} {g₂ : FockSectorDom ν r₂ → ℂ}
    (hg₁_meas : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r₁))
    (hg₂_meas : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r₂)) :
    ⟪liftSectorToFock ν r₁ g₁ hg₁_meas hg₁, liftSectorToFock ν r₂ g₂ hg₂_meas hg₂⟫_ℂ = 0 := by
  rw [L2.inner_def]
  have h_zero :
      (fun a : FockOmega ν =>
        ⟪(liftSectorToFock ν r₁ g₁ hg₁_meas hg₁ : FockOmega ν → ℂ) a,
          (liftSectorToFock ν r₂ g₂ hg₂_meas hg₂ : FockOmega ν → ℂ) a⟫_ℂ) =ᶠ[ae (fockMeasure ν)]
      0 := by
    filter_upwards [(memLp_sectorToOmega hg₁_meas hg₁).coeFn_toLp,
      (memLp_sectorToOmega hg₂_meas hg₂).coeFn_toLp] with a ha1 ha2
    unfold liftSectorToFock
    rw [ha1, ha2]
    have hmul := sectorToOmega_mul_ne ν hne g₁ g₂ a
    simpa [RCLike.inner_apply, mul_comm] using hmul
  rw [integral_congr_ae h_zero]
  simp

def fockSectorPermEquiv (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    FockSectorDom ν r ≃ᵐ FockSectorDom ν r where
  toFun x := (x.1 ∘ π, x.2 ∘ π)
  invFun x := (x.1 ∘ π.symm, x.2 ∘ π.symm)
  left_inv x := by
    rcases x with ⟨k, s⟩
    apply Prod.ext <;> ext a <;> simp
  right_inv x := by
    rcases x with ⟨k, s⟩
    apply Prod.ext <;> ext a <;> simp
  measurable_toFun :=
    (measurable_pi_lambda _ (fun a => (measurable_pi_apply (π a)).comp measurable_fst)).prodMk
      (measurable_pi_lambda _ (fun a => (measurable_pi_apply (π a)).comp measurable_snd))
  measurable_invFun :=
    (measurable_pi_lambda _
      (fun a => (measurable_pi_apply (π.symm a)).comp measurable_fst)).prodMk
      (measurable_pi_lambda _ (fun a => (measurable_pi_apply (π.symm a)).comp measurable_snd))

@[simp]
lemma fockSectorPermEquiv_apply (ν r : ℕ) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r) :
    fockSectorPermEquiv ν r π x = (x.1 ∘ π, x.2 ∘ π) := rfl

lemma measurePreserving_fockSectorPermEquiv (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    MeasurePreserving (fockSectorPermEquiv ν r π)
      (fockSectorMeasure ν r) (fockSectorMeasure ν r) := by
  have h1 : MeasurePreserving (fun k : Fin r → Fin 3 → ℝ => k ∘ π) volume volume := by
    have heq : (fun k : Fin r → Fin 3 → ℝ => k ∘ π) =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin r => Fin 3 → ℝ) π.symm) := by
      funext k a
      change k (π a) = Equiv.piCongrLeft (fun _ : Fin r => Fin 3 → ℝ) π.symm k a
      rw [Equiv.piCongrLeft_apply]
      simp
    rw [heq]
    exact volume_measurePreserving_piCongrLeft (fun _ : Fin r => Fin 3 → ℝ) π.symm
  have h2 : MeasurePreserving (fun s : Fin r → Fin ν => s ∘ π)
      Measure.count Measure.count := by
    let e : (Fin r → Fin ν) ≃ (Fin r → Fin ν) :=
      { toFun := fun s => s ∘ π
        invFun := fun s => s ∘ π.symm
        left_inv := fun s => by ext a; simp
        right_inv := fun s => by ext a; simp }
    have hm : Measurable e :=
      measurable_pi_lambda _ (fun a => measurable_pi_apply (π a))
    change MeasurePreserving e Measure.count Measure.count
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← e.injective.encard_image, e.image_preimage]
  exact MeasurePreserving.prod h1 h2

noncomputable def symmSector (ν r : ℕ) (η : ℂ) (F : FockSectorDom ν r → ℂ) :
    FockSectorDom ν r → ℂ :=
  fun x => (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
    ∑ π : Equiv.Perm (Fin r), η ^ permInversions π * F (fockSectorPermEquiv ν r π x)

lemma measurable_symmSector {ν r : ℕ} (η : ℂ) {F : FockSectorDom ν r → ℂ}
    (hF : Measurable F) :
    Measurable (symmSector ν r η F) :=
  measurable_const.mul <|
    Finset.measurable_sum Finset.univ (fun π _ =>
      measurable_const.mul (hF.comp (fockSectorPermEquiv ν r π).measurable))

lemma memLp_symmSector {ν r : ℕ} (η : ℂ) {F : FockSectorDom ν r → ℂ}
    (hF : MemLp F 2 (fockSectorMeasure ν r)) :
    MemLp (symmSector ν r η F) 2 (fockSectorMeasure ν r) := by
  unfold symmSector
  refine MemLp.const_mul ?_ _
  refine memLp_finsetSum Finset.univ (fun π _ => ?_)
  exact (hF.comp_measurePreserving (measurePreserving_fockSectorPermEquiv ν r π)).const_mul _

theorem inner_symmSector_eq {ν r : ℕ} {η : ℂ} (hη : η = 1 ∨ η = -1)
    {F₁ F₂ : FockSectorDom ν r → ℂ}
    (hF₁ : MemLp F₁ 2 (fockSectorMeasure ν r))
    (hF₂ : MemLp F₂ 2 (fockSectorMeasure ν r)) :
    (∫ x : FockSectorDom ν r,
      star (symmSector ν r η F₁ x) * symmSector ν r η F₂ x ∂(fockSectorMeasure ν r)) =
    ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
      ∫ x : FockSectorDom ν r,
        star (F₁ x) * F₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm) ∂(fockSectorMeasure ν r) := by
  let c : ℝ := ((r.factorial : ℝ).sqrt)⁻¹
  have hc_sq : (c : ℂ) * (c : ℂ) = (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    dsimp [c]
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have h_int_pair : ∀ (π₁ π₂ : Equiv.Perm (Fin r)),
      Integrable (fun x : FockSectorDom ν r =>
        star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
          (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x)))
        (fockSectorMeasure ν r) := by
    intro π₁ π₂
    have hm1 := (hF₁.comp_measurePreserving
      (measurePreserving_fockSectorPermEquiv ν r π₁)).const_mul (η ^ permInversions π₁)
    have hm2 := (hF₂.comp_measurePreserving
      (measurePreserving_fockSectorPermEquiv ν r π₂)).const_mul (η ^ permInversions π₂)
    have hi := L2.integrable_inner (𝕜 := ℂ) (hm1.toLp _) (hm2.toLp _)
    refine hi.congr ?_
    filter_upwards [hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [mul_comm]
  have h_expand :
      (fun x : FockSectorDom ν r =>
        star (symmSector ν r η F₁ x) * symmSector ν r η F₂ x) =
      fun x => (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) *
        ∑ π₁ : Equiv.Perm (Fin r), ∑ π₂ : Equiv.Perm (Fin r),
          star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x)) := by
    ext x
    simp only [symmSector]
    have hstar_c : star (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) =
        (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [star_mul', hstar_c, star_sum, Finset.mul_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun π₁ _ => ?_)
    refine Finset.sum_congr rfl (fun π₂ _ => ?_)
    have hmul :
        (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) * (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) =
          (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) := hc_sq
    calc (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
            star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            ((((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
              (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x)))
        = ((((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) * (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ)) *
            (star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
              (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x))) := by ring
      _ = _ := by rw [hmul]
  rw [h_expand, integral_const_mul,
    integral_finsetSum Finset.univ (fun π₁ _ =>
      integrable_finsetSum Finset.univ (fun π₂ _ => h_int_pair π₁ π₂))]
  have h_each : ∀ π₁ : Equiv.Perm (Fin r),
      (∫ x : FockSectorDom ν r,
        ∑ π₂ : Equiv.Perm (Fin r),
          star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            (η ^ permInversions π₂ * F₂ (fockSectorPermEquiv ν r π₂ x))
        ∂(fockSectorMeasure ν r)) =
      ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
        ∫ x : FockSectorDom ν r,
          star (F₁ x) * F₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm) ∂(fockSectorMeasure ν r) := by
    intro π₁
    rw [integral_finsetSum Finset.univ (fun π₂ _ => h_int_pair π₁ π₂)]
    rw [← Fintype.sum_equiv (Equiv.mulLeft π₁) _ _ (fun _ => rfl)]
    rw [← Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin r))) _ _ (fun _ => rfl)]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    change (∫ x : FockSectorDom ν r,
        star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
          (η ^ permInversions (π₁ * σ⁻¹) *
            F₂ (fockSectorPermEquiv ν r (π₁ * σ⁻¹) x))
        ∂(fockSectorMeasure ν r)) = _
    have h_sign :
        star (η ^ permInversions π₁) * η ^ permInversions (π₁ * σ⁻¹) =
          η ^ permInversions σ := by
      have hp1 : (η ^ permInversions π₁) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, eta_sq_eq_one hη, one_pow]
      rw [star_eta_pow hη, eta_pow_permInversions_mul hη π₁ σ⁻¹,
        eta_pow_permInversions_inv hη σ, ← mul_assoc, ← pow_two, hp1, one_mul]
    have h_pull :
        (∫ x : FockSectorDom ν r,
          star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
            (η ^ permInversions (π₁ * σ⁻¹) *
              F₂ (fockSectorPermEquiv ν r (π₁ * σ⁻¹) x))
          ∂(fockSectorMeasure ν r)) =
        η ^ permInversions σ *
          ∫ y : FockSectorDom ν r,
            star (F₁ y) * F₂ (fockSectorPermEquiv ν r σ⁻¹ y) ∂(fockSectorMeasure ν r) := by
      have h_alg :
          (fun x : FockSectorDom ν r =>
            star (η ^ permInversions π₁ * F₁ (fockSectorPermEquiv ν r π₁ x)) *
              (η ^ permInversions (π₁ * σ⁻¹) *
                F₂ (fockSectorPermEquiv ν r (π₁ * σ⁻¹) x))) =
          fun x => η ^ permInversions σ *
            ((fun y : FockSectorDom ν r =>
              star (F₁ y) * F₂ (fockSectorPermEquiv ν r σ⁻¹ y))
              (fockSectorPermEquiv ν r π₁ x)) := by
        ext x
        rw [star_mul']
        have hcomp : fockSectorPermEquiv ν r (π₁ * σ⁻¹) x =
            fockSectorPermEquiv ν r σ⁻¹ (fockSectorPermEquiv ν r π₁ x) := by
          rcases x with ⟨k, s⟩
          simp only [fockSectorPermEquiv_apply]
          rfl
        rw [hcomp]
        calc star (η ^ permInversions π₁) * star (F₁ (fockSectorPermEquiv ν r π₁ x)) *
              (η ^ permInversions (π₁ * σ⁻¹) *
                F₂ (fockSectorPermEquiv ν r σ⁻¹ (fockSectorPermEquiv ν r π₁ x)))
            = (star (η ^ permInversions π₁) * η ^ permInversions (π₁ * σ⁻¹)) *
                (star (F₁ (fockSectorPermEquiv ν r π₁ x)) *
                  F₂ (fockSectorPermEquiv ν r σ⁻¹ (fockSectorPermEquiv ν r π₁ x))) := by ring
          _ = _ := by rw [h_sign]
      rw [h_alg, integral_const_mul]
      congr 1
      exact (measurePreserving_fockSectorPermEquiv ν r π₁).integral_comp
        (fockSectorPermEquiv ν r π₁).measurableEmbedding
        (fun y : FockSectorDom ν r => star (F₁ y) * F₂ (fockSectorPermEquiv ν r σ⁻¹ y))
    rw [h_pull]
    rfl
  simp_rw [h_each, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [nsmul_eq_mul, ← mul_assoc]
  have hfact_ne : ((r.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r))
  have hmul_inv : (((r.factorial : ℝ)⁻¹ : ℝ) : ℂ) * ((r.factorial : ℕ) : ℂ) = 1 := by
    push_cast
    exact inv_mul_cancel₀ hfact_ne
  rw [hmul_inv, one_mul]

namespace PartialPairing

noncomputable def partialMomentum {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun i => match L.partialSlotEquiv.symm i with
    | Sum.inl a => -massShellVec m (k_ext a)
    | Sum.inr (c, 0) => massShellVec m (p_int c)
    | Sum.inr (c, 1) => -massShellVec m (p_int c)

@[simp]
lemma partialMomentum_unpaired {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (a : Fin r) :
    L.partialMomentum m p_int k_ext (L.unpaired a) = -massShellVec m (k_ext a) := by
  have hsym : L.partialSlotEquiv.symm (L.unpaired a) = Sum.inl a :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  unfold partialMomentum
  rw [hsym]

@[simp]
lemma partialMomentum_fst {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (c : L.InternalChord) :
    L.partialMomentum m p_int k_ext c.1 = massShellVec m (p_int c) := by
  have hsym : L.partialSlotEquiv.symm c.1 = Sum.inr (c, 0) :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  unfold partialMomentum
  rw [hsym]

@[simp]
lemma partialMomentum_mate {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (c : L.InternalChord) :
    L.partialMomentum m p_int k_ext (L.mate c.1) = -massShellVec m (p_int c) := by
  have hsym : L.partialSlotEquiv.symm (L.mate c.1) = Sum.inr (c, 1) :=
    L.partialSlotEquiv.symm_apply_eq.mpr rfl
  unfold partialMomentum
  rw [hsym]

lemma continuous_partialMomentum_uncurry {n r : ℕ} (m : ℝ) (L : PartialPairing n r) :
    Continuous (fun pk : (L.InternalChord → Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
      L.partialMomentum m pk.1 pk.2) := by
  refine continuous_pi (fun i => ?_)
  unfold partialMomentum
  rcases h : L.partialSlotEquiv.symm i with a | ⟨c, s⟩
  · exact ((continuous_massShellVec m).comp ((continuous_apply a).comp continuous_snd)).neg
  · fin_cases s
    · exact (continuous_massShellVec m).comp ((continuous_apply c).comp continuous_fst)
    · exact ((continuous_massShellVec m).comp ((continuous_apply c).comp continuous_fst)).neg

lemma measurable_partialMomentum_uncurry {n r : ℕ} (m : ℝ) (L : PartialPairing n r) :
    Measurable (fun pk : (L.InternalChord → Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
      L.partialMomentum m pk.1 pk.2) :=
  (L.continuous_partialMomentum_uncurry m).measurable

lemma one_add_norm_internal_le_momentumToEuclid {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (c : L.InternalChord) :
    1 + ‖p_int c‖ ≤
      (2 * Real.pi) * (1 + ‖momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)‖) := by
  let u := momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖p_int c‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (c.1, j.succ) = (2 * Real.pi)⁻¹ * p_int c j := by
      have hu_app :
          u (c.1, j.succ) = (2 * Real.pi)⁻¹ * L.partialMomentum m p_int k_ext c.1 j.succ := by
        dsimp only [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
          piSpaceEquiv, finCurryEquiv, finEuclidEquiv]
        simp
      rw [hu_app, L.partialMomentum_fst]
      fin_cases j <;> simp [massShellVec]
    have hpj : p_int c j = (2 * Real.pi) * u (c.1, j.succ) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖p_int c j‖ = ‖(2 * Real.pi) * u (c.1, j.succ)‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (c.1, j.succ)‖ := by
          rw [norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (c.1, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

lemma one_add_norm_unpaired_le_momentumToEuclid {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) (a : Fin r) :
    1 + ‖k_ext a‖ ≤
      (2 * Real.pi) * (1 + ‖momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)‖) := by
  let u := momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hp_norm : ‖k_ext a‖ ≤ (2 * Real.pi) * ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hpi.le (norm_nonneg u))).mpr (fun j => ?_)
    have hu_coord : u (L.unpaired a, j.succ) = -((2 * Real.pi)⁻¹ * k_ext a j) := by
      have hu_app :
          u (L.unpaired a, j.succ) =
            (2 * Real.pi)⁻¹ * L.partialMomentum m p_int k_ext (L.unpaired a) j.succ := by
        dsimp only [u, momentumToEuclidCLMN, posScaledMomentumCLMN, posScaledMomentumN,
          piSpaceEquiv, finCurryEquiv, finEuclidEquiv]
        simp
      rw [hu_app, L.partialMomentum_unpaired]
      fin_cases j <;> simp [massShellVec]
    have hpj : k_ext a j = -((2 * Real.pi) * u (L.unpaired a, j.succ)) := by
      rw [hu_coord]
      field_simp [hpi.ne']
    calc ‖k_ext a j‖ = ‖-((2 * Real.pi) * u (L.unpaired a, j.succ))‖ := by rw [hpj]
      _ = (2 * Real.pi) * ‖u (L.unpaired a, j.succ)‖ := by
          rw [norm_neg, norm_mul, Real.norm_of_nonneg hpi.le]
      _ ≤ (2 * Real.pi) * ‖u‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u (L.unpaired a, j.succ)) hpi.le
  have hpi1 : 1 ≤ 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  linarith

theorem norm_schwartz_momentumToEuclid_partial_le {n r : ℕ} (m : ℝ) (L : PartialPairing n r)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    ‖g (momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext))‖ ≤
      ((4 * Real.pi) ^ (4 * (Fintype.card L.InternalChord + r)) *
        ((Finset.Iic (4 * (Fintype.card L.InternalChord + r), 0)).sup
          (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g)) *
        (∏ c : L.InternalChord, ((1 + ‖p_int c‖) ^ 4)⁻¹) *
        (∏ a : Fin r, ((1 + ‖k_ext a‖) ^ 4)⁻¹) := by
  let d := Fintype.card L.InternalChord + r
  let u := momentumToEuclidCLMN n (L.partialMomentum m p_int k_ext)
  let S_sem : ℝ := (Finset.Iic (4 * d, 0)).sup
    (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
  have h_sch : (1 + ‖u‖) ^ (4 * d) * ‖g u‖ ≤ 2 ^ (4 * d) * S_sem := by
    have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (4 * d, 0)) (k := 4 * d) (n := 0) le_rfl le_rfl g u
    have h_fam :
        (fun m : ℕ × ℕ =>
          SchwartzMap.seminorm (E := EuclideanSpace ℝ (Fin n × Fin 4)) (F := ℂ) ℂ m.1 m.2) =
        schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ := rfl
    simpa [norm_iteratedFDeriv_zero, h_fam, S_sem] using h0
  have h_prod_c :
      (∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) ≤
        ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * Fintype.card L.InternalChord) := by
    calc (∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4)
        ≤ ∏ _c : L.InternalChord, ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun c _ => pow_le_pow_left₀ (by positivity)
              (L.one_add_norm_internal_le_momentumToEuclid m p_int k_ext c) 4)
      _ = (((2 * Real.pi) * (1 + ‖u‖)) ^ 4) ^ Fintype.card L.InternalChord := by
          rw [Finset.prod_const, Finset.card_univ]
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * Fintype.card L.InternalChord) :=
          (pow_mul _ 4 _).symm
  have h_prod_a :
      (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4) ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * r) := by
    calc (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)
        ≤ ∏ _a : Fin r, ((2 * Real.pi) * (1 + ‖u‖)) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => by positivity)
            (fun a _ => pow_le_pow_left₀ (by positivity)
              (L.one_add_norm_unpaired_le_momentumToEuclid m p_int k_ext a) 4)
      _ = (((2 * Real.pi) * (1 + ‖u‖)) ^ 4) ^ r := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * r) := (pow_mul _ 4 r).symm
  have h_prod_both :
      ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)) ≤
        (2 * Real.pi) ^ (4 * d) * (1 + ‖u‖) ^ (4 * d) := by
    calc ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4))
        ≤ ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * Fintype.card L.InternalChord) *
            ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * r) :=
          mul_le_mul h_prod_c h_prod_a
            (Finset.prod_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = ((2 * Real.pi) * (1 + ‖u‖)) ^ (4 * d) := by
          rw [← pow_add]
          congr 1
          dsimp [d]
          ring
      _ = (2 * Real.pi) ^ (4 * d) * (1 + ‖u‖) ^ (4 * d) := mul_pow _ _ (4 * d)
  have h_prod :
      ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)) *
        ‖g u‖ ≤ (4 * Real.pi) ^ (4 * d) * S_sem := by
    calc ((∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4)) *
          ‖g u‖
        ≤ ((2 * Real.pi) ^ (4 * d) * (1 + ‖u‖) ^ (4 * d)) * ‖g u‖ :=
          mul_le_mul_of_nonneg_right h_prod_both (norm_nonneg _)
      _ = (2 * Real.pi) ^ (4 * d) * ((1 + ‖u‖) ^ (4 * d) * ‖g u‖) := by ring
      _ ≤ (2 * Real.pi) ^ (4 * d) * (2 ^ (4 * d) * S_sem) :=
          mul_le_mul_of_nonneg_left h_sch (by positivity)
      _ = ((2 * Real.pi) * 2) ^ (4 * d) * S_sem := by rw [← mul_assoc, ← mul_pow]
      _ = (4 * Real.pi) ^ (4 * d) * S_sem := by congr 2; ring
  have h_pos :
      0 < (∏ c : L.InternalChord, (1 + ‖p_int c‖) ^ 4) * (∏ a : Fin r, (1 + ‖k_ext a‖) ^ 4) :=
    mul_pos (Finset.prod_pos (fun _ _ => by positivity))
      (Finset.prod_pos (fun _ _ => by positivity))
  rw [mul_assoc (_ * S_sem), Finset.prod_inv_distrib, Finset.prod_inv_distrib, ← mul_inv]
  exact (le_mul_inv_iff₀' h_pos).mpr h_prod

def concatRevParamEquiv {j k r : ℕ} (L : PartialPairing j r) (R : PartialPairing k r)
    (σ : Equiv.Perm (Fin r)) :
    (((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
      (Fin r → Fin 3 → ℝ)) ≃ᵐ
      ((concatRev L R σ).Chord → Fin 3 → ℝ) :=
  (((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : L.InternalChord ⊕ R.InternalChord => Fin 3 → ℝ)).symm.prodCongr
      (MeasurableEquiv.refl (Fin r → Fin 3 → ℝ))).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r => Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : (concatRev L R σ).Chord => Fin 3 → ℝ)
      (concatRevChordEquiv L R σ))

lemma measurePreserving_concatRevParamEquiv {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r)) :
    MeasurePreserving (concatRevParamEquiv L R σ) volume volume := by
  unfold concatRevParamEquiv
  exact (((volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : L.InternalChord ⊕ R.InternalChord => Fin 3 → ℝ)).prod
      (MeasurePreserving.id volume)).trans
    (volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : (L.InternalChord ⊕ R.InternalChord) ⊕ Fin r => Fin 3 → ℝ))).trans
    (volume_measurePreserving_piCongrLeft
      (fun _ : (concatRev L R σ).Chord => Fin 3 → ℝ)
      (concatRevChordEquiv L R σ))

@[simp]
lemma concatRevParamEquiv_apply_inl_inl {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) (cL : L.InternalChord) :
    concatRevParamEquiv L R σ ((p_L, p_R), k_ext)
      (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))) = p_L cL := by
  unfold concatRevParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

@[simp]
lemma concatRevParamEquiv_apply_inl_inr {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) (cR : R.InternalChord) :
    concatRevParamEquiv L R σ ((p_L, p_R), k_ext)
      (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))) = p_R cR := by
  unfold concatRevParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

@[simp]
lemma concatRevParamEquiv_apply_inr {j k r : ℕ}
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) (a : Fin r) :
    concatRevParamEquiv L R σ ((p_L, p_R), k_ext)
      (concatRevChordEquiv L R σ (Sum.inr a)) = k_ext a := by
  unfold concatRevParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

lemma concatRev_momentum_left {j k r : ℕ} (m : ℝ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    (fun i : Fin j =>
      -(concatRev L R σ).momentum m (concatRevParamEquiv L R σ ((p_L, p_R), k_ext))
        (Fin.castAdd k (Fin.rev i))) =
      L.partialMomentum m p_L k_ext := by
  funext i
  rcases L.partialSlotEquiv.surjective i with ⟨a | ⟨cL, s⟩, rfl⟩
  · have hslot : L.partialSlotEquiv (Sum.inl a) = L.unpaired a := rfl
    rw [hslot, L.partialMomentum_unpaired]
    have hc : Fin.castAdd k (Fin.rev (L.unpaired a)) =
        (concatRevChordEquiv L R σ (Sum.inr a)).1 := rfl
    rw [hc, ChordPairing.momentum_apply_fst, concatRevParamEquiv_apply_inr]
  · have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
    rcases hs with rfl | rfl
    · have hslot : L.partialSlotEquiv (Sum.inr (cL, 0)) = cL.1 := rfl
      rw [hslot, L.partialMomentum_fst]
      have hmate : (concatRev L R σ).mate
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 =
          Fin.castAdd k (Fin.rev cL.1) := by
        change (concatRev L R σ).mate (concatSlotEquiv j k (Sum.inl (L.mate cL.1))) =
          concatSlotEquiv j k (Sum.inl cL.1)
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_neg (L.mate_mate_ne_of_internalChord cL), L.mate_mate]
      rw [← hmate, ChordPairing.momentum_apply_mate, concatRevParamEquiv_apply_inl_inl, neg_neg]
    · have hslot : L.partialSlotEquiv (Sum.inr (cL, 1)) = L.mate cL.1 := rfl
      rw [hslot, L.partialMomentum_mate]
      have hc : Fin.castAdd k (Fin.rev (L.mate cL.1)) =
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 := rfl
      rw [hc, ChordPairing.momentum_apply_fst, concatRevParamEquiv_apply_inl_inl]

lemma concatRev_momentum_right {j k r : ℕ} (m : ℝ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    (fun t : Fin k =>
      (concatRev L R σ).momentum m (concatRevParamEquiv L R σ ((p_L, p_R), k_ext))
        (Fin.natAdd j t)) =
      R.partialMomentum m p_R (k_ext ∘ σ.symm) := by
  funext t
  rcases R.partialSlotEquiv.surjective t with ⟨b | ⟨cR, s⟩, rfl⟩
  · have hslot : R.partialSlotEquiv (Sum.inl b) = R.unpaired b := rfl
    rw [hslot, R.partialMomentum_unpaired]
    have hmate : (concatRev L R σ).mate
        (concatRevChordEquiv L R σ (Sum.inr (σ.symm b))).1 =
        Fin.natAdd j (R.unpaired b) := by
      change (concatRev L R σ).mate (concatSlotEquiv j k (Sum.inl (L.unpaired (σ.symm b)))) =
        concatSlotEquiv j k (Sum.inr (R.unpaired b))
      rw [concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_pos (L.mate_unpaired _), L.unpairedIdx_unpaired, σ.apply_symm_apply]
    rw [← hmate, ChordPairing.momentum_apply_mate, concatRevParamEquiv_apply_inr]
    rfl
  · have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
    rcases hs with rfl | rfl
    · have hslot : R.partialSlotEquiv (Sum.inr (cR, 0)) = cR.1 := rfl
      rw [hslot, R.partialMomentum_fst]
      have hc : Fin.natAdd j cR.1 =
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 := rfl
      rw [hc, ChordPairing.momentum_apply_fst, concatRevParamEquiv_apply_inl_inr]
    · have hslot : R.partialSlotEquiv (Sum.inr (cR, 1)) = R.mate cR.1 := rfl
      rw [hslot, R.partialMomentum_mate]
      have hmate : (concatRev L R σ).mate
          (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 =
          Fin.natAdd j (R.mate cR.1) := by
        change (concatRev L R σ).mate (concatSlotEquiv j k (Sum.inr cR.1)) =
          concatSlotEquiv j k (Sum.inr (R.mate cR.1))
        rw [concatRev_mate_slot]
        dsimp [concatSumFun]
        rw [dif_neg (R.mate_ne_self_of_internalChord cR)]
      rw [← hmate, ChordPairing.momentum_apply_mate, concatRevParamEquiv_apply_inl_inr]

lemma wickChordWeight_concatRev_aux {ι : Type*} {j k r : ℕ} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (β : Fin j → ι) (α' : Fin k → ι)
    (p : (concatRev L R σ).Chord → Fin 3 → ℝ) :
    wickChordWeight m C (concatRev L R σ) (Fin.append (β ∘ Fin.rev) α') p =
      (∏ cL : L.InternalChord,
        massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev)
          (p (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))))) *
      (∏ cR : R.InternalChord,
        massShellWeight m C ![α' cR.1, α' (R.mate cR.1)]
          (p (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))))) *
      (∏ a : Fin r,
        massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))]
          (p (concatRevChordEquiv L R σ (Sum.inr a)))) := by
  have h_inl : ∀ i : Fin j,
      Fin.append (β ∘ Fin.rev) α' (concatSlotEquiv j k (Sum.inl i)) = β i := by
    intro i
    change Fin.append (β ∘ Fin.rev) α' (Fin.castAdd k (Fin.rev i)) = β i
    rw [Fin.append_left]
    simp [Fin.rev_rev]
  have h_inr : ∀ t : Fin k,
      Fin.append (β ∘ Fin.rev) α' (concatSlotEquiv j k (Sum.inr t)) = α' t := by
    intro t
    change Fin.append (β ∘ Fin.rev) α' (Fin.natAdd j t) = α' t
    rw [Fin.append_right]
  unfold wickChordWeight
  rw [← (concatRevChordEquiv L R σ).prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · refine Finset.prod_congr rfl (fun cL _ => ?_)
    have hc1 : (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 =
        concatSlotEquiv j k (Sum.inl (L.mate cL.1)) := rfl
    have hcm : (concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1 =
        concatSlotEquiv j k (Sum.inl cL.1) := by
      rw [hc1, concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_neg (L.mate_mate_ne_of_internalChord cL), L.mate_mate]
    have h_vec :
        ![Fin.append (β ∘ Fin.rev) α' (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1,
          Fin.append (β ∘ Fin.rev) α'
            ((concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inl (Sum.inl cL))).1)] =
        ![β cL.1, β (L.mate cL.1)] ∘ Fin.rev := by
      rw [hcm, hc1, h_inl, h_inl]
      ext s
      fin_cases s <;> rfl
    rw [h_vec]
  · refine Finset.prod_congr rfl (fun cR _ => ?_)
    have hc1 : (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 =
        concatSlotEquiv j k (Sum.inr cR.1) := rfl
    have hcm : (concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inl (Sum.inr cR))).1 =
        concatSlotEquiv j k (Sum.inr (R.mate cR.1)) := by
      rw [hc1, concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_neg (R.mate_ne_self_of_internalChord cR)]
    rw [hcm, hc1, h_inr, h_inr]
  · refine Finset.prod_congr rfl (fun a _ => ?_)
    have hc1 : (concatRevChordEquiv L R σ (Sum.inr a)).1 =
        concatSlotEquiv j k (Sum.inl (L.unpaired a)) := rfl
    have hcm : (concatRev L R σ).mate (concatRevChordEquiv L R σ (Sum.inr a)).1 =
        concatSlotEquiv j k (Sum.inr (R.unpaired (σ a))) := by
      rw [hc1, concatRev_mate_slot]
      dsimp [concatSumFun]
      rw [dif_pos (L.mate_unpaired a), L.unpairedIdx_unpaired]
    rw [hcm, hc1, h_inl, h_inr]

lemma wickChordWeight_concatRev {ι : Type*} {j k r : ℕ} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r))
    (β : Fin j → ι) (α' : Fin k → ι)
    (p_L : L.InternalChord → Fin 3 → ℝ) (p_R : R.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    wickChordWeight m C (concatRev L R σ) (Fin.append (β ∘ Fin.rev) α')
        (concatRevParamEquiv L R σ ((p_L, p_R), k_ext)) =
      (∏ cL : L.InternalChord,
        massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)) *
      (∏ cR : R.InternalChord,
        massShellWeight m C ![α' cR.1, α' (R.mate cR.1)] (p_R cR)) *
      (∏ a : Fin r,
        massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))] (k_ext a)) := by
  rw [wickChordWeight_concatRev_aux]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · refine Finset.prod_congr rfl (fun cL _ => ?_)
    rw [concatRevParamEquiv_apply_inl_inl]
  · refine Finset.prod_congr rfl (fun cR _ => ?_)
    rw [concatRevParamEquiv_apply_inl_inr]
  · refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [concatRevParamEquiv_apply_inr]

end PartialPairing

structure PartialMomentumBound (m : ℝ) (j : ℕ) (φ : (Fin j → Fin 4 → ℝ) → ℂ) : Prop where
  measurable_φ : Measurable φ
  bound : ∀ (r : ℕ) (L : PartialPairing j r),
    ∃ (K : ℝ) (u : L.InternalChord → (Fin 3 → ℝ) → ℝ) (v : Fin r → (Fin 3 → ℝ) → ℝ),
      0 ≤ K ∧
      (∀ c, Integrable (u c) volume) ∧
      (∀ a, Measurable (v a)) ∧
      (∀ a, Integrable (fun q => (v a q) ^ 2) volume) ∧
      (∀ c q, 0 ≤ u c q) ∧
      (∀ a q, 0 ≤ v a q) ∧
      ∀ (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
        ‖φ (L.partialMomentum m p_int k_ext)‖ ≤
          K * (∏ c, u c (p_int c)) * (∏ a, v a (k_ext a))

noncomputable def fockPartialIntWeight {ι : Type*} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) {j r : ℕ} (α : Fin j → ι)
    (L : PartialPairing j r) (p_int : L.InternalChord → Fin 3 → ℝ) : ℂ :=
  ∏ c : L.InternalChord, massShellWeight m C ![α c.1, α (L.mate c.1)] (p_int c)

lemma measurable_fockPartialIntWeight {ι : Type*} {m : ℝ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) (L : PartialPairing j r) :
    Measurable (fockPartialIntWeight m C α L) :=
  Finset.measurable_prod Finset.univ (fun c _ =>
    (measurable_massShellWeight hC ![α c.1, α (L.mate c.1)]).comp (measurable_pi_apply c))

lemma exists_norm_fockPartialIntWeight_le {ι : Type*} {m : ℝ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) (L : PartialPairing j r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p_int : L.InternalChord → Fin 3 → ℝ,
      ‖fockPartialIntWeight m C α L p_int‖ ≤ B := by
  let Bc : L.InternalChord → ℝ := fun c => Classical.choose (hC.2 ![α c.1, α (L.mate c.1)])
  have hBc : ∀ c : L.InternalChord,
      0 ≤ Bc c ∧ ∀ q : Fin 3 → ℝ, ‖massShellWeight m C ![α c.1, α (L.mate c.1)] q‖ ≤ Bc c :=
    fun c => Classical.choose_spec (hC.2 ![α c.1, α (L.mate c.1)])
  refine ⟨∏ c : L.InternalChord, Bc c, Finset.prod_nonneg (fun c _ => (hBc c).1), fun p_int => ?_⟩
  unfold fockPartialIntWeight
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun c _ => (hBc c).2 (p_int c))

lemma integrable_fockPartialIntegrand {ι : Type*} {m : ℝ}
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) (L : PartialPairing j r)
    (k_ext : Fin r → Fin 3 → ℝ) :
    Integrable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
      fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int k_ext)) volume := by
  rcases exists_norm_fockPartialIntWeight_le hC α L with ⟨B, hB_nn, hB⟩
  rcases hφ.bound r L with ⟨K, u, v, hK_nn, hu_int, _, _, _, hv_nn, hbound⟩
  let Cv : ℝ := B * K * ∏ a : Fin r, v a (k_ext a)
  have h_dom : Integrable
      (fun p_int : L.InternalChord → Fin 3 → ℝ => Cv * ∏ c : L.InternalChord, u c (p_int c))
      volume :=
    (Integrable.fintype_prod (f := u) hu_int).const_mul Cv
  have h_meas_pm : Measurable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
      L.partialMomentum m p_int k_ext) :=
    (L.continuous_partialMomentum_uncurry m |>.comp
      (continuous_id.prodMk continuous_const)).measurable
  have h_meas : Measurable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
      fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int k_ext)) :=
    (measurable_fockPartialIntWeight hC α L).mul (hφ.measurable_φ.comp h_meas_pm)
  refine h_dom.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall (fun p_int => ?_))
  rw [norm_mul]
  calc ‖fockPartialIntWeight m C α L p_int‖ * ‖φ (L.partialMomentum m p_int k_ext)‖
      ≤ B * (K * (∏ c, u c (p_int c)) * (∏ a, v a (k_ext a))) :=
        mul_le_mul (hB p_int) (hbound p_int k_ext) (norm_nonneg _) hB_nn
    _ = Cv * ∏ c, u c (p_int c) := by dsimp [Cv]; ring

lemma norm_eta_pow {η : ℂ} (hη : η = 1 ∨ η = -1) (n : ℕ) : ‖η ^ n‖ = 1 := by
  rcases hη with rfl | rfl <;> simp

noncomputable def fockPartialTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) {j r : ℕ} (α : Fin j → ι)
    (φ : (Fin j → Fin 4 → ℝ) → ℂ) (L : PartialPairing j r)
    (x : FockSectorDom M_mode.ν r) : ℂ :=
  η ^ L.partialCross *
    (∏ a : Fin r, M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))) *
    ∫ p_int : L.InternalChord → Fin 3 → ℝ,
      fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)

lemma measurable_fockPartialTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) (L : PartialPairing j r) :
    Measurable (fockPartialTerm M_mode α φ L) := by
  have h_w : Measurable (fun x : FockSectorDom M_mode.ν r =>
      ∏ a : Fin r, M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))) := by
    refine Finset.measurable_prod Finset.univ (fun a _ => ?_)
    have h_sum : ∀ x : FockSectorDom M_mode.ν r,
        M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a)) =
          ∑ s : Fin M_mode.ν,
            (if x.2 a = s then (1 : ℂ) else 0) * M_mode.w s (x.1 a) (α (L.unpaired a)) := by
      intro x
      simp
    simp_rw [h_sum]
    refine Finset.measurable_sum Finset.univ (fun s _ => ?_)
    have h_ind : Measurable (fun x : FockSectorDom M_mode.ν r =>
        if x.2 a = s then (1 : ℂ) else 0) :=
      Measurable.ite
        ((measurableSet_singleton s).preimage ((measurable_pi_apply a).comp measurable_snd))
        measurable_const measurable_const
    exact h_ind.mul
      ((M_mode.measurable_w s (α (L.unpaired a))).comp
        ((measurable_pi_apply a).comp measurable_fst))
  have h_joint : Measurable
      (fun pk : (L.InternalChord → Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
        fockPartialIntWeight m C α L pk.1 * φ (L.partialMomentum m pk.1 pk.2)) :=
    ((measurable_fockPartialIntWeight hC α L).comp measurable_fst).mul
      (hφ.measurable_φ.comp (L.measurable_partialMomentum_uncurry m))
  have h_int : Measurable (fun k_ext : Fin r → Fin 3 → ℝ =>
      ∫ p_int : L.InternalChord → Fin 3 → ℝ,
        fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int k_ext)) :=
    (h_joint.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable
  exact (measurable_const.mul h_w).mul (h_int.comp measurable_fst)

lemma memLp_fockPartialTerm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) (L : PartialPairing j r) :
    MemLp (fockPartialTerm M_mode α φ L) 2 (fockSectorMeasure M_mode.ν r) := by
  have hm := measurable_fockPartialTerm M_mode hC α hφ L
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  rcases exists_norm_fockPartialIntWeight_le hC α L with ⟨B, hB_nn, hB⟩
  rcases hφ.bound r L with ⟨K, u, v, hK_nn, hu_int, _, hv_sq_int, hu_nn, hv_nn, hbound⟩
  let Iu : ℝ := ∫ p_int : L.InternalChord → Fin 3 → ℝ, ∏ c, u c (p_int c)
  have hIu_nn : 0 ≤ Iu :=
    integral_nonneg (fun p_int => Finset.prod_nonneg (fun c _ => hu_nn c (p_int c)))
  let CL : ℝ := M_mode.M ^ r * (B * K * Iu)
  have hCL_nn : 0 ≤ CL :=
    mul_nonneg (pow_nonneg M_mode.hM r) (mul_nonneg (mul_nonneg hB_nn hK_nn) hIu_nn)
  have h_pt : ∀ x : FockSectorDom M_mode.ν r,
      ‖fockPartialTerm M_mode α φ L x‖ ≤ CL * ∏ a : Fin r, v a (x.1 a) := by
    intro x
    unfold fockPartialTerm
    rw [norm_mul, norm_mul, norm_eta_pow M_mode.hη, one_mul, norm_prod]
    have hw_le : (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖) ≤ M_mode.M ^ r := by
      calc (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖)
          ≤ ∏ _a : Fin r, M_mode.M :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _)
              (fun a _ => M_mode.norm_w_le _ _ _)
        _ = M_mode.M ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hint_le :
        ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
          fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖ ≤
          (B * K * Iu) * ∏ a : Fin r, v a (x.1 a) := by
      have h_dom_int : Integrable (fun p_int : L.InternalChord → Fin 3 → ℝ =>
          (B * K * ∏ a : Fin r, v a (x.1 a)) * ∏ c, u c (p_int c)) volume :=
        (Integrable.fintype_prod (f := u) hu_int).const_mul _
      calc ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
            fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖
          ≤ ∫ p_int : L.InternalChord → Fin 3 → ℝ,
              ‖fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ p_int : L.InternalChord → Fin 3 → ℝ,
              (B * K * ∏ a : Fin r, v a (x.1 a)) * ∏ c, u c (p_int c) := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) h_dom_int
              (Filter.Eventually.of_forall (fun p_int => ?_))
            dsimp only
            rw [norm_mul]
            calc ‖fockPartialIntWeight m C α L p_int‖ * ‖φ (L.partialMomentum m p_int x.1)‖
                ≤ B * (K * (∏ c, u c (p_int c)) * (∏ a, v a (x.1 a))) :=
                  mul_le_mul (hB p_int) (hbound p_int x.1) (norm_nonneg _) hB_nn
              _ = (B * K * ∏ a : Fin r, v a (x.1 a)) * ∏ c, u c (p_int c) := by ring
        _ = (B * K * ∏ a : Fin r, v a (x.1 a)) * Iu := integral_const_mul _ _
        _ = (B * K * Iu) * ∏ a : Fin r, v a (x.1 a) := by ring
    calc (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖) *
          ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
            fockPartialIntWeight m C α L p_int * φ (L.partialMomentum m p_int x.1)‖
        ≤ M_mode.M ^ r * ((B * K * Iu) * ∏ a : Fin r, v a (x.1 a)) :=
          mul_le_mul hw_le hint_le (norm_nonneg _) (pow_nonneg M_mode.hM r)
      _ = CL * ∏ a : Fin r, v a (x.1 a) := by dsimp [CL]; ring
  have h_dom_k : Integrable
      (fun k_ext : Fin r → Fin 3 → ℝ => CL ^ 2 * ∏ a : Fin r, (v a (k_ext a)) ^ 2) volume :=
    (Integrable.fintype_prod (f := fun a q => (v a q) ^ 2) hv_sq_int).const_mul (CL ^ 2)
  have h_dom : Integrable
      (fun x : FockSectorDom M_mode.ν r =>
        (CL ^ 2 * ∏ a : Fin r, (v a (x.1 a)) ^ 2) * (1 : ℝ))
      (fockSectorMeasure M_mode.ν r) :=
    h_dom_k.mul_prod (integrable_const (1 : ℝ))
  refine h_dom.mono' ((hm.norm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_one, Finset.prod_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h_pt x) 2

noncomputable def fockRawSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) {j : ℕ} (r : ℕ) (α : Fin j → ι)
    (φ : (Fin j → Fin 4 → ℝ) → ℂ) (x : FockSectorDom M_mode.ν r) : ℂ :=
  ∑ L : PartialPairing j r, fockPartialTerm M_mode α φ L x

lemma measurable_fockRawSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j : ℕ} (r : ℕ) (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) :
    Measurable (fockRawSector M_mode r α φ) :=
  Finset.measurable_sum Finset.univ (fun L _ => measurable_fockPartialTerm M_mode hC α hφ L)

lemma memLp_fockRawSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j : ℕ} (r : ℕ) (α : Fin j → ι) {φ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ : PartialMomentumBound m j φ) :
    MemLp (fockRawSector M_mode r α φ) 2 (fockSectorMeasure M_mode.ν r) :=
  memLp_finsetSum Finset.univ (fun L _ => memLp_fockPartialTerm M_mode hC α hφ L)

noncomputable def fockMomentumVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (j : ℕ) (α : Fin j → ι) (φ : (Fin j → Fin 4 → ℝ) → ℂ)
    (hφ : PartialMomentumBound m j φ) : FockHilbert M_mode.ν :=
  ∑ r ∈ Finset.range (j + 1),
    liftSectorToFock M_mode.ν r
      (symmSector M_mode.ν r η (fockRawSector M_mode r α φ))
      (measurable_symmSector η (measurable_fockRawSector M_mode hC r α hφ))
      (memLp_symmSector η (memLp_fockRawSector M_mode hC r α hφ))

lemma star_massShellWeight_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} (S : StarStructure R_rep) (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (α₀ α₁ : ι) (q : Fin 3 → ℝ) :
    star (massShellWeight m C ![α₀, α₁] q) =
      ∑ γ : Fin 2 → ι, (S.C α₀ (γ 0) * S.C α₁ (γ 1)) *
        massShellWeight m C (γ ∘ Fin.rev) q := by
  unfold massShellWeight
  rw [Complex.star_def, map_mul, map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal,
    ← Complex.star_def, hC_herm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Fin.prod_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

lemma integrable_mul_of_sq {u v : (Fin 3 → ℝ) → ℝ}
    (hu_meas : AEStronglyMeasurable u volume) (hv_meas : AEStronglyMeasurable v volume)
    (hu_sq : Integrable (fun q => (u q) ^ 2) volume)
    (hv_sq : Integrable (fun q => (v q) ^ 2) volume) :
    Integrable (fun q : Fin 3 → ℝ => u q * v q) volume := by
  have h_dom : Integrable (fun q : Fin 3 → ℝ => ((u q) ^ 2 + (v q) ^ 2) / 2) volume :=
    (hu_sq.add hv_sq).div_const 2
  refine h_dom.mono' (hu_meas.mul hv_meas) (Filter.Eventually.of_forall (fun q => ?_))
  rw [Real.norm_eq_abs, abs_mul]
  have h_amgm : 2 * (|u q| * |v q|) ≤ |u q| ^ 2 + |v q| ^ 2 := by
    nlinarith [sq_nonneg (|u q| - |v q|)]
  rw [sq_abs, sq_abs] at h_amgm
  linarith

theorem inner_fockPartialTerm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    {j k r : ℕ} (α : Fin j → ι) (α' : Fin k → ι)
    {φ₁ : (Fin j → Fin 4 → ℝ) → ℂ} {φ₂ : (Fin k → Fin 4 → ℝ) → ℂ}
    (hφ₁ : PartialMomentumBound m j φ₁) (hφ₂ : PartialMomentumBound m k φ₂)
    (L : PartialPairing j r) (R : PartialPairing k r) (σ : Equiv.Perm (Fin r)) :
    η ^ permInversions σ *
      (∫ x : FockSectorDom M_mode.ν r,
        star (fockPartialTerm M_mode α φ₁ L x) *
          fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm)
        ∂(fockSectorMeasure M_mode.ν r)) =
    ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
      ((η ^ (PartialPairing.concatRev L R σ).cross) *
        ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
          wickChordWeight m C (PartialPairing.concatRev L R σ) (Fin.append (β ∘ Fin.rev) α') p *
            (star (φ₁ (fun i =>
                -(PartialPairing.concatRev L R σ).momentum m p (Fin.castAdd k (Fin.rev i)))) *
              φ₂ (fun t =>
                (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t)))) := by
  let P := PartialPairing.concatRev L R σ
  have hm1 := memLp_fockPartialTerm M_mode hC α hφ₁ L
  have hm2 := (memLp_fockPartialTerm M_mode hC α' hφ₂ R).comp_measurePreserving
    (measurePreserving_fockSectorPermEquiv M_mode.ν r σ.symm)
  have h_x_int : Integrable
      (fun x : FockSectorDom M_mode.ν r =>
        star (fockPartialTerm M_mode α φ₁ L x) *
          fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm))
      (fockSectorMeasure M_mode.ν r) := by
    have hi := L2.integrable_inner (𝕜 := ℂ) (hm1.toLp _) (hm2.toLp _)
    refine hi.congr ?_
    filter_upwards [hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [mul_comm]
  unfold fockSectorMeasure at h_x_int ⊢
  rw [integral_prod _ h_x_int]
  simp_rw [integral_count]
  let IL : (Fin r → Fin 3 → ℝ) → ℂ := fun k_ext =>
    ∫ p_L : L.InternalChord → Fin 3 → ℝ,
      fockPartialIntWeight m C α L p_L * φ₁ (L.partialMomentum m p_L k_ext)
  let IR : (Fin r → Fin 3 → ℝ) → ℂ := fun k_ext =>
    ∫ p_R : R.InternalChord → Fin 3 → ℝ,
      fockPartialIntWeight m C α' R p_R * φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm))
  have h_spin_sum : ∀ k_ext : Fin r → Fin 3 → ℝ,
      (∑ s : Fin r → Fin M_mode.ν,
        star (fockPartialTerm M_mode α φ₁ L (k_ext, s)) *
          fockPartialTerm M_mode α' φ₂ R (k_ext ∘ σ.symm, s ∘ σ.symm)) =
      (η ^ L.partialCross * η ^ R.partialCross) *
        (∏ a : Fin r,
          ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
            massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
        (star (IL k_ext) * IR k_ext) := by
    intro k_ext
    have h_term : ∀ s : Fin r → Fin M_mode.ν,
        star (fockPartialTerm M_mode α φ₁ L (k_ext, s)) *
          fockPartialTerm M_mode α' φ₂ R (k_ext ∘ σ.symm, s ∘ σ.symm) =
        ((η ^ L.partialCross * η ^ R.partialCross) * (star (IL k_ext) * IR k_ext)) *
          ∏ a : Fin r,
            star (M_mode.w (s a) (k_ext a) (α (L.unpaired a))) *
              M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))) := by
      intro s
      unfold fockPartialTerm
      change star (η ^ L.partialCross *
          (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α (L.unpaired a))) * IL k_ext) *
        (η ^ R.partialCross *
          (∏ b : Fin r, M_mode.w (s (σ.symm b)) (k_ext (σ.symm b)) (α' (R.unpaired b))) *
          IR k_ext) = _
      have h_reidx :
          (∏ b : Fin r, M_mode.w (s (σ.symm b)) (k_ext (σ.symm b)) (α' (R.unpaired b))) =
          ∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))) := by
        rw [← Equiv.prod_comp σ]
        simp
      rw [h_reidx, star_mul', star_mul', star_eta_pow M_mode.hη, star_prod]
      have h_pmul :
          (∏ a : Fin r, star (M_mode.w (s a) (k_ext a) (α (L.unpaired a)))) *
            (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a)))) =
          ∏ a : Fin r,
            star (M_mode.w (s a) (k_ext a) (α (L.unpaired a))) *
              M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))) :=
        Finset.prod_mul_distrib.symm
      calc η ^ L.partialCross *
            (∏ x : Fin r, star (M_mode.w (s x) (k_ext x) (α (L.unpaired x)))) *
            star (IL k_ext) *
            (η ^ R.partialCross *
              (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a)))) * IR k_ext)
          = ((η ^ L.partialCross * η ^ R.partialCross) * (star (IL k_ext) * IR k_ext)) *
              ((∏ a : Fin r, star (M_mode.w (s a) (k_ext a) (α (L.unpaired a)))) *
                (∏ a : Fin r, M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a))))) := by ring
        _ = _ := by rw [h_pmul]
    simp_rw [h_term]
    have h_ps :
        (∑ s : Fin r → Fin M_mode.ν,
          ∏ a : Fin r,
            star (M_mode.w (s a) (k_ext a) (α (L.unpaired a))) *
              M_mode.w (s a) (k_ext a) (α' (R.unpaired (σ a)))) =
        ∏ a : Fin r, ∑ s_a : Fin M_mode.ν,
          star (M_mode.w s_a (k_ext a) (α (L.unpaired a))) *
            M_mode.w s_a (k_ext a) (α' (R.unpaired (σ a))) :=
      (Fintype.prod_sum (fun (a : Fin r) (s_a : Fin M_mode.ν) =>
        star (M_mode.w s_a (k_ext a) (α (L.unpaired a))) *
          M_mode.w s_a (k_ext a) (α' (R.unpaired (σ a))))).symm
    have h_fw :
        (∏ a : Fin r, ∑ s_a : Fin M_mode.ν,
          star (M_mode.w s_a (k_ext a) (α (L.unpaired a))) *
            M_mode.w s_a (k_ext a) (α' (R.unpaired (σ a)))) =
        ∏ a : Fin r, ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
          massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a) :=
      Finset.prod_congr rfl (fun a _ => (M_mode.factor_weight _ _ _).symm)
    rw [← Finset.mul_sum, h_ps, h_fw]
    ring
  simp_rw [h_spin_sum]
  have h_joint_int : ∀ β : Fin j → ι,
      Integrable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
              (PartialPairing.concatRevParamEquiv L R σ q) *
            (star (φ₁ (L.partialMomentum m q.1.1 q.2)) *
              φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm)))) volume := by
    intro β
    rcases exists_norm_wickChordWeight_le hC P (Fin.append (β ∘ Fin.rev) α') with ⟨Bw, hBw_nn, hBw⟩
    rcases hφ₁.bound r L with ⟨K₁, u₁, v₁, hK₁_nn, hu₁_int, hv₁_meas, hv₁_sq, hu₁_nn, hv₁_nn, hb₁⟩
    rcases hφ₂.bound r R with ⟨K₂, u₂, v₂, hK₂_nn, hu₂_int, hv₂_meas, hv₂_sq, _, hv₂_nn, hb₂⟩
    let C0 : ℝ := Bw * K₁ * K₂
    have hC0_nn : 0 ≤ C0 := mul_nonneg (mul_nonneg hBw_nn hK₁_nn) hK₂_nn
    have h_dom_L : Integrable
        (fun p_L : L.InternalChord → Fin 3 → ℝ => C0 * ∏ cL, u₁ cL (p_L cL)) volume :=
      (Integrable.fintype_prod (f := u₁) hu₁_int).const_mul C0
    have h_dom_R : Integrable
        (fun p_R : R.InternalChord → Fin 3 → ℝ => ∏ cR, u₂ cR (p_R cR)) volume :=
      Integrable.fintype_prod (f := u₂) hu₂_int
    have h_dom_k : Integrable
        (fun k_ext : Fin r → Fin 3 → ℝ => ∏ a : Fin r, (v₁ a (k_ext a) * v₂ (σ a) (k_ext a)))
        volume := by
      refine Integrable.fintype_prod (f := fun a q => v₁ a q * v₂ (σ a) q) (fun a => ?_)
      exact integrable_mul_of_sq (hv₁_meas a).aestronglyMeasurable
        (hv₂_meas (σ a)).aestronglyMeasurable (hv₁_sq a) (hv₂_sq (σ a))
    have h_dom : Integrable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          ((C0 * ∏ cL, u₁ cL (q.1.1 cL)) * (∏ cR, u₂ cR (q.1.2 cR))) *
            (∏ a : Fin r, (v₁ a (q.2 a) * v₂ (σ a) (q.2 a)))) volume :=
      (h_dom_L.mul_prod h_dom_R).mul_prod h_dom_k
    have h_meas_w : Measurable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
            (PartialPairing.concatRevParamEquiv L R σ q)) :=
      (measurable_wickChordWeight hC P (Fin.append (β ∘ Fin.rev) α')).comp
        (PartialPairing.concatRevParamEquiv L R σ).measurable
    have h_meas_1 : Measurable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          star (φ₁ (L.partialMomentum m q.1.1 q.2))) :=
      continuous_star.measurable.comp <| hφ₁.measurable_φ.comp <|
        ((L.continuous_partialMomentum_uncurry m).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).measurable
    have h_cont_kσ : Continuous
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) => q.2 ∘ σ.symm) :=
      continuous_pi (fun b => (continuous_apply (σ.symm b)).comp continuous_snd)
    have h_meas_2 : Measurable
        (fun q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ) =>
          φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))) :=
      hφ₂.measurable_φ.comp <|
        ((R.continuous_partialMomentum_uncurry m).comp
          ((continuous_snd.comp continuous_fst).prodMk h_cont_kσ)).measurable
    refine h_dom.mono' (h_meas_w.mul (h_meas_1.mul h_meas_2)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => ?_))
    rw [norm_mul, norm_mul, norm_star]
    have hv_reidx : (∏ b : Fin r, v₂ b (q.2 (σ.symm b))) = ∏ a : Fin r, v₂ (σ a) (q.2 a) := by
      rw [← Equiv.prod_comp σ]
      simp
    have h1 := hb₁ q.1.1 q.2
    have h2 := hb₂ q.1.2 (q.2 ∘ σ.symm)
    dsimp only [Function.comp_apply] at h2
    rw [hv_reidx] at h2
    have h12 : ‖φ₁ (L.partialMomentum m q.1.1 q.2)‖ *
        ‖φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))‖ ≤
        (K₁ * (∏ cL, u₁ cL (q.1.1 cL)) * (∏ a, v₁ a (q.2 a))) *
          (K₂ * (∏ cR, u₂ cR (q.1.2 cR)) * (∏ a, v₂ (σ a) (q.2 a))) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by
        exact mul_nonneg (mul_nonneg hK₁_nn
          (Finset.prod_nonneg (fun c _ => hu₁_nn c (q.1.1 c))))
          (Finset.prod_nonneg (fun a _ => hv₁_nn a (q.2 a))))
    calc ‖wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
            (PartialPairing.concatRevParamEquiv L R σ q)‖ *
          (‖φ₁ (L.partialMomentum m q.1.1 q.2)‖ *
            ‖φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))‖)
        ≤ Bw * ((K₁ * (∏ cL, u₁ cL (q.1.1 cL)) * (∏ a, v₁ a (q.2 a))) *
            (K₂ * (∏ cR, u₂ cR (q.1.2 cR)) * (∏ a, v₂ (σ a) (q.2 a)))) :=
          mul_le_mul (hBw _) h12 (by positivity) hBw_nn
      _ = ((C0 * ∏ cL, u₁ cL (q.1.1 cL)) * (∏ cR, u₂ cR (q.1.2 cR))) *
            ((∏ a : Fin r, v₁ a (q.2 a)) * (∏ a : Fin r, v₂ (σ a) (q.2 a))) := by
          dsimp [C0]; ring
      _ = ((C0 * ∏ cL, u₁ cL (q.1.1 cL)) * (∏ cR, u₂ cR (q.1.2 cR))) *
            (∏ a : Fin r, (v₁ a (q.2 a) * v₂ (σ a) (q.2 a))) := by
          rw [Finset.prod_mul_distrib]
  have h_k_eq : ∀ k_ext : Fin r → Fin 3 → ℝ,
      (η ^ L.partialCross * η ^ R.partialCross) *
        (∏ a : Fin r,
          ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
            massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
        (star (IL k_ext) * IR k_ext) =
      ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        ((η ^ L.partialCross * η ^ R.partialCross) *
          ∫ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
              (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) := by
    intro k_ext
    have hIL_star : star (IL k_ext) =
        ∫ p_L : L.InternalChord → Fin 3 → ℝ,
          star (fockPartialIntWeight m C α L p_L) *
            star (φ₁ (L.partialMomentum m p_L k_ext)) := by
      dsimp only [IL]
      rw [Complex.star_def, ← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p_L => ?_))
      simp
    rw [hIL_star]
    dsimp only [IR]
    rw [← integral_mul_const]
    simp_rw [← integral_const_mul]
    have h_pLR_int : Integrable
        (fun pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ) =>
          (η ^ L.partialCross * η ^ R.partialCross) *
            (∏ a : Fin r,
              ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
                massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
            ((star (fockPartialIntWeight m C α L pq.1) *
                star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
              (fockPartialIntWeight m C α' R pq.2 *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))))) volume := by
      have hi0 := integrable_fockPartialIntegrand hC α hφ₁ L k_ext
      have hi1 : Integrable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
          star (fockPartialIntWeight m C α L p_L * φ₁ (L.partialMomentum m p_L k_ext))) volume :=
        hi0.mono hi0.1.star (Filter.Eventually.of_forall (fun _ => (norm_star _).le))
      have hi2 := integrable_fockPartialIntegrand hC α' hφ₂ R (k_ext ∘ σ.symm)
      have hp := (hi1.mul_prod hi2).const_mul
        ((η ^ L.partialCross * η ^ R.partialCross) *
          ∏ a : Fin r,
            ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
              massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a))
      refine hp.congr (Filter.Eventually.of_forall (fun pq => ?_))
      simp [star_mul']
    have h_fub :
        (∫ p_L : L.InternalChord → Fin 3 → ℝ,
          ∫ p_R : R.InternalChord → Fin 3 → ℝ,
            (η ^ L.partialCross * η ^ R.partialCross) *
              (∏ a : Fin r,
                ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
                  massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
              ((star (fockPartialIntWeight m C α L p_L) *
                  star (φ₁ (L.partialMomentum m p_L k_ext))) *
                (fockPartialIntWeight m C α' R p_R *
                  φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm))))) =
        ∫ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
          (η ^ L.partialCross * η ^ R.partialCross) *
            (∏ a : Fin r,
              ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
                massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
            ((star (fockPartialIntWeight m C α L pq.1) *
                star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
              (fockPartialIntWeight m C α' R pq.2 *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) :=
      (integral_prod _ h_pLR_int).symm
    rw [h_fub]
    have h_alg_pq : ∀ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
        (η ^ L.partialCross * η ^ R.partialCross) *
          (∏ a : Fin r,
            ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
              massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) *
          ((star (fockPartialIntWeight m C α L pq.1) *
              star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
            (fockPartialIntWeight m C α' R pq.2 *
              φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) =
        ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ L.partialCross * η ^ R.partialCross) *
            (wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
              (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))))) := by
      intro ⟨p_L, p_R⟩
      have h_star_L : star (fockPartialIntWeight m C α L p_L) =
          ∏ cL : L.InternalChord,
            ∑ γ : Fin 2 → ι, (S.C (α cL.1) (γ 0) * S.C (α (L.mate cL.1)) (γ 1)) *
              massShellWeight m C (γ ∘ Fin.rev) (p_L cL) := by
        unfold fockPartialIntWeight
        rw [star_prod]
        refine Finset.prod_congr rfl (fun cL _ => ?_)
        exact star_massShellWeight_eq S m C hC_herm (α cL.1) (α (L.mate cL.1)) (p_L cL)
      have h_cross_sum :
          (∏ a : Fin r,
            ∑ δ_a : ι, S.C (α (L.unpaired a)) δ_a *
              massShellWeight m C ![δ_a, α' (R.unpaired (σ a))] (k_ext a)) =
          ∑ δ : Fin r → ι,
            (∏ a : Fin r, S.C (α (L.unpaired a)) (δ a)) *
              (∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a)) := by
        rw [Fintype.prod_sum]
        refine Finset.sum_congr rfl (fun δ _ => Finset.prod_mul_distrib)
      have h_factor := (L.sum_prod_partial_factor
        (fun i b => S.C (α i) b)
        (fun δ => ∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a))
        (fun cL γ => massShellWeight m C (γ ∘ Fin.rev) (p_L cL))).symm
      rw [h_star_L, h_cross_sum]
      calc (η ^ L.partialCross * η ^ R.partialCross) *
            (∑ δ : Fin r → ι,
              (∏ a : Fin r, S.C (α (L.unpaired a)) (δ a)) *
                ∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a)) *
            (((∏ cL : L.InternalChord,
                ∑ γ : Fin 2 → ι, (S.C (α cL.1) (γ 0) * S.C (α (L.mate cL.1)) (γ 1)) *
                  massShellWeight m C (γ ∘ Fin.rev) (p_L cL)) *
                star (φ₁ (L.partialMomentum m p_L k_ext))) *
              (fockPartialIntWeight m C α' R p_R *
                φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm))))
          = ((∑ δ : Fin r → ι,
              (∏ a : Fin r, S.C (α (L.unpaired a)) (δ a)) *
                ∏ a : Fin r, massShellWeight m C ![δ a, α' (R.unpaired (σ a))] (k_ext a)) *
              (∏ cL : L.InternalChord,
                ∑ γ : Fin 2 → ι, (S.C (α cL.1) (γ 0) * S.C (α (L.mate cL.1)) (γ 1)) *
                  massShellWeight m C (γ ∘ Fin.rev) (p_L cL))) *
            ((η ^ L.partialCross * η ^ R.partialCross) *
              fockPartialIntWeight m C α' R p_R *
              (star (φ₁ (L.partialMomentum m p_L k_ext)) *
                φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm)))) := by ring
        _ = (∑ β : Fin j → ι,
              (∏ i : Fin j, S.C (α i) (β i)) *
                (∏ a : Fin r,
                  massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))] (k_ext a)) *
                (∏ cL : L.InternalChord,
                  massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL))) *
            ((η ^ L.partialCross * η ^ R.partialCross) *
              fockPartialIntWeight m C α' R p_R *
              (star (φ₁ (L.partialMomentum m p_L k_ext)) *
                φ₂ (R.partialMomentum m p_R (k_ext ∘ σ.symm)))) := by
            rw [h_factor]
        _ = _ := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun β _ => ?_)
            dsimp only [P]
            rw [PartialPairing.wickChordWeight_concatRev]
            unfold fockPartialIntWeight
            ring
    have h_each_pq_int : ∀ β : Fin j → ι,
        Integrable
          (fun pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ) =>
            (∏ i : Fin j, S.C (α i) (β i)) *
              ((η ^ L.partialCross * η ^ R.partialCross) *
                (wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                    (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
                  (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                    φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))))) volume := by
      intro β
      have hw_eq : ∀ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
              (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
            (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
              φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))) =
          (∏ a : Fin r,
            massShellWeight m C ![β (L.unpaired a), α' (R.unpaired (σ a))] (k_ext a)) *
          (((∏ cL : L.InternalChord,
              massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (pq.1 cL)) *
              star (φ₁ (L.partialMomentum m pq.1 k_ext))) *
            (fockPartialIntWeight m C α' R pq.2 *
              φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm)))) := by
        intro pq
        dsimp only [P, fockPartialIntWeight]
        rw [PartialPairing.wickChordWeight_concatRev]
        ring
      simp_rw [hw_eq]
      have hL_rev : Integrable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
          (∏ cL : L.InternalChord,
            massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)) *
            star (φ₁ (L.partialMomentum m p_L k_ext))) volume := by
        rcases hφ₁.bound r L with ⟨K₁, u₁, v₁, hK₁_nn, hu₁_int, _, _, _, hv₁_nn, hb₁⟩
        let Bc : L.InternalChord → ℝ := fun cL =>
          Classical.choose (hC.2 (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev))
        have hBc : ∀ cL : L.InternalChord, 0 ≤ Bc cL ∧ ∀ q : Fin 3 → ℝ,
            ‖massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) q‖ ≤ Bc cL :=
          fun cL => Classical.choose_spec (hC.2 (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev))
        let CL' : ℝ := (∏ cL, Bc cL) * K₁ * (∏ a, v₁ a (k_ext a))
        have h_dom' : Integrable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
            CL' * ∏ cL, u₁ cL (p_L cL)) volume :=
          (Integrable.fintype_prod (f := u₁) hu₁_int).const_mul CL'
        have h_m' : Measurable (fun p_L : L.InternalChord → Fin 3 → ℝ =>
            (∏ cL : L.InternalChord,
              massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)) *
              star (φ₁ (L.partialMomentum m p_L k_ext))) :=
          (Finset.measurable_prod Finset.univ (fun cL _ =>
            (measurable_massShellWeight hC _).comp (measurable_pi_apply cL))).mul
            (continuous_star.measurable.comp (hφ₁.measurable_φ.comp
              ((L.continuous_partialMomentum_uncurry m |>.comp
                (continuous_id.prodMk continuous_const)).measurable)))
        refine h_dom'.mono' h_m'.aestronglyMeasurable (Filter.Eventually.of_forall (fun p_L => ?_))
        rw [norm_mul, norm_star, norm_prod]
        have hB_le : (∏ cL, ‖massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)‖) ≤
            ∏ cL, Bc cL :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun cL _ => (hBc cL).2 (p_L cL))
        calc (∏ cL, ‖massShellWeight m C (![β cL.1, β (L.mate cL.1)] ∘ Fin.rev) (p_L cL)‖) *
              ‖φ₁ (L.partialMomentum m p_L k_ext)‖
            ≤ (∏ cL, Bc cL) * (K₁ * (∏ cL, u₁ cL (p_L cL)) * (∏ a, v₁ a (k_ext a))) :=
              mul_le_mul hB_le (hb₁ p_L k_ext) (norm_nonneg _)
                (Finset.prod_nonneg (fun cL _ => (hBc cL).1))
          _ = CL' * ∏ cL, u₁ cL (p_L cL) := by dsimp [CL']; ring
      have hR_int := integrable_fockPartialIntegrand hC α' hφ₂ R (k_ext ∘ σ.symm)
      exact (((hL_rev.mul_prod hR_int).const_mul _).const_mul _).const_mul _
    simp_rw [h_alg_pq]
    rw [integral_finsetSum Finset.univ (fun β _ => h_each_pq_int β)]
  simp_rw [h_k_eq]
  have h_k_int : ∀ β : Fin j → ι,
      Integrable (fun k_ext : Fin r → Fin 3 → ℝ =>
        (∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ L.partialCross * η ^ R.partialCross) *
            ∫ pq : (L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ),
              wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
                  (PartialPairing.concatRevParamEquiv L R σ (pq, k_ext)) *
                (star (φ₁ (L.partialMomentum m pq.1 k_ext)) *
                  φ₂ (R.partialMomentum m pq.2 (k_ext ∘ σ.symm))))) volume :=
    fun β => ((h_joint_int β).integral_prod_right.const_mul _).const_mul _
  rw [integral_finsetSum Finset.univ (fun β _ => h_k_int β), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [integral_const_mul, integral_const_mul, ← integral_prod_symm _ (h_joint_int β)]
  change η ^ permInversions σ * ((∏ i : Fin j, S.C (α i) (β i)) *
      ((η ^ L.partialCross * η ^ R.partialCross) *
        ∫ q : ((L.InternalChord → Fin 3 → ℝ) × (R.InternalChord → Fin 3 → ℝ)) ×
            (Fin r → Fin 3 → ℝ),
          wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α')
              (PartialPairing.concatRevParamEquiv L R σ q) *
            (star (φ₁ (L.partialMomentum m q.1.1 q.2)) *
              φ₂ (R.partialMomentum m q.1.2 (q.2 ∘ σ.symm))))) = _
  have hp_cross : η ^ L.partialCross * η ^ R.partialCross * η ^ permInversions σ =
      η ^ P.cross := by
    dsimp [P]
    rw [PartialPairing.cross_concatRev, pow_add, pow_add]
  have h_cross_eq : ∀ J : ℂ,
      η ^ permInversions σ * ((∏ i : Fin j, S.C (α i) (β i)) *
        ((η ^ L.partialCross * η ^ R.partialCross) * J)) =
      (∏ i : Fin j, S.C (α i) (β i)) * (η ^ P.cross * J) := by
    intro J
    calc η ^ permInversions σ * ((∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ L.partialCross * η ^ R.partialCross) * J))
        = (∏ i : Fin j, S.C (α i) (β i)) *
            ((η ^ L.partialCross * η ^ R.partialCross * η ^ permInversions σ) * J) := by ring
      _ = (∏ i : Fin j, S.C (α i) (β i)) * (η ^ P.cross * J) := by rw [hp_cross]
  rw [h_cross_eq]
  congr 2
  have h_mp := PartialPairing.measurePreserving_concatRevParamEquiv L R σ
  have h_push := h_mp.integral_comp (PartialPairing.concatRevParamEquiv L R σ).measurableEmbedding
    (fun p : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
        (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
          φ₂ (fun t => P.momentum m p (Fin.natAdd j t))))
  rw [← h_push]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
  dsimp only [P]
  rcases q with ⟨⟨p_L, p_R⟩, k_ext⟩
  rw [PartialPairing.concatRev_momentum_left, PartialPairing.concatRev_momentum_right]

theorem inner_fockMomentumVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    {φ₁ : (Fin j → Fin 4 → ℝ) → ℂ} {φ₂ : (Fin k → Fin 4 → ℝ) → ℂ}
    (hφ₁ : PartialMomentumBound m j φ₁) (hφ₂ : PartialMomentumBound m k φ₂) :
    ⟪fockMomentumVec M_mode hC j α φ₁ hφ₁, fockMomentumVec M_mode hC k α' φ₂ hφ₂⟫_ℂ =
      ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        ∑ P : ChordPairing (j + k), η ^ P.cross *
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
              (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
                φ₂ (fun t => P.momentum m p (Fin.natAdd j t))) := by
  unfold fockMomentumVec
  rw [sum_inner]
  have h_diag : ∀ r₁ ∈ Finset.range (j + 1),
      ⟪liftSectorToFock M_mode.ν r₁
          (symmSector M_mode.ν r₁ η (fockRawSector M_mode r₁ α φ₁))
          (measurable_symmSector η (measurable_fockRawSector M_mode hC r₁ α hφ₁))
          (memLp_symmSector η (memLp_fockRawSector M_mode hC r₁ α hφ₁)),
        ∑ r₂ ∈ Finset.range (k + 1),
          liftSectorToFock M_mode.ν r₂
            (symmSector M_mode.ν r₂ η (fockRawSector M_mode r₂ α' φ₂))
            (measurable_symmSector η (measurable_fockRawSector M_mode hC r₂ α' hφ₂))
            (memLp_symmSector η (memLp_fockRawSector M_mode hC r₂ α' hφ₂))⟫_ℂ =
      if r₁ < k + 1 then
        ∫ x : FockSectorDom M_mode.ν r₁,
          star (symmSector M_mode.ν r₁ η (fockRawSector M_mode r₁ α φ₁) x) *
            symmSector M_mode.ν r₁ η (fockRawSector M_mode r₁ α' φ₂) x
          ∂(fockSectorMeasure M_mode.ν r₁)
      else 0 := by
    intro r₁ _
    rw [inner_sum]
    by_cases hr₁ : r₁ < k + 1
    · rw [if_pos hr₁, Finset.sum_eq_single r₁]
      · exact inner_liftSectorToFock_eq _ _ _ _
      · intro r₂ _ hne
        exact inner_liftSectorToFock_ne hne.symm _ _ _ _
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr hr₁))
    · rw [if_neg hr₁]
      refine Finset.sum_eq_zero (fun r₂ hr₂ => ?_)
      have hne : r₁ ≠ r₂ := by
        have hr₂_lt : r₂ < k + 1 := Finset.mem_range.mp hr₂
        omega
      exact inner_liftSectorToFock_ne hne _ _ _ _
  rw [Finset.sum_congr rfl h_diag, ← Finset.sum_filter]
  have h_filter_eq : (Finset.range (j + 1)).filter (· < k + 1) = Finset.range (min j k + 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h_filter_eq, ← Fin.sum_univ_eq_sum_range]
  have h_sec : ∀ r : Fin (min j k + 1),
      (∫ x : FockSectorDom M_mode.ν r.val,
        star (symmSector M_mode.ν r.val η (fockRawSector M_mode r.val α φ₁) x) *
          symmSector M_mode.ν r.val η (fockRawSector M_mode r.val α' φ₂) x
        ∂(fockSectorMeasure M_mode.ν r.val)) =
      ∑ L : PartialPairing j r.val, ∑ R : PartialPairing k r.val, ∑ σ : Equiv.Perm (Fin r.val),
        ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
          ((η ^ (PartialPairing.concatRev L R σ).cross) *
            ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
              wickChordWeight m C (PartialPairing.concatRev L R σ)
                  (Fin.append (β ∘ Fin.rev) α') p *
                (star (φ₁ (fun i =>
                    -(PartialPairing.concatRev L R σ).momentum m p
                      (Fin.castAdd k (Fin.rev i)))) *
                  φ₂ (fun t =>
                    (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t)))) := by
    intro r
    rw [inner_symmSector_eq M_mode.hη
      (memLp_fockRawSector M_mode hC r.val α hφ₁)
      (memLp_fockRawSector M_mode hC r.val α' hφ₂)]
    have h_pair_int : ∀ (σ : Equiv.Perm (Fin r.val))
        (L : PartialPairing j r.val) (R : PartialPairing k r.val),
        Integrable
          (fun x : FockSectorDom M_mode.ν r.val =>
            star (fockPartialTerm M_mode α φ₁ L x) *
              fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm))
          (fockSectorMeasure M_mode.ν r.val) := by
      intro σ L R
      have hm1 := memLp_fockPartialTerm M_mode hC α hφ₁ L
      have hm2 := (memLp_fockPartialTerm M_mode hC α' hφ₂ R).comp_measurePreserving
        (measurePreserving_fockSectorPermEquiv M_mode.ν r.val σ.symm)
      have hi := L2.integrable_inner (𝕜 := ℂ) (hm1.toLp _) (hm2.toLp _)
      refine hi.congr ?_
      filter_upwards [hm1.coeFn_toLp, hm2.coeFn_toLp] with x hx1 hx2
      rw [RCLike.inner_apply, hx1, hx2]
      simp [mul_comm]
    have h_expand_raw : ∀ σ : Equiv.Perm (Fin r.val),
        η ^ permInversions σ *
          (∫ x : FockSectorDom M_mode.ν r.val,
            star (fockRawSector M_mode r.val α φ₁ x) *
              fockRawSector M_mode r.val α' φ₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm)
            ∂(fockSectorMeasure M_mode.ν r.val)) =
        ∑ L : PartialPairing j r.val, ∑ R : PartialPairing k r.val,
          η ^ permInversions σ *
            (∫ x : FockSectorDom M_mode.ν r.val,
              star (fockPartialTerm M_mode α φ₁ L x) *
                fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm)
              ∂(fockSectorMeasure M_mode.ν r.val)) := by
      intro σ
      have h_fn :
          (fun x : FockSectorDom M_mode.ν r.val =>
            star (fockRawSector M_mode r.val α φ₁ x) *
              fockRawSector M_mode r.val α' φ₂ (x.1 ∘ σ.symm, x.2 ∘ σ.symm)) =
          fun x => ∑ L : PartialPairing j r.val, ∑ R : PartialPairing k r.val,
            star (fockPartialTerm M_mode α φ₁ L x) *
              fockPartialTerm M_mode α' φ₂ R (x.1 ∘ σ.symm, x.2 ∘ σ.symm) := by
        ext x
        unfold fockRawSector
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun L _ => Finset.mul_sum _ _ _)
      rw [h_fn, integral_finsetSum Finset.univ (fun L _ =>
        integrable_finsetSum Finset.univ (fun R _ => h_pair_int σ L R))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun L _ => ?_)
      rw [integral_finsetSum Finset.univ (fun R _ => h_pair_int σ L R), Finset.mul_sum]
    simp_rw [h_expand_raw]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    exact inner_fockPartialTerm_eq M_mode hC hC_herm α α' hφ₁ hφ₂ L R σ
  simp_rw [h_sec]
  have h_rhs_swap :
      (∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        ∑ P : ChordPairing (j + k), η ^ P.cross *
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
              (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
                φ₂ (fun t => P.momentum m p (Fin.natAdd j t)))) =
      ∑ r : Fin (min j k + 1), ∑ L : PartialPairing j r.val,
        ∑ R : PartialPairing k r.val, ∑ σ : Equiv.Perm (Fin r.val),
          ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
            ((η ^ (PartialPairing.concatRev L R σ).cross) *
              ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
                wickChordWeight m C (PartialPairing.concatRev L R σ)
                    (Fin.append (β ∘ Fin.rev) α') p *
                  (star (φ₁ (fun i =>
                      -(PartialPairing.concatRev L R σ).momentum m p
                        (Fin.castAdd k (Fin.rev i)))) *
                    φ₂ (fun t =>
                      (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t)))) := by
    have h_equiv : ∀ β : Fin j → ι,
        (∑ P : ChordPairing (j + k), η ^ P.cross *
          ∫ p : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P (Fin.append (β ∘ Fin.rev) α') p *
              (star (φ₁ (fun i => -P.momentum m p (Fin.castAdd k (Fin.rev i)))) *
                φ₂ (fun t => P.momentum m p (Fin.natAdd j t)))) =
        ∑ r : Fin (min j k + 1), ∑ L : PartialPairing j r.val,
          ∑ R : PartialPairing k r.val, ∑ σ : Equiv.Perm (Fin r.val),
            (η ^ (PartialPairing.concatRev L R σ).cross) *
              ∫ p : (PartialPairing.concatRev L R σ).Chord → Fin 3 → ℝ,
                wickChordWeight m C (PartialPairing.concatRev L R σ)
                    (Fin.append (β ∘ Fin.rev) α') p *
                  (star (φ₁ (fun i =>
                      -(PartialPairing.concatRev L R σ).momentum m p
                        (Fin.castAdd k (Fin.rev i)))) *
                    φ₂ (fun t =>
                      (PartialPairing.concatRev L R σ).momentum m p (Fin.natAdd j t))) := by
      intro β
      rw [← (PartialPairing.chordPairingConcatRevEquiv j k).sum_comp, Fintype.sum_sigma]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun L _ => ?_)
      rw [Fintype.sum_prod_type]
      rfl
    simp_rw [h_equiv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun L _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [Finset.sum_comm]
  rw [h_rhs_swap]

lemma measurable_massShellDecay :
    Measurable (fun q : Fin 3 → ℝ => ((1 + ‖q‖) ^ 4)⁻¹) := by
  have hc : Continuous (fun q : Fin 3 → ℝ => (1 + ‖q‖) ^ 4) :=
    (continuous_const.add continuous_norm).pow 4
  exact (hc.inv₀ (fun q => ne_of_gt (pow_pos (by linarith [norm_nonneg q]) 4))).measurable

lemma integrable_sq_massShellDecay :
    Integrable (fun q : Fin 3 → ℝ => (((1 + ‖q‖) ^ 4)⁻¹) ^ 2) volume := by
  refine integrable_massShellDecay.mono' ?_ (Filter.Eventually.of_forall (fun q => ?_))
  · exact (measurable_massShellDecay.pow_const 2).aestronglyMeasurable
  · have h1 : 1 ≤ (1 + ‖q‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg q])
    have h_inv_le : ((1 + ‖q‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have h_nn : 0 ≤ ((1 + ‖q‖) ^ 4)⁻¹ := by positivity
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    exact mul_le_of_le_one_right h_nn h_inv_le

lemma partialMomentumBound_minkowskiFourier (m : ℝ) (j : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    PartialMomentumBound m j (minkowskiFourier f) := by
  have h_eq : minkowskiFourier f =
      fun q => (minkowskiFourierSchwartzCLM j f) (momentumToEuclidCLMN j q) := by
    ext q
    exact minkowskiFourier_eq_minkowskiFourierSchwartzCLM j f q
  refine ⟨?_, fun r L => ?_⟩
  · rw [h_eq]
    exact ((minkowskiFourierSchwartzCLM j f).continuous.comp
      (momentumToEuclidCLMN j).continuous).measurable
  · let g := minkowskiFourierSchwartzCLM j f
    let d := Fintype.card L.InternalChord + r
    let K : ℝ := (4 * Real.pi) ^ (4 * d) *
      ((Finset.Iic (4 * d, 0)).sup
        (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin j × Fin 4)) ℂ) g)
    have hK_nn : 0 ≤ K :=
      mul_nonneg (by positivity) (apply_nonneg _ g)
    refine ⟨K, fun _ q => ((1 + ‖q‖) ^ 4)⁻¹, fun _ q => ((1 + ‖q‖) ^ 4)⁻¹,
      hK_nn, fun _ => integrable_massShellDecay, fun _ => measurable_massShellDecay,
      fun _ => integrable_sq_massShellDecay,
      fun _ _ => by positivity, fun _ _ => by positivity, fun p_int k_ext => ?_⟩
    rw [h_eq]
    exact L.norm_schwartz_momentumToEuclid_partial_le m g p_int k_ext

noncomputable def fockSchwartzVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (j : ℕ) (α : Fin j → ι) (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    FockHilbert M_mode.ν :=
  fockMomentumVec M_mode hC j α (minkowskiFourier f) (partialMomentumBound_minkowskiFourier m j f)

theorem inner_fockSchwartzVec_eq_wickMassShellW {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      G x = (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun t => x (Fin.natAdd j t))) :
    ⟪fockSchwartzVec M_mode hC j α f, fockSchwartzVec M_mode hC k α' g⟫_ℂ =
      ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
        wickMassShellW m η C hC (j + k) (Fin.append (β ∘ Fin.rev) α') G := by
  unfold fockSchwartzVec
  rw [inner_fockMomentumVec M_mode hC hC_herm j k α α']
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  rw [wickMassShellW_apply]
  refine Finset.sum_congr rfl (fun P _ => congrArg (_ * ·) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [minkowskiFourier_borchersProduct_eq j k f g G hG (P.momentum m p)]

noncomputable def fockWightmanMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (A : WightmanConfig ι) : FockHilbert M_mode.ν :=
  fockSchwartzVec M_mode hC A.1 A.2.1 A.2.2.val

theorem inner_fockWightmanMap_eq_wightmanKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (A B : WightmanConfig ι) :
    ⟪fockWightmanMap M_mode hC A, fockWightmanMap M_mode hC B⟫_ℂ =
      wightmanKernel S (wickMassShellW m η C hC) A B := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  unfold fockWightmanMap wightmanKernel osConcatIdx
  exact inner_fockSchwartzVec_eq_wickMassShellW M_mode hC hC_herm j k α α'
    f.val g.val (wightmanConcatSchwartz j k f g) (wightmanConcatSchwartz_apply j k f g)

theorem wickMassShellPositivity {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    Positivity S (wickMassShellW m η C hC) :=
  positivity_of_hilbertWavepacketConfig S (wickMassShellW m η C hC)
    (fockWightmanMap M_mode hC)
    (inner_fockWightmanMap_eq_wightmanKernel M_mode hC hC_herm)

lemma norm_euclidLaplace_partialMomentum {j r : ℕ} (m : ℝ)
    (x : Fin j → Fin 4 → ℝ) (L : PartialPairing j r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    ‖euclidLaplace x (L.partialMomentum m p_int k_ext)‖ =
      (∏ c : L.InternalChord,
        Real.exp (-((x (L.mate c.1) 0 - x c.1 0) * massShellEnergy m (p_int c)))) *
      (∏ a : Fin r,
        Real.exp (-(x (L.unpaired a) 0 * massShellEnergy m (k_ext a)))) := by
  unfold euclidLaplace
  rw [Complex.norm_exp]
  have h_re_term : ∀ i : Fin j,
      (((L.partialMomentum m p_int k_ext i 0 : ℂ) * (x i 0 : ℂ) +
        Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (x i 1 : ℂ) +
          (L.partialMomentum m p_int k_ext i 2 : ℂ) * (x i 2 : ℂ) +
          (L.partialMomentum m p_int k_ext i 3 : ℂ) * (x i 3 : ℂ)))).re =
      L.partialMomentum m p_int k_ext i 0 * x i 0 := by
    intro i
    simp [Complex.add_re, Complex.mul_re]
  rw [Complex.re_sum]
  simp_rw [h_re_term]
  have h_split :
      (∑ i : Fin j, L.partialMomentum m p_int k_ext i 0 * x i 0) =
      (∑ a : Fin r, -(x (L.unpaired a) 0 * massShellEnergy m (k_ext a))) +
      (∑ c : L.InternalChord, -((x (L.mate c.1) 0 - x c.1 0) * massShellEnergy m (p_int c))) := by
    rw [← L.partialSlotEquiv.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
    congr 1
    · refine Finset.sum_congr rfl (fun a _ => ?_)
      have hs : L.partialSlotEquiv (Sum.inl a) = L.unpaired a := rfl
      rw [hs, L.partialMomentum_unpaired]
      simp [massShellVec]
      ring
    · refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Fin.sum_univ_two]
      have hs0 : L.partialSlotEquiv (Sum.inr (c, 0)) = c.1 := rfl
      have hs1 : L.partialSlotEquiv (Sum.inr (c, 1)) = L.mate c.1 := rfl
      rw [hs0, hs1, L.partialMomentum_fst, L.partialMomentum_mate]
      simp [massShellVec]
      ring
  rw [h_split, Real.exp_add, Real.exp_sum, Real.exp_sum, mul_comm]

lemma partialMomentumBound_euclidLaplace {m : ℝ} (hm : 0 < m) {j : ℕ}
    {x : Fin j → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN j) :
    PartialMomentumBound m j (euclidLaplace x) := by
  refine ⟨(continuous_euclidLaplace x).measurable, fun r L => ?_⟩
  refine ⟨1,
    fun c q => Real.exp (-((x (L.mate c.1) 0 - x c.1 0) * massShellEnergy m q)),
    fun a q => Real.exp (-(x (L.unpaired a) 0 * massShellEnergy m q)),
    zero_le_one,
    fun c => integrable_exp_neg_massShellEnergy hm
      (sub_pos.mpr (orderedEuclidN_time_lt_of_lt hx.2 c.2)),
    fun a => (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_massShellEnergy m)).neg)).measurable,
    fun a => ?_,
    fun _ _ => (Real.exp_pos _).le,
    fun _ _ => (Real.exp_pos _).le,
    fun p_int k_ext => ?_⟩
  · have h_sq : (fun q : Fin 3 → ℝ =>
        (Real.exp (-(x (L.unpaired a) 0 * massShellEnergy m q))) ^ 2) =
        fun q => Real.exp (-((2 * x (L.unpaired a) 0) * massShellEnergy m q)) := by
      ext q
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [h_sq]
    exact integrable_exp_neg_massShellEnergy hm (mul_pos two_pos (hx.1 (L.unpaired a)))
  · rw [one_mul, norm_euclidLaplace_partialMomentum]

noncomputable def fockOSMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (A : OSConfig ι) : FockHilbert M_mode.ν :=
  fockMomentumVec M_mode hC A.1 A.2.1 (euclidLaplace A.2.2.val)
    (partialMomentumBound_euclidLaplace hm A.2.2.property)

theorem inner_fockOSMap_eq_osKernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (A B : OSConfig ι) :
    ⟪fockOSMap hm M_mode hC A, fockOSMap hm M_mode hC B⟫_ℂ =
      osKernel S (wickMassShellS m hm η C hC) A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold fockOSMap osKernel osConcatIdx
  dsimp only
  rw [inner_fockMomentumVec M_mode hC hC_herm j k α α']
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  change (∑ P : ChordPairing (j + k), η ^ P.cross * _) =
    wickMassShellH m η C (j + k) (Fin.append (β ∘ Fin.rev) α')
      (wickEmbedN (j + k) (osConcatPoint j k x y))
  rw [wickMassShellH_eq_sum_integral]
  refine Finset.sum_congr rfl (fun P _ => congrArg (_ * ·) ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  dsimp only
  rw [vladimirov_kernel_osConcatPoint_eq j k x y (P.momentum m p)]

theorem wickMassShellOSReflectionPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSReflectionPositive S (wickMassShellS m hm η C hC) := by
  intro Ψ
  let v : FockHilbert M_mode.ν := Ψ.sum (fun A c => c • fockOSMap hm M_mode hC A)
  have h_inner : ⟪v, v⟫_ℂ = osPreInner S (wickMassShellS m hm η C hC) Ψ Ψ := by
    dsimp [v]
    unfold osPreInner
    simp only [Finsupp.sum]
    rw [sum_inner (𝕜 := ℂ)]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [inner_smul_left, inner_sum (𝕜 := ℂ), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun B _ => ?_)
    rw [inner_smul_right, inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A B,
      ← Complex.star_def]
    ring
  rw [← h_inner]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem wickMassShellOSAxioms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSAxioms R_rep S η (wickMassShellS m hm η C hC) :=
  schwingerFromTube_osAxioms R_rep S (wickMassShellW m η C hC)
    (wickMassShellTubeExtension m hm η C hC)
    (wickMassShellTubeTranslationInvariant hm η hC)
    (wickMassShellTubeCovariant R_rep hm η hC hC_cov)
    (wickMassShellTubeWickHermiticity S hm M_mode.hη hC hC_herm)
    (wickMassShellTubePCT R_rep hm M_mode.hη hC hC_pct)
    (wickMassShellOSReflectionPositive hm M_mode hC hC_herm)

theorem freeKGPositivity {m : ℝ} (hm : 0 < m) :
    Positivity trivialStarStructure (freeKGW m hm) :=
  wickMassShellPositivity (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGOSReflectionPositive {m : ℝ} (hm : 0 < m) :
    OSReflectionPositive trivialStarStructure (freeKGS m hm) :=
  wickMassShellOSReflectionPositive hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])

theorem freeKGOSAxioms {m : ℝ} (hm : 0 < m) :
    OSAxioms trivialRep trivialStarStructure 1 (freeKGS m hm) :=
  wickMassShellOSAxioms trivialRep trivialStarStructure hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeDiracPositivity {m : ℝ} (hm : 0 < m) :
    Positivity diracStarStructure (freeDiracW m hm) :=
  wickMassShellPositivity (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m)

theorem freeDiracOSReflectionPositive {m : ℝ} (hm : 0 < m) :
    OSReflectionPositive diracStarStructure (freeDiracS m hm) :=
  wickMassShellOSReflectionPositive hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m)

theorem freeDiracOSAxioms {m : ℝ} (hm : 0 < m) :
    OSAxioms diracRep diracStarStructure (-1) (freeDiracS m hm) :=
  wickMassShellOSAxioms diracRep diracStarStructure hm (diracModeData hm)
    (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

lemma fockSectorMeasure_zero_univ (ν : ℕ) :
    fockSectorMeasure ν 0 Set.univ = 1 := by
  unfold fockSectorMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  have h1 : (volume : Measure (Fin 0 → Fin 3 → ℝ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp
  have h2 : (Measure.count : Measure (Fin 0 → Fin ν)) Set.univ = 1 := by
    simp
  rw [h1, h2, mul_one]

instance instIsFiniteMeasureFockSectorZero (ν : ℕ) :
    IsFiniteMeasure (fockSectorMeasure ν 0) :=
  ⟨by rw [fockSectorMeasure_zero_univ]; exact ENNReal.one_lt_top⟩

lemma integral_fockSectorMeasure_zero {ν : ℕ} (g : FockSectorDom ν 0 → ℂ) :
    (∫ x : FockSectorDom ν 0, g x ∂(fockSectorMeasure ν 0)) = g default := by
  have hg : g = fun _ => g default :=
    funext (fun x => congrArg g (Subsingleton.elim x default))
  rw [hg, integral_const]
  simp [Measure.real, fockSectorMeasure_zero_univ]

noncomputable def fockVacuum (ν : ℕ) : FockHilbert ν :=
  liftSectorToFock ν 0 (fun _ => 1) measurable_const (memLp_const (1 : ℂ))

@[simp]
theorem inner_fockVacuum_self (ν : ℕ) :
    ⟪fockVacuum ν, fockVacuum ν⟫_ℂ = 1 := by
  unfold fockVacuum
  rw [inner_liftSectorToFock_eq, integral_fockSectorMeasure_zero]
  simp

@[simp]
theorem norm_fockVacuum (ν : ℕ) :
    ‖fockVacuum ν‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fockVacuum_self]
  simp

lemma integral_fockMeasure_sectorZero_mul {ν : ℕ} {h : FockOmega ν → ℂ}
    (hh_int : Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * h a) (fockMeasure ν)) :
    (∫ a : FockOmega ν,
      (if a.1 = 0 then (1 : ℂ) else 0) * h a ∂(fockMeasure ν)) = h ⟨0, default⟩ := by
  let F : FockOmega ν → ℂ := fun a => (if a.1 = 0 then (1 : ℂ) else 0) * h a
  have hF_r : ∀ r : ℕ, AEStronglyMeasurable F ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
    fun r => (hh_int.mono_measure (Measure.le_sum _ r)).aestronglyMeasurable
  change ∫ a : FockOmega ν, F a ∂(fockMeasure ν) = _
  unfold fockMeasure
  rw [integral_sum_measure hh_int, tsum_eq_single 0]
  · rw [integral_map (measurable_fockSigmaMk ν 0).aemeasurable (hF_r 0),
        integral_fockSectorMeasure_zero]
    simp [F]
  · intro r hne
    rw [integral_map (measurable_fockSigmaMk ν r).aemeasurable (hF_r r)]
    simp [F, hne]

lemma integrable_sectorZero_mul_of_integrable {ν : ℕ} {h : FockOmega ν → ℂ}
    (hh : Integrable h (fockMeasure ν)) :
    Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * h a) (fockMeasure ν) := by
  have h_eq : (fun a : FockOmega ν => if a.1 = 0 then (1 : ℂ) else 0) =
      sectorToOmega ν 0 (fun _ => (1 : ℂ)) := by
    ext a
    by_cases h0 : a.1 = 0 <;> simp [sectorToOmega, h0]
  have h_ind : Measurable (fun a : FockOmega ν => if a.1 = 0 then (1 : ℂ) else 0) := by
    rw [h_eq]
    exact measurable_sectorToOmega measurable_const
  refine hh.norm.mono' (h_ind.aestronglyMeasurable.mul hh.1)
    (Filter.Eventually.of_forall (fun a => ?_))
  by_cases h0 : a.1 = 0 <;> simp [h0]

theorem inner_fockVacuum_mul_eq_integral {ν : ℕ} (x y : FockHilbert ν) :
    ⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ =
      ∫ a : FockOmega ν,
        (if a.1 = 0 then (1 : ℂ) else 0) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  have hvac_ae :=
    (memLp_sectorToOmega (ν := ν) (r := 0) (g := fun _ => (1 : ℂ))
      measurable_const (memLp_const (1 : ℂ))).coeFn_toLp
  have hx_eq : ⟪x, fockVacuum ν⟫_ℂ =
      ∫ a : FockOmega ν,
        (if a.1 = 0 then (1 : ℂ) else 0) * star ((x : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hy_eq : ⟪fockVacuum ν, y⟫_ℂ =
      ∫ a : FockOmega ν,
        (if a.1 = 0 then (1 : ℂ) else 0) * (y : FockOmega ν → ℂ) a ∂(fockMeasure ν) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hx_int : Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * star ((x : FockOmega ν → ℂ) a)) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x (fockVacuum ν)).congr ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hy_int : Integrable (fun a : FockOmega ν =>
      (if a.1 = 0 then (1 : ℂ) else 0) * (y : FockOmega ν → ℂ) a) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) (fockVacuum ν) y).congr ?_
    filter_upwards [hvac_ae] with a ha
    unfold fockVacuum liftSectorToFock
    rw [ha]
    by_cases h0 : a.1 = 0 <;> simp [RCLike.inner_apply, sectorToOmega, h0]
  have hxy_int : Integrable (fun a : FockOmega ν =>
      star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x y).congr (Filter.Eventually.of_forall (fun a => ?_))
    simp [RCLike.inner_apply, mul_comm]
  rw [hx_eq, hy_eq, integral_fockMeasure_sectorZero_mul hx_int,
      integral_fockMeasure_sectorZero_mul hy_int,
      integral_fockMeasure_sectorZero_mul (integrable_sectorZero_mul_of_integrable hxy_int)]

def partialPairingZero : PartialPairing 0 0 where
  unpaired := Fin.elim0
  mate := 1
  strictMono_unpaired a := Fin.elim0 a
  involutive i := Fin.elim0 i
  fixed_iff i := Fin.elim0 i

lemma partialPairing_zero_zero_eq (L : PartialPairing 0 0) :
    L = partialPairingZero :=
  PartialPairing.ext_mate (Subsingleton.elim L.mate 1)

theorem fockMomentumVec_zero_eq_smul_fockVacuum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (α : Fin 0 → ι) (φ : (Fin 0 → Fin 4 → ℝ) → ℂ) (hφ : PartialMomentumBound m 0 φ) :
    fockMomentumVec M_mode hC 0 α φ hφ = φ 0 • fockVacuum M_mode.ν := by
  unfold fockMomentumVec fockVacuum
  rw [Finset.sum_range_one]
  have h_fn : symmSector M_mode.ν 0 η (fockRawSector M_mode 0 α φ) =
      fun _ : FockSectorDom M_mode.ν 0 => φ 0 := by
    ext x
    unfold symmSector fockRawSector
    have h_perm : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} := by
      ext π
      simp [Subsingleton.elim π 1]
    have h_pp : (Finset.univ : Finset (PartialPairing 0 0)) = {partialPairingZero} := by
      ext L
      simp [partialPairing_zero_zero_eq L]
    rw [h_perm, Finset.sum_singleton, permInversions_one, pow_zero, one_mul,
        Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul,
        h_pp, Finset.sum_singleton]
    unfold fockPartialTerm
    haveI : IsEmpty partialPairingZero.InternalChord := ⟨fun c => Fin.elim0 c.1⟩
    have h_cross : partialPairingZero.partialCross = 0 := by
      unfold PartialPairing.partialCross PartialPairing.internalCross PartialPairing.openCross
      simp
    have h_vol :
        (volume : Measure (partialPairingZero.InternalChord → Fin 3 → ℝ)) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp
    have h_ig :
        (fun p_int : partialPairingZero.InternalChord → Fin 3 → ℝ =>
          fockPartialIntWeight m C α partialPairingZero p_int *
            φ (partialPairingZero.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν 0 1 x).1)) =
        fun _ => φ 0 := by
      ext p_int
      have hw : fockPartialIntWeight m C α partialPairingZero p_int = 1 := by
        unfold fockPartialIntWeight
        simp
      have hp :
          partialPairingZero.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν 0 1 x).1 = 0 :=
        Subsingleton.elim _ _
      rw [hw, one_mul, hp]
    rw [h_cross, pow_zero, one_mul, Fin.prod_univ_zero, one_mul, h_ig, integral_const]
    simp [Measure.real, h_vol]
  unfold liftSectorToFock
  have h_smul := (memLp_sectorToOmega (ν := M_mode.ν) (r := 0) (g := fun _ => (1 : ℂ))
    measurable_const (memLp_const (1 : ℂ))).toLp_const_smul (φ 0)
  rw [← h_smul]
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun a => ?_))
  by_cases h0 : a.1 = 0 <;> simp [sectorToOmega, h0, h_fn]

@[simp]
theorem fockOSMap_osVacuumConfig {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C) :
    fockOSMap hm M_mode hC (osVacuumConfig ι) = fockVacuum M_mode.ν := by
  unfold fockOSMap osVacuumConfig
  dsimp only
  rw [fockMomentumVec_zero_eq_smul_fockVacuum]
  have h1 : euclidLaplace (euclidOrderedBasePoint 0) 0 = 1 := by
    simp [euclidLaplace]
  rw [h1, one_smul]

@[simp]
theorem fockWightmanMap_wightmanVacuumConfig {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C) :
    fockWightmanMap M_mode hC (wightmanVacuumConfig ι) = fockVacuum M_mode.ν := by
  unfold fockWightmanMap fockSchwartzVec wightmanVacuumConfig wightmanBaseConfig
  dsimp only
  rw [fockMomentumVec_zero_eq_smul_fockVacuum]
  have h1 : minkowskiFourier (momentumWavepacketCompactSchwartz 0 0).val 0 = 1 := by
    have hm : (∫ y : Fin 0 → Fin 4 → ℝ,
        (momentumWavepacketCompactSchwartz 0 0 : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) y) = 1 :=
      integral_momentumWavepacketSchwartz_zero 0
    rw [minkowskiFourier_fin0]
    rwa [integral_fin0] at hm
  rw [h1, one_smul]

lemma lp2_integrable_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x : Lp ℂ 2 μ) :
    Integrable (fun a : Ω => ‖(x : Ω → ℂ) a‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x)).mp (Lp.memLp x)

lemma lp2_norm_sq_eq_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x : Lp ℂ 2 μ) :
    ‖x‖ ^ 2 = ∫ a : Ω, ‖(x : Ω → ℂ) a‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) x x)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  norm_cast

lemma lp2_integral_norm_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (x y : Lp ℂ 2 μ) :
    (∫ a : Ω, ‖(x : Ω → ℂ) a‖ * ‖(y : Ω → ℂ) a‖ ∂μ) ≤ ‖x‖ * ‖y‖ := by
  let x' : Lp ℝ 2 μ := (Lp.memLp x).norm.toLp (fun a => ‖(x : Ω → ℂ) a‖)
  let y' : Lp ℝ 2 μ := (Lp.memLp y).norm.toLp (fun a => ‖(y : Ω → ℂ) a‖)
  have hx' : ‖x'‖ = ‖x‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hy' : ‖y'‖ = ‖y‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have h_eq : (∫ a : Ω, ‖(x : Ω → ℂ) a‖ * ‖(y : Ω → ℂ) a‖ ∂μ) = ⟪x', y'⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.memLp x).norm.coeFn_toLp, (Lp.memLp y).norm.coeFn_toLp] with a hxa hya
    dsimp [x', y']
    rw [hxa, hya]
    simp [mul_comm]
  rw [h_eq, ← hx', ← hy']
  exact real_inner_le_norm x' y'

lemma memLp_bdd_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m_fn : Ω → ℂ} (hm_meas : Measurable m_fn) {C_bd : ℝ} (_hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : Ω, ‖m_fn a‖ ≤ C_bd) {g : Ω → ℂ} (hg : MemLp g 2 μ) :
    MemLp (fun a => m_fn a * g a) 2 μ := by
  have h_meas : AEStronglyMeasurable (fun a => m_fn a * g a) μ :=
    hm_meas.aestronglyMeasurable.mul hg.1
  rw [memLp_two_iff_integrable_sq_norm h_meas]
  have hg_sq : Integrable (fun a => ‖g a‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hg.1).mp hg
  refine (hg_sq.const_mul (C_bd ^ 2)).mono'
    ((continuous_pow 2).comp_aestronglyMeasurable h_meas.norm)
    (Filter.Eventually.of_forall (fun a => ?_))
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (h_bd a) 2) (sq_nonneg _)

noncomputable def fockMultLM {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) :
    FockHilbert ν →ₗ[ℂ] FockHilbert ν where
  toFun x := (memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)).toLp
    (fun a => m_fn a * (x : FockOmega ν → ℂ) a)
  map_add' x y := by
    have h1 := memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)
    have h2 := memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp y)
    rw [← h1.toLp_add h2]
    refine MeasureTheory.MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add x y] with a ha
    have ha' : ((x + y : FockHilbert ν) : FockOmega ν → ℂ) a =
        (x : FockOmega ν → ℂ) a + (y : FockOmega ν → ℂ) a := ha
    change m_fn a * ((x + y : FockHilbert ν) : FockOmega ν → ℂ) a = _
    rw [ha', mul_add]
    rfl
  map_smul' c x := by
    have h1 := memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)
    rw [RingHom.id_apply, ← h1.toLp_const_smul c]
    refine MeasureTheory.MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul c x] with a ha
    have ha' : ((c • x : FockHilbert ν) : FockOmega ν → ℂ) a =
        c * (x : FockOmega ν → ℂ) a := ha
    change m_fn a * ((c • x : FockHilbert ν) : FockOmega ν → ℂ) a = _
    rw [ha']
    dsimp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma norm_fockMultLM_le {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x : FockHilbert ν) :
    ‖fockMultLM m_fn hm_meas hC_nn h_bd x‖ ≤ C_bd * ‖x‖ := by
  have h_sq : ‖fockMultLM m_fn hm_meas hC_nn h_bd x‖ ^ 2 ≤ (C_bd * ‖x‖) ^ 2 := by
    rw [lp2_norm_sq_eq_integral, mul_pow, lp2_norm_sq_eq_integral, ← integral_const_mul]
    have h_ae := (memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)).coeFn_toLp
    refine integral_mono_ae (lp2_integrable_norm_sq _)
      ((lp2_integrable_norm_sq x).const_mul (C_bd ^ 2)) ?_
    filter_upwards [h_ae] with a ha
    dsimp [fockMultLM] at ha ⊢
    rw [ha, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (h_bd a) 2) (sq_nonneg _)
  nlinarith [norm_nonneg (fockMultLM m_fn hm_meas hC_nn h_bd x),
    mul_nonneg hC_nn (norm_nonneg x)]

noncomputable def fockMultCLM {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  (fockMultLM m_fn hm_meas hC_nn h_bd).mkContinuous C_bd
    (norm_fockMultLM_le m_fn hm_meas hC_nn h_bd)

lemma fockMultCLM_coeFn {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x : FockHilbert ν) :
    (fockMultCLM m_fn hm_meas hC_nn h_bd x : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      fun a => m_fn a * (x : FockOmega ν → ℂ) a :=
  (memLp_bdd_mul hm_meas hC_nn h_bd (Lp.memLp x)).coeFn_toLp

lemma norm_fockMultCLM_apply_le {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x : FockHilbert ν) :
    ‖fockMultCLM m_fn hm_meas hC_nn h_bd x‖ ≤ C_bd * ‖x‖ :=
  norm_fockMultLM_le m_fn hm_meas hC_nn h_bd x

lemma fockMultCLM_congr {ν : ℕ} {m₁ m₂ : FockOmega ν → ℂ}
    (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb₁ : ∀ a, ‖m₁ a‖ ≤ C₁) (hb₂ : ∀ a, ‖m₂ a‖ ≤ C₂)
    (heq : ∀ a, m₁ a = m₂ a) :
    fockMultCLM m₁ hm₁ hC₁ hb₁ = fockMultCLM m₂ hm₂ hC₂ hb₂ := by
  ext x : 1
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn m₁ hm₁ hC₁ hb₁ x,
    fockMultCLM_coeFn m₂ hm₂ hC₂ hb₂ x] with a ha₁ ha₂
  rw [ha₁, ha₂, heq a]

lemma fockMultCLM_comp {ν : ℕ}
    {m₁ m₂ : FockOmega ν → ℂ} (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hb₁ : ∀ a, ‖m₁ a‖ ≤ C₁) (hb₂ : ∀ a, ‖m₂ a‖ ≤ C₂) :
    (fockMultCLM m₁ hm₁ hC₁ hb₁).comp (fockMultCLM m₂ hm₂ hC₂ hb₂) =
      fockMultCLM (fun a => m₁ a * m₂ a) (hm₁.mul hm₂) (mul_nonneg hC₁ hC₂)
        (fun a => by rw [norm_mul]; exact mul_le_mul (hb₁ a) (hb₂ a) (norm_nonneg _) hC₁) := by
  ext x : 1
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn m₁ hm₁ hC₁ hb₁ (fockMultCLM m₂ hm₂ hC₂ hb₂ x),
    fockMultCLM_coeFn m₂ hm₂ hC₂ hb₂ x,
    fockMultCLM_coeFn (fun a => m₁ a * m₂ a) (hm₁.mul hm₂) (mul_nonneg hC₁ hC₂)
      (fun a => by rw [norm_mul]; exact mul_le_mul (hb₁ a) (hb₂ a) (norm_nonneg _) hC₁) x]
    with a ha₁ ha₂ ha₁₂
  simp only [ContinuousLinearMap.comp_apply] at ha₁ ⊢
  rw [ha₁, ha₂, ha₁₂, mul_assoc]

lemma fockMultCLM_one (ν : ℕ) :
    fockMultCLM (fun _ : FockOmega ν => (1 : ℂ)) measurable_const zero_le_one
      (fun _ => by simp) = ContinuousLinearMap.id ℂ (FockHilbert ν) := by
  ext x : 1
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn (fun _ : FockOmega ν => (1 : ℂ))
    measurable_const zero_le_one (fun _ => by simp) x] with a ha
  simp [ha]

lemma inner_fockMultCLM_right {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x y : FockHilbert ν) :
    ⟪x, fockMultCLM m_fn hm_meas hC_nn h_bd y⟫_ℂ =
      ∫ a : FockOmega ν,
        m_fn a * (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fockMultCLM_coeFn m_fn hm_meas hC_nn h_bd y] with a ha
  rw [RCLike.inner_apply, ha, ← Complex.star_def]
  ring

lemma inner_fockMultCLM_left {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd) (x y : FockHilbert ν) :
    ⟪fockMultCLM m_fn hm_meas hC_nn h_bd x, y⟫_ℂ =
      ∫ a : FockOmega ν,
        star (m_fn a) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fockMultCLM_coeFn m_fn hm_meas hC_nn h_bd x] with a ha
  rw [RCLike.inner_apply, ha, map_mul, ← Complex.star_def]
  ring

lemma fockMultCLM_liftSectorToFock {ν r : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd)
    (g : FockSectorDom ν r → ℂ) (hg_meas : Measurable g)
    (hg : MemLp g 2 (fockSectorMeasure ν r)) :
    fockMultCLM m_fn hm_meas hC_nn h_bd (liftSectorToFock ν r g hg_meas hg) =
      liftSectorToFock ν r (fun x => m_fn ⟨r, x⟩ * g x)
        (by exact (hm_meas.comp (measurable_fockSigmaMk ν r)).mul hg_meas)
        (memLp_bdd_mul (hm_meas.comp (measurable_fockSigmaMk ν r)) hC_nn
          (fun x => h_bd ⟨r, x⟩) hg) := by
  have h_prod_meas : Measurable (fun x : FockSectorDom ν r => m_fn ⟨r, x⟩ * g x) :=
    (hm_meas.comp (measurable_fockSigmaMk ν r)).mul hg_meas
  rw [Lp.ext_iff]
  filter_upwards [fockMultCLM_coeFn m_fn hm_meas hC_nn h_bd
      (liftSectorToFock ν r g hg_meas hg),
    (memLp_sectorToOmega hg_meas hg).coeFn_toLp,
    (memLp_sectorToOmega h_prod_meas
      (memLp_bdd_mul (hm_meas.comp (measurable_fockSigmaMk ν r)) hC_nn
        (fun x => h_bd ⟨r, x⟩) hg)).coeFn_toLp] with a ha₁ ha₂ ha₃
  unfold liftSectorToFock at ha₁ ⊢
  rw [ha₁, ha₂, ha₃]
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r
  · subst hr
    simp [sectorToOmega]
  · simp [sectorToOmega, hr]

lemma fockMultCLM_fockVacuum {ν : ℕ} (m_fn : FockOmega ν → ℂ)
    (hm_meas : Measurable m_fn) {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (h_bd : ∀ a : FockOmega ν, ‖m_fn a‖ ≤ C_bd)
    (h0 : m_fn ⟨0, default⟩ = 1) :
    fockMultCLM m_fn hm_meas hC_nn h_bd (fockVacuum ν) = fockVacuum ν := by
  unfold fockVacuum
  rw [fockMultCLM_liftSectorToFock]
  unfold liftSectorToFock
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun a => ?_))
  rcases a with ⟨r, x⟩
  by_cases hr : r = 0
  · subst hr
    rw [Subsingleton.elim x default]
    simp [sectorToOmega, h0]
  · simp [sectorToOmega, hr]

noncomputable def fockTotalMomentum {ν : ℕ} (m : ℝ) (a : FockOmega ν) : Fin 4 → ℝ :=
  ∑ i : Fin a.1, massShellVec m (a.2.1 i)

lemma measurable_fockTotalMomentum (ν : ℕ) (m : ℝ) :
    Measurable (fockTotalMomentum (ν := ν) m) := by
  intro U hU
  rw [measurableSet_fockOmega_iff]
  intro r
  have h_sec : Measurable (fun x : FockSectorDom ν r =>
      ∑ i : Fin r, massShellVec m (x.1 i)) :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      (continuous_massShellVec m).measurable.comp ((measurable_pi_apply i).comp measurable_fst))
  exact h_sec hU

@[simp]
lemma fockTotalMomentum_zero {ν : ℕ} (m : ℝ) (x : FockSectorDom ν 0) :
    fockTotalMomentum m ⟨0, x⟩ = 0 := by
  simp [fockTotalMomentum]

lemma fockTotalMomentum_perm {ν r : ℕ} (m : ℝ) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r) :
    fockTotalMomentum m ⟨r, fockSectorPermEquiv ν r π x⟩ = fockTotalMomentum m ⟨r, x⟩ := by
  unfold fockTotalMomentum fockSectorPermEquiv
  dsimp only
  exact Equiv.sum_comp π (fun i => massShellVec m (x.1 i))

lemma partialMomentum_sum_eq {j r : ℕ} (m : ℝ) (L : PartialPairing j r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ) :
    ∑ i : Fin j, L.partialMomentum m p_int k_ext i =
      -∑ a : Fin r, massShellVec m (k_ext a) := by
  rw [← L.partialSlotEquiv.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have h_int :
      (∑ c : L.InternalChord, ∑ s : Fin 2,
        L.partialMomentum m p_int k_ext (L.partialSlotEquiv (Sum.inr (c, s)))) = 0 := by
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [Fin.sum_univ_two]
    have hs0 : L.partialSlotEquiv (Sum.inr (c, 0)) = c.1 := rfl
    have hs1 : L.partialSlotEquiv (Sum.inr (c, 1)) = L.mate c.1 := rfl
    rw [hs0, hs1, L.partialMomentum_fst, L.partialMomentum_mate, add_neg_cancel]
  rw [h_int, add_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hsa : L.partialSlotEquiv (Sum.inl a) = L.unpaired a := rfl
  rw [hsa, L.partialMomentum_unpaired]

theorem fockMomentumVec_mul_totalMomentum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (j : ℕ) (α : Fin j → ι)
    {φ₁ φ₂ : (Fin j → Fin 4 → ℝ) → ℂ}
    (hφ₁ : PartialMomentumBound m j φ₁) (hφ₂ : PartialMomentumBound m j φ₂)
    {ψ : (Fin 4 → ℝ) → ℂ} (hψ_meas : Measurable ψ)
    {C_bd : ℝ} (hC_nn : 0 ≤ C_bd)
    (hψ_bd : ∀ a : FockOmega M_mode.ν, ‖ψ (fockTotalMomentum m a)‖ ≤ C_bd)
    (h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      φ₂ (L.partialMomentum m p_int k_ext) =
        ψ (∑ a : Fin r, massShellVec m (k_ext a)) * φ₁ (L.partialMomentum m p_int k_ext)) :
    fockMomentumVec M_mode hC j α φ₂ hφ₂ =
      fockMultCLM (fun a => ψ (fockTotalMomentum m a))
        (hψ_meas.comp (measurable_fockTotalMomentum M_mode.ν m)) hC_nn hψ_bd
        (fockMomentumVec M_mode hC j α φ₁ hφ₁) := by
  unfold fockMomentumVec
  rw [map_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [fockMultCLM_liftSectorToFock]
  unfold liftSectorToFock
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall (fun a => ?_))
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r
  · subst hr
    simp only [sectorToOmega_sigmaMk_eq]
    unfold symmSector
    have h_sum :
        (∑ π : Equiv.Perm (Fin r'),
          η ^ permInversions π *
            fockRawSector M_mode r' α φ₂ (fockSectorPermEquiv M_mode.ν r' π x)) =
        ∑ π : Equiv.Perm (Fin r'),
          ψ (fockTotalMomentum m ⟨r', x⟩) *
            (η ^ permInversions π *
              fockRawSector M_mode r' α φ₁ (fockSectorPermEquiv M_mode.ν r' π x)) := by
      refine Finset.sum_congr rfl (fun π _ => ?_)
      rw [← fockTotalMomentum_perm m π x]
      unfold fockRawSector
      have h_raw :
          (∑ L : PartialPairing j r',
            fockPartialTerm M_mode α φ₂ L (fockSectorPermEquiv M_mode.ν r' π x)) =
          ψ (fockTotalMomentum m ⟨r', fockSectorPermEquiv M_mode.ν r' π x⟩) *
            ∑ L : PartialPairing j r',
              fockPartialTerm M_mode α φ₁ L (fockSectorPermEquiv M_mode.ν r' π x) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun L _ => ?_)
        unfold fockPartialTerm fockTotalMomentum
        have h_int :
            (∫ p_int : L.InternalChord → Fin 3 → ℝ,
              fockPartialIntWeight m C α L p_int *
                φ₂ (L.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν r' π x).1)) =
            ψ (∑ a : Fin r', massShellVec m ((fockSectorPermEquiv M_mode.ν r' π x).1 a)) *
              ∫ p_int : L.InternalChord → Fin 3 → ℝ,
                fockPartialIntWeight m C α L p_int *
                  φ₁ (L.partialMomentum m p_int (fockSectorPermEquiv M_mode.ν r' π x).1) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun p_int => ?_))
          dsimp only
          rw [h_eq r' L p_int (fockSectorPermEquiv M_mode.ν r' π x).1]
          ring
        rw [h_int]
        ring
      rw [h_raw]
      ring
    rw [h_sum, ← Finset.mul_sum]
    ring
  · simp [sectorToOmega, hr]

noncomputable def fockEnergy {ν : ℕ} (m : ℝ) (a : FockOmega ν) : ℝ :=
  fockTotalMomentum m a 0

lemma fockEnergy_eq_sum {ν : ℕ} (m : ℝ) (a : FockOmega ν) :
    fockEnergy m a = ∑ i : Fin a.1, massShellEnergy m (a.2.1 i) := by
  simp [fockEnergy, fockTotalMomentum, massShellVec]

lemma measurable_fockEnergy (ν : ℕ) (m : ℝ) :
    Measurable (fockEnergy (ν := ν) m) :=
  (measurable_pi_apply 0).comp (measurable_fockTotalMomentum ν m)

lemma fockEnergy_nonneg {ν : ℕ} (m : ℝ) (a : FockOmega ν) :
    0 ≤ fockEnergy m a := by
  rw [fockEnergy_eq_sum]
  exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)

@[simp]
lemma fockEnergy_zero {ν : ℕ} (m : ℝ) (x : FockSectorDom ν 0) :
    fockEnergy m ⟨0, x⟩ = 0 := by
  simp [fockEnergy]

lemma fockEnergy_ge_mass_of_ne_zero {ν : ℕ} {m : ℝ} (hm : 0 < m)
    {a : FockOmega ν} (ha : a.1 ≠ 0) :
    m ≤ fockEnergy m a := by
  rcases a with ⟨r, x⟩
  dsimp at ha
  cases r with
  | zero => exact False.elim (ha rfl)
  | succ r' =>
    rw [fockEnergy_eq_sum]
    have h0 : (0 : Fin (r' + 1)) ∈ (Finset.univ : Finset (Fin (r' + 1))) := Finset.mem_univ 0
    have h_le : massShellEnergy m (x.1 0) ≤
        ∑ i : Fin (r' + 1), massShellEnergy m (x.1 i) :=
      Finset.single_le_sum (f := fun i => massShellEnergy m (x.1 i))
        (fun i _ => Real.sqrt_nonneg _) h0
    exact (massShellEnergy_ge_mass hm (x.1 0)).trans h_le

noncomputable def fockSemigroup {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fun a => laplaceExp (fockEnergy m a) z)
    ((differentiable_laplaceExp 1 |>.continuous |> fun _ =>
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable).comp
      (measurable_fockEnergy ν m))
    zero_le_one
    (fun a => norm_laplaceExp_le_one (fockEnergy_nonneg m a) hz)

@[simp]
lemma fockSemigroup_zero {ν : ℕ} (m : ℝ) :
    fockSemigroup (ν := ν) m 0 zero_mem_rightHalfPlane =
      ContinuousLinearMap.id ℂ (FockHilbert ν) := by
  rw [← fockMultCLM_one ν]
  exact fockMultCLM_congr _ _ zero_le_one zero_le_one _ _ (fun a => laplaceExp_zero_right _)

lemma fockSemigroup_add {ν : ℕ} (m : ℝ) {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ rightHalfPlane) (h₂ : z₂ ∈ rightHalfPlane) :
    fockSemigroup (ν := ν) m (z₁ + z₂) (add_mem_rightHalfPlane h₁ h₂) =
      (fockSemigroup m z₁ h₁).comp (fockSemigroup m z₂ h₂) := by
  unfold fockSemigroup
  rw [fockMultCLM_comp]
  exact fockMultCLM_congr _ _ zero_le_one _ _ _ (fun a => laplaceExp_add (fockEnergy m a) z₁ z₂)

@[simp]
lemma fockSemigroup_fockVacuum {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane) :
    fockSemigroup m z hz (fockVacuum ν) = fockVacuum ν := by
  unfold fockSemigroup
  exact fockMultCLM_fockVacuum _ _ zero_le_one _ (by simp)

lemma norm_fockSemigroup_le {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (x : FockHilbert ν) :
    ‖fockSemigroup m z hz x‖ ≤ ‖x‖ := by
  unfold fockSemigroup
  simpa using norm_fockMultCLM_apply_le _ _ zero_le_one _ x

lemma inner_fockSemigroup_eq {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (x y : FockHilbert ν) :
    ⟪x, fockSemigroup m z hz y⟫_ℂ =
      ∫ a : FockOmega ν,
        laplaceExp (fockEnergy m a) z *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) ∂(fockMeasure ν) := by
  unfold fockSemigroup
  exact inner_fockMultCLM_right _ _ zero_le_one _ x y

lemma fockSemigroup_adjoint_symm {ν : ℕ} (m : ℝ) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (x y : FockHilbert ν) :
    ⟪fockSemigroup m z hz x, y⟫_ℂ =
      ⟪x, fockSemigroup m (star z) (star_mem_rightHalfPlane hz) y⟫_ℂ := by
  unfold fockSemigroup
  rw [inner_fockMultCLM_left, inner_fockMultCLM_right]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp only
  rw [laplaceExp_star]

noncomputable def fockSpatialPhase (b : Fin 3 → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((P 1 : ℂ) * (b 0 : ℂ) + (P 2 : ℂ) * (b 1 : ℂ) +
    (P 3 : ℂ) * (b 2 : ℂ)))

lemma continuous_fockSpatialPhase (b : Fin 3 → ℝ) :
    Continuous (fockSpatialPhase b) := by
  unfold fockSpatialPhase
  have hc : ∀ μ : Fin 4, Continuous (fun P : Fin 4 → ℝ => (P μ : ℂ)) :=
    fun μ => Complex.continuous_ofReal.comp (continuous_apply μ)
  exact Complex.continuous_exp.comp
    (continuous_const.mul
      ((((hc 1).mul continuous_const).add ((hc 2).mul continuous_const)).add
        ((hc 3).mul continuous_const)))

lemma norm_fockSpatialPhase (b : Fin 3 → ℝ) (P : Fin 4 → ℝ) :
    ‖fockSpatialPhase b P‖ = 1 := by
  unfold fockSpatialPhase
  rw [Complex.norm_exp]
  have hre : (-Complex.I * ((P 1 : ℂ) * (b 0 : ℂ) + (P 2 : ℂ) * (b 1 : ℂ) +
      (P 3 : ℂ) * (b 2 : ℂ))).re = 0 := by
    simp [Complex.mul_re, Complex.add_re]
  rw [hre, Real.exp_zero]

noncomputable def fockSpatialTranslate {ν : ℕ} (m : ℝ) (b : Fin 3 → ℝ) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fun a => fockSpatialPhase b (fockTotalMomentum m a))
    ((continuous_fockSpatialPhase b).measurable.comp (measurable_fockTotalMomentum ν m))
    zero_le_one
    (fun a => (norm_fockSpatialPhase b (fockTotalMomentum m a)).le)

lemma fockSpatialTranslate_comm_fockSemigroup {ν : ℕ} (m : ℝ) (b : Fin 3 → ℝ)
    (z : ℂ) (hz : z ∈ rightHalfPlane) :
    (fockSpatialTranslate (ν := ν) m b).comp (fockSemigroup m z hz) =
      (fockSemigroup m z hz).comp (fockSpatialTranslate m b) := by
  unfold fockSpatialTranslate fockSemigroup
  rw [fockMultCLM_comp, fockMultCLM_comp]
  exact fockMultCLM_congr _ _ _ _ _ _ (fun a => mul_comm _ _)

theorem fockOSMap_osConfigTimeShift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig ι) :
    fockOSMap hm M_mode hC (osConfigTimeShift τ hτ A) =
      fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) (fockOSMap hm M_mode hC A) := by
  rcases A with ⟨j, α, x, hx⟩
  unfold fockOSMap osConfigTimeShift fockSemigroup
  dsimp only
  let ψ : (Fin 4 → ℝ) → ℂ := fun P => laplaceExp (P 0) (τ : ℂ)
  have hψ_meas : Measurable ψ :=
    (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0)))).measurable
  have h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      euclidLaplace (fun i => x i + euclidTimeVec τ) (L.partialMomentum m p_int k_ext) =
        ψ (∑ a : Fin r, massShellVec m (k_ext a)) *
          euclidLaplace x (L.partialMomentum m p_int k_ext) := by
    intro r L p_int k_ext
    unfold euclidLaplace ψ laplaceExp
    rw [← Complex.exp_add]
    congr 1
    have h_sum0 : (∑ i : Fin j, L.partialMomentum m p_int k_ext i 0) =
        -(∑ a : Fin r, massShellVec m (k_ext a)) 0 := by
      have h := congrArg (fun v : Fin 4 → ℝ => v 0)
        (partialMomentum_sum_eq m L p_int k_ext)
      simpa using h
    have h_term : ∀ i : Fin j,
        (L.partialMomentum m p_int k_ext i 0 : ℂ) * ((x i + euclidTimeVec τ) 0 : ℂ) +
          Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) *
              ((x i + euclidTimeVec τ) 1 : ℂ) +
            (L.partialMomentum m p_int k_ext i 2 : ℂ) * ((x i + euclidTimeVec τ) 2 : ℂ) +
            (L.partialMomentum m p_int k_ext i 3 : ℂ) * ((x i + euclidTimeVec τ) 3 : ℂ)) =
        (L.partialMomentum m p_int k_ext i 0 : ℂ) * (τ : ℂ) +
          ((L.partialMomentum m p_int k_ext i 0 : ℂ) * (x i 0 : ℂ) +
            Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (x i 1 : ℂ) +
              (L.partialMomentum m p_int k_ext i 2 : ℂ) * (x i 2 : ℂ) +
              (L.partialMomentum m p_int k_ext i 3 : ℂ) * (x i 3 : ℂ))) := by
      intro i
      simp [euclidTimeVec]
      ring
    simp_rw [h_term]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, h_sum0,
        Complex.ofReal_neg]
    ring
  rw [fockMomentumVec_mul_totalMomentum M_mode hC j α
    (partialMomentumBound_euclidLaplace hm hx)
    (partialMomentumBound_euclidLaplace hm (timeShift_mem_posOrderedEuclidN j hx hτ))
    hψ_meas zero_le_one
    (fun a => norm_laplaceExp_le_one (fockEnergy_nonneg m a) (ofReal_mem_rightHalfPlane hτ))
    h_eq]
  exact ContinuousLinearMap.ext_iff.mp
    (fockMultCLM_congr _ _ zero_le_one zero_le_one _ _ (fun _ => rfl)) _

theorem fockOSMap_osConfigSpatialShift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (b : Fin 3 → ℝ) (A : OSConfig ι) :
    fockOSMap hm M_mode hC (osConfigSpatialShift b A) =
      fockSpatialTranslate m b (fockOSMap hm M_mode hC A) := by
  rcases A with ⟨j, α, x, hx⟩
  unfold fockOSMap osConfigSpatialShift fockSpatialTranslate
  dsimp only
  have h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      euclidLaplace (fun i => x i + euclidSpatialVec b) (L.partialMomentum m p_int k_ext) =
        fockSpatialPhase b (∑ a : Fin r, massShellVec m (k_ext a)) *
          euclidLaplace x (L.partialMomentum m p_int k_ext) := by
    intro r L p_int k_ext
    unfold euclidLaplace fockSpatialPhase
    rw [← Complex.exp_add]
    congr 1
    have h_sum_μ : ∀ μ : Fin 4,
        (∑ i : Fin j, L.partialMomentum m p_int k_ext i μ) =
          -(∑ a : Fin r, massShellVec m (k_ext a)) μ := by
      intro μ
      have h := congrArg (fun v : Fin 4 → ℝ => v μ)
        (partialMomentum_sum_eq m L p_int k_ext)
      simpa using h
    have h_term : ∀ i : Fin j,
        (L.partialMomentum m p_int k_ext i 0 : ℂ) * ((x i + euclidSpatialVec b) 0 : ℂ) +
          Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) *
              ((x i + euclidSpatialVec b) 1 : ℂ) +
            (L.partialMomentum m p_int k_ext i 2 : ℂ) *
              ((x i + euclidSpatialVec b) 2 : ℂ) +
            (L.partialMomentum m p_int k_ext i 3 : ℂ) *
              ((x i + euclidSpatialVec b) 3 : ℂ)) =
        Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (b 0 : ℂ) +
            (L.partialMomentum m p_int k_ext i 2 : ℂ) * (b 1 : ℂ) +
            (L.partialMomentum m p_int k_ext i 3 : ℂ) * (b 2 : ℂ)) +
          ((L.partialMomentum m p_int k_ext i 0 : ℂ) * (x i 0 : ℂ) +
            Complex.I * ((L.partialMomentum m p_int k_ext i 1 : ℂ) * (x i 1 : ℂ) +
              (L.partialMomentum m p_int k_ext i 2 : ℂ) * (x i 2 : ℂ) +
              (L.partialMomentum m p_int k_ext i 3 : ℂ) * (x i 3 : ℂ))) := by
      intro i
      have hb0 : euclidSpatialVec b 0 = 0 := rfl
      have hb1 : euclidSpatialVec b 1 = b 0 := rfl
      have hb2 : euclidSpatialVec b 2 = b 1 := rfl
      have hb3 : euclidSpatialVec b 3 = b 2 := rfl
      simp only [Pi.add_apply, hb0, hb1, hb2, hb3, add_zero]
      push_cast
      ring
    simp_rw [h_term]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
        h_sum_μ 1, h_sum_μ 2, h_sum_μ 3,
        Complex.ofReal_neg, Complex.ofReal_neg, Complex.ofReal_neg]
    ring
  exact fockMomentumVec_mul_totalMomentum M_mode hC j α
    (partialMomentumBound_euclidLaplace hm hx)
    (partialMomentumBound_euclidLaplace hm (spatialShift_mem_posOrderedEuclidN j hx b))
    (continuous_fockSpatialPhase b).measurable zero_le_one
    (fun a => (norm_fockSpatialPhase b (fockTotalMomentum m a)).le) h_eq

theorem norm_inner_fockSemigroup_sub_fockVacuum_le {ν : ℕ} {m : ℝ} (hm : 0 < m)
    {τ : ℝ} (hτ : 0 ≤ τ) (x y : FockHilbert ν) :
    ‖⟪x, fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) y⟫_ℂ -
        ⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ‖ ≤
      ‖x‖ * ‖y‖ * Real.exp (-(m * τ)) := by
  have hxy_int : Integrable (fun a : FockOmega ν =>
      star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x y).congr (Filter.Eventually.of_forall (fun a => ?_))
    simp [RCLike.inner_apply, mul_comm]
  have h1_int : Integrable (fun a : FockOmega ν =>
      laplaceExp (fockEnergy m a) (τ : ℂ) *
        (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)) (fockMeasure ν) := by
    have h_meas : Measurable (fun a : FockOmega ν => laplaceExp (fockEnergy m a) (τ : ℂ)) :=
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
        (measurable_fockEnergy ν m)
    refine hxy_int.norm.mono' (h_meas.aestronglyMeasurable.mul hxy_int.1)
      (Filter.Eventually.of_forall (fun a => ?_))
    rw [norm_mul]
    calc ‖laplaceExp (fockEnergy m a) (τ : ℂ)‖ *
            ‖star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a‖
        ≤ 1 * ‖star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a‖ :=
          mul_le_mul_of_nonneg_right
            (norm_laplaceExp_le_one (fockEnergy_nonneg m a) (ofReal_mem_rightHalfPlane hτ))
            (norm_nonneg _)
      _ = _ := one_mul _
  have h0_int := integrable_sectorZero_mul_of_integrable hxy_int
  rw [inner_fockSemigroup_eq, inner_fockVacuum_mul_eq_integral, ← integral_sub h1_int h0_int]
  have h_pt : ∀ a : FockOmega ν,
      ‖laplaceExp (fockEnergy m a) (τ : ℂ) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) -
        (if a.1 = 0 then (1 : ℂ) else 0) *
          (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)‖ ≤
      Real.exp (-(m * τ)) * (‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖) := by
    intro a
    rw [← sub_mul, norm_mul, norm_mul, norm_star]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rcases a with ⟨r, z⟩
    by_cases hr : r = 0
    · subst hr
      simp only [fockEnergy_zero, laplaceExp_zero_left, ↓reduceIte, sub_self, norm_zero]
      exact (Real.exp_pos _).le
    · simp only [hr, ↓reduceIte, sub_zero, norm_laplaceExp, Complex.ofReal_re]
      exact Real.exp_le_exp.mpr
        (by nlinarith [fockEnergy_ge_mass_of_ne_zero hm (a := ⟨r, z⟩) hr])
  calc ‖∫ a : FockOmega ν,
          (laplaceExp (fockEnergy m a) (τ : ℂ) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) -
            (if a.1 = 0 then (1 : ℂ) else 0) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)) ∂(fockMeasure ν)‖
      ≤ ∫ a : FockOmega ν,
          ‖laplaceExp (fockEnergy m a) (τ : ℂ) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a) -
            (if a.1 = 0 then (1 : ℂ) else 0) *
              (star ((x : FockOmega ν → ℂ) a) * (y : FockOmega ν → ℂ) a)‖ ∂(fockMeasure ν) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ a : FockOmega ν,
          Real.exp (-(m * τ)) *
            (‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖) ∂(fockMeasure ν) := by
        have h_norm_int : Integrable (fun a : FockOmega ν =>
            ‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖) (fockMeasure ν) := by
          refine hxy_int.norm.congr (Filter.Eventually.of_forall (fun a => ?_))
          simp
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (h_norm_int.const_mul _) (Filter.Eventually.of_forall h_pt)
    _ = Real.exp (-(m * τ)) *
          ∫ a : FockOmega ν,
            ‖(x : FockOmega ν → ℂ) a‖ * ‖(y : FockOmega ν → ℂ) a‖ ∂(fockMeasure ν) :=
        integral_const_mul _ _
    _ ≤ Real.exp (-(m * τ)) * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (lp2_integral_norm_mul_le x y) (Real.exp_pos _).le
    _ = ‖x‖ * ‖y‖ * Real.exp (-(m * τ)) := by ring

theorem wickMassShellOS_exponential_cluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    {τ : ℝ} (hτ : 0 ≤ τ) (A B : OSConfig ι) :
    ‖osKernel S (wickMassShellS m hm η C hC) A (osConfigTimeShift τ hτ B) -
        osKernel S (wickMassShellS m hm η C hC) A (osVacuumConfig ι) *
          osKernel S (wickMassShellS m hm η C hC) (osVacuumConfig ι) B‖ ≤
      ‖fockOSMap hm M_mode hC A‖ * ‖fockOSMap hm M_mode hC B‖ * Real.exp (-(m * τ)) := by
  rw [← inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A (osConfigTimeShift τ hτ B),
      ← inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A (osVacuumConfig ι),
      ← inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm (osVacuumConfig ι) B,
      fockOSMap_osConfigTimeShift hm M_mode hC τ hτ B,
      fockOSMap_osVacuumConfig hm M_mode hC]
  exact norm_inner_fockSemigroup_sub_fockVacuum_le hm hτ
    (fockOSMap hm M_mode hC A) (fockOSMap hm M_mode hC B)

theorem wickMassShellOSTimeCluster {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (D : OSReflectionPositiveData R_rep S)
    (hD : D.𝒮 = wickMassShellS m hm η C hC) :
    OSTimeClusterDecomposition D := by
  intro A B
  rw [hD, tendsto_iff_norm_sub_tendsto_zero]
  have h_tendsto :
      Tendsto (fun τ : ℝ =>
        ‖fockOSMap hm M_mode hC A‖ * ‖fockOSMap hm M_mode hC B‖ *
          Real.exp (-(m * max τ 0))) atTop (𝓝 0) := by
    have h_lin : Tendsto (fun τ : ℝ => -(m * max τ 0)) atTop atBot := by
      have h_max : Filter.Tendsto (fun τ : ℝ => max τ 0) atTop atTop :=
        tendsto_atTop_mono (fun τ => le_max_left τ 0) tendsto_id
      exact tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hm h_max)
    simpa only [Function.comp_def, mul_zero] using
      tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp h_lin)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun τ => wickMassShellOS_exponential_cluster hm M_mode hC hC_herm (le_max_right τ 0) A B)
    h_tendsto

theorem freeKGOSTimeCluster {m : ℝ} (hm : 0 < m) :
    OSTimeClusterDecomposition (freeKGOSAxioms hm).toReflectionPositiveData :=
  wickMassShellOSTimeCluster hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure]) _ rfl

theorem freeDiracOSTimeCluster {m : ℝ} (hm : 0 < m) :
    OSTimeClusterDecomposition (freeDiracOSAxioms hm).toReflectionPositiveData :=
  wickMassShellOSTimeCluster hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m) _ rfl

lemma fockSemigroup_weaklyHolomorphic {ν : ℕ} (m : ℝ) (χ ψ : FockHilbert ν) :
    ∃ F : ℂ → ℂ,
      (∀ (z : ℂ) (hz : z ∈ rightHalfPlane), F z = ⟪χ, fockSemigroup m z hz ψ⟫_ℂ) ∧
      ContinuousOn F rightHalfPlane ∧
      DifferentiableOn ℂ F {z : ℂ | 0 < z.re} := by
  let g : FockOmega ν → ℂ :=
    fun a => star ((χ : FockOmega ν → ℂ) a) * (ψ : FockOmega ν → ℂ) a
  let dom : FockOmega ν → ℝ :=
    fun a => (‖(χ : FockOmega ν → ℂ) a‖ ^ 2 + ‖(ψ : FockOmega ν → ℂ) a‖ ^ 2) / 2
  have hdom_int : Integrable dom (fockMeasure ν) :=
    ((lp2_integrable_norm_sq χ).add (lp2_integrable_norm_sq ψ)).div_const 2
  have hg_le : ∀ a : FockOmega ν, ‖g a‖ ≤ dom a := by
    intro a
    simp only [g, dom, norm_mul, norm_star]
    nlinarith [sq_nonneg (‖(χ : FockOmega ν → ℂ) a‖ - ‖(ψ : FockOmega ν → ℂ) a‖)]
  have hg_meas : AEStronglyMeasurable g (fockMeasure ν) :=
    (Lp.aestronglyMeasurable χ).star.mul (Lp.aestronglyMeasurable ψ)
  have h_meas_F : ∀ z : ℂ,
      AEStronglyMeasurable
        (fun a : FockOmega ν => laplaceExp (fockEnergy m a) z * g a) (fockMeasure ν) := by
    intro z
    have h_lap : Measurable (fun a : FockOmega ν => laplaceExp (fockEnergy m a) z) :=
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
        (measurable_fockEnergy ν m)
    exact h_lap.aestronglyMeasurable.mul hg_meas
  have h_dom_rhp : ∀ {z : ℂ}, z ∈ rightHalfPlane → ∀ a : FockOmega ν,
      ‖laplaceExp (fockEnergy m a) z * g a‖ ≤ dom a := by
    intro z hz a
    rw [norm_mul]
    calc ‖laplaceExp (fockEnergy m a) z‖ * ‖g a‖
        ≤ 1 * dom a :=
          mul_le_mul (norm_laplaceExp_le_one (fockEnergy_nonneg m a) hz) (hg_le a)
            (norm_nonneg _) zero_le_one
      _ = dom a := one_mul _
  let F : ℂ → ℂ := fun z =>
    ∫ a : FockOmega ν, laplaceExp (fockEnergy m a) z * g a ∂(fockMeasure ν)
  refine ⟨F, fun z hz => (inner_fockSemigroup_eq m z hz χ ψ).symm, ?_, ?_⟩
  · exact MeasureTheory.continuousOn_of_dominated
      (fun z _ => h_meas_F z)
      (fun z hz => Filter.Eventually.of_forall (h_dom_rhp hz))
      hdom_int
      (Filter.Eventually.of_forall (fun a =>
        ((differentiable_laplaceExp (fockEnergy m a)).continuous.mul
          continuous_const).continuousOn))
  · intro z₀ hz₀
    have hz₀_pos : 0 < z₀.re := hz₀
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀_pos
    let s : Set ℂ := Metric.ball z₀ r
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr_pos
    have hs_re : ∀ z ∈ s, r ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h_abs : |z.re - z₀.re| < r := (Complex.abs_re_le_norm (z - z₀)).trans_lt hz
      have h_low := (abs_lt.mp h_abs).1
      dsimp [r] at h_low ⊢
      linarith
    let F' : ℂ → FockOmega ν → ℂ :=
      fun z a => (-(fockEnergy m a : ℂ) * laplaceExp (fockEnergy m a) z) * g a
    have hF'_meas : AEStronglyMeasurable (F' z₀) (fockMeasure ν) := by
      have hE_c : Measurable (fun a : FockOmega ν => -(fockEnergy m a : ℂ)) :=
        (continuous_neg.comp Complex.continuous_ofReal).measurable.comp
          (measurable_fockEnergy ν m)
      have h_eq' : F' z₀ = fun a => (-(fockEnergy m a : ℂ)) *
          (laplaceExp (fockEnergy m a) z₀ * g a) := by
        ext a
        dsimp [F']
        ring
      rw [h_eq']
      exact hE_c.aestronglyMeasurable.mul (h_meas_F z₀)
    let bound : FockOmega ν → ℝ := fun a => r⁻¹ * dom a
    have h_bound_int : Integrable bound (fockMeasure ν) := hdom_int.const_mul r⁻¹
    have h_bound : ∀ᵐ a : FockOmega ν ∂(fockMeasure ν), ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
      refine Filter.Eventually.of_forall (fun a z hz => ?_)
      have h_lap_norm : ‖-(fockEnergy m a : ℂ) * laplaceExp (fockEnergy m a) z‖ ≤ r⁻¹ := by
        have h_exp_arg : -z.re * fockEnergy m a = -(fockEnergy m a * z.re) := by ring
        rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (fockEnergy_nonneg m a), norm_laplaceExp, h_exp_arg]
        exact mul_exp_neg_mul_le_inv_of_nonneg (fockEnergy_nonneg m a) hr_pos (hs_re z hz)
      dsimp [F', bound]
      rw [norm_mul]
      exact mul_le_mul h_lap_norm (hg_le a) (norm_nonneg _) (inv_nonneg.mpr hr_pos.le)
    have h_diff : ∀ᵐ a : FockOmega ν ∂(fockMeasure ν), ∀ z ∈ s,
        HasDerivAt (fun w => laplaceExp (fockEnergy m a) w * g a) (F' z a) z := by
      refine Filter.Eventually.of_forall (fun a z _ => ?_)
      have h_lin : HasDerivAt (fun w : ℂ => -w * (fockEnergy m a : ℂ))
          (-1 * (fockEnergy m a : ℂ)) z :=
        (hasDerivAt_id z).neg.mul_const (fockEnergy m a : ℂ)
      have h_mul := h_lin.cexp.mul_const (g a)
      unfold laplaceExp
      exact h_mul.congr_deriv (by dsimp [F', laplaceExp]; ring)
    have hz₀_rhp : z₀ ∈ rightHalfPlane := le_of_lt hz₀_pos
    have hF_z₀_int : Integrable
        (fun a : FockOmega ν => laplaceExp (fockEnergy m a) z₀ * g a) (fockMeasure ν) :=
      hdom_int.mono' (h_meas_F z₀) (Filter.Eventually.of_forall (h_dom_rhp hz₀_rhp))
    have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds (Filter.Eventually.of_forall h_meas_F) hF_z₀_int hF'_meas
      h_bound h_bound_int h_diff).2
    exact h_deriv.differentiableAt.differentiableWithinAt

lemma fockSemigroup_mem_closedSubmodule {ν : ℕ} (m : ℝ)
    {K : Submodule ℂ (FockHilbert ν)} (hK_closed : IsClosed (K : Set (FockHilbert ν)))
    (hK_real : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (ψ : FockHilbert ν),
      ψ ∈ K → fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) ψ ∈ K)
    (z : ℂ) (hz : z ∈ rightHalfPlane) {ψ : FockHilbert ν} (hψ : ψ ∈ K) :
    fockSemigroup m z hz ψ ∈ K := by
  have hK_ortho : Kᗮᗮ = K := by
    rw [K.orthogonal_orthogonal_eq_closure]
    exact SetLike.ext' hK_closed.closure_eq
  rw [← hK_ortho, Submodule.mem_orthogonal]
  intro χ hχ
  rcases fockSemigroup_weaklyHolomorphic m χ ψ with ⟨F, hF_eq, hF_cont, hF_diff⟩
  rw [← hF_eq z hz]
  refine eq_zero_on_rightHalfPlane_of_real_zero hF_diff hF_cont (fun τ hτ => ?_) z hz
  rw [hF_eq (τ : ℂ) (ofReal_mem_rightHalfPlane hτ)]
  exact Submodule.inner_left_of_mem_orthogonal (hK_real τ hτ ψ hψ) hχ

noncomputable def conjugateSubmoduleCLM {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι_E : E →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : ∀ v ∈ LinearMap.range ι_E.toLinearMap,
      T v ∈ LinearMap.range ι_E.toLinearMap) :
    E →L[ℂ] E :=
  let K : Submodule ℂ H := LinearMap.range ι_E.toLinearMap
  let e : E ≃ₗᵢ[ℂ] K := ι_E.equivRange
  let T_K : K →L[ℂ] K :=
    (LinearMap.codRestrict K (T.toLinearMap.comp K.subtype)
      (fun v => hT v.1 v.2)).mkContinuous ‖T‖
      (fun v => by
        change ‖T v.1‖ ≤ ‖T‖ * ‖v.1‖
        exact T.le_opNorm v.1)
  (e.symm.toContinuousLinearEquiv : K →L[ℂ] E).comp
    (T_K.comp (e.toContinuousLinearEquiv : E →L[ℂ] K))

lemma ι_conjugateSubmoduleCLM {E H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι_E : E →ₗᵢ[ℂ] H) (T : H →L[ℂ] H)
    (hT : ∀ v ∈ LinearMap.range ι_E.toLinearMap,
      T v ∈ LinearMap.range ι_E.toLinearMap)
    (x : E) :
    ι_E (conjugateSubmoduleCLM ι_E T hT x) = T (ι_E x) := by
  let K : Submodule ℂ H := LinearMap.range ι_E.toLinearMap
  let e : E ≃ₗᵢ[ℂ] K := ι_E.equivRange
  have he_symm : ∀ u : K, ι_E (e.symm u) = u.1 := by
    intro u
    have h1 : (e (e.symm u)).1 = u.1 := congrArg Subtype.val (e.apply_symm_apply u)
    exact h1
  exact he_symm ⟨T (ι_E x), hT (ι_E x) ⟨x, rfl⟩⟩

noncomputable def wickMassShellOSContinuousSpectralData {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (D : OSReflectionPositiveData R_rep S)
    (hD : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = wickMassShellS m hm η C hC n α x)
    (hcontr : OSContractionCondition D) :
    OSContinuousSpectralData D hcontr (FockOmega M_mode.ν) :=
  let h_ker : ∀ A B : OSConfig ι,
      ⟪fockOSMap hm M_mode hC A, fockOSMap hm M_mode hC B⟫_ℂ = osKernel S D.𝒮 A B := by
    intro A B
    rw [osKernel_congr_of_eq_on_orderedEuclidN S hD A B]
    exact inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A B
  let ι_OS : OSHilbert D →ₗᵢ[ℂ] FockHilbert M_mode.ν :=
    wavepacketOSLinearIsometry D (fockOSMap hm M_mode hC) h_ker
  let K : Submodule ℂ (FockHilbert M_mode.ν) := LinearMap.range ι_OS.toLinearMap
  have hK_closed : IsClosed (K : Set (FockHilbert M_mode.ν)) :=
    ι_OS.isometry.isUniformInducing.isComplete_range.isClosed
  have h_inter_real : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (x : OSHilbert D),
      ι_OS (osContractionSemigroup D hcontr τ hτ x) =
        fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) (ι_OS x) :=
    fun τ hτ x => wavepacketOSLinearIsometry_intertwines_contraction D hcontr
      (fockOSMap hm M_mode hC) h_ker τ hτ
      (fockSemigroup m (τ : ℂ) (ofReal_mem_rightHalfPlane hτ))
      (fockOSMap_osConfigTimeShift hm M_mode hC τ hτ) x
  have hK_inv : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane),
      ∀ v ∈ K, fockSemigroup m z hz v ∈ K := by
    intro z hz v hv
    refine fockSemigroup_mem_closedSubmodule m hK_closed (fun τ hτ ψ hψ => ?_) z hz hv
    rcases hψ with ⟨x, rfl⟩
    exact ⟨osContractionSemigroup D hcontr τ hτ x, h_inter_real τ hτ x⟩
  let Z : ∀ z : ℂ, z ∈ rightHalfPlane → (OSHilbert D →L[ℂ] OSHilbert D) :=
    fun z hz => conjugateSubmoduleCLM ι_OS (fockSemigroup m z hz) (hK_inv z hz)
  have hZ_inter : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane) (x : OSHilbert D),
      ι_OS (Z z hz x) = fockSemigroup m z hz (ι_OS x) :=
    fun z hz x => ι_conjugateSubmoduleCLM ι_OS (fockSemigroup m z hz) (hK_inv z hz) x
  have h_vac : ι_OS (osVacuum D) = fockVacuum M_mode.ν :=
    (wavepacketOSLinearIsometry_osVacuum D (fockOSMap hm M_mode hC) h_ker).trans
      (fockOSMap_osVacuumConfig hm M_mode hC)
  { μ := fockMeasure M_mode.ν
    E := fockEnergy m
    measurable_E := measurable_fockEnergy M_mode.ν m
    energy_nonneg := fockEnergy_nonneg m
    ℰ :=
      { Z := Z
        real_eq := fun τ hτ => by
          ext x
          apply ι_OS.injective
          rw [hZ_inter, h_inter_real]
        map_add := fun z₁ z₂ h₁ h₂ => by
          ext x
          apply ι_OS.injective
          simp only [ContinuousLinearMap.comp_apply, hZ_inter]
          rw [fockSemigroup_add m h₁ h₂, ContinuousLinearMap.comp_apply]
        vacuum := fun z hz => by
          apply ι_OS.injective
          rw [hZ_inter, h_vac, fockSemigroup_fockVacuum]
        contraction := fun z hz x => by
          rw [← ι_OS.norm_map, ← ι_OS.norm_map x, hZ_inter]
          exact norm_fockSemigroup_le m z hz (ι_OS x)
        adjoint_symm := fun z hz x y => by
          rw [← ι_OS.inner_map_map, ← ι_OS.inner_map_map x, hZ_inter, hZ_inter]
          exact fockSemigroup_adjoint_symm m z hz (ι_OS x) (ι_OS y)
        comm_spatial := fun htrans b z hz => by
          have h_sp : ∀ x : OSHilbert D,
              ι_OS (osSpatialTranslate D htrans b x) =
                fockSpatialTranslate m b (ι_OS x) :=
            wavepacketOSLinearIsometry_intertwines_spatial D htrans
              (fockOSMap hm M_mode hC) h_ker b (fockSpatialTranslate m b)
              (fockOSMap_osConfigSpatialShift hm M_mode hC b)
          ext x
          apply ι_OS.injective
          have hc := congrArg (fun T => T (ι_OS x))
            (fockSpatialTranslate_comm_fockSemigroup (ν := M_mode.ν) m b z hz)
          simp only [ContinuousLinearMap.comp_apply] at hc ⊢
          rw [h_sp, hZ_inter, hc, ← h_sp, ← hZ_inter] }
    wave := fun x => (ι_OS x : FockOmega M_mode.ν → ℂ)
    aestronglyMeasurable_wave := fun x => Lp.aestronglyMeasurable (ι_OS x)
    integrable_norm_sq := fun x => lp2_integrable_norm_sq (ι_OS x)
    norm_sq_eq_integral := fun x => by
      rw [← ι_OS.norm_map x]
      exact lp2_norm_sq_eq_integral (ι_OS x)
    semigroup_inner_eq := fun z hz x y => by
      rw [← ι_OS.inner_map_map, hZ_inter]
      exact inner_fockSemigroup_eq m z hz (ι_OS x) (ι_OS y) }

noncomputable def freeKGOSContinuousSpectralData {m : ℝ} (hm : 0 < m) :
    OSContinuousSpectralData (freeKGOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeKGOSAxioms hm).toReflectionPositiveData
        (freeKGOSAxioms hm).os1_translation (freeKGOSTimeCluster hm))
      (FockOmega (kgModeData hm).ν) :=
  wickMassShellOSContinuousSpectralData hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure]) _ (fun _ _ _ _ => rfl) _

noncomputable def freeDiracOSContinuousSpectralData {m : ℝ} (hm : 0 < m) :
    OSContinuousSpectralData (freeDiracOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeDiracOSAxioms hm).toReflectionPositiveData
        (freeDiracOSAxioms hm).os1_translation (freeDiracOSTimeCluster hm))
      (FockOmega (diracModeData hm).ν) :=
  wickMassShellOSContinuousSpectralData hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m) _ (fun _ _ _ _ => rfl) _

noncomputable def freeKGOSHolomorphicSemigroup {m : ℝ} (hm : 0 < m) :
    OSHolomorphicSemigroup (freeKGOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeKGOSAxioms hm).toReflectionPositiveData
        (freeKGOSAxioms hm).os1_translation (freeKGOSTimeCluster hm)) :=
  (freeKGOSContinuousSpectralData hm).ℰ

theorem freeKGOSHolomorphicSemigroup_isWeaklyHolomorphic {m : ℝ} (hm : 0 < m) :
    (freeKGOSHolomorphicSemigroup hm).IsWeaklyHolomorphic :=
  (freeKGOSContinuousSpectralData hm).isWeaklyHolomorphic

noncomputable def freeDiracOSHolomorphicSemigroup {m : ℝ} (hm : 0 < m) :
    OSHolomorphicSemigroup (freeDiracOSAxioms hm).toReflectionPositiveData
      (osContractionCondition_of_timeCluster (freeDiracOSAxioms hm).toReflectionPositiveData
        (freeDiracOSAxioms hm).os1_translation (freeDiracOSTimeCluster hm)) :=
  (freeDiracOSContinuousSpectralData hm).ℰ

theorem freeDiracOSHolomorphicSemigroup_isWeaklyHolomorphic {m : ℝ} (hm : 0 < m) :
    (freeDiracOSHolomorphicSemigroup hm).IsWeaklyHolomorphic :=
  (freeDiracOSContinuousSpectralData hm).isWeaklyHolomorphic

lemma tendsto_integral_exp_I_mul_atTop (f : ℝ → ℂ) :
    Tendsto (fun t : ℝ => ∫ s : ℝ, f s * Complex.exp (Complex.I * (t : ℂ) * (s : ℂ)))
      atTop (𝓝 0) := by
  have hc : Tendsto (fun t : ℝ => -(t / (2 * Real.pi))) atTop (cocompact ℝ) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ) ?_
    have h_pos : (0 : ℝ) < (2 * Real.pi)⁻¹ := inv_pos.mpr (by positivity)
    have h_lin : Tendsto (fun t : ℝ => (2 * Real.pi)⁻¹ * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop h_pos tendsto_id
    refine tendsto_atTop_mono (fun t => ?_) h_lin
    rw [Real.dist_eq, sub_zero, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi),
        div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (le_abs_self t) h_pos.le
  have h_rl := (Real.tendsto_integral_exp_smul_cocompact f).comp hc
  refine h_rl.congr (fun t => ?_)
  dsimp only [Function.comp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun s => ?_))
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  have h_arg : (((2 * Real.pi * -(s * -(t / (2 * Real.pi))) : ℝ) : ℂ) * Complex.I) =
      Complex.I * (t : ℂ) * (s : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hpi]
  rw [h_arg, mul_comm]

lemma tendsto_setIntegral_oscillatory_of_injOn
    {S : Set ℝ} (hS : MeasurableSet S)
    {φ φ' : ℝ → ℝ} (hφ' : ∀ s ∈ S, HasDerivWithinAt φ (φ' s) S s)
    (h_inj : Set.InjOn φ S) (h_ne : ∀ s ∈ S, φ' s ≠ 0)
    (h_img : MeasurableSet (φ '' S)) (g : ℝ → ℂ) :
    Tendsto (fun t : ℝ =>
      ∫ s in S, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
      atTop (𝓝 0) := by
  let H : ℝ → ℂ := Set.indicator (φ '' S)
    (fun u => (|φ' (Function.invFunOn φ S u)|)⁻¹ • g (Function.invFunOn φ S u))
  have h_eq : ∀ t : ℝ,
      (∫ u : ℝ, H u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))) =
        ∫ s in S, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)) := by
    intro t
    let Kt : ℝ → ℂ := fun u => H u * Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))
    have h_ind : Kt = Set.indicator (φ '' S) Kt := by
      ext u
      by_cases hu : u ∈ φ '' S
      · simp [hu]
      · simp [Kt, H, hu]
    change (∫ u : ℝ, Kt u) = _
    rw [h_ind, integral_indicator h_img,
        integral_image_eq_integral_abs_deriv_smul hS hφ' h_inj Kt]
    refine setIntegral_congr_fun hS (fun s hs => ?_)
    dsimp only [Kt, H]
    have hmem : φ s ∈ φ '' S := Set.mem_image_of_mem φ hs
    have hinv : Function.invFunOn φ S (φ s) = s := h_inj.leftInvOn_invFunOn hs
    have habs : |φ' s| ≠ 0 := abs_ne_zero.mpr (h_ne s hs)
    rw [Set.indicator_of_mem hmem, hinv, Complex.real_smul, Complex.real_smul,
        ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ habs,
        Complex.ofReal_one, one_mul]
  exact (tendsto_integral_exp_I_mul_atTop H).congr h_eq

lemma tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
    {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_conv : Convex ℝ S)
    {φ φ' : ℝ → ℝ} (hφ : ∀ s : ℝ, HasDerivAt φ (φ' s) s)
    (h_sign : (∀ s ∈ S, 0 < φ' s) ∨ (∀ s ∈ S, φ' s < 0))
    (g : ℝ → ℂ) :
    Tendsto (fun t : ℝ =>
      ∫ s in S, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
      atTop (𝓝 0) := by
  have hφ_cont : Continuous φ :=
    Differentiable.continuous (𝕜 := ℝ) (fun s => (hφ s).differentiableAt)
  have hφ_within : ∀ s ∈ S, HasDerivWithinAt φ (φ' s) S s :=
    fun s _ => (hφ s).hasDerivWithinAt
  rcases h_sign with h_pos | h_neg
  · have h_sm : StrictMonoOn φ S :=
      strictMonoOn_of_deriv_pos hS_conv hφ_cont.continuousOn
        (fun s hs => by rw [(hφ s).deriv]; exact h_pos s (interior_subset hs))
    exact tendsto_setIntegral_oscillatory_of_injOn hS_meas hφ_within h_sm.injOn
      (fun s hs => (h_pos s hs).ne') (hS_meas.image_of_monotoneOn h_sm.monotoneOn) g
  · have h_sa : StrictAntiOn φ S :=
      strictAntiOn_of_deriv_neg hS_conv hφ_cont.continuousOn
        (fun s hs => by rw [(hφ s).deriv]; exact h_neg s (interior_subset hs))
    exact tendsto_setIntegral_oscillatory_of_injOn hS_meas hφ_within h_sa.injOn
      (fun s hs => (h_neg s hs).ne) (hS_meas.image_of_antitoneOn h_sa.antitoneOn) g

noncomputable def hyperboloidVel (M s : ℝ) : ℝ :=
  s / Real.sqrt (M ^ 2 + s ^ 2)

lemma abs_hyperboloidVel_lt_one {M : ℝ} (hM : 0 < M) (s : ℝ) :
    |hyperboloidVel M s| < 1 := by
  have hden : 0 < Real.sqrt (M ^ 2 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h_lt : |s| < Real.sqrt (M ^ 2 + s ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg s) (by nlinarith [mul_self_pos.mpr hM.ne'])
  unfold hyperboloidVel
  rw [abs_div, abs_of_pos hden, div_lt_one hden]
  exact h_lt

lemma hasDerivAt_sqrt_sq_add_sq {M : ℝ} (hM : 0 < M) (s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sqrt (M ^ 2 + x ^ 2)) (hyperboloidVel M s) s := by
  have h_pos : M ^ 2 + s ^ 2 ≠ 0 := by positivity
  have h_quad : HasDerivAt (fun x : ℝ => M ^ 2 + x ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add (M ^ 2))
  refine (h_quad.sqrt h_pos).congr_deriv ?_
  unfold hyperboloidVel
  have h_sqrt_ne : Real.sqrt (M ^ 2 + s ^ 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp [h_sqrt_ne]

lemma strictMono_hyperboloidVel {M : ℝ} (hM : 0 < M) :
    StrictMono (hyperboloidVel M) := by
  have h_deriv : ∀ s : ℝ,
      HasDerivAt (hyperboloidVel M)
        (M ^ 2 / (Real.sqrt (M ^ 2 + s ^ 2) * (M ^ 2 + s ^ 2))) s := by
    intro s
    have h_pos : 0 < M ^ 2 + s ^ 2 := by positivity
    have h_sqrt_pos : 0 < Real.sqrt (M ^ 2 + s ^ 2) := Real.sqrt_pos.mpr h_pos
    have h_q := (hasDerivAt_id s).div (hasDerivAt_sqrt_sq_add_sq hM s) h_sqrt_pos.ne'
    refine h_q.congr_deriv ?_
    unfold hyperboloidVel
    dsimp only [id_eq]
    have h_sq : Real.sqrt (M ^ 2 + s ^ 2) ^ 2 = M ^ 2 + s ^ 2 := Real.sq_sqrt h_pos.le
    rw [h_sq]
    field_simp [h_sqrt_pos.ne', h_pos.ne']
    rw [h_sq]
    ring
  refine strictMono_of_deriv_pos (fun s => ?_)
  rw [(h_deriv s).deriv]
  have h_pos : 0 < M ^ 2 + s ^ 2 := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (M ^ 2 + s ^ 2) := Real.sqrt_pos.mpr h_pos
  positivity

lemma tendsto_hyperboloid_oscillatory {M : ℝ} (hM : 0 < M)
    {a₀ a₁ : ℝ} (ha₀ : a₀ ≠ 0) (c₀ : ℝ)
    {g : ℝ → ℂ} (hg : Integrable g volume) :
    Tendsto (fun t : ℝ =>
      ∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) *
        ((a₀ * Real.sqrt (M ^ 2 + s ^ 2) - a₁ * s + c₀ : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  let φ : ℝ → ℝ := fun s => a₀ * Real.sqrt (M ^ 2 + s ^ 2) - a₁ * s + c₀
  let φ' : ℝ → ℝ := fun s => a₀ * hyperboloidVel M s - a₁
  have hφ : ∀ s : ℝ, HasDerivAt φ (φ' s) s := by
    intro s
    have h1 := (hasDerivAt_sqrt_sq_add_sq hM s).const_mul a₀
    have h2 : HasDerivAt (fun x : ℝ => a₁ * x) a₁ s := by
      simpa using (hasDerivAt_id s).const_mul a₁
    simpa [φ, φ'] using (h1.sub h2).add_const c₀
  change Tendsto (fun t : ℝ =>
    ∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) atTop (𝓝 0)
  by_cases h_cmp : |a₀| ≤ |a₁|
  · have h_univ : ∀ t : ℝ,
        (∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) =
          ∫ s in Set.univ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)) :=
      fun _ => Measure.restrict_univ.symm ▸ rfl
    rw [funext h_univ]
    refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
      MeasurableSet.univ convex_univ hφ ?_ g
    have h_abs_lt : ∀ s : ℝ, |a₀ * hyperboloidVel M s| < |a₁| := by
      intro s
      rw [abs_mul]
      have hv := abs_hyperboloidVel_lt_one hM s
      have ha₀_pos : 0 < |a₀| := abs_pos.mpr ha₀
      exact (mul_lt_of_lt_one_right ha₀_pos hv).trans_le h_cmp
    by_cases ha₁_nn : 0 ≤ a₁
    · refine Or.inr (fun s _ => ?_)
      have h_lt := (abs_lt.mp (h_abs_lt s)).2
      rw [abs_of_nonneg ha₁_nn] at h_lt
      dsimp [φ']
      linarith
    · refine Or.inl (fun s _ => ?_)
      have ha₁_neg : a₁ < 0 := not_le.mp ha₁_nn
      have h_lt := (abs_lt.mp (h_abs_lt s)).1
      rw [abs_of_neg ha₁_neg] at h_lt
      dsimp [φ']
      linarith
  · have h_cmp_lt : |a₁| < |a₀| := not_le.mp h_cmp
    let r : ℝ := a₁ / a₀
    have hr_abs : |r| < 1 := by
      dsimp [r]
      rw [abs_div, div_lt_one (abs_pos.mpr ha₀)]
      exact h_cmp_lt
    have hr_sq : 0 < 1 - r ^ 2 := by
      have hsq : r ^ 2 < 1 ^ 2 := sq_lt_sq.mpr (by simpa using hr_abs)
      linarith
    let s₀ : ℝ := r * M / Real.sqrt (1 - r ^ 2)
    have hv_s₀ : hyperboloidVel M s₀ = r := by
      have h_root_pos : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.mpr hr_sq
      have h_sum_sq : M ^ 2 + s₀ ^ 2 = M ^ 2 / (1 - r ^ 2) := by
        dsimp [s₀]
        rw [div_pow, mul_pow, Real.sq_sqrt hr_sq.le]
        field_simp [hr_sq.ne']
        ring
      unfold hyperboloidVel
      rw [h_sum_sq, Real.sqrt_div (sq_nonneg M), Real.sqrt_sq hM.le]
      dsimp [s₀]
      field_simp [hM.ne', h_root_pos.ne']
    have hφ'_eq : ∀ s : ℝ, φ' s = a₀ * (hyperboloidVel M s - hyperboloidVel M s₀) := by
      intro s
      dsimp [φ']
      rw [hv_s₀]
      dsimp [r]
      field_simp [ha₀]
    have h_split : ∀ t : ℝ,
        (∫ s : ℝ, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) =
          (∫ s in Set.Iio s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) +
            (∫ s in Set.Ioi s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) := by
      intro t
      let F_t : ℝ → ℂ := fun s => g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))
      have hF_int : Integrable F_t volume := by
        have h_meas : Measurable (fun s : ℝ =>
            Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))) := by
          have hφ_cont : Continuous φ :=
            Differentiable.continuous (𝕜 := ℝ) (fun s => (hφ s).differentiableAt)
          exact Complex.continuous_exp.measurable.comp
            (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hφ_cont.measurable))
        refine hg.norm.mono' (hg.1.mul h_meas.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun s => ?_))
        dsimp [F_t]
        rw [norm_mul]
        have h_exp_norm : ‖Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ))‖ = 1 := by
          have h_im : Complex.I * (t : ℂ) * (φ s : ℂ) = ((t * φ s : ℝ) : ℂ) * Complex.I := by
            push_cast
            ring
          rw [h_im, Complex.norm_exp_ofReal_mul_I]
        rw [h_exp_norm, mul_one]
      have h_union1 : Set.Iio s₀ ∪ Set.Ici s₀ = Set.univ := Set.Iio_union_Ici
      have h_disj1 : Disjoint (Set.Iio s₀) (Set.Ici s₀) :=
        Set.disjoint_left.mpr (fun _ hx₁ hx₂ =>
          not_le_of_gt (Set.mem_Iio.mp hx₁) (Set.mem_Ici.mp hx₂))
      have h_union2 : ({s₀} : Set ℝ) ∪ Set.Ioi s₀ = Set.Ici s₀ := by
        ext x
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_Ici]
        rw [eq_comm]
        exact le_iff_eq_or_lt.symm
      have h_disj2 : Disjoint ({s₀} : Set ℝ) (Set.Ioi s₀) :=
        Set.disjoint_singleton_left.mpr (Set.notMem_Ioi.mpr le_rfl)
      have h_sing : (∫ s in ({s₀} : Set ℝ), F_t s) = 0 := by
        rw [Measure.restrict_eq_zero.mpr (measure_singleton s₀), integral_zero_measure]
      change (∫ s : ℝ, F_t s) = (∫ s in Set.Iio s₀, F_t s) + (∫ s in Set.Ioi s₀, F_t s)
      have h_lhs : (∫ s : ℝ, F_t s) = ∫ s in Set.univ, F_t s :=
        Measure.restrict_univ.symm ▸ rfl
      rw [h_lhs, ← h_union1,
          setIntegral_union h_disj1 measurableSet_Ici hF_int.integrableOn hF_int.integrableOn,
          ← h_union2,
          setIntegral_union h_disj2 measurableSet_Ioi hF_int.integrableOn hF_int.integrableOn,
          h_sing, zero_add]
    rw [funext h_split]
    have h_left : Tendsto (fun t : ℝ =>
        ∫ s in Set.Iio s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
        atTop (𝓝 0) := by
      refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
        measurableSet_Iio (convex_Iio s₀) hφ ?_ g
      rcases lt_or_gt_of_ne ha₀ with ha_neg | ha_pos
      · refine Or.inl (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_pos_of_neg_of_neg ha_neg (sub_neg.mpr (strictMono_hyperboloidVel hM hs))
      · refine Or.inr (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_neg_of_pos_of_neg ha_pos (sub_neg.mpr (strictMono_hyperboloidVel hM hs))
    have h_right : Tendsto (fun t : ℝ =>
        ∫ s in Set.Ioi s₀, g s * Complex.exp (Complex.I * (t : ℂ) * (φ s : ℂ)))
        atTop (𝓝 0) := by
      refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
        measurableSet_Ioi (convex_Ioi s₀) hφ ?_ g
      rcases lt_or_gt_of_ne ha₀ with ha_neg | ha_pos
      · refine Or.inr (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_neg_of_neg_of_pos ha_neg (sub_pos.mpr (strictMono_hyperboloidVel hM hs))
      · refine Or.inl (fun s hs => ?_)
        rw [hφ'_eq s]
        exact mul_pos ha_pos (sub_pos.mpr (strictMono_hyperboloidVel hM hs))
    simpa using h_left.add h_right

theorem tendsto_massShell_oscillatory {m : ℝ} (hm : 0 < m)
    {a : Fin 4 → ℝ} (ha : a ≠ 0)
    {G : (Fin 3 → ℝ) → ℂ} (hG : Integrable G volume) :
    Tendsto (fun t : ℝ =>
      ∫ q : Fin 3 → ℝ,
        G q * Complex.exp (Complex.I * (t : ℂ) * (minkowskiInner (massShellVec m q) a : ℂ)))
      atTop (𝓝 0) := by
  by_cases ha0 : a 0 = 0
  · have hex : ∃ j : Fin 3, a j.succ ≠ 0 := by
      by_contra h_all
      apply ha
      ext μ
      refine Fin.cases ha0 (fun j => not_ne_iff.mp (fun hj => h_all ⟨j, hj⟩)) μ
    rcases hex with ⟨j, hj⟩
    let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j).symm
    have hG_prod : Integrable (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq)) (volume.prod volume) :=
      (mp.integrable_comp_emb e.measurableEmbedding).mpr hG
    have h_int_prod : ∀ t : ℝ, Integrable
        (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq) * Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ)))
        (volume.prod volume) := by
      intro t
      have h_cont : Continuous (fun q : Fin 3 → ℝ =>
          Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) := by
        have h_in : Continuous (fun q : Fin 3 → ℝ => minkowskiInner (massShellVec m q) a) := by
          simp only [minkowskiInner_explicit]
          have hc : ∀ μ : Fin 4, Continuous (fun q : Fin 3 → ℝ => massShellVec m q μ) :=
            fun μ => (continuous_apply μ).comp (continuous_massShellVec m)
          exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
            ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
        exact Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp h_in))
      refine hG_prod.norm.mono'
        (hG_prod.1.mul (h_cont.measurable.comp e.measurable).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun sq => ?_))
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) * (minkowskiInner (massShellVec m (e sq)) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e sq)) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    have h_fub : ∀ t : ℝ,
        (∫ q : Fin 3 → ℝ,
          G q * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) =
        ∫ q' : Fin 2 → ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) := by
      intro t
      rw [← mp.integral_comp']
      exact integral_prod_symm _ (h_int_prod t)
    rw [funext h_fub]
    have h_dom_int : Integrable
        (fun q' : Fin 2 → ℝ => ∫ s : ℝ, ‖G (e (s, q'))‖) volume :=
      hG_prod.norm.integral_prod_right
    have h0_int : (0 : ℂ) = ∫ _ : Fin 2 → ℝ, (0 : ℂ) := by simp
    rw [h0_int]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun q' => ∫ s : ℝ, ‖G (e (s, q'))‖) ?_ ?_ h_dom_int ?_
    · exact Filter.Eventually.of_forall (fun t => (h_int_prod t).integral_prod_right.1)
    · refine Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun q' => ?_))
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Filter.Eventually.of_forall (fun s => ?_))))
      dsimp only
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e (s, q'))) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    · refine Filter.Eventually.of_forall (fun q' => ?_)
      have h_lin_phase : ∃ c₀ : ℝ, ∀ s : ℝ,
          minkowskiInner (massShellVec m (e (s, q'))) a = -(a j.succ) * s + c₀ := by
        fin_cases j
        · refine ⟨-(q' 0 * a 2 + q' 1 * a 3), fun s => ?_⟩
          have he0 : e (s, q') 0 = s := by simp [e]
          have he1 : e (s, q') 1 = q' 0 := by simp [e]
          have he2 : e (s, q') 2 = q' 1 := by
            suffices h : @Fin.cons 2 (fun _ => ℝ) s q' 2 = q' 1 by simpa [e] using h
            rw [← Fin.succ_one_eq_two, Fin.cons_succ]
          simp [minkowskiInner_explicit, massShellVec, ha0, he0, he1, he2]
          ring
        · refine ⟨-(q' 0 * a 1 + q' 1 * a 3), fun s => ?_⟩
          have hi0 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 1 s q' 0 = q' 0 := rfl
          have hi2 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 1 s q' 2 = q' 1 := rfl
          simp [e, minkowskiInner_explicit, massShellVec, ha0, hi0, hi2]
          ring
        · refine ⟨-(q' 0 * a 1 + q' 1 * a 2), fun s => ?_⟩
          have hi0 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 2 s q' 0 = q' 0 := rfl
          have hi1 : Fin.insertNth (α := fun _ : Fin 3 => ℝ) 2 s q' 1 = q' 1 := rfl
          simp [e, minkowskiInner_explicit, massShellVec, ha0, hi0, hi1]
          ring
      rcases h_lin_phase with ⟨c₀, hc₀⟩
      have h_univ : ∀ t : ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) =
          ∫ s in Set.univ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            ((-(a j.succ) * s + c₀ : ℝ) : ℂ)) := by
        intro t
        rw [Measure.restrict_univ]
        exact integral_congr_ae (Filter.Eventually.of_forall (fun s => by dsimp only; rw [hc₀ s]))
      rw [funext h_univ]
      have h_deriv : ∀ s : ℝ, HasDerivAt (fun x : ℝ => -(a j.succ) * x + c₀) (-(a j.succ)) s := by
        intro s
        simpa using ((hasDerivAt_id s).const_mul (-(a j.succ))).add_const c₀
      refine tendsto_setIntegral_oscillatory_of_hasDerivAt_sign
        MeasurableSet.univ convex_univ h_deriv ?_ (fun s => G (e (s, q')))
      rcases lt_or_gt_of_ne (neg_ne_zero.mpr hj) with hneg | hpos
      · exact Or.inr (fun _ _ => hneg)
      · exact Or.inl (fun _ _ => hpos)
  · let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
    have hG_prod : Integrable (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq)) (volume.prod volume) :=
      (mp.integrable_comp_emb e.measurableEmbedding).mpr hG
    have h_int_prod : ∀ t : ℝ, Integrable
        (fun sq : ℝ × (Fin 2 → ℝ) => G (e sq) * Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ)))
        (volume.prod volume) := by
      intro t
      have h_cont : Continuous (fun q : Fin 3 → ℝ =>
          Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) := by
        have h_in : Continuous (fun q : Fin 3 → ℝ => minkowskiInner (massShellVec m q) a) := by
          simp only [minkowskiInner_explicit]
          have hc : ∀ μ : Fin 4, Continuous (fun q : Fin 3 → ℝ => massShellVec m q μ) :=
            fun μ => (continuous_apply μ).comp (continuous_massShellVec m)
          exact (((hc 0).mul continuous_const).sub ((hc 1).mul continuous_const)).sub
            ((hc 2).mul continuous_const) |>.sub ((hc 3).mul continuous_const)
        exact Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp h_in))
      refine hG_prod.norm.mono'
        (hG_prod.1.mul (h_cont.measurable.comp e.measurable).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun sq => ?_))
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e sq)) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) * (minkowskiInner (massShellVec m (e sq)) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e sq)) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    have h_fub : ∀ t : ℝ,
        (∫ q : Fin 3 → ℝ,
          G q * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m q) a : ℂ))) =
        ∫ q' : Fin 2 → ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) := by
      intro t
      rw [← mp.integral_comp']
      exact integral_prod_symm _ (h_int_prod t)
    rw [funext h_fub]
    have h_dom_int : Integrable
        (fun q' : Fin 2 → ℝ => ∫ s : ℝ, ‖G (e (s, q'))‖) volume :=
      hG_prod.norm.integral_prod_right
    have h_ae_int : ∀ᵐ q' : Fin 2 → ℝ ∂volume,
        Integrable (fun s : ℝ => G (e (s, q'))) volume :=
      (integrable_prod_iff' hG_prod.1).mp hG_prod |>.1
    have h0_int : (0 : ℂ) = ∫ _ : Fin 2 → ℝ, (0 : ℂ) := by simp
    rw [h0_int]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun q' => ∫ s : ℝ, ‖G (e (s, q'))‖) ?_ ?_ h_dom_int ?_
    · exact Filter.Eventually.of_forall (fun t => (h_int_prod t).integral_prod_right.1)
    · refine Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun q' => ?_))
      refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
        (Filter.Eventually.of_forall (fun s => ?_))))
      dsimp only
      rw [norm_mul]
      have h_en : ‖Complex.exp (Complex.I * (t : ℂ) *
          (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))‖ = 1 := by
        have h_im : Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ) =
            ((t * minkowskiInner (massShellVec m (e (s, q'))) a : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h_im, Complex.norm_exp_ofReal_mul_I]
      rw [h_en, mul_one]
    · filter_upwards [h_ae_int] with q' hGq'
      let M : ℝ := Real.sqrt (m ^ 2 + (q' 0) ^ 2 + (q' 1) ^ 2)
      have hM_pos : 0 < M := Real.sqrt_pos.mpr (by positivity)
      let c₀ : ℝ := -(q' 0 * a 2 + q' 1 * a 3)
      have h_phase : ∀ s : ℝ,
          minkowskiInner (massShellVec m (e (s, q'))) a =
            a 0 * Real.sqrt (M ^ 2 + s ^ 2) - a 1 * s + c₀ := by
        intro s
        have hM_sq : M ^ 2 = m ^ 2 + (q' 0) ^ 2 + (q' 1) ^ 2 :=
          Real.sq_sqrt (by positivity)
        have he0 : e (s, q') 0 = s := by simp [e]
        have he1 : e (s, q') 1 = q' 0 := by simp [e]
        have he2 : e (s, q') 2 = q' 1 := by
          suffices h : @Fin.cons 2 (fun _ => ℝ) s q' 2 = q' 1 by simpa [e] using h
          rw [← Fin.succ_one_eq_two, Fin.cons_succ]
        have h_en_eq : massShellEnergy m (e (s, q')) = Real.sqrt (M ^ 2 + s ^ 2) := by
          unfold massShellEnergy massShellSpatialSq
          rw [he0, he1, he2]
          congr 1
          rw [hM_sq]
          ring
        simp [minkowskiInner_explicit, massShellVec, he0, he1, he2, h_en_eq]
        dsimp [c₀]
        ring
      have h_phase_int : ∀ t : ℝ,
          (∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            (minkowskiInner (massShellVec m (e (s, q'))) a : ℂ))) =
          ∫ s : ℝ, G (e (s, q')) * Complex.exp (Complex.I * (t : ℂ) *
            ((a 0 * Real.sqrt (M ^ 2 + s ^ 2) - a 1 * s + c₀ : ℝ) : ℂ)) :=
        fun _ => integral_congr_ae (Filter.Eventually.of_forall (fun s => by
          dsimp only; rw [h_phase s]))
      rw [funext h_phase_int]
      exact tendsto_hyperboloid_oscillatory hM_pos ha0 c₀ hGq'

noncomputable def fockMinkowskiPhase (b : Fin 4 → ℝ) (P : Fin 4 → ℝ) : ℂ :=
  Complex.exp (Complex.I * (minkowskiInner P b : ℂ))

lemma continuous_fockMinkowskiPhase (b : Fin 4 → ℝ) :
    Continuous (fockMinkowskiPhase b) := by
  unfold fockMinkowskiPhase
  have h_in : Continuous (fun P : Fin 4 → ℝ => minkowskiInner P b) := by
    simp only [minkowskiInner_explicit]
    exact (((continuous_apply 0).mul continuous_const).sub
      ((continuous_apply 1).mul continuous_const)).sub
      ((continuous_apply 2).mul continuous_const) |>.sub
      ((continuous_apply 3).mul continuous_const)
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp h_in))

lemma norm_fockMinkowskiPhase (b : Fin 4 → ℝ) (P : Fin 4 → ℝ) :
    ‖fockMinkowskiPhase b P‖ = 1 := by
  unfold fockMinkowskiPhase
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

noncomputable def fockMinkowskiTranslate {ν : ℕ} (m : ℝ) (b : Fin 4 → ℝ) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fun z => fockMinkowskiPhase b (fockTotalMomentum m z))
    ((continuous_fockMinkowskiPhase b).measurable.comp (measurable_fockTotalMomentum ν m))
    zero_le_one
    (fun z => (norm_fockMinkowskiPhase b (fockTotalMomentum m z)).le)

theorem fockWightmanMap_wightmanConfigTranslate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (b : Fin 4 → ℝ) (A : WightmanConfig ι) :
    fockWightmanMap M_mode hC (wightmanConfigTranslate b A) =
      fockMinkowskiTranslate m b (fockWightmanMap M_mode hC A) := by
  rcases A with ⟨j, α, f⟩
  unfold fockWightmanMap fockSchwartzVec wightmanConfigTranslate fockMinkowskiTranslate
  dsimp only [compactSchwartzTranslate_val]
  have h_eq : ∀ (r : ℕ) (L : PartialPairing j r)
      (p_int : L.InternalChord → Fin 3 → ℝ) (k_ext : Fin r → Fin 3 → ℝ),
      minkowskiFourier (schwartzDiagTranslateN j b f.val) (L.partialMomentum m p_int k_ext) =
        fockMinkowskiPhase b (∑ a : Fin r, massShellVec m (k_ext a)) *
          minkowskiFourier f.val (L.partialMomentum m p_int k_ext) := by
    intro r L p_int k_ext
    rw [minkowskiFourier_schwartzDiagTranslateN, partialMomentum_sum_eq m L p_int k_ext]
    unfold fockMinkowskiPhase
    congr 1
    have h_neg : minkowskiInner (-∑ a : Fin r, massShellVec m (k_ext a)) b =
        -minkowskiInner (∑ a : Fin r, massShellVec m (k_ext a)) b := by
      simp only [minkowskiInner_explicit, Pi.neg_apply]
      ring
    rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg]
  exact fockMomentumVec_mul_totalMomentum M_mode hC j α
    (partialMomentumBound_minkowskiFourier m j f.val)
    (partialMomentumBound_minkowskiFourier m j (schwartzDiagTranslateN j b f.val))
    (continuous_fockMinkowskiPhase b).measurable zero_le_one
    (fun z => (norm_fockMinkowskiPhase b (fockTotalMomentum m z)).le) h_eq

theorem tendsto_inner_fockMinkowskiTranslate_atTop {ν : ℕ} {m : ℝ} (hm : 0 < m)
    {a : Fin 4 → ℝ} (ha : a ≠ 0) (x y : FockHilbert ν) :
    Tendsto (fun t : ℝ => ⟪x, fockMinkowskiTranslate m (t • a) y⟫_ℂ)
      atTop (𝓝 (⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ)) := by
  rw [tendsto_sub_nhds_zero_iff.symm]
  let h : FockOmega ν → ℂ :=
    fun z => star ((x : FockOmega ν → ℂ) z) * (y : FockOmega ν → ℂ) z
  have hh_int : Integrable h (fockMeasure ν) := by
    refine (L2.integrable_inner (𝕜 := ℂ) x y).congr (Filter.Eventually.of_forall (fun z => ?_))
    simp [h, RCLike.inner_apply, mul_comm]
  let F_t : ℝ → FockOmega ν → ℂ := fun t z =>
    (fockMinkowskiPhase (t • a) (fockTotalMomentum m z) -
      (if z.1 = 0 then (1 : ℂ) else 0)) * h z
  have hF_meas : ∀ t : ℝ, AEStronglyMeasurable (F_t t) (fockMeasure ν) := by
    intro t
    have h_ind_eq : (fun z : FockOmega ν => if z.1 = 0 then (1 : ℂ) else 0) =
        sectorToOmega ν 0 (fun _ => (1 : ℂ)) := by
      ext z
      by_cases h0 : z.1 = 0 <;> simp [sectorToOmega, h0]
    have h_ind : Measurable (fun z : FockOmega ν => if z.1 = 0 then (1 : ℂ) else 0) := by
      rw [h_ind_eq]
      exact measurable_sectorToOmega measurable_const
    have h_ph : Measurable (fun z : FockOmega ν =>
        fockMinkowskiPhase (t • a) (fockTotalMomentum m z)) :=
      (continuous_fockMinkowskiPhase (t • a)).measurable.comp (measurable_fockTotalMomentum ν m)
    exact (h_ph.sub h_ind).aestronglyMeasurable.mul hh_int.1
  have hF_le : ∀ (t : ℝ) (z : FockOmega ν), ‖F_t t z‖ ≤ 2 * ‖h z‖ := by
    intro t z
    dsimp [F_t]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_fockMinkowskiPhase]
    by_cases h0 : z.1 = 0
    · simp [h0]
      norm_num
    · simp [h0]
  have hF_int : ∀ t : ℝ, Integrable (F_t t) (fockMeasure ν) :=
    fun t => (hh_int.norm.const_mul 2).mono' (hF_meas t)
      (Filter.Eventually.of_forall (hF_le t))
  have h_diff_eq : ∀ t : ℝ,
      ⟪x, fockMinkowskiTranslate m (t • a) y⟫_ℂ -
        ⟪x, fockVacuum ν⟫_ℂ * ⟪fockVacuum ν, y⟫_ℂ =
      ∑' r : ℕ, ∫ w : FockSectorDom ν r, F_t t ⟨r, w⟩ ∂(fockSectorMeasure ν r) := by
    intro t
    unfold fockMinkowskiTranslate
    rw [inner_fockMultCLM_right, inner_fockVacuum_mul_eq_integral,
        ← integral_sub (by
          refine hh_int.norm.mono'
            (((continuous_fockMinkowskiPhase (t • a)).measurable.comp
              (measurable_fockTotalMomentum ν m)).aestronglyMeasurable.mul hh_int.1)
            (Filter.Eventually.of_forall (fun z => ?_))
          rw [norm_mul, norm_fockMinkowskiPhase, one_mul])
          (integrable_sectorZero_mul_of_integrable hh_int)]
    have h_sub : (fun z : FockOmega ν =>
        fockMinkowskiPhase (t • a) (fockTotalMomentum m z) * h z -
          (if z.1 = 0 then (1 : ℂ) else 0) * h z) = F_t t := by
      ext z
      dsimp [F_t]
      ring
    rw [h_sub]
    have h_int_sum := hF_int t
    unfold fockMeasure at h_int_sum ⊢
    rw [integral_sum_measure h_int_sum]
    refine tsum_congr (fun r => ?_)
    have hr_int : Integrable (F_t t) ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
      h_int_sum.mono_measure (Measure.le_sum _ r)
    exact integral_map (measurable_fockSigmaMk ν r).aemeasurable hr_int.1
  rw [funext h_diff_eq]
  let B_sec : ℕ → ℝ := fun r =>
    ∫ z : FockOmega ν, 2 * ‖h z‖ ∂((fockSectorMeasure ν r).map (Sigma.mk r))
  have hB_summable : Summable B_sec := by
    have hh2 : Integrable (fun z : FockOmega ν => 2 * ‖h z‖) (fockMeasure ν) :=
      hh_int.norm.const_mul 2
    unfold fockMeasure at hh2
    exact (hasSum_integral_measure hh2).summable
  have hB_eq : ∀ r : ℕ, B_sec r =
      ∫ w : FockSectorDom ν r, 2 * ‖h ⟨r, w⟩‖ ∂(fockSectorMeasure ν r) := by
    intro r
    have hr_int : Integrable (fun z : FockOmega ν => 2 * ‖h z‖)
        ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
      (hh_int.norm.const_mul 2).mono_measure (Measure.le_sum _ r)
    exact integral_map (measurable_fockSigmaMk ν r).aemeasurable hr_int.1
  have h0_tsum : (0 : ℂ) = ∑' _ : ℕ, (0 : ℂ) := tsum_zero.symm
  rw [h0_tsum]
  refine tendsto_tsum_of_dominated_convergence hB_summable (fun r => ?_)
    (Filter.Eventually.of_forall (fun t r => ?_))
  · cases r with
    | zero =>
      have h0 : (fun t : ℝ =>
          ∫ w : FockSectorDom ν 0, F_t t ⟨0, w⟩ ∂(fockSectorMeasure ν 0)) = fun _ => 0 := by
        ext t
        have hw0 : (fun w : FockSectorDom ν 0 => F_t t ⟨0, w⟩) = fun _ => 0 := by
          ext w
          simp [F_t, fockMinkowskiPhase, minkowskiInner_explicit]
        rw [hw0, integral_zero]
      rw [h0]
      exact tendsto_const_nhds
    | succ r' =>
      have hh_sec : Integrable (fun w : FockSectorDom ν (r' + 1) => h ⟨r' + 1, w⟩)
          (fockSectorMeasure ν (r' + 1)) := by
        have hm_map : Integrable h ((fockSectorMeasure ν (r' + 1)).map (Sigma.mk (r' + 1))) :=
          hh_int.mono_measure (Measure.le_sum _ (r' + 1))
        exact (integrable_map_measure hm_map.1
          (measurable_fockSigmaMk ν (r' + 1)).aemeasurable).mp hm_map
      have hF_sec : ∀ t : ℝ, Integrable (fun w : FockSectorDom ν (r' + 1) => F_t t ⟨r' + 1, w⟩)
          (fockSectorMeasure ν (r' + 1)) := by
        intro t
        have hm_map : Integrable (F_t t)
            ((fockSectorMeasure ν (r' + 1)).map (Sigma.mk (r' + 1))) :=
          (hF_int t).mono_measure (Measure.le_sum _ (r' + 1))
        exact (integrable_map_measure hm_map.1
          (measurable_fockSigmaMk ν (r' + 1)).aemeasurable).mp hm_map
      have h_fub_s : ∀ t : ℝ,
          (∫ w : FockSectorDom ν (r' + 1), F_t t ⟨r' + 1, w⟩
            ∂(fockSectorMeasure ν (r' + 1))) =
          ∑ s : Fin (r' + 1) → Fin ν,
            ∫ k : Fin (r' + 1) → Fin 3 → ℝ, F_t t ⟨r' + 1, (k, s)⟩ := by
        intro t
        have hf := hF_sec t
        unfold fockSectorMeasure at hf ⊢
        rw [integral_prod_symm _ hf, integral_fintype_count]
      rw [funext h_fub_s]
      have hh_s_ae : ∀ᵐ s : Fin (r' + 1) → Fin ν ∂Measure.count,
          Integrable (fun k : Fin (r' + 1) → Fin 3 → ℝ => h ⟨r' + 1, (k, s)⟩) volume := by
        unfold fockSectorMeasure at hh_sec
        exact ((integrable_prod_iff' hh_sec.1).mp hh_sec).1
      have hh_s : ∀ s : Fin (r' + 1) → Fin ν,
          Integrable (fun k : Fin (r' + 1) → Fin 3 → ℝ => h ⟨r' + 1, (k, s)⟩) volume := by
        rwa [Measure.ae_count_iff] at hh_s_ae
      have h0_sum : (0 : ℂ) = ∑ _ : Fin (r' + 1) → Fin ν, (0 : ℂ) :=
        Finset.sum_const_zero.symm
      rw [h0_sum]
      refine tendsto_finsetSum (Finset.univ : Finset (Fin (r' + 1) → Fin ν)) (fun s _ => ?_)
      let mp := (volume_preserving_piFinSuccAbove
        (fun _ : Fin (r' + 1) => Fin 3 → ℝ) 0).symm
      let e := (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r' + 1) => Fin 3 → ℝ) 0).symm
      have h_hs_prod : Integrable
          (fun qk : (Fin 3 → ℝ) × (Fin r' → Fin 3 → ℝ) => h ⟨r' + 1, (e qk, s)⟩)
          (volume.prod volume) :=
        (mp.integrable_comp_emb e.measurableEmbedding).mpr (hh_s s)
      have h_Fs_prod : ∀ t : ℝ, Integrable
          (fun qk : (Fin 3 → ℝ) × (Fin r' → Fin 3 → ℝ) => F_t t ⟨r' + 1, (e qk, s)⟩)
          (volume.prod volume) := by
        intro t
        have hFs_ae : ∀ᵐ s' : Fin (r' + 1) → Fin ν ∂Measure.count,
            Integrable (fun k : Fin (r' + 1) → Fin 3 → ℝ =>
              F_t t ⟨r' + 1, (k, s')⟩) volume := by
          have hf := hF_sec t
          unfold fockSectorMeasure at hf
          exact ((integrable_prod_iff' hf.1).mp hf).1
        rw [Measure.ae_count_iff] at hFs_ae
        exact (mp.integrable_comp_emb e.measurableEmbedding).mpr (hFs_ae s)
      have h_split_k : ∀ t : ℝ,
          (∫ k : Fin (r' + 1) → Fin 3 → ℝ, F_t t ⟨r' + 1, (k, s)⟩) =
          ∫ k' : Fin r' → Fin 3 → ℝ,
            (∫ q : Fin 3 → ℝ, F_t t ⟨r' + 1, (e (q, k'), s)⟩) := by
        intro t
        rw [← mp.integral_comp']
        exact integral_prod_symm _ (h_Fs_prod t)
      rw [funext h_split_k]
      have h_dom_k' : Integrable
          (fun k' : Fin r' → Fin 3 → ℝ => ∫ q : Fin 3 → ℝ, ‖h ⟨r' + 1, (e (q, k'), s)⟩‖)
          volume :=
        h_hs_prod.norm.integral_prod_right
      have h_ae_k' : ∀ᵐ k' : Fin r' → Fin 3 → ℝ ∂volume,
          Integrable (fun q : Fin 3 → ℝ => h ⟨r' + 1, (e (q, k'), s)⟩) volume :=
        ((integrable_prod_iff' h_hs_prod.1).mp h_hs_prod).1
      have h0_k' : (0 : ℂ) = ∫ _ : Fin r' → Fin 3 → ℝ, (0 : ℂ) := by simp
      rw [h0_k']
      refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
        (fun k' => ∫ q : Fin 3 → ℝ, ‖h ⟨r' + 1, (e (q, k'), s)⟩‖) ?_ ?_ h_dom_k' ?_
      · exact Filter.Eventually.of_forall (fun t => (h_Fs_prod t).integral_prod_right.1)
      · refine Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (fun k' => ?_))
        refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
          (Filter.Eventually.of_forall (fun q => ?_))))
        dsimp [F_t]
        simp only [sub_zero, norm_mul, norm_fockMinkowskiPhase, one_mul]
      · filter_upwards [h_ae_k'] with k' hk'
        let P_rest : Fin 4 → ℝ := ∑ i : Fin r', massShellVec m (k' i)
        have h_fac : ∀ t : ℝ,
            (∫ q : Fin 3 → ℝ, F_t t ⟨r' + 1, (e (q, k'), s)⟩) =
            fockMinkowskiPhase (t • a) P_rest *
              ∫ q : Fin 3 → ℝ, h ⟨r' + 1, (e (q, k'), s)⟩ *
                Complex.exp (Complex.I * (t : ℂ) *
                  (minkowskiInner (massShellVec m q) a : ℂ)) := by
          intro t
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun q => ?_))
          dsimp only [F_t]
          simp only [Nat.succ_ne_zero, ↓reduceIte, sub_zero]
          have he_cons : e (q, k') = Fin.cons q k' := by
            ext i
            refine Fin.cases ?_ ?_ i <;> simp [e]
          have h_tot : fockTotalMomentum m ⟨r' + 1, (e (q, k'), s)⟩ =
              massShellVec m q + P_rest := by
            unfold fockTotalMomentum
            dsimp only
            rw [he_cons, Fin.sum_univ_succ]
            simp [P_rest]
          have h_ph_mul : fockMinkowskiPhase (t • a) (massShellVec m q + P_rest) =
              fockMinkowskiPhase (t • a) P_rest *
                Complex.exp (Complex.I * (t : ℂ) *
                  (minkowskiInner (massShellVec m q) a : ℂ)) := by
            unfold fockMinkowskiPhase
            rw [← Complex.exp_add]
            congr 1
            have h_lin : minkowskiInner (massShellVec m q + P_rest) (t • a) =
                minkowskiInner P_rest (t • a) +
                  t * minkowskiInner (massShellVec m q) a := by
              simp only [minkowskiInner_explicit, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              ring
            rw [h_lin]
            push_cast
            ring
          rw [h_tot, h_ph_mul]
          ring
        rw [funext h_fac]
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have h_osc := (tendsto_zero_iff_norm_tendsto_zero.mp
          (tendsto_massShell_oscillatory hm ha hk'))
        refine h_osc.congr (fun t => ?_)
        rw [norm_mul, norm_fockMinkowskiPhase, one_mul]
  · rw [hB_eq r]
    have h_dom_sec : Integrable (fun w : FockSectorDom ν r => 2 * ‖h ⟨r, w⟩‖)
        (fockSectorMeasure ν r) := by
      have hm_map : Integrable (fun z : FockOmega ν => 2 * ‖h z‖)
          ((fockSectorMeasure ν r).map (Sigma.mk r)) :=
        (hh_int.norm.const_mul 2).mono_measure (Measure.le_sum _ r)
      exact (integrable_map_measure hm_map.1
        (measurable_fockSigmaMk ν r).aemeasurable).mp hm_map
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        h_dom_sec (Filter.Eventually.of_forall (fun w => hF_le t ⟨r, w⟩)))

theorem wickMassShellWightmanClusterAlong {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (WData : WightmanPositiveData R_rep S)
    (hW : WData.W = wickMassShellW m η C hC)
    {a : Fin 4 → ℝ} (ha : a ≠ 0) :
    WightmanClusterAlong WData a := by
  have htr : WightmanTranslationInvariant WData.W := by
    rw [hW]
    exact wightmanTranslationInvariant_of_tubeTranslationInvariant
      (wickMassShellTubeExtension m hm η C hC)
      (wickMassShellTubeTranslationInvariant hm η hC)
  have h_ker : ∀ A B : WightmanConfig ι,
      ⟪fockWightmanMap M_mode hC A, fockWightmanMap M_mode hC B⟫_ℂ =
        wightmanKernel S WData.W A B := by
    intro A B
    rw [hW]
    exact inner_fockWightmanMap_eq_wightmanKernel M_mode hC hC_herm A B
  let ι_W := wavepacketWightmanLinearIsometry WData (fockWightmanMap M_mode hC) h_ker
  have hvac : ι_W (wightmanVacuum WData) = fockVacuum M_mode.ν :=
    (wavepacketWightmanLinearIsometry_wightmanVacuum WData
      (fockWightmanMap M_mode hC) h_ker).trans
      (fockWightmanMap_wightmanVacuumConfig M_mode hC)
  exact wightmanClusterAlong_of_linearIsometry WData htr ι_W hvac
    (fockMinkowskiTranslate m)
    (wavepacketWightmanLinearIsometry_intertwines_translate WData htr
      (fockWightmanMap M_mode hC) h_ker (fockMinkowskiTranslate m)
      (fockWightmanMap_wightmanConfigTranslate M_mode hC))
    (tendsto_inner_fockMinkowskiTranslate_atTop hm ha)

theorem wickMassShellWightmanVacuumUnique {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (WData : WightmanPositiveData R_rep S)
    (hW : WData.W = wickMassShellW m η C hC)
    (htrans : WightmanTranslationInvariant WData.W) :
    WightmanVacuumUnique WData htrans := by
  have ha : euclidTimeVec 1 ≠ 0 := by
    intro h0
    have h1 : euclidTimeVec 1 0 = (0 : Fin 4 → ℝ) 0 := congrArg (fun v => v 0) h0
    norm_num [euclidTimeVec] at h1
  exact wightmanVacuumUnique_of_clusterAlong WData htrans
    (wickMassShellWightmanClusterAlong hm M_mode hC hC_herm WData hW ha)

theorem wickMassShellWightmanVacuumNormalized {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanVacuumNormalized S (wickMassShellW m η C hC) := by
  let WData := wightmanPositiveDataOfPositivity S (wickMassShellW m η C hC)
    (wickMassShellPositivity M_mode hC hC_herm)
  have h_ker : ∀ A B : WightmanConfig ι,
      ⟪fockWightmanMap M_mode hC A, fockWightmanMap M_mode hC B⟫_ℂ =
        wightmanKernel S WData.W A B :=
    inner_fockWightmanMap_eq_wightmanKernel M_mode hC hC_herm
  let ι_W := wavepacketWightmanLinearIsometry WData (fockWightmanMap M_mode hC) h_ker
  have hvac : ι_W (wightmanVacuum WData) = fockVacuum M_mode.ν :=
    (wavepacketWightmanLinearIsometry_wightmanVacuum WData
      (fockWightmanMap M_mode hC) h_ker).trans
      (fockWightmanMap_wightmanVacuumConfig M_mode hC)
  exact wightmanVacuumNormalized_of_linearIsometry WData ι_W hvac (inner_fockVacuum_self M_mode.ν)

lemma ChordPairing.card_chord_eq {n : ℕ} (P : ChordPairing n) :
    Fintype.card P.Chord = n / 2 := by
  have h := P.two_mul_card_chord
  omega

noncomputable def toChordMom {n : ℕ} (P : ChordPairing n) :
    (Fin (n / 2) → Fin 3 → ℝ) ≃ᵐ (P.Chord → Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : P.Chord => Fin 3 → ℝ)
    (Fintype.equivFinOfCardEq P.card_chord_eq).symm

lemma measurePreserving_toChordMom {n : ℕ} (P : ChordPairing n) :
    MeasurePreserving (toChordMom P) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : P.Chord => Fin 3 → ℝ)
    (Fintype.equivFinOfCardEq P.card_chord_eq).symm

instance instMeasChordPairing (n : ℕ) : MeasurableSpace (ChordPairing n) := ⊤

instance instMeasurableSingletonChordPairing (n : ℕ) :
    MeasurableSingletonClass (ChordPairing n) :=
  ⟨fun _ => trivial⟩

abbrev WickSpectralIndex (n : ℕ) : Type :=
  ChordPairing n × (Fin (n / 2) → Fin 3 → ℝ)

noncomputable def wickSpectralMeasure (n : ℕ) : Measure (WickSpectralIndex n) :=
  Measure.count.prod volume

lemma measurable_wickSpectralIndex {n : ℕ} {β : Type*} [MeasurableSpace β]
    {Φ : ChordPairing n → (Fin (n / 2) → Fin 3 → ℝ) → β}
    (hΦ : ∀ P : ChordPairing n, Measurable (Φ P)) :
    Measurable (fun a : WickSpectralIndex n => Φ a.1 a.2) := by
  intro U hU
  have h_pre :
      (fun a : WickSpectralIndex n => Φ a.1 a.2) ⁻¹' U =
        ⋃ P : ChordPairing n, ({P} : Set (ChordPairing n)) ×ˢ (Φ P ⁻¹' U) := by
    ext ⟨P, q⟩
    simp
  rw [h_pre]
  exact MeasurableSet.iUnion (fun P => MeasurableSet.prod trivial (hΦ P hU))

lemma integrable_wickSpectralMeasure {n : ℕ}
    {Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ}
    (hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P))
    (hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume) :
    Integrable (fun a : WickSpectralIndex n => Φ a.1 (toChordMom a.1 a.2))
      (wickSpectralMeasure n) := by
  have h_meas := measurable_wickSpectralIndex
    (fun P => (hΦ_meas P).comp (toChordMom P).measurable)
  unfold wickSpectralMeasure
  refine (integrable_prod_iff h_meas.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall (fun P => ?_), Integrable.of_finite⟩
  exact ((measurePreserving_toChordMom P).integrable_comp_emb
    (toChordMom P).measurableEmbedding).mpr (hΦ_int P)

lemma integral_wickSpectralMeasure {n : ℕ}
    {Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ}
    (hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P))
    (hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume) :
    (∫ a : WickSpectralIndex n, Φ a.1 (toChordMom a.1 a.2) ∂(wickSpectralMeasure n)) =
      ∑ P : ChordPairing n, ∫ q : P.Chord → Fin 3 → ℝ, Φ P q := by
  have h_int := integrable_wickSpectralMeasure hΦ_meas hΦ_int
  unfold wickSpectralMeasure at h_int ⊢
  rw [integral_prod _ h_int, integral_fintype_count]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  exact (measurePreserving_toChordMom P).integral_comp' (Φ P)

theorem integrable_wickChordWeight_mul_vladimirov_kernel {κ : Type*} {n : ℕ} {m : ℝ}
    (hm : 0 < m) {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (P : ChordPairing n) (α : Fin n → κ)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    Integrable (fun q : P.Chord → Fin 3 → ℝ =>
      wickChordWeight m C P α q * vladimirov_kernel n z (P.momentum m q)) volume := by
  have h_prod : Integrable
      (fun q : P.Chord → Fin 3 → ℝ =>
        ∏ c : P.Chord,
          (massShellWeight m C ![α c.1, α (P.mate c.1)] (q c) *
            vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
              (twoPointMomentum (massShellVec m (q c)))))
      volume :=
    Integrable.fintype_prod
      (f := fun c : P.Chord => fun p : Fin 3 → ℝ =>
        massShellWeight m C ![α c.1, α (P.mate c.1)] p *
          vladimirov_kernel 2 ![z c.1, z (P.mate c.1)]
            (twoPointMomentum (massShellVec m p)))
      (fun c => integrable_massShellWeight_mul_kernel hm hC
        ![α c.1, α (P.mate c.1)] (pair_mem_forward_tube_two hz c.2))
  refine h_prod.congr (Filter.Eventually.of_forall (fun q => ?_))
  dsimp only [wickChordWeight]
  rw [Finset.prod_mul_distrib, ← P.vladimirov_kernel_momentum m z q]

noncomputable def wickTemperedSpectralMeasureFamily {ι : Type*} (m : ℝ) (hm : 0 < m)
    (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) (hC : MassShellCoeffData m C) :
    TemperedForwardConeSpectralMeasureFamily ι where
  A n := WickSpectralIndex n
  instMeas _ := inferInstance
  μ n := wickSpectralMeasure n
  instSFinite n := by
    unfold wickSpectralMeasure
    infer_instance
  ρ n α a := η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)
  p _ _ a := a.1.momentum m (toChordMom a.1 a.2)
  measurable_p n _ :=
    measurable_wickSpectralIndex (fun P => (P.measurable_momentum m).comp (toChordMom P).measurable)
  mem_forwardCone _ _ a :=
    a.1.momentum_mem_forwardConeSpectralRegion hm (toChordMom a.1 a.2)
  integrable_ρ_mul_schwartz n α g := by
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        g (momentumToEuclidCLMN n (P.momentum m q)))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((g.continuous.comp (momentumToEuclidCLMN n).continuous).measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_schwartz hC P α g).const_mul (η ^ P.cross)
    refine (integrable_wickSpectralMeasure hΦ_meas hΦ_int).congr
      (Filter.Eventually.of_forall (fun a => ?_))
    dsimp [Φ]
    ring
  schwartz_seminorm_bound n α := by
    let s : Finset (ℕ × ℕ) := Finset.Iic (4 * (n / 2), 0)
    let B_fn : ChordPairing n → ℝ :=
      fun P => Classical.choose (exists_norm_wickChordWeight_le hC P α)
    have hB_fn : ∀ P : ChordPairing n,
        0 ≤ B_fn P ∧ ∀ q : P.Chord → Fin 3 → ℝ, ‖wickChordWeight m C P α q‖ ≤ B_fn P :=
      fun P => Classical.choose_spec (exists_norm_wickChordWeight_le hC P α)
    let I_fn : ChordPairing n → ℝ :=
      fun P => ∫ q : P.Chord → Fin 3 → ℝ, ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹
    have hI_nn : ∀ P : ChordPairing n, 0 ≤ I_fn P :=
      fun P => integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => by positivity))
    let C_fn : ChordPairing n → ℝ :=
      fun P => ‖η ^ P.cross‖ * (B_fn P * (4 * Real.pi) ^ (4 * (n / 2)) * I_fn P)
    have hC_nn : ∀ P : ChordPairing n, 0 ≤ C_fn P := fun P => by
      have hB := (hB_fn P).1
      have hI := hI_nn P
      positivity
    refine ⟨s, ∑ P : ChordPairing n, C_fn P, Finset.sum_nonneg (fun P _ => hC_nn P), fun g => ?_⟩
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        g (momentumToEuclidCLMN n (P.momentum m q)))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((g.continuous.comp (momentumToEuclidCLMN n).continuous).measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_schwartz hC P α g).const_mul (η ^ P.cross)
    have h_eq :
        (∫ a : WickSpectralIndex n,
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            g (momentumToEuclidCLMN n (a.1.momentum m (toChordMom a.1 a.2)))
          ∂(wickSpectralMeasure n)) =
        ∑ P : ChordPairing n, η ^ P.cross *
          ∫ q : P.Chord → Fin 3 → ℝ,
            wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q)) := by
      have h_congr :
          (fun a : WickSpectralIndex n =>
            (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
              g (momentumToEuclidCLMN n (a.1.momentum m (toChordMom a.1 a.2)))) =
          fun a => Φ a.1 (toChordMom a.1 a.2) := by
        ext a
        dsimp [Φ]
        ring
      rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int]
      refine Finset.sum_congr rfl (fun P _ => ?_)
      exact integral_const_mul (η ^ P.cross) _
    rw [h_eq]
    let S_val : ℝ := s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ) g
    calc ‖∑ P : ChordPairing n, η ^ P.cross *
            ∫ q : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖
        ≤ ∑ P : ChordPairing n, ‖η ^ P.cross *
            ∫ q : P.Chord → Fin 3 → ℝ,
              wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ P : ChordPairing n, C_fn P * S_val := by
          refine Finset.sum_le_sum (fun P _ => ?_)
          rw [norm_mul]
          dsimp [C_fn]
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have h_each :
              ‖∫ q : P.Chord → Fin 3 → ℝ,
                  wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖ ≤
                (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) * I_fn P := by
            calc ‖∫ q : P.Chord → Fin 3 → ℝ,
                    wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖
                ≤ ∫ q : P.Chord → Fin 3 → ℝ,
                    ‖wickChordWeight m C P α q * g (momentumToEuclidCLMN n (P.momentum m q))‖ :=
                  norm_integral_le_integral_norm _
              _ ≤ ∫ q : P.Chord → Fin 3 → ℝ,
                    (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) *
                      ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹ := by
                  refine integral_mono_of_nonneg
                    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
                    ((integrable_chordDecay P).const_mul _)
                    (Filter.Eventually.of_forall (fun q => ?_))
                  dsimp only
                  rw [norm_mul]
                  have h_sch := P.norm_schwartz_momentumToEuclid_chord_le m g q
                  rw [P.card_chord_eq] at h_sch
                  calc ‖wickChordWeight m C P α q‖ *
                        ‖g (momentumToEuclidCLMN n (P.momentum m q))‖
                      ≤ B_fn P * (((4 * Real.pi) ^ (4 * (n / 2)) * S_val) *
                          ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹) :=
                        mul_le_mul ((hB_fn P).2 q) h_sch (norm_nonneg _) (hB_fn P).1
                    _ = (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) *
                          ∏ c : P.Chord, ((1 + ‖q c‖) ^ 4)⁻¹ := by ring
              _ = (B_fn P * ((4 * Real.pi) ^ (4 * (n / 2)) * S_val)) * I_fn P :=
                  integral_const_mul _ _
          exact h_each.trans_eq (by ring)
      _ = (∑ P : ChordPairing n, C_fn P) * S_val := (Finset.sum_mul _ _ _).symm
  analyticOn_H_raw n α := by
    refine (analyticOn_wickMassShellH hm η hC n α).congr (fun z hz => ?_)
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        vladimirov_kernel n z (P.momentum m q))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((vladimirov_kernel_contDiff n z).continuous.measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_vladimirov_kernel hm hC P α hz).const_mul
        (η ^ P.cross)
    have h_congr :
        (fun a : WickSpectralIndex n =>
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            vladimirov_kernel n z (a.1.momentum m (toChordMom a.1 a.2))) =
        fun a => Φ a.1 (toChordMom a.1 a.2) := by
      ext a
      dsimp [Φ]
      ring
    rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellH_eq_sum_integral]
    exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)
  tendsto_boundary n α f _v hv := by
    have h_rhs :
        (∫ a : WickSpectralIndex n,
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            minkowskiFourier f (a.1.momentum m (toChordMom a.1 a.2))
          ∂(wickSpectralMeasure n)) =
        wickMassShellW m η C hC n α f := by
      let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
        fun P q => η ^ P.cross * (wickChordWeight m C P α q *
          minkowskiFourier f (P.momentum m q))
      have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
        fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
          ((continuous_minkowskiFourier n f).measurable.comp (P.measurable_momentum m)))
      have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
        fun P => (integrable_wickChordWeight_mul_minkowskiFourier hC P α f).const_mul
          (η ^ P.cross)
      have h_congr :
          (fun a : WickSpectralIndex n =>
            (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
              minkowskiFourier f (a.1.momentum m (toChordMom a.1 a.2))) =
          fun a => Φ a.1 (toChordMom a.1 a.2) := by
        ext a
        dsimp [Φ]
        ring
      rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellW_apply]
      exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)
    rw [h_rhs]
    refine (tendsto_wickMassShellH_boundary hm η hC n α f hv).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => congrArg (· * f x) ?_))
    have hz : tubeBoundaryLine n x _v t ∈ forward_tube_n n :=
      line_mem_forward_tube n x _v hv t ht
    let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
      fun P q => η ^ P.cross * (wickChordWeight m C P α q *
        vladimirov_kernel n (tubeBoundaryLine n x _v t) (P.momentum m q))
    have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
      fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
        ((vladimirov_kernel_contDiff n (tubeBoundaryLine n x _v t)).continuous.measurable.comp
          (P.measurable_momentum m)))
    have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
      fun P => (integrable_wickChordWeight_mul_vladimirov_kernel hm hC P α hz).const_mul
        (η ^ P.cross)
    have h_congr :
        (fun a : WickSpectralIndex n =>
          (η ^ a.1.cross * wickChordWeight m C a.1 α (toChordMom a.1 a.2)) *
            vladimirov_kernel n (tubeBoundaryLine n x _v t)
              (a.1.momentum m (toChordMom a.1 a.2))) =
        fun a => Φ a.1 (toChordMom a.1 a.2) := by
      ext a
      dsimp [Φ]
      ring
    rw [h_congr, integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellH_eq_sum_integral]
    exact (Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)).symm

@[simp]
theorem wickTemperedSpectralMeasureFamily_toWightmanFamily {ι : Type*}
    (m : ℝ) (hm : 0 < m) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC : MassShellCoeffData m C) :
    (wickTemperedSpectralMeasureFamily m hm η C hC).toWightmanFamily =
      wickMassShellW m η C hC := by
  ext n α f
  rw [TemperedForwardConeSpectralMeasureFamily.toWightmanFamily_apply, wickMassShellW_apply]
  let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
    fun P q => η ^ P.cross * (wickChordWeight m C P α q * minkowskiFourier f (P.momentum m q))
  have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
    fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
      ((continuous_minkowskiFourier n f).measurable.comp (P.measurable_momentum m)))
  have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
    fun P => (integrable_wickChordWeight_mul_minkowskiFourier hC P α f).const_mul (η ^ P.cross)
  have h_congr :
      (fun a : (wickTemperedSpectralMeasureFamily m hm η C hC).A n =>
        (wickTemperedSpectralMeasureFamily m hm η C hC).ρ n α a *
          minkowskiFourier f ((wickTemperedSpectralMeasureFamily m hm η C hC).p n α a)) =
      fun a => Φ a.1 (toChordMom a.1 a.2) := by
    ext a
    dsimp [wickTemperedSpectralMeasureFamily, Φ]
    ring
  rw [h_congr]
  change (∫ a : WickSpectralIndex n, Φ a.1 (toChordMom a.1 a.2) ∂(wickSpectralMeasure n)) = _
  rw [integral_wickSpectralMeasure hΦ_meas hΦ_int]
  exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)

theorem wickTemperedSpectralMeasureFamily_H {ι : Type*}
    (m : ℝ) (hm : 0 < m) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC : MassShellCoeffData m C) (n : ℕ) (α : Fin n → ι)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    (wickTemperedSpectralMeasureFamily m hm η C hC).H n α z =
      wickMassShellH m η C n α z := by
  unfold TemperedForwardConeSpectralMeasureFamily.H
  let Φ : ∀ P : ChordPairing n, (P.Chord → Fin 3 → ℝ) → ℂ :=
    fun P q => η ^ P.cross * (wickChordWeight m C P α q *
      vladimirov_kernel n z (P.momentum m q))
  have hΦ_meas : ∀ P : ChordPairing n, Measurable (Φ P) :=
    fun P => measurable_const.mul ((measurable_wickChordWeight hC P α).mul
      ((vladimirov_kernel_contDiff n z).continuous.measurable.comp
        (P.measurable_momentum m)))
  have hΦ_int : ∀ P : ChordPairing n, Integrable (Φ P) volume :=
    fun P => (integrable_wickChordWeight_mul_vladimirov_kernel hm hC P α hz).const_mul
      (η ^ P.cross)
  have h_congr :
      (fun a : (wickTemperedSpectralMeasureFamily m hm η C hC).A n =>
        (wickTemperedSpectralMeasureFamily m hm η C hC).ρ n α a *
          vladimirov_kernel n z ((wickTemperedSpectralMeasureFamily m hm η C hC).p n α a)) =
      fun a => Φ a.1 (toChordMom a.1 a.2) := by
    ext a
    dsimp [wickTemperedSpectralMeasureFamily, Φ]
    ring
  rw [h_congr]
  change (∫ a : WickSpectralIndex n, Φ a.1 (toChordMom a.1 a.2) ∂(wickSpectralMeasure n)) = _
  rw [integral_wickSpectralMeasure hΦ_meas hΦ_int, wickMassShellH_eq_sum_integral]
  exact Finset.sum_congr rfl (fun P _ => integral_const_mul (η ^ P.cross) _)

theorem wickTemperedSpectralMeasureFamily_toSchwingerFamily {ι : Type*}
    (m : ℝ) (hm : 0 < m) (η : ℂ) (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ)
    (hC : MassShellCoeffData m C) (n : ℕ) (α : Fin n → ι)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    (wickTemperedSpectralMeasureFamily m hm η C hC).toSchwingerFamily n α x =
      wickMassShellS m hm η C hC n α x :=
  wickTemperedSpectralMeasureFamily_H m hm η C hC n α (wickEmbedN_mem_forward_tube_n n hx)

theorem wickTemperedSpectralMeasureFamily_tubeCovariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q) :
    TubeCovariant R (wickTemperedSpectralMeasureFamily m hm η C hC).toTubeExtension := by
  intro n A z hz hAz α
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n α hAz]
  have h_cov := wickMassShellTubeCovariant R hm η hC hC_cov n A z hz hAz α
  rw [wickMassShellTubeExtension_H] at h_cov
  rw [h_cov]
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n β hz]

theorem wickTemperedSpectralMeasureFamily_tubePCT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    TubePCT η R (wickTemperedSpectralMeasureFamily m hm η C hC).toTubeExtension := by
  intro n α z hz
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n α (neg_rev_mem_forward_tube_n n z hz)]
  have h_pct := wickMassShellTubePCT R hm hη hC hC_pct n α z hz
  rw [wickMassShellTubeExtension_H] at h_pct
  rw [h_pct]
  congr 1
  refine Finset.sum_congr rfl (fun β _ => congrArg (_ * ·) ?_)
  rw [TemperedForwardConeSpectralMeasureFamily.toTubeExtension_H,
      wickTemperedSpectralMeasureFamily_H m hm η C hC n (β ∘ Fin.rev) hz]

noncomputable def freeKGTemperedSpectralMeasureFamily {m : ℝ} (hm : 0 < m) :
    TemperedForwardConeSpectralMeasureFamily Unit :=
  wickTemperedSpectralMeasureFamily m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

noncomputable def freeDiracTemperedSpectralMeasureFamily {m : ℝ} (hm : 0 < m) :
    TemperedForwardConeSpectralMeasureFamily (Fin 2 ⊕ Fin 2) :=
  wickTemperedSpectralMeasureFamily m hm (-1) (diracMassShellCoeff m)
    (diracMassShellCoeff_data hm)

theorem vacFullEuclidOSAxioms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    FullEuclidOSAxioms R S η vacS where
  os0_smooth n _ := by
    cases n with
    | zero => exact contDiffOn_const
    | succ _ => exact contDiffOn_const
  os1_translation n _ _ _ _ := by
    cases n <;> rfl
  os1_rotation n _ _ α _ _ := by
    cases n with
    | zero =>
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      simp [vacS_zero]
    | succ _ =>
      simp [vacS_succ]
  os2_hermiticity := (vacOSAxioms R S η).os2_hermiticity
  os2_positivity := vacOSReflectionPositive S
  os3_permutation n π _ _ _ := by
    cases n with
    | zero =>
      have h0 : permInversions π = 0 := by
        unfold permInversions
        simp
      rw [h0, pow_zero, one_mul]
      rfl
    | succ _ =>
      simp [vacS_succ]

def vacForwardConeSpectralFamily (ι : Type*) : ForwardConeSpectralFamily ι where
  m
    | 0 => 1
    | _ + 1 => 0
  c
    | 0, _, _ => 1
    | _ + 1, _, k => Fin.elim0 k
  p
    | 0, _, _ => 0
    | _ + 1, _, k => Fin.elim0 k
  mem_forwardCone
    | 0, _, _ => zero_mem_forwardConeSpectralRegion 0
    | _ + 1, _, k => Fin.elim0 k

@[simp]
lemma vacForwardConeSpectralFamily_H (ι : Type*) :
    (vacForwardConeSpectralFamily ι).H = vacH := by
  ext n α z
  cases n with
  | zero =>
    change ∑ _k : Fin 1, (1 : ℂ) * vladimirov_kernel 0 z 0 = 1
    rw [Fin.sum_univ_one, vladimirov_kernel_zero_p_n, one_mul]
  | succ _ =>
    change ∑ k : Fin 0, _ = 0
    simp

@[simp]
lemma vacForwardConeSpectralFamily_toWightmanFamily (ι : Type*) :
    (vacForwardConeSpectralFamily ι).toWightmanFamily = vacW := by
  ext n α f
  rw [ForwardConeSpectralFamily.toWightmanFamily_apply]
  cases n with
  | zero =>
    change ∑ _k : Fin 1, (1 : ℂ) * minkowskiFourier f 0 = f 0
    rw [Fin.sum_univ_one, one_mul, minkowskiFourier_fin0]
  | succ _ =>
    change ∑ k : Fin 0, _ = 0
    simp

@[simp]
lemma vacForwardConeSpectralFamily_toSchwingerFamily (ι : Type*) :
    (vacForwardConeSpectralFamily ι).toSchwingerFamily = vacS := by
  ext n α x
  rw [ForwardConeSpectralFamily.toSchwingerFamily_apply, vacForwardConeSpectralFamily_H]
  cases n <;> rfl

noncomputable def vacOSReconstructionData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSReconstructionData (vacOSAxioms R S η) (vacOSTimeCluster R S) where
  m_spec := 1
  spec := vacSpectralDecomposition R S
  F := vacForwardConeSpectralFamily ι
  schwinger_eq n α x _ := by rw [vacForwardConeSpectralFamily_toSchwingerFamily]
  tube_covariant n A z hz hAz α := by
    change (vacForwardConeSpectralFamily ι).H n α (spinorPhi (A, sl2c_conj A) • z) =
      ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * (vacForwardConeSpectralFamily ι).H n β z
    simp_rw [vacForwardConeSpectralFamily_H]
    exact vacTubeCovariant R n A z hz hAz α
  tube_pct n α z hz := by
    change (vacForwardConeSpectralFamily ι).H n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) * ∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * (vacForwardConeSpectralFamily ι).H n (β ∘ Fin.rev) z
    simp_rw [vacForwardConeSpectralFamily_H]
    exact vacTubePCT R η n α z hz
  poincare := by
    rw [vacForwardConeSpectralFamily_toWightmanFamily]
    exact vacPoincareCovariant R
  weakLocality := by
    rw [vacForwardConeSpectralFamily_toWightmanFamily]
    exact vacWeakLocality η
  positivity := by
    rw [vacForwardConeSpectralFamily_toWightmanFamily]
    exact vacPositivity S

noncomputable def wickMassShellOSMeasureReconstructionData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hOS : OSAxioms R_rep S η (wickMassShellS m hm η C hC))
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    OSMeasureReconstructionData hOS hcluster where
  Ω_spec := FockOmega M_mode.ν
  instMeasSpec := inferInstance
  spec := wickMassShellOSContinuousSpectralData hm M_mode hC hC_herm
    hOS.toReflectionPositiveData (fun _ _ _ _ => rfl)
    (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
      hOS.os1_translation hcluster)
  F := wickTemperedSpectralMeasureFamily m hm η C hC
  schwinger_eq n α x hx :=
    (wickTemperedSpectralMeasureFamily_toSchwingerFamily m hm η C hC n α hx).symm
  tube_covariant := wickTemperedSpectralMeasureFamily_tubeCovariant R_rep hm η hC hC_cov
  tube_pct := wickTemperedSpectralMeasureFamily_tubePCT R_rep hm M_mode.hη hC hC_pct
  poincare := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellPoincareCovariant R_rep hm η hC hC_cov
  weakLocality := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellWeakLocality R_rep hm M_mode.hη hC hC_cov hC_pct
  positivity := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellPositivity M_mode hC hC_herm

noncomputable def freeKGOSMeasureReconstructionData {m : ℝ} (hm : 0 < m) :
    OSMeasureReconstructionData (freeKGOSAxioms hm) (freeKGOSTimeCluster hm) :=
  wickMassShellOSMeasureReconstructionData hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])
    (freeKGOSAxioms hm) (freeKGOSTimeCluster hm)

noncomputable def freeDiracOSMeasureReconstructionData {m : ℝ} (hm : 0 < m) :
    OSMeasureReconstructionData (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm) :=
  wickMassShellOSMeasureReconstructionData hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)
    (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm)

noncomputable def freeKGForwardConeOSEuclideanTubeBridge {m : ℝ} (hm : 0 < m) :
    ForwardConeOSEuclideanTubeBridge trivialRep trivialStarStructure 1 (freeKGS m hm) :=
  (freeKGOSMeasureReconstructionData hm).toForwardConeOSEuclideanTubeBridge

noncomputable def freeKGForwardConeOSReconstructedWightman {m : ℝ} (hm : 0 < m) :
    ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1 (freeKGS m hm) :=
  (freeKGOSMeasureReconstructionData hm).toForwardConeOSReconstructedWightman

noncomputable def freeDiracForwardConeOSEuclideanTubeBridge {m : ℝ} (hm : 0 < m) :
    ForwardConeOSEuclideanTubeBridge diracRep diracStarStructure (-1) (freeDiracS m hm) :=
  (freeDiracOSMeasureReconstructionData hm).toForwardConeOSEuclideanTubeBridge

noncomputable def freeDiracForwardConeOSReconstructedWightman {m : ℝ} (hm : 0 < m) :
    ForwardConeOSReconstructedWightman diracRep diracStarStructure (-1) (freeDiracS m hm) :=
  (freeDiracOSMeasureReconstructionData hm).toForwardConeOSReconstructedWightman

noncomputable def wickMassShellWightmanAxioms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanAxioms R_rep S η where
  WData := wightmanPositiveDataOfPositivity S (wickMassShellW m η C hC)
    (wickMassShellPositivity M_mode hC hC_herm)
  E := wickMassShellTubeExtension m hm η C hC
  positivity := wickMassShellPositivity M_mode hC hC_herm
  poincare := wickMassShellPoincareCovariant R_rep hm η hC hC_cov
  spectrum := wickMassShell_forwardConeSpectrumCondition hm η hC
  weakLocality := wickMassShellWeakLocality R_rep hm M_mode.hη hC hC_cov hC_pct
  tube_covariant := wickMassShellTubeCovariant R_rep hm η hC hC_cov
  tube_pct := wickMassShellTubePCT R_rep hm M_mode.hη hC hC_pct
  cyclic := wightmanVacuumCyclic _

noncomputable def wickMassShellWightmanAxiomsWithUniqueVacuum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    WightmanAxiomsWithUniqueVacuum R_rep S η where
  toWightmanAxioms :=
    wickMassShellWightmanAxioms R_rep S hm M_mode hC hC_cov hC_herm hC_pct
  vacuumNormalized := wickMassShellWightmanVacuumNormalized M_mode hC hC_herm
  cluster _ ha := wickMassShellWightmanClusterAlong hm M_mode hC hC_herm _ rfl ha
  vacuumUnique := wickMassShellWightmanVacuumUnique hm M_mode hC hC_herm _ rfl _

noncomputable def freeKGWightmanAxioms {m : ℝ} (hm : 0 < m) :
    WightmanAxioms trivialRep trivialStarStructure 1 :=
  wickMassShellWightmanAxioms trivialRep trivialStarStructure hm (kgModeData hm)
    (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

noncomputable def freeDiracWightmanAxioms {m : ℝ} (hm : 0 < m) :
    WightmanAxioms diracRep diracStarStructure (-1) :=
  wickMassShellWightmanAxioms diracRep diracStarStructure hm (diracModeData hm)
    (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

noncomputable def freeKGWightmanAxiomsWithUniqueVacuum {m : ℝ} (hm : 0 < m) :
    WightmanAxiomsWithUniqueVacuum trivialRep trivialStarStructure 1 :=
  wickMassShellWightmanAxiomsWithUniqueVacuum trivialRep trivialStarStructure hm
    (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

noncomputable def freeDiracWightmanAxiomsWithUniqueVacuum {m : ℝ} (hm : 0 < m) :
    WightmanAxiomsWithUniqueVacuum diracRep diracStarStructure (-1) :=
  wickMassShellWightmanAxiomsWithUniqueVacuum diracRep diracStarStructure hm
    (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

theorem freeKGClusterAlong {m : ℝ} (hm : 0 < m) {a : Fin 4 → ℝ} (ha : a ≠ 0) :
    WightmanClusterAlong (freeKGWightmanAxioms hm).WData a :=
  (freeKGWightmanAxiomsWithUniqueVacuum hm).cluster a ha

theorem freeDiracClusterAlong {m : ℝ} (hm : 0 < m) {a : Fin 4 → ℝ} (ha : a ≠ 0) :
    WightmanClusterAlong (freeDiracWightmanAxioms hm).WData a :=
  (freeDiracWightmanAxiomsWithUniqueVacuum hm).cluster a ha

theorem freeKGVacuumUnique {m : ℝ} (hm : 0 < m) :
    WightmanVacuumUnique (freeKGWightmanAxioms hm).WData
      (freeKGWightmanAxioms hm).translationInvariant :=
  (freeKGWightmanAxiomsWithUniqueVacuum hm).vacuumUnique

theorem freeDiracVacuumUnique {m : ℝ} (hm : 0 < m) :
    WightmanVacuumUnique (freeDiracWightmanAxioms hm).WData
      (freeDiracWightmanAxioms hm).translationInvariant :=
  (freeDiracWightmanAxiomsWithUniqueVacuum hm).vacuumUnique

theorem freeKGWightmanVacuumNormalized {m : ℝ} (hm : 0 < m) :
    WightmanVacuumNormalized trivialStarStructure (freeKGW m hm) :=
  (freeKGWightmanAxiomsWithUniqueVacuum hm).vacuumNormalized

theorem freeDiracWightmanVacuumNormalized {m : ℝ} (hm : 0 < m) :
    WightmanVacuumNormalized diracStarStructure (freeDiracW m hm) :=
  (freeDiracWightmanAxiomsWithUniqueVacuum hm).vacuumNormalized

theorem freeKGOSVacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (freeKGS m hm) :=
  wickMassShellS_vacuumNormalized m hm 1 massiveKGCoeff (massiveKGCoeff_data hm)

theorem freeDiracOSVacuumNormalized {m : ℝ} (hm : 0 < m) :
    OSVacuumNormalized (freeDiracS m hm) :=
  wickMassShellS_vacuumNormalized m hm (-1) (diracMassShellCoeff m) (diracMassShellCoeff_data hm)

theorem freeKGOS_exponential_cluster {m : ℝ} (hm : 0 < m) {τ : ℝ} (hτ : 0 ≤ τ)
    (A B : OSConfig Unit) :
    ‖osKernel trivialStarStructure (freeKGS m hm) A (osConfigTimeShift τ hτ B) -
        osKernel trivialStarStructure (freeKGS m hm) A (osVacuumConfig Unit) *
          osKernel trivialStarStructure (freeKGS m hm) (osVacuumConfig Unit) B‖ ≤
      ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) A‖ *
        ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) B‖ *
          Real.exp (-(m * τ)) :=
  wickMassShellOS_exponential_cluster hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure]) hτ A B

theorem freeDiracOS_exponential_cluster {m : ℝ} (hm : 0 < m) {τ : ℝ} (hτ : 0 ≤ τ)
    (A B : OSConfig (Fin 2 ⊕ Fin 2)) :
    ‖osKernel diracStarStructure (freeDiracS m hm) A (osConfigTimeShift τ hτ B) -
        osKernel diracStarStructure (freeDiracS m hm) A (osVacuumConfig (Fin 2 ⊕ Fin 2)) *
          osKernel diracStarStructure (freeDiracS m hm) (osVacuumConfig (Fin 2 ⊕ Fin 2)) B‖ ≤
      ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) A‖ *
        ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) B‖ *
          Real.exp (-(m * τ)) :=
  wickMassShellOS_exponential_cluster hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_herm m) hτ A B

theorem wickMassShellFullS_osHermiticity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSHermiticity S (wickMassShellFullS R_rep m hm η C hC) :=
  (osHermiticity_congr_of_eq_on_orderedEuclidN S
    (fun n α _x hx =>
      wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx)).mpr
    (wickMassShellOSHermiticity S hm hη hC hC_herm)

theorem wickMassShellFullS_osReflectionPositive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSReflectionPositive S (wickMassShellFullS R_rep m hm η C hC) :=
  (osReflectionPositive_congr_of_eq_on_orderedEuclidN S
    (fun n α _x hx =>
      wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx)).mpr
    (wickMassShellOSReflectionPositive hm M_mode hC hC_herm)

theorem wickMassShellFullEuclidOSAxioms {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    FullEuclidOSAxioms R_rep S η (wickMassShellFullS R_rep m hm η C hC) where
  os0_smooth := wickMassShellFullS_contDiffOn R_rep hm η hC hC_cov
  os1_translation := wickMassShellFullS_translation_invariant R_rep hm η hC hC_cov
  os1_rotation := wickMassShellFullS_rotCovariant R_rep hm η hC hC_cov
  os2_hermiticity := wickMassShellFullS_osHermiticity R_rep S hm M_mode.hη hC hC_cov hC_herm
  os2_positivity := wickMassShellFullS_osReflectionPositive R_rep hm M_mode hC hC_cov hC_herm
  os3_permutation := wickMassShellFullS_permutation R_rep hm M_mode.hη hC hC_cov hC_pct

theorem freeKGFullEuclidOSAxioms {m : ℝ} (hm : 0 < m) :
    FullEuclidOSAxioms trivialRep trivialStarStructure 1 (freeKGFullS m hm) :=
  wickMassShellFullEuclidOSAxioms trivialRep trivialStarStructure hm
    (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeDiracFullEuclidOSAxioms {m : ℝ} (hm : 0 < m) :
    FullEuclidOSAxioms diracRep diracStarStructure (-1) (freeDiracFullS m hm) :=
  wickMassShellFullEuclidOSAxioms diracRep diracStarStructure hm
    (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

theorem freeKGFullOSTimeCluster {m : ℝ} (hm : 0 < m) :
    OSTimeClusterDecomposition
      (freeKGFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData :=
  (osTimeClusterDecomposition_congr_of_eq_on_orderedEuclidN
    (D₁ := (freeKGFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData)
    (D₂ := (freeKGOSAxioms hm).toReflectionPositiveData)
    (fun n α _x hx => freeKGFullS_eq_freeKGS_on_orderedEuclidN hm n α hx)).mpr
    (freeKGOSTimeCluster hm)

theorem freeDiracFullOSTimeCluster {m : ℝ} (hm : 0 < m) :
    OSTimeClusterDecomposition
      (freeDiracFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData :=
  (osTimeClusterDecomposition_congr_of_eq_on_orderedEuclidN
    (D₁ := (freeDiracFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData)
    (D₂ := (freeDiracOSAxioms hm).toReflectionPositiveData)
    (fun n α _x hx => freeDiracFullS_eq_freeDiracS_on_orderedEuclidN hm n α hx)).mpr
    (freeDiracOSTimeCluster hm)

noncomputable def wickMassShellFullOSMeasureReconstructionData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hOS : FullEuclidOSAxioms R_rep S η (wickMassShellFullS R_rep m hm η C hC))
    (hcluster : OSTimeClusterDecomposition hOS.toOSAxioms.toReflectionPositiveData) :
    OSMeasureReconstructionData hOS.toOSAxioms hcluster where
  Ω_spec := FockOmega M_mode.ν
  instMeasSpec := inferInstance
  spec := wickMassShellOSContinuousSpectralData hm M_mode hC hC_herm
    hOS.toOSAxioms.toReflectionPositiveData
    (fun n α _x hx =>
      wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx)
    (osContractionCondition_of_timeCluster hOS.toOSAxioms.toReflectionPositiveData
      hOS.toOSAxioms.os1_translation hcluster)
  F := wickTemperedSpectralMeasureFamily m hm η C hC
  schwinger_eq n α _x hx :=
    (wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx).trans
      (wickTemperedSpectralMeasureFamily_toSchwingerFamily m hm η C hC n α hx).symm
  tube_covariant := wickTemperedSpectralMeasureFamily_tubeCovariant R_rep hm η hC hC_cov
  tube_pct := wickTemperedSpectralMeasureFamily_tubePCT R_rep hm M_mode.hη hC hC_pct
  poincare := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellPoincareCovariant R_rep hm η hC hC_cov
  weakLocality := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellWeakLocality R_rep hm M_mode.hη hC hC_cov hC_pct
  positivity := by
    rw [wickTemperedSpectralMeasureFamily_toWightmanFamily]
    exact wickMassShellPositivity M_mode hC hC_herm

noncomputable def freeKGFullOSMeasureReconstructionData {m : ℝ} (hm : 0 < m) :
    OSMeasureReconstructionData (freeKGFullEuclidOSAxioms hm).toOSAxioms
      (freeKGFullOSTimeCluster hm) :=
  wickMassShellFullOSMeasureReconstructionData hm (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])
    (freeKGFullEuclidOSAxioms hm) (freeKGFullOSTimeCluster hm)

noncomputable def freeDiracFullOSMeasureReconstructionData {m : ℝ} (hm : 0 < m) :
    OSMeasureReconstructionData (freeDiracFullEuclidOSAxioms hm).toOSAxioms
      (freeDiracFullOSTimeCluster hm) :=
  wickMassShellFullOSMeasureReconstructionData hm (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)
    (freeDiracFullEuclidOSAxioms hm) (freeDiracFullOSTimeCluster hm)

noncomputable def freeKGFullForwardConeOSReconstructedWightman {m : ℝ} (hm : 0 < m) :
    ForwardConeOSReconstructedWightman trivialRep trivialStarStructure 1 (freeKGFullS m hm) :=
  (freeKGFullOSMeasureReconstructionData hm).toForwardConeOSReconstructedWightman

noncomputable def freeDiracFullForwardConeOSReconstructedWightman {m : ℝ} (hm : 0 < m) :
    ForwardConeOSReconstructedWightman diracRep diracStarStructure (-1) (freeDiracFullS m hm) :=
  (freeDiracFullOSMeasureReconstructionData hm).toForwardConeOSReconstructedWightman

theorem freeKGFullS_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hOS : FullEuclidOSAxioms trivialRep trivialStarStructure η (freeKGFullS m hm)) :
    η = 1 :=
  fullEuclidOSAxioms_spin_statistics hOS trivialRep_spinParity
    ⟨2, by omega, default, equalTimeTwoPoint 1,
      equalTimeTwoPoint_mem_nonCoincidentEuclidN one_ne_zero,
      freeKGFullS_equalTime_ne_zero hm zero_lt_one⟩

theorem freeDiracFullS_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hOS : FullEuclidOSAxioms diracRep diracStarStructure η (freeDiracFullS m hm)) :
    η = -1 := by
  rcases freeDiracFullS_equalTime_exists_ne_zero hm (r := 1) zero_lt_one with ⟨α, hne⟩
  exact fullEuclidOSAxioms_spin_statistics hOS diracRep_spinParity
    ⟨2, by omega, α, equalTimeTwoPoint 1,
      equalTimeTwoPoint_mem_nonCoincidentEuclidN one_ne_zero, hne⟩

theorem norm_massShellTwoPointH_two_le {κ : Type*} {m : ℝ} (hm : 0 < m)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) (α : Fin 2 → κ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {z : Fin 2 → Fin 4 → ℂ}, z ∈ forward_tube_n 2 →
      ‖massShellTwoPointH m C 2 α z‖ ≤
        C₀ * (coneGap (diff_im 2 z 0 (by decide)))⁻¹ ^ 4 := by
  rcases hC.2 α with ⟨B, hB_nn, hB⟩
  let I_dec : ℝ := ∫ p : Fin 3 → ℝ, ((1 + ‖p‖) ^ 4)⁻¹
  have hI_nn : 0 ≤ I_dec := integral_nonneg (fun _ => by positivity)
  let C₀ : ℝ := B * 24 * (1 / m + 1) ^ 4 * I_dec
  refine ⟨C₀, by positivity, fun {z} hz => ?_⟩
  let c : ℝ := coneGap (diff_im 2 z 0 (by decide))
  have hc : 0 < c := coneGap_pos _ (diff_im_mem_forward_cone 2 z hz 0 (by decide))
  let K : ℝ := (1 / m + 1) / c
  have hK_nn : 0 ≤ K := by
    dsimp [K]
    positivity
  have hK_pow : K ^ 4 = (1 / m + 1) ^ 4 * c⁻¹ ^ 4 := by
    dsimp [K]
    rw [div_eq_mul_inv, mul_pow]
  rw [massShellTwoPointH_two]
  calc ‖∫ p : Fin 3 → ℝ, massShellWeight m C α p *
          vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))‖
      ≤ ∫ p : Fin 3 → ℝ,
          ‖massShellWeight m C α p *
            vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p : Fin 3 → ℝ, (B * (24 * K ^ 4)) * ((1 + ‖p‖) ^ 4)⁻¹ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (integrable_massShellDecay.const_mul (B * (24 * K ^ 4)))
          (Filter.Eventually.of_forall (fun p => ?_))
        dsimp only
        have hω_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
        have hcω_nn : 0 ≤ c * massShellEnergy m p := mul_nonneg hc.le hω_pos.le
        have h_lin : 1 + ‖p‖ ≤ K * (c * massShellEnergy m p) := by
          have h1 := one_add_norm_le_scale_massShellEnergy hm p
          have hK_eq : K * (c * massShellEnergy m p) =
              (1 / m + 1) * massShellEnergy m p := by
            dsimp [K]
            field_simp [hc.ne']
          linarith
        have h_pow : (1 + ‖p‖) ^ 4 ≤ K ^ 4 * (c * massShellEnergy m p) ^ 4 :=
          (pow_le_pow_left₀ (by positivity) h_lin 4).trans_eq (mul_pow _ _ 4)
        have h_exp_fac :
            (c * massShellEnergy m p) ^ 4 / (24 : ℝ) ≤
              Real.exp (c * massShellEnergy m p) := by
          simpa [Nat.factorial] using
            Real.pow_div_factorial_le_exp (c * massShellEnergy m p) hcω_nn 4
        have h_prod :
            (1 + ‖p‖) ^ 4 * Real.exp (-(c * massShellEnergy m p)) ≤ 24 * K ^ 4 := by
          calc (1 + ‖p‖) ^ 4 * Real.exp (-(c * massShellEnergy m p))
              ≤ (K ^ 4 * (c * massShellEnergy m p) ^ 4) *
                  Real.exp (-(c * massShellEnergy m p)) :=
                mul_le_mul_of_nonneg_right h_pow (Real.exp_pos _).le
            _ = (24 * K ^ 4) * (((c * massShellEnergy m p) ^ 4 / 24) *
                  Real.exp (-(c * massShellEnergy m p))) := by ring
            _ ≤ (24 * K ^ 4) *
                  (Real.exp (c * massShellEnergy m p) *
                    Real.exp (-(c * massShellEnergy m p))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right h_exp_fac (Real.exp_pos _).le) (by positivity)
            _ = 24 * K ^ 4 := by
                rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        have h_pos4 : 0 < (1 + ‖p‖) ^ 4 := by positivity
        have h_exp_le :
            Real.exp (-(c * massShellEnergy m p)) ≤
              (24 * K ^ 4) * ((1 + ‖p‖) ^ 4)⁻¹ :=
          (le_mul_inv_iff₀' h_pos4).mpr h_prod
        have h_ker_le :
            ‖vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))‖ ≤
              (24 * K ^ 4) * ((1 + ‖p‖) ^ 4)⁻¹ :=
          (norm_vladimirov_kernel_twoPoint_le_exp hm hz p).trans h_exp_le
        rw [norm_mul]
        calc ‖massShellWeight m C α p‖ *
              ‖vladimirov_kernel 2 z (twoPointMomentum (massShellVec m p))‖
            ≤ B * ((24 * K ^ 4) * ((1 + ‖p‖) ^ 4)⁻¹) :=
              mul_le_mul (hB p) h_ker_le (norm_nonneg _) hB_nn
          _ = (B * (24 * K ^ 4)) * ((1 + ‖p‖) ^ 4)⁻¹ := by ring
    _ = C₀ * c⁻¹ ^ 4 := by
        rw [integral_const_mul, hK_pow]
        dsimp [C₀, I_dec]
        ring

lemma coneGap_im_sub_ge_first_aux {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) :
    ∀ (d u : ℕ) (hv : u + (d + 1) < n),
      coneGap (diff_im n z ⟨u, by omega⟩ (by dsimp; omega)) ≤
        coneGap (fun μ => (z ⟨u + (d + 1), hv⟩ μ).im - (z ⟨u, by omega⟩ μ).im)
  | 0, u, hv => by
      have h_eq :
          (fun μ => (z ⟨u + (0 + 1), hv⟩ μ).im - (z ⟨u, by omega⟩ μ).im) =
            diff_im n z ⟨u, by omega⟩ (by dsimp; omega) := by
        ext μ
        simp [diff_im, diff_z]
      rw [h_eq]
  | d + 1, u, hv => by
      have h1 := coneGap_im_sub_ge_first_aux hz d u (by omega)
      have h2_pos : 0 < coneGap (diff_im n z ⟨u + (d + 1), by omega⟩ hv) :=
        coneGap_pos _ (diff_im_mem_forward_cone n z hz ⟨u + (d + 1), by omega⟩ hv)
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
      have h_add := coneGap_add_ge
        (fun μ => (z ⟨u + (d + 1), by omega⟩ μ).im - (z ⟨u, by omega⟩ μ).im)
        (diff_im n z ⟨u + (d + 1), by omega⟩ hv)
      rw [h_eq]
      linarith

lemma inv_coneGap_pair_le_tubeGapFactor {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) {u v : Fin n} (huv : u < v) :
    (coneGap (diff_im 2 ![z u, z v] 0 (by decide)))⁻¹ ≤ tubeGapFactor n z := by
  have hu1 : u.val + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt huv) v.isLt
  have hv_eq : u.val + ((v.val - u.val - 1) + 1) = v.val := by
    have hlt : u.val < v.val := huv
    omega
  have hv_lt : u.val + ((v.val - u.val - 1) + 1) < n := by
    rw [hv_eq]
    exact v.isLt
  have h_ge := coneGap_im_sub_ge_first_aux hz (v.val - u.val - 1) u.val hv_lt
  have h_lhs_eq :
      diff_im n z ⟨u.val, by omega⟩ (by dsimp; omega) = diff_im n z u hu1 := by
    ext μ
    simp [diff_im, diff_z]
  have h_rhs_eq :
      (fun μ =>
        (z ⟨u.val + ((v.val - u.val - 1) + 1), hv_lt⟩ μ).im -
          (z ⟨u.val, by omega⟩ μ).im) =
        diff_im 2 ![z u, z v] 0 (by decide) := by
    have hv_fin : (⟨u.val + ((v.val - u.val - 1) + 1), hv_lt⟩ : Fin n) = v := Fin.ext hv_eq
    have hu_fin : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
    ext μ
    rw [hv_fin, hu_fin]
    simp [diff_im, diff_z]
  rw [h_lhs_eq, h_rhs_eq] at h_ge
  let a := coneGap (diff_im n z u hu1)
  let b := coneGap (diff_im 2 ![z u, z v] 0 (by decide))
  have ha : 0 < a := coneGap_pos _ (diff_im_mem_forward_cone n z hz u hu1)
  have hb : 0 < b := lt_of_lt_of_le ha h_ge
  have h_inv_le : b⁻¹ ≤ a⁻¹ := by
    have ha_mul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.ne'
    have hb_mul : b * b⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
    have h_ab : a * b⁻¹ ≤ b * b⁻¹ := mul_le_mul_of_nonneg_right h_ge (inv_nonneg.mpr hb.le)
    exact le_of_mul_le_mul_left (by linarith : a * b⁻¹ ≤ a * a⁻¹) ha
  exact h_inv_le.trans (inv_coneGap_le_tubeGapFactor hz u hu1)

theorem ostubeGrowthBound_wickMassShellH {κ : Type*} {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → κ) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    OSTubeGrowthBound (wickMassShellH m η C) := by
  intro n α
  let C_c : ∀ P : ChordPairing n, P.Chord → ℝ := fun P c =>
    Classical.choose (norm_massShellTwoPointH_two_le hm hC ![α c.1, α (P.mate c.1)])
  have hC_c : ∀ (P : ChordPairing n) (c : P.Chord),
      0 ≤ C_c P c ∧ ∀ {w : Fin 2 → Fin 4 → ℂ}, w ∈ forward_tube_n 2 →
        ‖massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] w‖ ≤
          C_c P c * (coneGap (diff_im 2 w 0 (by decide)))⁻¹ ^ 4 :=
    fun P c => Classical.choose_spec
      (norm_massShellTwoPointH_two_le hm hC ![α c.1, α (P.mate c.1)])
  let C_tot : ℝ := ∑ P : ChordPairing n, ‖η‖ ^ P.cross * ∏ c : P.Chord, C_c P c
  have hC_tot_nn : 0 ≤ C_tot :=
    Finset.sum_nonneg fun P _ => mul_nonneg (pow_nonneg (norm_nonneg η) _)
      (Finset.prod_nonneg fun c _ => (hC_c P c).1)
  refine ⟨C_tot, 0, 2 * n, hC_tot_nn, fun z hz => ?_⟩
  unfold wickMassShellH
  rw [pow_zero, mul_one]
  refine (norm_sum_le Finset.univ _).trans ?_
  have h_sum_le :
      (∑ P : ChordPairing n,
        ‖η ^ P.cross * ∏ c : P.Chord,
          massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖) ≤
      ∑ P : ChordPairing n,
        (‖η‖ ^ P.cross * ∏ c : P.Chord, C_c P c) * (tubeGapFactor n z) ^ (2 * n) := by
    refine Finset.sum_le_sum fun P _ => ?_
    rw [norm_mul, norm_pow, norm_prod]
    have h_prod_le :
        (∏ c : P.Chord,
          ‖massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖) ≤
        ∏ c : P.Chord, (C_c P c * (tubeGapFactor n z) ^ 4) := by
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun c _ => ?_
      have hzc : ![z c.1, z (P.mate c.1)] ∈ forward_tube_n 2 :=
        pair_mem_forward_tube_two hz c.2
      have h_inv_nn :
          0 ≤ (coneGap (diff_im 2 ![z c.1, z (P.mate c.1)] 0 (by decide)))⁻¹ :=
        inv_nonneg.mpr (coneGap_pos _
          (diff_im_mem_forward_cone 2 _ hzc 0 (by decide))).le
      have h_pow_le :
          (coneGap (diff_im 2 ![z c.1, z (P.mate c.1)] 0 (by decide)))⁻¹ ^ 4 ≤
            (tubeGapFactor n z) ^ 4 :=
        pow_le_pow_left₀ h_inv_nn (inv_coneGap_pair_le_tubeGapFactor hz c.2) 4
      exact ((hC_c P c).2 hzc).trans
        (mul_le_mul_of_nonneg_left h_pow_le (hC_c P c).1)
    have h_card : 4 * Fintype.card P.Chord = 2 * n := by
      have h2 := P.two_mul_card_chord
      omega
    have h_prod_eq :
        (∏ c : P.Chord, (C_c P c * (tubeGapFactor n z) ^ 4)) =
          (∏ c : P.Chord, C_c P c) * (tubeGapFactor n z) ^ (2 * n) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, h_card]
    calc ‖η‖ ^ P.cross *
          (∏ c : P.Chord,
            ‖massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖)
        ≤ ‖η‖ ^ P.cross * ∏ c : P.Chord, (C_c P c * (tubeGapFactor n z) ^ 4) :=
          mul_le_mul_of_nonneg_left h_prod_le (pow_nonneg (norm_nonneg η) _)
      _ = (‖η‖ ^ P.cross * ∏ c : P.Chord, C_c P c) * (tubeGapFactor n z) ^ (2 * n) := by
          rw [h_prod_eq, mul_assoc]
  exact h_sum_le.trans_eq (Finset.sum_mul Finset.univ _ _).symm

noncomputable def wickMassShellOSTubeExtensionData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q) :
    OSTubeExtensionData R_rep (wickMassShellS m hm η C hC) where
  H := wickMassShellH m η C
  analytic n α := analyticOn_wickMassShellH hm η hC n α
  growth := ostubeGrowthBound_wickMassShellH hm η hC
  schwinger_eq _ _ _ _ := rfl
  tube_covariant := wickMassShellTubeCovariant R_rep hm η hC hC_cov

theorem wickMassShellOSTubeExtensionData_W {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q) :
    (wickMassShellOSTubeExtensionData R_rep hm η hC hC_cov).W =
      wickMassShellW m η C hC :=
  wightman_eq_of_tubeExtension_eq
    (wickMassShellOSTubeExtensionData R_rep hm η hC hC_cov).E
    (wickMassShellTubeExtension m hm η C hC)
    (fun _ _ _ _ => rfl)

noncomputable def wickMassShellFullOSTubeExtensionData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q) :
    OSTubeExtensionData R_rep (wickMassShellFullS R_rep m hm η C hC) where
  H := wickMassShellH m η C
  analytic n α := analyticOn_wickMassShellH hm η hC n α
  growth := ostubeGrowthBound_wickMassShellH hm η hC
  schwinger_eq n α _x hx :=
    wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx
  tube_covariant := wickMassShellTubeCovariant R_rep hm η hC hC_cov

theorem wickMassShellFullOSTubeExtensionData_W {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) {m : ℝ} (hm : 0 < m) (η : ℂ)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q) :
    (wickMassShellFullOSTubeExtensionData R_rep hm η hC hC_cov).W =
      wickMassShellW m η C hC :=
  wightman_eq_of_tubeExtension_eq
    (wickMassShellFullOSTubeExtensionData R_rep hm η hC hC_cov).E
    (wickMassShellTubeExtension m hm η C hC)
    (fun _ _ _ _ => rfl)

noncomputable def freeKGOSTubeExtensionData {m : ℝ} (hm : 0 < m) :
    OSTubeExtensionData trivialRep (freeKGS m hm) :=
  wickMassShellOSTubeExtensionData trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGOSTubeExtensionData_W {m : ℝ} (hm : 0 < m) :
    (freeKGOSTubeExtensionData hm).W = freeKGW m hm :=
  wickMassShellOSTubeExtensionData_W trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

noncomputable def freeDiracOSTubeExtensionData {m : ℝ} (hm : 0 < m) :
    OSTubeExtensionData diracRep (freeDiracS m hm) :=
  wickMassShellOSTubeExtensionData diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem freeDiracOSTubeExtensionData_W {m : ℝ} (hm : 0 < m) :
    (freeDiracOSTubeExtensionData hm).W = freeDiracW m hm :=
  wickMassShellOSTubeExtensionData_W diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

noncomputable def freeKGFullOSTubeExtensionData {m : ℝ} (hm : 0 < m) :
    OSTubeExtensionData trivialRep (freeKGFullS m hm) :=
  wickMassShellFullOSTubeExtensionData trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeKGFullOSTubeExtensionData_W {m : ℝ} (hm : 0 < m) :
    (freeKGFullOSTubeExtensionData hm).W = freeKGW m hm :=
  wickMassShellFullOSTubeExtensionData_W trivialRep hm 1 (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

noncomputable def freeDiracFullOSTubeExtensionData {m : ℝ} (hm : 0 < m) :
    OSTubeExtensionData diracRep (freeDiracFullS m hm) :=
  wickMassShellFullOSTubeExtensionData diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem freeDiracFullOSTubeExtensionData_W {m : ℝ} (hm : 0 < m) :
    (freeDiracFullOSTubeExtensionData hm).W = freeDiracW m hm :=
  wickMassShellFullOSTubeExtensionData_W diracRep hm (-1) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)

theorem wickMassShellS_positiveTimeTwoPointPowerBound {ι : Type*} [Finite ι]
    {m : ℝ} (hm : 0 < m) (η : ℂ) {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C) :
    OSPositiveTimeTwoPointPowerBound (wickMassShellS m hm η C hC) := by
  letI : Fintype ι := Fintype.ofFinite ι
  let C_α : (Fin 2 → ι) → ℝ := fun β =>
    Classical.choose (norm_massShellTwoPointH_two_le hm hC β)
  have hC_α : ∀ β : Fin 2 → ι,
      0 ≤ C_α β ∧ ∀ {z : Fin 2 → Fin 4 → ℂ}, z ∈ forward_tube_n 2 →
        ‖massShellTwoPointH m C 2 β z‖ ≤
          C_α β * (coneGap (diff_im 2 z 0 (by decide)))⁻¹ ^ 4 :=
    fun β => Classical.choose_spec (norm_massShellTwoPointH_two_le hm hC β)
  let C_sum : ℝ := ∑ β : Fin 2 → ι, C_α β
  refine ⟨C_sum, 4, Finset.sum_nonneg (fun β _ => (hC_α β).1), fun α t ht => ?_⟩
  let x_t : Fin 2 → Fin 4 → ℝ := ![0, euclidTimeVec t]
  have hx_t : x_t ∈ orderedEuclidN 2 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [x_t, euclidTimeVec] using ht
  have hz_t : wickEmbedN 2 x_t ∈ forward_tube_n 2 :=
    wickEmbedN_mem_forward_tube_n 2 hx_t
  have h_eq : wickMassShellS m hm η C hC 2 α x_t =
      massShellTwoPointH m C 2 α (wickEmbedN 2 x_t) := by
    change wickMassShellH m η C 2 α (wickEmbedN 2 x_t) = _
    exact wickMassShellH_two m η C α (wickEmbedN 2 x_t)
  have h_diff :
      diff_im 2 (wickEmbedN 2 x_t) 0 (by decide) = euclidTimeVec t := by
    ext μ
    fin_cases μ <;> simp [diff_im, diff_z, wickEmbedN, wickEmbed, x_t, euclidTimeVec]
  have h_gap : coneGap (diff_im 2 (wickEmbedN 2 x_t) 0 (by decide)) = t := by
    rw [h_diff]
    simp [coneGap, euclidTimeVec]
  have h_le_α : C_α α ≤ C_sum :=
    Finset.single_le_sum (fun β _ => (hC_α β).1) (Finset.mem_univ α)
  have h_pow_le : t⁻¹ ^ 4 ≤ (1 + t + t⁻¹) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  rw [h_eq]
  refine ((hC_α α).2 hz_t).trans ?_
  rw [h_gap]
  exact mul_le_mul h_le_α h_pow_le (by positivity)
    (Finset.sum_nonneg (fun β _ => (hC_α β).1))

theorem freeKGS_positiveTimeTwoPointPowerBound {m : ℝ} (hm : 0 < m) :
    OSPositiveTimeTwoPointPowerBound (freeKGS m hm) :=
  wickMassShellS_positiveTimeTwoPointPowerBound hm 1 (massiveKGCoeff_data hm)

theorem freeDiracS_positiveTimeTwoPointPowerBound {m : ℝ} (hm : 0 < m) :
    OSPositiveTimeTwoPointPowerBound (freeDiracS m hm) :=
  wickMassShellS_positiveTimeTwoPointPowerBound hm (-1) (diracMassShellCoeff_data hm)

theorem freeKG_two_point_os_reconstruction {m : ℝ} (hm : 0 < m) :
    let W₂ := osTwoPointWightmanFamily (freeKGOSAxioms hm)
      (freeKGOSTimeCluster hm) (freeKGS_positiveTimeTwoPointPowerBound hm)
    let E₂ := osTwoPointExtension (freeKGOSAxioms hm)
      (freeKGOSTimeCluster hm) (freeKGS_positiveTimeTwoPointPowerBound hm)
    (∀ (n : ℕ), n ≤ 2 → ∀ (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeKGS m hm n α x = schwingerFromTube E₂ n α x) ∧
    TubeCovariant trivialRep E₂ ∧
    TubeTranslationInvariant E₂ ∧
    SpectrumCondition W₂ ∧
    PoincareCovariant trivialRep W₂ ∧
    TubePCT 1 trivialRep E₂ ∧
    WeakLocality 1 W₂ ∧
    PositivityUpTo 1 trivialStarStructure W₂ :=
  os_two_point_wightman_reconstruction (freeKGOSAxioms hm)
    (freeKGOSTimeCluster hm) (freeKGS_positiveTimeTwoPointPowerBound hm)

theorem freeKG_two_point_os_eq_freeKGW {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : n ≤ 2) :
    osTwoPointWightmanFamily (freeKGOSAxioms hm) (freeKGOSTimeCluster hm)
      (freeKGS_positiveTimeTwoPointPowerBound hm) n = freeKGW m hm n := by
  rw [osTwoPointWightmanFamily_eq_of_tubeExtensionData (freeKGOSAxioms hm)
    (freeKGOSTimeCluster hm) (freeKGS_positiveTimeTwoPointPowerBound hm)
    (freeKGOSTubeExtensionData hm) hn, freeKGOSTubeExtensionData_W hm]

theorem freeDirac_two_point_os_reconstruction {m : ℝ} (hm : 0 < m) :
    let W₂ := osTwoPointWightmanFamily (freeDiracOSAxioms hm)
      (freeDiracOSTimeCluster hm) (freeDiracS_positiveTimeTwoPointPowerBound hm)
    let E₂ := osTwoPointExtension (freeDiracOSAxioms hm)
      (freeDiracOSTimeCluster hm) (freeDiracS_positiveTimeTwoPointPowerBound hm)
    (∀ (n : ℕ), n ≤ 2 → ∀ (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeDiracS m hm n α x = schwingerFromTube E₂ n α x) ∧
    TubeCovariant diracRep E₂ ∧
    TubeTranslationInvariant E₂ ∧
    SpectrumCondition W₂ ∧
    PoincareCovariant diracRep W₂ ∧
    TubePCT (-1) diracRep E₂ ∧
    WeakLocality (-1) W₂ ∧
    PositivityUpTo 1 diracStarStructure W₂ :=
  os_two_point_wightman_reconstruction (freeDiracOSAxioms hm)
    (freeDiracOSTimeCluster hm) (freeDiracS_positiveTimeTwoPointPowerBound hm)

theorem freeDirac_two_point_os_eq_freeDiracW {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : n ≤ 2) :
    osTwoPointWightmanFamily (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm)
      (freeDiracS_positiveTimeTwoPointPowerBound hm) n = freeDiracW m hm n := by
  rw [osTwoPointWightmanFamily_eq_of_tubeExtensionData (freeDiracOSAxioms hm)
    (freeDiracOSTimeCluster hm) (freeDiracS_positiveTimeTwoPointPowerBound hm)
    (freeDiracOSTubeExtensionData hm) hn, freeDiracOSTubeExtensionData_W hm]

theorem freeKG_os_to_wightman_synthesis {m : ℝ} (hm : 0 < m) :
    let hOS := freeKGOSAxioms hm
    let hcluster := freeKGOSTimeCluster hm
    let hnorm := freeKGOSVacuumNormalized hm
    let T := freeKGOSTubeExtensionData hm
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeKGW m hm ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeKGS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare trivialRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms trivialRep trivialStarStructure 1 P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = freeKGS m hm n α x) := by
  have hsyn := os_to_wightman_full_synthesis (freeKGOSAxioms hm)
    (freeKGOSTimeCluster hm) (freeKGOSVacuumNormalized hm) (freeKGOSTubeExtensionData hm)
  have hW : (freeKGOSTubeExtensionData hm).W = freeKGW m hm :=
    freeKGOSTubeExtensionData_W hm
  have hloc : LocalCommutativity 1 (freeKGOSTubeExtensionData hm).W := by
    rw [hW]
    exact freeKG_localCommutativity hm
  rcases hsyn with ⟨hG, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inl rfl) hloc with ⟨hFE, hperm⟩
  exact ⟨hG.trans hW, hschw, hvac, htr, hFE, hperm⟩

theorem freeDirac_os_to_wightman_synthesis {m : ℝ} (hm : 0 < m) :
    let hOS := freeDiracOSAxioms hm
    let hcluster := freeDiracOSTimeCluster hm
    let hnorm := freeDiracOSVacuumNormalized hm
    let T := freeDiracOSTubeExtensionData hm
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeDiracW m hm ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeDiracS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare diracRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms diracRep diracStarStructure (-1) P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = freeDiracS m hm n α x) := by
  have hsyn := os_to_wightman_full_synthesis (freeDiracOSAxioms hm)
    (freeDiracOSTimeCluster hm) (freeDiracOSVacuumNormalized hm) (freeDiracOSTubeExtensionData hm)
  have hW : (freeDiracOSTubeExtensionData hm).W = freeDiracW m hm :=
    freeDiracOSTubeExtensionData_W hm
  have hloc : LocalCommutativity (-1) (freeDiracOSTubeExtensionData hm).W := by
    rw [hW]
    exact freeDirac_localCommutativity hm
  rcases hsyn with ⟨hG, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inr rfl) hloc with ⟨hFE, hperm⟩
  exact ⟨hG.trans hW, hschw, hvac, htr, hFE, hperm⟩

def liftTailPerm {r : ℕ} (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, σ)

@[simp]
lemma liftTailPerm_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    liftTailPerm σ 0 = 0 := by
  simp [liftTailPerm]

@[simp]
lemma liftTailPerm_succ {r : ℕ} (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    liftTailPerm σ j.succ = (σ j).succ := by
  simp [liftTailPerm]

@[simp]
lemma liftTailPerm_symm {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    (liftTailPerm σ).symm = liftTailPerm σ.symm := by
  apply Equiv.Perm.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply (liftTailPerm σ).injective
    simp
  · apply (liftTailPerm σ).injective
    simp

lemma liftTailPerm_decomposeFin_snd {n : ℕ} {q : Equiv.Perm (Fin (n + 1))} (hq : q 0 = 0) :
    liftTailPerm (Equiv.Perm.decomposeFin q).2 = q := by
  dsimp [liftTailPerm]
  have hf : (Equiv.Perm.decomposeFin q).1 = q 0 := by
    conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply q]
    rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  have h_dec : Equiv.Perm.decomposeFin q = (0, (Equiv.Perm.decomposeFin q).2) :=
    Prod.ext (hf.trans hq) rfl
  rw [← h_dec, Equiv.symm_apply_apply]

lemma sign_liftTailPerm {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    Equiv.Perm.sign (liftTailPerm σ) = Equiv.Perm.sign σ := by
  simp [liftTailPerm]

lemma eta_pow_permInversions_liftTailPerm {η : ℂ} (hη : η = 1 ∨ η = -1)
    {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    η ^ permInversions (liftTailPerm σ) = η ^ permInversions σ := by
  rcases hη with rfl | rfl
  · simp
  · rw [eta_pow_permInversions_eq_sign, eta_pow_permInversions_eq_sign, sign_liftTailPerm]

lemma eta_pow_permInversions_cycleRange {η : ℂ} (hη : η = 1 ∨ η = -1)
    {r : ℕ} (p : Fin (r + 1)) :
    η ^ permInversions p.cycleRange = η ^ (p : ℕ) := by
  rcases hη with rfl | rfl
  · simp
  · rw [eta_pow_permInversions_eq_sign, Fin.sign_cycleRange]
    push_cast
    rfl

def createPermEquiv (r : ℕ) :
    Fin (r + 1) × Equiv.Perm (Fin r) ≃ Equiv.Perm (Fin (r + 1)) where
  toFun ps := ps.1.cycleRange.symm * liftTailPerm ps.2
  invFun π := (π 0, (Equiv.Perm.decomposeFin ((π 0).cycleRange * π)).2)
  left_inv := by
    rintro ⟨p, σ⟩
    have h0 : (p.cycleRange.symm * liftTailPerm σ) 0 = p := by simp
    ext1
    · exact h0
    · dsimp only
      rw [h0]
      have h_mul : p.cycleRange * (p.cycleRange.symm * liftTailPerm σ) = liftTailPerm σ := by
        ext x
        simp
      rw [h_mul]
      dsimp [liftTailPerm]
      rw [Equiv.apply_symm_apply]
  right_inv := by
    intro π
    let q := (π 0).cycleRange * π
    have hq0 : q 0 = 0 := by simp [q]
    have h_dec : Equiv.Perm.decomposeFin q = (0, (Equiv.Perm.decomposeFin q).2) := by
      have hf : (Equiv.Perm.decomposeFin q).1 = q 0 := by
        conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply q]
        rw [Equiv.Perm.decomposeFin_symm_apply_zero]
      exact Prod.ext (hf.trans hq0) rfl
    have h_lift : liftTailPerm (Equiv.Perm.decomposeFin q).2 = q := by
      dsimp [liftTailPerm]
      rw [← h_dec, Equiv.symm_apply_apply]
    dsimp only
    change (π 0).cycleRange.symm * liftTailPerm (Equiv.Perm.decomposeFin q).2 = π
    rw [h_lift]
    ext x
    simp [q]

@[simp]
lemma createPermEquiv_apply_zero {r : ℕ} (p : Fin (r + 1)) (σ : Equiv.Perm (Fin r)) :
    createPermEquiv r (p, σ) 0 = p := by
  simp [createPermEquiv]

@[simp]
lemma createPermEquiv_apply_succ {r : ℕ} (p : Fin (r + 1)) (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    createPermEquiv r (p, σ) j.succ = p.succAbove (σ j) := by
  simp [createPermEquiv]

lemma eta_pow_permInversions_createPermEquiv {η : ℂ} (hη : η = 1 ∨ η = -1)
    {r : ℕ} (p : Fin (r + 1)) (σ : Equiv.Perm (Fin r)) :
    η ^ permInversions (createPermEquiv r (p, σ)) = η ^ (p : ℕ) * η ^ permInversions σ := by
  dsimp [createPermEquiv]
  change η ^ permInversions ((p.cycleRange)⁻¹ * liftTailPerm σ) = _
  rw [eta_pow_permInversions_mul hη, eta_pow_permInversions_inv hη,
      eta_pow_permInversions_cycleRange hη, eta_pow_permInversions_liftTailPerm hη]

def annihPermEquiv (r : ℕ) :
    Fin (r + 1) × Equiv.Perm (Fin r) ≃ Equiv.Perm (Fin (r + 1)) :=
  ((Equiv.refl (Fin (r + 1))).prodCongr (Equiv.inv (Equiv.Perm (Fin r)))).trans
    ((createPermEquiv r).trans (Equiv.inv (Equiv.Perm (Fin (r + 1)))))

lemma annihPermEquiv_eq {r : ℕ} (p : Fin (r + 1)) (σ : Equiv.Perm (Fin r)) :
    annihPermEquiv r (p, σ) = liftTailPerm σ * p.cycleRange := by
  apply Equiv.Perm.ext
  intro x
  have h_inv : annihPermEquiv r (p, σ) = (p.cycleRange.symm * liftTailPerm σ⁻¹)⁻¹ := rfl
  rw [h_inv, _root_.mul_inv_rev]
  change (liftTailPerm σ⁻¹).symm (p.cycleRange.symm.symm x) = _
  rw [liftTailPerm_symm]
  rfl

lemma cons_comp_annihPermEquiv {α_t : Type*} {r : ℕ} (a : α_t) (f : Fin r → α_t)
    (p : Fin (r + 1)) (σ : Equiv.Perm (Fin r)) :
    (Fin.cons a f : Fin (r + 1) → α_t) ∘ annihPermEquiv r (p, σ) =
      p.insertNth a (f ∘ σ) := by
  rw [annihPermEquiv_eq]
  have h_left : (Fin.cons a f : Fin (r + 1) → α_t) ∘ liftTailPerm σ = Fin.cons a (f ∘ σ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  change ((Fin.cons a f : Fin (r + 1) → α_t) ∘ liftTailPerm σ) ∘ p.cycleRange = _
  rw [h_left, Fin.cons_comp_cycleRange]

lemma eta_pow_permInversions_annihPermEquiv {η : ℂ} (hη : η = 1 ∨ η = -1)
    {r : ℕ} (p : Fin (r + 1)) (σ : Equiv.Perm (Fin r)) :
    η ^ permInversions (annihPermEquiv r (p, σ)) = η ^ (p : ℕ) * η ^ permInversions σ := by
  rw [annihPermEquiv_eq, eta_pow_permInversions_mul hη,
      eta_pow_permInversions_liftTailPerm hη, eta_pow_permInversions_cycleRange hη, mul_comm]

namespace PartialPairing

def prependUnpaired {j r : ℕ} (L : PartialPairing j r) :
    PartialPairing (j + 1) (r + 1) where
  unpaired := Fin.cons 0 (fun a => (L.unpaired a).succ)
  strictMono_unpaired a b hab := by
    revert hab
    refine Fin.cases ?_ (fun a' => ?_) a
    · refine Fin.cases (fun h => False.elim (lt_irrefl 0 h)) (fun _ _ => Fin.succ_pos _) b
    · refine Fin.cases (fun h => False.elim (Nat.not_lt_zero _ h)) (fun b' h => ?_) b
      exact Fin.succ_lt_succ_iff.mpr (L.strictMono_unpaired (Fin.succ_lt_succ_iff.mp h))
  mate := liftTailPerm L.mate
  involutive u := by
    refine Fin.cases ?_ (fun i => ?_) u <;> simp
  fixed_iff u := by
    refine Fin.cases ?_ (fun i => ?_) u
    · simp only [liftTailPerm_zero, true_iff]
      exact ⟨0, rfl⟩
    · simp only [liftTailPerm_succ, Fin.succ_inj, L.fixed_iff]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.succ, rfl⟩
      · rintro ⟨a, ha⟩
        refine Fin.cases (fun h0 => False.elim (Fin.succ_ne_zero _ h0.symm))
          (fun b hb => ⟨b, Fin.succ_inj.mp hb⟩) a ha

def unprependUnpaired {j r : ℕ} (L : PartialPairing (j + 1) (r + 1))
    (h0 : L.mate 0 = 0) : PartialPairing j r where
  unpaired b :=
    have hb_pos : L.unpaired b.succ ≠ 0 := by
      have h0_mem := (L.fixed_iff 0).mp h0
      rcases h0_mem with ⟨a₀, ha₀⟩
      have ha₀_eq : a₀ = 0 := by
        by_contra hne
        have hpos : 0 < a₀ := Fin.pos_of_ne_zero hne
        have hlt := L.strictMono_unpaired hpos
        rw [ha₀] at hlt
        exact Nat.not_lt_zero _ hlt
      subst ha₀_eq
      exact ne_of_gt (ha₀ ▸ L.strictMono_unpaired (Fin.succ_pos b))
    (L.unpaired b.succ).pred hb_pos
  strictMono_unpaired b₁ b₂ hb := by
    dsimp only
    rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
    exact L.strictMono_unpaired (Fin.succ_lt_succ_iff.mpr hb)
  mate := (Equiv.Perm.decomposeFin L.mate).2
  involutive i := by
    have h_lift := liftTailPerm_decomposeFin_snd h0
    have h_succ := congrArg (fun p : Equiv.Perm (Fin (j + 1)) => p (p i.succ)) h_lift
    simp only [liftTailPerm_succ, L.mate_mate] at h_succ
    exact Fin.succ_inj.mp h_succ
  fixed_iff i := by
    have h_lift := liftTailPerm_decomposeFin_snd h0
    have h_app : ((Equiv.Perm.decomposeFin L.mate).2 i).succ = L.mate i.succ :=
      (liftTailPerm_succ _ i).symm.trans (congrArg (fun p => p i.succ) h_lift)
    have h0_eq : L.unpaired 0 = 0 := by
      rcases (L.fixed_iff 0).mp h0 with ⟨a₀, ha₀⟩
      have ha₀_z : a₀ = 0 := by
        by_contra hne
        have hlt := L.strictMono_unpaired (Fin.pos_of_ne_zero hne)
        rw [ha₀] at hlt
        exact Nat.not_lt_zero _ hlt
      exact ha₀_z ▸ ha₀
    rw [← Fin.succ_inj, h_app, L.fixed_iff]
    constructor
    · rintro ⟨a, ha⟩
      refine Fin.cases (fun hz => False.elim (Fin.succ_ne_zero i (hz.symm.trans h0_eq)))
        (fun b hb => ⟨b, ?_⟩) a ha
      dsimp only
      rw [← Fin.succ_inj, Fin.succ_pred, hb]
    · rintro ⟨b, rfl⟩
      refine ⟨b.succ, ?_⟩
      dsimp only
      exact (Fin.succ_pred _ _).symm

lemma prependUnpaired_InternalChord_equiv_aux {j r : ℕ} (L : PartialPairing j r)
    (u : Fin (j + 1)) :
    u < (prependUnpaired L).mate u ↔ ∃ i : Fin j, u = i.succ ∧ i < L.mate i := by
  refine Fin.cases ?_ (fun i => ?_) u
  · simp only [prependUnpaired, liftTailPerm_zero, lt_self_iff_false, false_iff]
    rintro ⟨x, hx, _⟩
    exact Fin.succ_ne_zero x hx.symm
  · simp only [prependUnpaired, liftTailPerm_succ, Fin.succ_lt_succ_iff, Fin.succ_inj]
    exact ⟨fun h => ⟨i, rfl, h⟩, fun ⟨i', hi', h⟩ => hi' ▸ h⟩

def prependUnpairedChordEquiv {j r : ℕ} (L : PartialPairing j r) :
    L.InternalChord ≃ (prependUnpaired L).InternalChord where
  toFun c := ⟨c.1.succ, by simpa [prependUnpaired] using c.2⟩
  invFun c :=
    have hc0 : c.1 ≠ 0 := by
      intro h0
      have hlt := c.2
      rw [h0] at hlt
      simp [prependUnpaired] at hlt
    ⟨c.1.pred hc0, by
      have hlt := c.2
      have hs : (c.1.pred hc0).succ = c.1 := Fin.succ_pred c.1 hc0
      rw [← hs] at hlt
      change (c.1.pred hc0).succ < (L.mate (c.1.pred hc0)).succ at hlt
      exact Fin.succ_lt_succ_iff.mp hlt⟩
  left_inv c := by ext; simp
  right_inv c := by ext; simp

lemma partialCross_prependUnpaired {j r : ℕ} (L : PartialPairing j r) :
    (prependUnpaired L).partialCross = L.partialCross := by
  have h_int : (prependUnpaired L).internalCross = L.internalCross := by
    dsimp [internalCross]
    refine Finset.card_bij
      (fun uv huv =>
        have hu0 : uv.1 ≠ 0 := by
          intro h0
          rcases Finset.mem_filter.mp huv with ⟨_, _, h2, _⟩
          rw [h0] at h2
          simp [prependUnpaired] at h2
        have hv0 : uv.2 ≠ 0 := by
          intro h0
          rcases Finset.mem_filter.mp huv with ⟨_, h1, _, _⟩
          rw [h0] at h1
          exact Nat.not_lt_zero _ h1
        (uv.1.pred hu0, uv.2.pred hv0))
      (fun uv huv => ?_)
      (fun a ha b hb hab => ?_)
      (fun pq hpq => ⟨(pq.1.succ, pq.2.succ), ?_, by ext <;> simp⟩)
    · rcases Finset.mem_filter.mp huv with ⟨_, h1, h2, h3⟩
      have hu0 : uv.1 ≠ 0 := by
        intro h0; rw [h0] at h2; simp [prependUnpaired] at h2
      have hv0 : uv.2 ≠ 0 := by
        intro h0; rw [h0] at h1; exact Nat.not_lt_zero _ h1
      have hsu : (uv.1.pred hu0).succ = uv.1 := Fin.succ_pred uv.1 hu0
      have hsv : (uv.2.pred hv0).succ = uv.2 := Fin.succ_pred uv.2 hv0
      rw [← hsu, ← hsv] at h1 h2 h3
      simp only [prependUnpaired, liftTailPerm_succ, Fin.succ_lt_succ_iff] at h1 h2 h3
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2, h3⟩
    · have h1 := (Prod.mk.inj hab).1
      have h2 := (Prod.mk.inj hab).2
      ext1
      · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ h1)
      · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ h2)
    · rcases Finset.mem_filter.mp hpq with ⟨_, h1, h2, h3⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [prependUnpaired, h1, h2, h3]
  have h_open : (prependUnpaired L).openCross = L.openCross := by
    dsimp [openCross]
    refine Finset.card_bij
      (fun ca hca =>
        have hc0 : ca.1 ≠ 0 := by
          intro h0
          rcases Finset.mem_filter.mp hca with ⟨_, _, h2⟩
          rw [h0] at h2
          simp [prependUnpaired] at h2
        have ha0 : ca.2 ≠ 0 := by
          intro h0
          rcases Finset.mem_filter.mp hca with ⟨_, h1, _⟩
          rw [h0] at h1
          simp [prependUnpaired] at h1
        (ca.1.pred hc0, ca.2.pred ha0))
      (fun ca hca => ?_)
      (fun a ha b hb hab => ?_)
      (fun ia hia => ⟨(ia.1.succ, ia.2.succ), ?_, by ext <;> simp⟩)
    · rcases Finset.mem_filter.mp hca with ⟨_, h1, h2⟩
      have hc0 : ca.1 ≠ 0 := by
        intro h0; rw [h0] at h2; simp [prependUnpaired] at h2
      have ha0 : ca.2 ≠ 0 := by
        intro h0; rw [h0] at h1; simp [prependUnpaired] at h1
      have hsc : (ca.1.pred hc0).succ = ca.1 := Fin.succ_pred ca.1 hc0
      have hsa : (ca.2.pred ha0).succ = ca.2 := Fin.succ_pred ca.2 ha0
      rw [← hsc, ← hsa] at h1 h2
      simp only [prependUnpaired, Fin.cons_succ, liftTailPerm_succ, Fin.succ_lt_succ_iff] at h1 h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
    · have h1 := (Prod.mk.inj hab).1
      have h2 := (Prod.mk.inj hab).2
      ext1
      · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ h1)
      · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ h2)
    · rcases Finset.mem_filter.mp hia with ⟨_, h1, h2⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [prependUnpaired, h1, h2]
  dsimp [partialCross]
  rw [h_int, h_open]

def prependPaired {j r : ℕ} (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1)) :
    PartialPairing (j + 1) r where
  unpaired b := (L'.unpaired (a₀.succAbove b)).succ
  strictMono_unpaired b₁ b₂ hb :=
    Fin.succ_lt_succ_iff.mpr (L'.strictMono_unpaired (Fin.succAbove_lt_succAbove_iff.mpr hb))
  mate := Equiv.swap 0 (L'.unpaired a₀).succ * liftTailPerm L'.mate
  involutive u := by
    let i₀ := L'.unpaired a₀
    have hi₀_fix : L'.mate i₀ = i₀ := L'.mate_unpaired a₀
    refine Fin.cases ?_ (fun i => ?_) u
    · change (Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate
        ((Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate 0))) = 0
      simp [i₀, hi₀_fix]
    · by_cases hi : i = i₀
      · subst hi
        change (Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate
          ((Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate i₀.succ))) = i₀.succ
        simp [i₀, hi₀_fix]
      · have hmi : L'.mate i ≠ i₀ := fun hc =>
          hi (by rw [← L'.mate_mate i, hc, hi₀_fix])
        have hs1 : (L'.mate i).succ ≠ 0 := Fin.succ_ne_zero _
        have hs2 : (L'.mate i).succ ≠ i₀.succ := Fin.succ_inj.ne.mpr hmi
        have hs3 : i.succ ≠ 0 := Fin.succ_ne_zero _
        have hs4 : i.succ ≠ i₀.succ := Fin.succ_inj.ne.mpr hi
        change (Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate
          ((Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate i.succ))) = i.succ
        rw [liftTailPerm_succ, Equiv.swap_apply_of_ne_of_ne hs1 hs2,
            liftTailPerm_succ, L'.mate_mate, Equiv.swap_apply_of_ne_of_ne hs3 hs4]
  fixed_iff u := by
    let i₀ := L'.unpaired a₀
    have hi₀_fix : L'.mate i₀ = i₀ := L'.mate_unpaired a₀
    refine Fin.cases ?_ (fun i => ?_) u
    · constructor
      · intro h0
        change (Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate 0) = 0 at h0
        simp only [liftTailPerm_zero, Equiv.swap_apply_left] at h0
        exact False.elim (Fin.succ_ne_zero _ h0)
      · rintro ⟨b, hb⟩
        exact False.elim (Fin.succ_ne_zero _ hb)
    · by_cases hi : i = i₀
      · subst hi
        constructor
        · intro hh
          change (Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate i₀.succ) = i₀.succ at hh
          simp only [liftTailPerm_succ, hi₀_fix, Equiv.swap_apply_right] at hh
          exact False.elim (Fin.succ_ne_zero _ hh.symm)
        · rintro ⟨b, hb⟩
          have h_eq := L'.unpaired_injective (Fin.succ_inj.mp hb)
          exact False.elim (Fin.succAbove_ne a₀ b h_eq)
      · have hmi : L'.mate i ≠ i₀ := fun hc =>
          hi (by rw [← L'.mate_mate i, hc, hi₀_fix])
        have hs1 : (L'.mate i).succ ≠ 0 := Fin.succ_ne_zero _
        have hs2 : (L'.mate i).succ ≠ i₀.succ := Fin.succ_inj.ne.mpr hmi
        have h_eval : (Equiv.swap 0 i₀.succ * liftTailPerm L'.mate) i.succ = (L'.mate i).succ := by
          change (Equiv.swap 0 i₀.succ) (liftTailPerm L'.mate i.succ) = _
          rw [liftTailPerm_succ, Equiv.swap_apply_of_ne_of_ne hs1 hs2]
        rw [h_eval, Fin.succ_inj, L'.fixed_iff]
        constructor
        · rintro ⟨a, rfl⟩
          have ha_ne : a ≠ a₀ := fun hc => hi (hc ▸ rfl)
          rcases Fin.exists_succAbove_eq ha_ne with ⟨b, rfl⟩
          exact ⟨b, rfl⟩
        · rintro ⟨b, hb⟩
          exact ⟨a₀.succAbove b, Fin.succ_inj.mp hb⟩

end PartialPairing

namespace PartialPairing

lemma prependPaired_mate_zero {j r : ℕ} (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1)) :
    (prependPaired L' a₀).mate 0 = (L'.unpaired a₀).succ := by
  change (Equiv.swap 0 (L'.unpaired a₀).succ) (liftTailPerm L'.mate 0) = _
  simp

lemma prependPaired_mate_unpaired_succ {j r : ℕ} (L' : PartialPairing j (r + 1))
    (a₀ : Fin (r + 1)) :
    (prependPaired L' a₀).mate (L'.unpaired a₀).succ = 0 := by
  change (Equiv.swap 0 (L'.unpaired a₀).succ) (liftTailPerm L'.mate (L'.unpaired a₀).succ) = 0
  simp [L'.mate_unpaired a₀]

lemma prependPaired_mate_succ_of_ne {j r : ℕ} (L' : PartialPairing j (r + 1))
    (a₀ : Fin (r + 1)) {i : Fin j} (hi : i ≠ L'.unpaired a₀) :
    (prependPaired L' a₀).mate i.succ = (L'.mate i).succ := by
  have hmi : L'.mate i ≠ L'.unpaired a₀ := fun hc =>
    hi (by rw [← L'.mate_mate i, hc, L'.mate_unpaired a₀])
  change (Equiv.swap 0 (L'.unpaired a₀).succ) (liftTailPerm L'.mate i.succ) = _
  rw [liftTailPerm_succ,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_inj.ne.mpr hmi)]

def unprependPaired {j r : ℕ} (L : PartialPairing (j + 1) r) (h0 : L.mate 0 ≠ 0) :
    PartialPairing j (r + 1) × Fin (r + 1) :=
  let i₀ : Fin j := (L.mate 0).pred h0
  have hi₀_succ : i₀.succ = L.mate 0 := Fin.succ_pred (L.mate 0) h0
  have hub_ne0 : ∀ b : Fin r, L.unpaired b ≠ 0 := fun b hb =>
    h0 (by rw [← hb, L.mate_unpaired b])
  let u_tail : Fin r → Fin j := fun b => (L.unpaired b).pred (hub_ne0 b)
  have hu_strict : StrictMono u_tail := fun b₁ b₂ hb => by
    dsimp [u_tail]
    rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
    exact L.strictMono_unpaired hb
  have hu_ne_i₀ : ∀ b : Fin r, u_tail b ≠ i₀ := fun b hc => by
    have hs : L.unpaired b = L.mate 0 := by
      rw [← Fin.succ_pred (L.unpaired b) (hub_ne0 b), ← hi₀_succ]
      exact congrArg Fin.succ hc
    have hm := L.mate_unpaired b
    rw [hs, L.mate_mate] at hm
    exact h0 hm.symm
  let S_lt : Finset (Fin r) := Finset.univ.filter (fun b : Fin r => u_tail b < i₀)
  let a₀ : Fin (r + 1) :=
    ⟨S_lt.card, Nat.lt_succ_of_le ((Finset.card_le_univ S_lt).trans_eq (Fintype.card_fin r))⟩
  have h_lt_iff : ∀ b : Fin r, u_tail b < i₀ ↔ (b : ℕ) < (a₀ : ℕ) := by
    intro b
    dsimp [a₀]
    constructor
    · intro hlt
      have h_sub : Finset.Iic b ⊆ S_lt := fun c hc =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          lt_of_le_of_lt (hu_strict.monotone (Finset.mem_Iic.mp hc)) hlt⟩
      have h_card := Finset.card_le_card h_sub
      rw [Fin.card_Iic] at h_card
      omega
    · intro hlt_card
      by_contra h_nlt
      have hgt : i₀ < u_tail b :=
        (lt_or_gt_of_ne (hu_ne_i₀ b)).resolve_left h_nlt
      have h_sub : S_lt ⊆ Finset.Iio b := fun c hc =>
        Finset.mem_Iio.mpr (hu_strict.lt_iff_lt.mp (lt_trans (Finset.mem_filter.mp hc).2 hgt))
      have h_card := Finset.card_le_card h_sub
      rw [Fin.card_Iio] at h_card
      omega
  let m_comb : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 i₀.succ * L.mate
  have hm_zero : m_comb 0 = 0 := by
    change (Equiv.swap 0 i₀.succ) (L.mate 0) = 0
    rw [← hi₀_succ, Equiv.swap_apply_right]
  have hm_lift : liftTailPerm (Equiv.Perm.decomposeFin m_comb).2 = m_comb :=
    liftTailPerm_decomposeFin_snd hm_zero
  let L' : PartialPairing j (r + 1) :=
    { unpaired := a₀.insertNth i₀ u_tail
      strictMono_unpaired := fun x y hxy => by
        by_cases hx : x = a₀
        · subst hx
          have hy_ne : y ≠ a₀ := ne_of_gt hxy
          rcases Fin.exists_succAbove_eq hy_ne with ⟨b, rfl⟩
          rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
          have h_nlt : ¬ (b : ℕ) < (a₀ : ℕ) := by
            have h_sa : a₀ < a₀.succAbove b := hxy
            rcases lt_or_ge (Fin.castSucc b) a₀ with hcb | hcb
            · rw [Fin.succAbove_of_castSucc_lt a₀ b hcb] at h_sa
              exact False.elim (lt_asymm hcb h_sa)
            · exact not_lt.mpr (Fin.le_iff_val_le_val.mp hcb)
          exact (lt_or_gt_of_ne (hu_ne_i₀ b)).resolve_left
            (fun hc => h_nlt ((h_lt_iff b).mp hc))
        · rcases Fin.exists_succAbove_eq hx with ⟨b₁, rfl⟩
          by_cases hy : y = a₀
          · subst hy
            rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
            have h_cb : Fin.castSucc b₁ < a₀ := by
              rcases lt_or_ge (Fin.castSucc b₁) a₀ with hcb | hcb
              · exact hcb
              · rw [Fin.succAbove_of_le_castSucc a₀ b₁ hcb] at hxy
                exact False.elim (not_lt_of_ge
                  (le_trans hcb (Fin.castSucc_lt_succ (i := b₁)).le) hxy)
            exact (h_lt_iff b₁).mpr h_cb
          · rcases Fin.exists_succAbove_eq hy with ⟨b₂, rfl⟩
            rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
            exact hu_strict (Fin.succAbove_lt_succAbove_iff.mp hxy)
      mate := (Equiv.Perm.decomposeFin m_comb).2
      involutive := fun i => by
        have h_app : ∀ k : Fin j,
            ((Equiv.Perm.decomposeFin m_comb).2 k).succ = m_comb k.succ := fun k =>
          (liftTailPerm_succ _ k).symm.trans (congrArg (fun p => p k.succ) hm_lift)
        have hm_inv : ∀ u : Fin (j + 1), m_comb (m_comb u) = u := by
          intro u
          by_cases hu0 : u = 0
          · subst hu0; rw [hm_zero, hm_zero]
          · by_cases hui : u = i₀.succ
            · subst hui
              have hmi : m_comb i₀.succ = i₀.succ := by
                change (Equiv.swap 0 i₀.succ) (L.mate i₀.succ) = i₀.succ
                rw [hi₀_succ, L.mate_mate, Equiv.swap_apply_left]
              rw [hmi, hmi]
            · have hlu_ne0 : L.mate u ≠ 0 := fun hc =>
                hui (by rw [← L.mate_mate u, hc, ← hi₀_succ])
              have hlu_nei : L.mate u ≠ i₀.succ := fun hc =>
                hu0 (by rw [← L.mate_mate u, hc, hi₀_succ, L.mate_mate])
              have hmu : m_comb u = L.mate u := by
                change (Equiv.swap 0 i₀.succ) (L.mate u) = L.mate u
                exact Equiv.swap_apply_of_ne_of_ne hlu_ne0 hlu_nei
              rw [hmu]
              change (Equiv.swap 0 i₀.succ) (L.mate (L.mate u)) = u
              rw [L.mate_mate, Equiv.swap_apply_of_ne_of_ne hu0 hui]
        exact Fin.succ_inj.mp ((h_app _).trans ((congrArg m_comb (h_app i)).trans (hm_inv i.succ)))
      fixed_iff := fun i => by
        have h_app : ((Equiv.Perm.decomposeFin m_comb).2 i).succ = m_comb i.succ :=
          (liftTailPerm_succ _ i).symm.trans (congrArg (fun p => p i.succ) hm_lift)
        rw [← Fin.succ_inj, h_app]
        by_cases hi : i = i₀
        · subst hi
          have hmi : m_comb i₀.succ = i₀.succ := by
            change (Equiv.swap 0 i₀.succ) (L.mate i₀.succ) = i₀.succ
            rw [hi₀_succ, L.mate_mate, Equiv.swap_apply_left]
          simp only [hmi, true_iff]
          exact ⟨a₀, by simp⟩
        · have hli_ne0 : L.mate i.succ ≠ 0 := fun hc =>
            hi (Fin.succ_inj.mp (by rw [← L.mate_mate i.succ, hc, ← hi₀_succ]))
          have hli_nei : L.mate i.succ ≠ i₀.succ := fun hc =>
            Fin.succ_ne_zero i (by rw [← L.mate_mate i.succ, hc, hi₀_succ, L.mate_mate])
          have hmi : m_comb i.succ = L.mate i.succ := by
            change (Equiv.swap 0 i₀.succ) (L.mate i.succ) = L.mate i.succ
            exact Equiv.swap_apply_of_ne_of_ne hli_ne0 hli_nei
          rw [hmi, L.fixed_iff]
          constructor
          · rintro ⟨b, hb⟩
            refine ⟨a₀.succAbove b, ?_⟩
            rw [Fin.insertNth_apply_succAbove]
            dsimp [u_tail]
            exact Fin.succ_inj.mp ((Fin.succ_pred _ _).trans hb)
          · rintro ⟨a, ha⟩
            have ha_ne : a ≠ a₀ := fun hc => by
              rw [hc, Fin.insertNth_apply_same] at ha
              exact hi ha.symm
            rcases Fin.exists_succAbove_eq ha_ne with ⟨b, rfl⟩
            rw [Fin.insertNth_apply_succAbove] at ha
            exact ⟨b, (Fin.succ_pred _ _).symm.trans (congrArg Fin.succ ha)⟩ }
  (L', a₀)

end PartialPairing

namespace PartialPairing

lemma prependPaired_unprependPaired {j r : ℕ} (L : PartialPairing (j + 1) r)
    (h0 : L.mate 0 ≠ 0) :
    prependPaired (unprependPaired L h0).1 (unprependPaired L h0).2 = L := by
  let p := unprependPaired L h0
  let i₀ : Fin j := (L.mate 0).pred h0
  have hi₀_succ : i₀.succ = L.mate 0 := Fin.succ_pred (L.mate 0) h0
  have hp_unp : p.1.unpaired p.2 = i₀ := by
    dsimp [p, unprependPaired]
    exact Fin.insertNth_apply_same _ _ _
  let m_comb : Equiv.Perm (Fin (j + 1)) := Equiv.swap 0 i₀.succ * L.mate
  have hm_zero : m_comb 0 = 0 := by
    change (Equiv.swap 0 i₀.succ) (L.mate 0) = 0
    rw [← hi₀_succ, Equiv.swap_apply_right]
  have hm_lift : liftTailPerm (Equiv.Perm.decomposeFin m_comb).2 = m_comb :=
    liftTailPerm_decomposeFin_snd hm_zero
  refine ext_mate ?_
  dsimp [prependPaired]
  rw [hp_unp]
  change Equiv.swap 0 i₀.succ * liftTailPerm (Equiv.Perm.decomposeFin m_comb).2 = L.mate
  rw [hm_lift]
  apply Equiv.Perm.ext
  intro u
  change (Equiv.swap 0 i₀.succ) ((Equiv.swap 0 i₀.succ) (L.mate u)) = L.mate u
  exact Equiv.swap_apply_self _ _ _

lemma unprependPaired_prependPaired {j r : ℕ} (L' : PartialPairing j (r + 1))
    (a₀ : Fin (r + 1)) :
    unprependPaired (prependPaired L' a₀)
      (by rw [prependPaired_mate_zero]; exact Fin.succ_ne_zero _) = (L', a₀) := by
  let L := prependPaired L' a₀
  have h0 : L.mate 0 ≠ 0 := by
    dsimp [L]
    rw [prependPaired_mate_zero]
    exact Fin.succ_ne_zero _
  have h_rec := prependPaired_unprependPaired L h0
  let p := unprependPaired L h0
  have hL_eq : p.1 = L' := by
    refine ext_mate ?_
    apply Equiv.Perm.ext
    intro i
    have h_i₀ : (L.mate 0).pred h0 = L'.unpaired a₀ := by
      dsimp [L]
      simp [prependPaired_mate_zero]
    have hp_unp : p.1.unpaired p.2 = L'.unpaired a₀ := by
      dsimp [p, unprependPaired]
      rw [Fin.insertNth_apply_same, h_i₀]
    by_cases hi : i = L'.unpaired a₀
    · subst hi
      rw [← hp_unp, p.1.mate_unpaired, hp_unp, L'.mate_unpaired]
    · have hi_p : i ≠ p.1.unpaired p.2 := by rwa [hp_unp]
      have hm1 := prependPaired_mate_succ_of_ne p.1 p.2 hi_p
      have hm2 := prependPaired_mate_succ_of_ne L' a₀ hi
      have h_eq_m : (prependPaired p.1 p.2).mate i.succ = L.mate i.succ := by
        rw [h_rec]
      exact Fin.succ_inj.mp (hm1.symm.trans (h_eq_m.trans hm2))
  have ha_eq : p.2 = a₀ := by
    have h_i₀ : (L.mate 0).pred h0 = L'.unpaired a₀ := by
      dsimp [L]
      simp [prependPaired_mate_zero]
    have hp_unp : p.1.unpaired p.2 = L'.unpaired a₀ := by
      dsimp [p, unprependPaired]
      rw [Fin.insertNth_apply_same, h_i₀]
    rw [hL_eq] at hp_unp
    exact L'.unpaired_injective hp_unp
  exact Prod.ext hL_eq ha_eq

def partialPairingSuccZeroEquiv (j : ℕ) :
    (PartialPairing j 1 × Fin 1) ≃ PartialPairing (j + 1) 0 where
  toFun pa := prependPaired pa.1 pa.2
  invFun L := unprependPaired L (fun h0 => by
    rcases (L.fixed_iff 0).mp h0 with ⟨a, _⟩
    exact Fin.elim0 a)
  left_inv pa := unprependPaired_prependPaired pa.1 pa.2
  right_inv L := prependPaired_unprependPaired L _

def partialPairingSuccSuccEquiv (j r : ℕ) :
    PartialPairing j r ⊕ (PartialPairing j (r + 2) × Fin (r + 2)) ≃
      PartialPairing (j + 1) (r + 1) where
  toFun
    | Sum.inl L => prependUnpaired L
    | Sum.inr pa => prependPaired pa.1 pa.2
  invFun L :=
    if h0 : L.mate 0 = 0 then
      Sum.inl (unprependUnpaired L h0)
    else
      Sum.inr (unprependPaired L h0)
  left_inv x := by
    rcases x with L | ⟨L', a₀⟩
    · have h0 : (prependUnpaired L).mate 0 = 0 := by simp [prependUnpaired]
      dsimp only
      rw [dif_pos h0]
      refine congrArg Sum.inl (ext_mate ?_)
      dsimp [unprependUnpaired, prependUnpaired, liftTailPerm]
      rw [Equiv.apply_symm_apply]
    · have h0 : (prependPaired L' a₀).mate 0 ≠ 0 := by
        rw [prependPaired_mate_zero]
        exact Fin.succ_ne_zero _
      dsimp only
      rw [dif_neg h0, unprependPaired_prependPaired]
  right_inv L := by
    dsimp only
    split_ifs with h0
    · refine ext_mate ?_
      exact liftTailPerm_decomposeFin_snd h0
    · exact prependPaired_unprependPaired L h0

def prependPairedChordEquiv {j r : ℕ} (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1)) :
    Unit ⊕ L'.InternalChord ≃ (prependPaired L' a₀).InternalChord where
  toFun
    | Sum.inl () => ⟨0, by rw [prependPaired_mate_zero]; exact Fin.succ_pos _⟩
    | Sum.inr c =>
      have hc_ne : c.1 ≠ L'.unpaired a₀ := fun hc => by
        have hlt := c.2
        rw [hc, L'.mate_unpaired] at hlt
        exact lt_irrefl _ hlt
      ⟨c.1.succ, by
        rw [prependPaired_mate_succ_of_ne L' a₀ hc_ne]
        exact Fin.succ_lt_succ_iff.mpr c.2⟩
  invFun u :=
    if hu0 : u.1 = 0 then
      Sum.inl ()
    else
      Sum.inr ⟨u.1.pred hu0, by
        have hlt := u.2
        have hsu : (u.1.pred hu0).succ = u.1 := Fin.succ_pred u.1 hu0
        have hne : u.1.pred hu0 ≠ L'.unpaired a₀ := fun hc => by
          rw [← hsu, hc, prependPaired_mate_unpaired_succ] at hlt
          exact Nat.not_lt_zero _ hlt
        rw [← hsu, prependPaired_mate_succ_of_ne L' a₀ hne] at hlt
        exact Fin.succ_lt_succ_iff.mp hlt⟩
  left_inv x := by
    rcases x with ⟨⟩ | c
    · simp
    · simp only [Fin.succ_ne_zero, ↓reduceDIte]
      exact congrArg Sum.inr (Subtype.ext (by simp))
  right_inv u := by
    by_cases hu0 : u.1 = 0
    · simp only [hu0, ↓reduceDIte]
      apply Subtype.ext
      exact hu0.symm
    · simp only [hu0, ↓reduceDIte]
      apply Subtype.ext
      exact Fin.succ_pred u.1 hu0

end PartialPairing

namespace PartialPairing

lemma partialCross_prependPaired {j r : ℕ} (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1)) :
    (prependPaired L' a₀).partialCross = L'.partialCross + (a₀ : ℕ) := by
  let i₀ := L'.unpaired a₀
  let C_cross : Finset (Fin j) := Finset.univ.filter (fun c : Fin j => c < i₀ ∧ i₀ < L'.mate c)
  let C_rest : Finset (Fin j × Fin r) := Finset.univ.filter (fun cb : Fin j × Fin r =>
    cb.1 < L'.unpaired (a₀.succAbove cb.2) ∧ L'.unpaired (a₀.succAbove cb.2) < L'.mate cb.1)
  have h_int : (prependPaired L' a₀).internalCross = C_cross.card + L'.internalCross := by
    let S_int := Finset.univ.filter (fun uv : Fin (j + 1) × Fin (j + 1) =>
      uv.1 < uv.2 ∧ uv.2 < (prependPaired L' a₀).mate uv.1 ∧
        (prependPaired L' a₀).mate uv.1 < (prependPaired L' a₀).mate uv.2)
    have h_card_split := (Finset.card_filter_add_card_filter_not
      (s := S_int) (p := fun uv : Fin (j + 1) × Fin (j + 1) => uv.1 = 0)).symm
    have h1 : (S_int.filter (fun uv => uv.1 = 0)).card = C_cross.card := by
      refine Finset.card_bij
        (fun uv huv =>
          have hv0 : uv.2 ≠ 0 := by
            rcases Finset.mem_filter.mp (Finset.mem_filter.mp huv).1 with ⟨_, hlt, _, _⟩
            exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hlt)
          uv.2.pred hv0)
        (fun uv huv => ?_)
        (fun a ha b hb hab => ?_)
        (fun c hc => ⟨(0, c.succ), ?_, by simp⟩)
      · rcases Finset.mem_filter.mp huv with ⟨hS, hu0⟩
        rcases Finset.mem_filter.mp hS with ⟨_, hlt1, hlt2, hlt3⟩
        have hv0 : uv.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hlt1)
        have hsv : (uv.2.pred hv0).succ = uv.2 := Fin.succ_pred uv.2 hv0
        rw [hu0, prependPaired_mate_zero, ← hsv] at hlt2 hlt3
        have hc_lt : uv.2.pred hv0 < i₀ := Fin.succ_lt_succ_iff.mp hlt2
        have hc_ne : uv.2.pred hv0 ≠ i₀ := ne_of_lt hc_lt
        rw [prependPaired_mate_succ_of_ne L' a₀ hc_ne] at hlt3
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_lt, Fin.succ_lt_succ_iff.mp hlt3⟩
      · have ha0 : a.1 = 0 := (Finset.mem_filter.mp ha).2
        have hb0 : b.1 = 0 := (Finset.mem_filter.mp hb).2
        ext1
        · exact ha0.trans hb0.symm
        · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ hab)
      · rcases Finset.mem_filter.mp hc with ⟨_, hc1, hc2⟩
        have hc_ne : c ≠ i₀ := ne_of_lt hc1
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.succ_pos c, ?_, ?_⟩, rfl⟩
        · rw [prependPaired_mate_zero]
          exact Fin.succ_lt_succ_iff.mpr hc1
        · rw [prependPaired_mate_zero, prependPaired_mate_succ_of_ne L' a₀ hc_ne]
          exact Fin.succ_lt_succ_iff.mpr hc2
    have h2 : (S_int.filter (fun uv => ¬ uv.1 = 0)).card = L'.internalCross := by
      dsimp [internalCross]
      refine Finset.card_bij
        (fun uv huv =>
          have hu0 : uv.1 ≠ 0 := (Finset.mem_filter.mp huv).2
          have hv0 : uv.2 ≠ 0 := by
            rcases Finset.mem_filter.mp (Finset.mem_filter.mp huv).1 with ⟨_, hlt, _, _⟩
            exact ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hlt)
          (uv.1.pred hu0, uv.2.pred hv0))
        (fun uv huv => ?_)
        (fun a ha b hb hab => ?_)
        (fun pq hpq => ⟨(pq.1.succ, pq.2.succ), ?_, by ext <;> simp⟩)
      · rcases Finset.mem_filter.mp huv with ⟨hS, hu0⟩
        rcases Finset.mem_filter.mp hS with ⟨_, hlt1, hlt2, hlt3⟩
        have hv0 : uv.2 ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) hlt1)
        have hsu : (uv.1.pred hu0).succ = uv.1 := Fin.succ_pred uv.1 hu0
        have hsv : (uv.2.pred hv0).succ = uv.2 := Fin.succ_pred uv.2 hv0
        rw [← hsu, ← hsv] at hlt1 hlt2 hlt3
        have hu_ne_i₀ : uv.1.pred hu0 ≠ i₀ := fun hc => by
          rw [hc, prependPaired_mate_unpaired_succ] at hlt2
          exact Nat.not_lt_zero _ hlt2
        have hv_ne_i₀ : uv.2.pred hv0 ≠ i₀ := fun hc => by
          rw [hc, prependPaired_mate_unpaired_succ] at hlt3
          exact Nat.not_lt_zero _ hlt3
        rw [prependPaired_mate_succ_of_ne L' a₀ hu_ne_i₀] at hlt2 hlt3
        rw [prependPaired_mate_succ_of_ne L' a₀ hv_ne_i₀] at hlt3
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.succ_lt_succ_iff.mp hlt1, Fin.succ_lt_succ_iff.mp hlt2,
          Fin.succ_lt_succ_iff.mp hlt3⟩
      · have h1' := (Prod.mk.inj hab).1
        have h2' := (Prod.mk.inj hab).2
        ext1
        · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ h1')
        · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ h2')
      · rcases Finset.mem_filter.mp hpq with ⟨_, hlt1, hlt2, hlt3⟩
        have hp_ne : pq.1 ≠ i₀ := fun hc => by
          rw [hc] at hlt1 hlt2
          rw [L'.mate_unpaired] at hlt2
          exact lt_asymm hlt1 hlt2
        have hq_ne : pq.2 ≠ i₀ := fun hc => by
          rw [hc] at hlt2 hlt3
          rw [L'.mate_unpaired] at hlt3
          exact lt_asymm hlt2 hlt3
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.succ_lt_succ_iff.mpr hlt1, ?_, ?_⟩, Fin.succ_ne_zero _⟩
        · rw [prependPaired_mate_succ_of_ne L' a₀ hp_ne]
          exact Fin.succ_lt_succ_iff.mpr hlt2
        · rw [prependPaired_mate_succ_of_ne L' a₀ hp_ne,
              prependPaired_mate_succ_of_ne L' a₀ hq_ne]
          exact Fin.succ_lt_succ_iff.mpr hlt3
    change S_int.card = _
    rw [h_card_split, h1, h2]
  have h_open : (prependPaired L' a₀).openCross = (a₀ : ℕ) + C_rest.card := by
    let S_open := Finset.univ.filter (fun ub : Fin (j + 1) × Fin r =>
      ub.1 < (prependPaired L' a₀).unpaired ub.2 ∧
        (prependPaired L' a₀).unpaired ub.2 < (prependPaired L' a₀).mate ub.1)
    have h_card_split := (Finset.card_filter_add_card_filter_not
      (s := S_open) (p := fun ub : Fin (j + 1) × Fin r => ub.1 = 0)).symm
    have h1 : (S_open.filter (fun ub => ub.1 = 0)).card = (a₀ : ℕ) := by
      have ha₀_le : (a₀ : ℕ) ≤ r := Nat.le_of_lt_succ a₀.isLt
      refine (Finset.card_bij (t := (Finset.univ : Finset (Fin (a₀ : ℕ))))
        (fun ub hub => ⟨(ub.2 : ℕ), ?_⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun a ha b hb hab => ?_)
        (fun k _ => ⟨(0, ⟨k.val, lt_of_lt_of_le k.isLt ha₀_le⟩), ?_, by ext; rfl⟩)).trans
        (Finset.card_fin (a₀ : ℕ))
      · rcases Finset.mem_filter.mp hub with ⟨hS, hu0⟩
        rcases Finset.mem_filter.mp hS with ⟨_, _, hlt2⟩
        rw [hu0, prependPaired_mate_zero] at hlt2
        have h_sa : a₀.succAbove ub.2 < a₀ :=
          L'.strictMono_unpaired.lt_iff_lt.mp (Fin.succ_lt_succ_iff.mp hlt2)
        rcases lt_or_ge (Fin.castSucc ub.2) a₀ with hcb | hcb
        · exact hcb
        · rw [Fin.succAbove_of_le_castSucc a₀ ub.2 hcb] at h_sa
          exact False.elim (not_lt_of_ge
            (le_trans hcb (Fin.castSucc_lt_succ (i := ub.2)).le) h_sa)
      · have ha0 : a.1 = 0 := (Finset.mem_filter.mp ha).2
        have hb0 : b.1 = 0 := (Finset.mem_filter.mp hb).2
        ext1
        · exact ha0.trans hb0.symm
        · exact Fin.ext (Fin.mk.inj hab)
      · let b_k : Fin r := ⟨k.val, lt_of_lt_of_le k.isLt ha₀_le⟩
        have hcb : Fin.castSucc b_k < a₀ := k.isLt
        have h_sa : a₀.succAbove b_k < a₀ := by
          rw [Fin.succAbove_of_castSucc_lt a₀ b_k hcb]
          exact hcb
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.succ_pos _, ?_⟩, rfl⟩
        rw [prependPaired_mate_zero]
        exact Fin.succ_lt_succ_iff.mpr (L'.strictMono_unpaired h_sa)
    have h2 : (S_open.filter (fun ub => ¬ ub.1 = 0)).card = C_rest.card := by
      refine Finset.card_bij
        (fun ub hub => (ub.1.pred (Finset.mem_filter.mp hub).2, ub.2))
        (fun ub hub => ?_)
        (fun a ha b hb hab => ?_)
        (fun cb hcb => ⟨(cb.1.succ, cb.2), ?_, by ext <;> simp⟩)
      · rcases Finset.mem_filter.mp hub with ⟨hS, hu0⟩
        rcases Finset.mem_filter.mp hS with ⟨_, hlt1, hlt2⟩
        have hsu : (ub.1.pred hu0).succ = ub.1 := Fin.succ_pred ub.1 hu0
        rw [← hsu] at hlt1 hlt2
        have hc_ne : ub.1.pred hu0 ≠ i₀ := fun hc => by
          rw [hc, prependPaired_mate_unpaired_succ] at hlt2
          exact Nat.not_lt_zero _ hlt2
        rw [prependPaired_mate_succ_of_ne L' a₀ hc_ne] at hlt2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.succ_lt_succ_iff.mp hlt1, Fin.succ_lt_succ_iff.mp hlt2⟩
      · ext1
        · exact Fin.succ_inj.mp (by simpa using congrArg Fin.succ (Prod.mk.inj hab).1)
        · exact (Prod.mk.inj hab).2
      · rcases Finset.mem_filter.mp hcb with ⟨_, hlt1, hlt2⟩
        have hc_ne : cb.1 ≠ i₀ := fun hc => by
          rw [hc] at hlt1 hlt2
          rw [L'.mate_unpaired] at hlt2
          exact lt_asymm hlt1 hlt2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Fin.succ_lt_succ_iff.mpr hlt1, ?_⟩, Fin.succ_ne_zero _⟩
        rw [prependPaired_mate_succ_of_ne L' a₀ hc_ne]
        exact Fin.succ_lt_succ_iff.mpr hlt2
    change S_open.card = _
    rw [h_card_split, h1, h2]
  have h_open_L' : L'.openCross = C_cross.card + C_rest.card := by
    let S_L' := Finset.univ.filter (fun ca : Fin j × Fin (r + 1) =>
      ca.1 < L'.unpaired ca.2 ∧ L'.unpaired ca.2 < L'.mate ca.1)
    have h_card_split := (Finset.card_filter_add_card_filter_not
      (s := S_L') (p := fun ca : Fin j × Fin (r + 1) => ca.2 = a₀)).symm
    have h1 : (S_L'.filter (fun ca => ca.2 = a₀)).card = C_cross.card := by
      refine Finset.card_bij
        (fun ca _ => ca.1)
        (fun ca hca => ?_)
        (fun a ha b hb hab => ?_)
        (fun c hc => ⟨(c, a₀), ?_, rfl⟩)
      · rcases Finset.mem_filter.mp hca with ⟨hS, ha_eq⟩
        rcases Finset.mem_filter.mp hS with ⟨_, hlt1, hlt2⟩
        rw [ha_eq] at hlt1 hlt2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt1, hlt2⟩
      · exact Prod.ext hab ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      · rcases Finset.mem_filter.mp hc with ⟨_, hc1, hc2⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc1, hc2⟩, rfl⟩
    have h2 : (S_L'.filter (fun ca => ¬ ca.2 = a₀)).card = C_rest.card := by
      refine Finset.card_bij
        (fun ca hca =>
          have hne : ca.2 ≠ a₀ := (Finset.mem_filter.mp hca).2
          (ca.1, (Fin.exists_succAbove_eq hne).choose))
        (fun ca hca => ?_)
        (fun a ha b hb hab => ?_)
        (fun cb hcb => ⟨(cb.1, a₀.succAbove cb.2), ?_, ?_⟩)
      · rcases Finset.mem_filter.mp hca with ⟨hS, hne⟩
        rcases Finset.mem_filter.mp hS with ⟨_, hlt1, hlt2⟩
        have hb_spec := (Fin.exists_succAbove_eq hne).choose_spec
        rw [← hb_spec] at hlt1 hlt2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt1, hlt2⟩
      · have h1' := (Prod.mk.inj hab).1
        have h2' := (Prod.mk.inj hab).2
        have ha_spec := (Fin.exists_succAbove_eq (Finset.mem_filter.mp ha).2).choose_spec
        have hb_spec := (Fin.exists_succAbove_eq (Finset.mem_filter.mp hb).2).choose_spec
        exact Prod.ext h1' (ha_spec.symm.trans ((congrArg a₀.succAbove h2').trans hb_spec))
      · rcases Finset.mem_filter.mp hcb with ⟨_, hlt1, hlt2⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt1, hlt2⟩, Fin.succAbove_ne a₀ cb.2⟩
      · ext1
        · rfl
        · dsimp only
          exact Fin.succAbove_right_injective
            (Fin.exists_succAbove_eq (Fin.succAbove_ne a₀ cb.2)).choose_spec
    change S_L'.card = _
    rw [h_card_split, h1, h2]
  dsimp [partialCross]
  omega

end PartialPairing

namespace PartialPairing

lemma isEmpty_of_lt {j r : ℕ} (h : j < r) : IsEmpty (PartialPairing j r) :=
  ⟨fun L => by
    have hcard := Fintype.card_le_of_injective L.unpaired L.unpaired_injective
    simp only [Fintype.card_fin] at hcard
    omega⟩

def prependUnpairedParamEquiv {j r : ℕ} (L : PartialPairing j r) :
    (L.InternalChord → Fin 3 → ℝ) ≃ᵐ ((prependUnpaired L).InternalChord → Fin 3 → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : (prependUnpaired L).InternalChord => Fin 3 → ℝ)
    (prependUnpairedChordEquiv L)

lemma measurePreserving_prependUnpairedParamEquiv {j r : ℕ} (L : PartialPairing j r) :
    MeasurePreserving (prependUnpairedParamEquiv L) volume volume :=
  volume_measurePreserving_piCongrLeft
    (fun _ : (prependUnpaired L).InternalChord => Fin 3 → ℝ)
    (prependUnpairedChordEquiv L)

@[simp]
lemma prependUnpairedParamEquiv_apply {j r : ℕ} (L : PartialPairing j r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (c : L.InternalChord) :
    prependUnpairedParamEquiv L p_int (prependUnpairedChordEquiv L c) = p_int c := by
  unfold prependUnpairedParamEquiv
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]

def prependPairedParamEquiv {j r : ℕ} (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1)) :
    ((Fin 3 → ℝ) × (L'.InternalChord → Fin 3 → ℝ)) ≃ᵐ
      ((prependPaired L' a₀).InternalChord → Fin 3 → ℝ) :=
  (((MeasurableEquiv.funUnique Unit (Fin 3 → ℝ)).symm.prodCongr
      (MeasurableEquiv.refl (L'.InternalChord → Fin 3 → ℝ))).trans
    (MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Unit ⊕ L'.InternalChord => Fin 3 → ℝ)).symm).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : (prependPaired L' a₀).InternalChord => Fin 3 → ℝ)
      (prependPairedChordEquiv L' a₀))

lemma measurePreserving_prependPairedParamEquiv {j r : ℕ}
    (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1)) :
    MeasurePreserving (prependPairedParamEquiv L' a₀) volume volume := by
  unfold prependPairedParamEquiv
  exact (((volume_preserving_funUnique Unit (Fin 3 → ℝ)).symm.prod
      (MeasurePreserving.id volume)).trans
    (volume_measurePreserving_sumPiEquivProdPi_symm
      (fun _ : Unit ⊕ L'.InternalChord => Fin 3 → ℝ))).trans
    (volume_measurePreserving_piCongrLeft
      (fun _ : (prependPaired L' a₀).InternalChord => Fin 3 → ℝ)
      (prependPairedChordEquiv L' a₀))

@[simp]
lemma prependPairedParamEquiv_apply_inl {j r : ℕ}
    (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1))
    (q₀ : Fin 3 → ℝ) (p_int : L'.InternalChord → Fin 3 → ℝ) :
    prependPairedParamEquiv L' a₀ (q₀, p_int)
      (prependPairedChordEquiv L' a₀ (Sum.inl ())) = q₀ := by
  unfold prependPairedParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

@[simp]
lemma prependPairedParamEquiv_apply_inr {j r : ℕ}
    (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1))
    (q₀ : Fin 3 → ℝ) (p_int : L'.InternalChord → Fin 3 → ℝ) (c : L'.InternalChord) :
    prependPairedParamEquiv L' a₀ (q₀, p_int)
      (prependPairedChordEquiv L' a₀ (Sum.inr c)) = p_int c := by
  unfold prependPairedParamEquiv
  simp only [MeasurableEquiv.trans_apply, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  rfl

lemma partialMomentum_prependUnpaired {j r : ℕ} (m : ℝ) (L : PartialPairing j r)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k' : Fin (r + 1) → Fin 3 → ℝ) :
    (prependUnpaired L).partialMomentum m (prependUnpairedParamEquiv L p_int) k' =
      Fin.cons (-massShellVec m (k' 0)) (L.partialMomentum m p_int (k' ∘ Fin.succ)) := by
  ext u μ
  refine Fin.cases ?_ (fun i => ?_) u
  · rw [Fin.cons_zero]
    have h0 : (0 : Fin (j + 1)) = (prependUnpaired L).unpaired 0 := rfl
    rw [h0, (prependUnpaired L).partialMomentum_unpaired]
  · let s := L.partialSlotEquiv.symm i
    have hi : i = L.partialSlotEquiv s := (L.partialSlotEquiv.apply_symm_apply i).symm
    rw [hi, Fin.cons_succ]
    rcases s with b | ⟨c, idx⟩
    · have hs1 : L.partialSlotEquiv (Sum.inl b) = L.unpaired b := rfl
      have hs2 : (L.unpaired b).succ = (prependUnpaired L).unpaired b.succ := rfl
      rw [hs1, hs2, (prependUnpaired L).partialMomentum_unpaired, L.partialMomentum_unpaired]
      rfl
    · refine Fin.cases ?_ (fun j0 => ?_) idx
      · have hs1 : L.partialSlotEquiv (Sum.inr (c, 0)) = c.1 := rfl
        have hs2 : c.1.succ = (prependUnpairedChordEquiv L c).1 := rfl
        rw [hs1, hs2, (prependUnpaired L).partialMomentum_fst,
            prependUnpairedParamEquiv_apply, L.partialMomentum_fst]
      · have hj0 : j0 = 0 := Subsingleton.elim j0 0
        subst hj0
        have hs1 : L.partialSlotEquiv (Sum.inr (c, (0 : Fin 1).succ)) = L.mate c.1 := rfl
        have hs2 : (L.mate c.1).succ =
            (prependUnpaired L).mate (prependUnpairedChordEquiv L c).1 := rfl
        rw [hs1, hs2, (prependUnpaired L).partialMomentum_mate,
            prependUnpairedParamEquiv_apply, L.partialMomentum_mate]

lemma partialMomentum_prependPaired {j r : ℕ} (m : ℝ) (L' : PartialPairing j (r + 1))
    (a₀ : Fin (r + 1)) (q₀ : Fin 3 → ℝ) (p_int : L'.InternalChord → Fin 3 → ℝ)
    (k_ext : Fin r → Fin 3 → ℝ) :
    (prependPaired L' a₀).partialMomentum m
        (prependPairedParamEquiv L' a₀ (q₀, p_int)) k_ext =
      Fin.cons (massShellVec m q₀)
        (L'.partialMomentum m p_int (a₀.insertNth q₀ k_ext)) := by
  ext u μ
  refine Fin.cases ?_ (fun i => ?_) u
  · rw [Fin.cons_zero]
    have h0 : (0 : Fin (j + 1)) = (prependPairedChordEquiv L' a₀ (Sum.inl ())).1 := rfl
    rw [h0, (prependPaired L' a₀).partialMomentum_fst, prependPairedParamEquiv_apply_inl]
  · let s := L'.partialSlotEquiv.symm i
    have hi : i = L'.partialSlotEquiv s := (L'.partialSlotEquiv.apply_symm_apply i).symm
    rw [hi, Fin.cons_succ]
    rcases s with a | ⟨c, idx⟩
    · have hs1 : L'.partialSlotEquiv (Sum.inl a) = L'.unpaired a := rfl
      rw [hs1]
      by_cases ha : a = a₀
      · subst ha
        have hs2 : (L'.unpaired a).succ =
            (prependPaired L' a).mate (prependPairedChordEquiv L' a (Sum.inl ())).1 := by
          change _ = (prependPaired L' a).mate 0
          exact (prependPaired_mate_zero L' a).symm
        rw [hs2, (prependPaired L' a).partialMomentum_mate, prependPairedParamEquiv_apply_inl,
            L'.partialMomentum_unpaired, Fin.insertNth_apply_same]
      · rcases Fin.exists_succAbove_eq ha with ⟨b, rfl⟩
        have hs2 : (L'.unpaired (a₀.succAbove b)).succ = (prependPaired L' a₀).unpaired b := rfl
        rw [hs2, (prependPaired L' a₀).partialMomentum_unpaired, L'.partialMomentum_unpaired,
            Fin.insertNth_apply_succAbove]
    · refine Fin.cases ?_ (fun j0 => ?_) idx
      · have hs1 : L'.partialSlotEquiv (Sum.inr (c, 0)) = c.1 := rfl
        have hs2 : c.1.succ = (prependPairedChordEquiv L' a₀ (Sum.inr c)).1 := rfl
        rw [hs1, hs2, (prependPaired L' a₀).partialMomentum_fst,
            prependPairedParamEquiv_apply_inr, L'.partialMomentum_fst]
      · have hj0 : j0 = 0 := Subsingleton.elim j0 0
        subst hj0
        have hs1 : L'.partialSlotEquiv (Sum.inr (c, (0 : Fin 1).succ)) = L'.mate c.1 := rfl
        have hc_ne : c.1 ≠ L'.unpaired a₀ := fun hc => by
          have hlt := c.2
          rw [hc, L'.mate_unpaired] at hlt
          exact lt_irrefl _ hlt
        have hs2 : (L'.mate c.1).succ =
            (prependPaired L' a₀).mate (prependPairedChordEquiv L' a₀ (Sum.inr c)).1 :=
          (prependPaired_mate_succ_of_ne L' a₀ hc_ne).symm
        rw [hs1, hs2, (prependPaired L' a₀).partialMomentum_mate,
            prependPairedParamEquiv_apply_inr, L'.partialMomentum_mate]

end PartialPairing

noncomputable def conjMode {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    (s : Fin M_mode.ν) (p : Fin 3 → ℝ) (α₀ : ι) : ℂ :=
  ∑ c : ι, star (S.C α₀ c) * star (M_mode.w s p c)

lemma measurable_conjMode {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    (s : Fin M_mode.ν) (α₀ : ι) :
    Measurable (fun p : Fin 3 → ℝ => conjMode M_mode s p α₀) :=
  Finset.measurable_sum Finset.univ fun c _ =>
    measurable_const.mul (continuous_star.measurable.comp (M_mode.measurable_w s c))

lemma norm_conjMode_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    (s : Fin M_mode.ν) (p : Fin 3 → ℝ) (α₀ : ι) :
    ‖conjMode M_mode s p α₀‖ ≤ (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M := by
  unfold conjMode
  calc ‖∑ c : ι, star (S.C α₀ c) * star (M_mode.w s p c)‖
      ≤ ∑ c : ι, ‖star (S.C α₀ c) * star (M_mode.w s p c)‖ := norm_sum_le _ _
    _ ≤ ∑ c : ι, ‖S.C α₀ c‖ * M_mode.M := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul, norm_star, norm_star]
        exact mul_le_mul_of_nonneg_left (M_mode.norm_w_le s p c) (norm_nonneg _)
    _ = (∑ c : ι, ‖S.C α₀ c‖) * M_mode.M := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ α₀))
          M_mode.hM

lemma massShellWeight_eq_sum_conjMode_mul_w {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    (p : Fin 3 → ℝ) (α₀ β : ι) :
    massShellWeight m C ![α₀, β] p =
      ∑ s : Fin M_mode.ν, conjMode M_mode s p α₀ * M_mode.w s p β := by
  unfold conjMode
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have h_inner : ∀ c : ι,
      (∑ s : Fin M_mode.ν, star (S.C α₀ c) * star (M_mode.w s p c) * M_mode.w s p β) =
      star (S.C α₀ c) * ∑ δ : ι, S.C c δ * massShellWeight m C ![δ, β] p := by
    intro c
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← M_mode.factor_weight p c β]
  simp_rw [h_inner, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  have h_orth : ∀ δ : ι,
      (∑ c : ι, star (S.C α₀ c) * S.C c δ) = if α₀ = δ then 1 else 0 := by
    intro δ
    have hm : (∑ c : ι, star (S.C α₀ c) * S.C c δ) = (S.C.map star * S.C) α₀ δ := by
      simp [Matrix.mul_apply]
    rw [hm, starStructure_map_star_mul_self S]
    rfl
  have h_term : ∀ δ : ι,
      (∑ c : ι, star (S.C α₀ c) * S.C c δ * massShellWeight m C ![δ, β] p) =
      (if α₀ = δ then 1 else 0) * massShellWeight m C ![δ, β] p := by
    intro δ
    rw [← Finset.sum_mul, h_orth]
  simp_rw [h_term, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ α₀, if_pos (Finset.mem_univ α₀)]

lemma fockPartialIntWeight_prependUnpaired {ι : Type*} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) {j r : ℕ} (α₀ : ι) (α : Fin j → ι)
    (L : PartialPairing j r) (p_int : L.InternalChord → Fin 3 → ℝ) :
    fockPartialIntWeight m C (Fin.cons α₀ α) (PartialPairing.prependUnpaired L)
        (PartialPairing.prependUnpairedParamEquiv L p_int) =
      fockPartialIntWeight m C α L p_int := by
  unfold fockPartialIntWeight
  rw [← Equiv.prod_comp (PartialPairing.prependUnpairedChordEquiv L)]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [PartialPairing.prependUnpairedParamEquiv_apply]
  have h1 : (PartialPairing.prependUnpairedChordEquiv L c).1 = c.1.succ := rfl
  have h2 : (PartialPairing.prependUnpaired L).mate c.1.succ = (L.mate c.1).succ := rfl
  rw [h1, h2]
  rfl

lemma fockPartialIntWeight_prependPaired {ι : Type*} (m : ℝ)
    (C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) {j r : ℕ} (α₀ : ι) (α : Fin j → ι)
    (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1))
    (q₀ : Fin 3 → ℝ) (p_int : L'.InternalChord → Fin 3 → ℝ) :
    fockPartialIntWeight m C (Fin.cons α₀ α) (PartialPairing.prependPaired L' a₀)
        (PartialPairing.prependPairedParamEquiv L' a₀ (q₀, p_int)) =
      massShellWeight m C ![α₀, α (L'.unpaired a₀)] q₀ *
        fockPartialIntWeight m C α L' p_int := by
  unfold fockPartialIntWeight
  rw [← Equiv.prod_comp (PartialPairing.prependPairedChordEquiv L' a₀),
      Fintype.prod_sum_type, Fintype.prod_unique]
  have hu : (default : Unit) = () := rfl
  rw [hu]
  refine congr_arg₂ (· * ·) ?_ ?_
  · rw [PartialPairing.prependPairedParamEquiv_apply_inl]
    have h1 : (PartialPairing.prependPairedChordEquiv L' a₀ (Sum.inl ())).1 = 0 := rfl
    have h2 : (PartialPairing.prependPaired L' a₀).mate
        (PartialPairing.prependPairedChordEquiv L' a₀ (Sum.inl ())).1 =
        (L'.unpaired a₀).succ :=
      PartialPairing.prependPaired_mate_zero L' a₀
    rw [h1] at h2 ⊢
    rw [h2]
    rfl
  · refine Finset.prod_congr rfl fun c _ => ?_
    rw [PartialPairing.prependPairedParamEquiv_apply_inr]
    have hc_ne : c.1 ≠ L'.unpaired a₀ := fun hc => by
      have hlt := c.2
      rw [hc, L'.mate_unpaired] at hlt
      exact lt_irrefl _ hlt
    have h1 : (PartialPairing.prependPairedChordEquiv L' a₀ (Sum.inr c)).1 = c.1.succ := rfl
    have h2 : (PartialPairing.prependPaired L' a₀).mate
        (PartialPairing.prependPairedChordEquiv L' a₀ (Sum.inr c)).1 =
        (L'.mate c.1).succ :=
      PartialPairing.prependPaired_mate_succ_of_ne L' a₀ hc_ne
    rw [h1] at h2 ⊢
    rw [h2]
    rfl

lemma euclidLaplace_cons_timeVec_partialMomentum {j r_t : ℕ} (m ε : ℝ)
    (y : Fin j → Fin 4 → ℝ) (p₀ : Fin 4 → ℝ) (L : PartialPairing j r_t)
    (p_int : L.InternalChord → Fin 3 → ℝ) (k_tail : Fin r_t → Fin 3 → ℝ) :
    euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))
        (Fin.cons p₀ (L.partialMomentum m p_int k_tail)) =
      (Real.exp (p₀ 0 * ε) : ℂ) *
        (Real.exp (-(2 * ε * ∑ a : Fin r_t, massShellEnergy m (k_tail a))) : ℂ) *
        euclidLaplace y (L.partialMomentum m p_int k_tail) := by
  have h_cons :
      euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))
          (Fin.cons p₀ (L.partialMomentum m p_int k_tail)) =
        (Real.exp (p₀ 0 * ε) : ℂ) *
          euclidLaplace (fun i => y i + euclidTimeVec (2 * ε))
            (L.partialMomentum m p_int k_tail) := by
    unfold euclidLaplace
    rw [Fin.sum_univ_succ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have h00 : euclidTimeVec ε 0 = ε := rfl
    have h10 : euclidTimeVec ε 1 = 0 := rfl
    have h20 : euclidTimeVec ε 2 = 0 := rfl
    have h30 : euclidTimeVec ε 3 = 0 := rfl
    simp only [Fin.cons_zero, Fin.cons_succ, h00, h10, h20, h30, Complex.ofReal_zero, mul_zero,
      add_zero, Complex.ofReal_mul]
  have h_tail :
      euclidLaplace (fun i => y i + euclidTimeVec (2 * ε)) (L.partialMomentum m p_int k_tail) =
        (Real.exp (-(2 * ε * ∑ a : Fin r_t, massShellEnergy m (k_tail a))) : ℂ) *
          euclidLaplace y (L.partialMomentum m p_int k_tail) := by
    unfold euclidLaplace
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    have h_sum0 : (∑ i : Fin j, L.partialMomentum m p_int k_tail i 0) =
        -∑ a : Fin r_t, massShellEnergy m (k_tail a) := by
      have h := congrArg (fun v : Fin 4 → ℝ => v 0)
        (partialMomentum_sum_eq m L p_int k_tail)
      simpa [massShellVec] using h
    have h_term : ∀ i : Fin j,
        (L.partialMomentum m p_int k_tail i 0 : ℂ) * ((y i + euclidTimeVec (2 * ε)) 0 : ℂ) +
          Complex.I * ((L.partialMomentum m p_int k_tail i 1 : ℂ) *
              ((y i + euclidTimeVec (2 * ε)) 1 : ℂ) +
            (L.partialMomentum m p_int k_tail i 2 : ℂ) *
              ((y i + euclidTimeVec (2 * ε)) 2 : ℂ) +
            (L.partialMomentum m p_int k_tail i 3 : ℂ) *
              ((y i + euclidTimeVec (2 * ε)) 3 : ℂ)) =
        (L.partialMomentum m p_int k_tail i 0 : ℂ) * ((2 * ε : ℝ) : ℂ) +
          ((L.partialMomentum m p_int k_tail i 0 : ℂ) * (y i 0 : ℂ) +
            Complex.I * ((L.partialMomentum m p_int k_tail i 1 : ℂ) * (y i 1 : ℂ) +
              (L.partialMomentum m p_int k_tail i 2 : ℂ) * (y i 2 : ℂ) +
              (L.partialMomentum m p_int k_tail i 3 : ℂ) * (y i 3 : ℂ))) := by
      intro i
      simp [euclidTimeVec]
      ring
    simp_rw [h_term]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, h_sum0]
    push_cast
    ring
  rw [h_cons, h_tail]
  ring

lemma norm_fockPartialTerm_euclidLaplace_le_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α : Fin j → ι) {y : Fin j → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN j)
    (L : PartialPairing j r) :
    ∃ B_L : ℝ, 0 ≤ B_L ∧ ∀ x : FockSectorDom M_mode.ν r,
      ‖fockPartialTerm M_mode α (euclidLaplace y) L x‖ ≤ B_L := by
  rcases exists_norm_fockPartialIntWeight_le hC α L with ⟨B, hB_nn, hB⟩
  let u_c : L.InternalChord → (Fin 3 → ℝ) → ℝ :=
    fun c q => Real.exp (-((y (L.mate c.1) 0 - y c.1 0) * massShellEnergy m q))
  have hu_int : ∀ c, Integrable (u_c c) volume :=
    fun c => integrable_exp_neg_massShellEnergy hm
      (sub_pos.mpr (orderedEuclidN_time_lt_of_lt hy.2 c.2))
  let Iu : ℝ := ∫ p_int : L.InternalChord → Fin 3 → ℝ, ∏ c, u_c c (p_int c)
  have hIu_nn : 0 ≤ Iu :=
    integral_nonneg fun p_int => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  refine ⟨M_mode.M ^ r * (B * Iu),
    mul_nonneg (pow_nonneg M_mode.hM r) (mul_nonneg hB_nn hIu_nn), fun x => ?_⟩
  unfold fockPartialTerm
  rw [norm_mul, norm_mul, norm_eta_pow M_mode.hη, one_mul, norm_prod]
  have hw_le : (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖) ≤ M_mode.M ^ r := by
    calc (∏ a : Fin r, ‖M_mode.w (x.2 a) (x.1 a) (α (L.unpaired a))‖)
        ≤ ∏ _a : Fin r, M_mode.M :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => M_mode.norm_w_le _ _ _)
      _ = M_mode.M ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hint_le :
      ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
        fockPartialIntWeight m C α L p_int * euclidLaplace y (L.partialMomentum m p_int x.1)‖ ≤
        B * Iu := by
    have h_dom : Integrable
        (fun p_int : L.InternalChord → Fin 3 → ℝ => B * ∏ c, u_c c (p_int c)) volume :=
      (Integrable.fintype_prod (f := u_c) hu_int).const_mul B
    calc ‖∫ p_int : L.InternalChord → Fin 3 → ℝ,
          fockPartialIntWeight m C α L p_int * euclidLaplace y (L.partialMomentum m p_int x.1)‖
        ≤ ∫ p_int : L.InternalChord → Fin 3 → ℝ,
            ‖fockPartialIntWeight m C α L p_int *
              euclidLaplace y (L.partialMomentum m p_int x.1)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ p_int : L.InternalChord → Fin 3 → ℝ, B * ∏ c, u_c c (p_int c) := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => norm_nonneg _) h_dom
            (Filter.Eventually.of_forall fun p_int => ?_)
          dsimp only
          rw [norm_mul, norm_euclidLaplace_partialMomentum]
          have h_ext_le :
              (∏ a : Fin r, Real.exp (-(y (L.unpaired a) 0 * massShellEnergy m (x.1 a)))) ≤ 1 := by
            calc (∏ a : Fin r, Real.exp (-(y (L.unpaired a) 0 * massShellEnergy m (x.1 a))))
                ≤ ∏ _a : Fin r, (1 : ℝ) := by
                  refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun a _ => ?_
                  exact Real.exp_le_one_iff.mpr
                    (by nlinarith [hy.1 (L.unpaired a), massShellEnergy_pos hm (x.1 a)])
              _ = 1 := Finset.prod_const_one
          have h_lap_le :
              (∏ c : L.InternalChord, u_c c (p_int c)) *
                (∏ a : Fin r, Real.exp (-(y (L.unpaired a) 0 * massShellEnergy m (x.1 a)))) ≤
              ∏ c : L.InternalChord, u_c c (p_int c) := by
            calc _ ≤ (∏ c : L.InternalChord, u_c c (p_int c)) * 1 :=
                  mul_le_mul_of_nonneg_left h_ext_le
                    (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
              _ = _ := mul_one _
          exact mul_le_mul (hB p_int) h_lap_le (by positivity) hB_nn
      _ = B * Iu := integral_const_mul B _
  exact mul_le_mul hw_le hint_le (norm_nonneg _) (pow_nonneg M_mode.hM r)

lemma fockPartialTerm_prependUnpaired_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    {j r : ℕ} (α₀ : ι) (α : Fin j → ι) (ε : ℝ) (y : Fin j → Fin 4 → ℝ)
    (L : PartialPairing j r) (x : FockSectorDom M_mode.ν (r + 1)) :
    fockPartialTerm M_mode (Fin.cons α₀ α)
        (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
        (PartialPairing.prependUnpaired L) x =
      ((Real.exp (-(ε * massShellEnergy m (x.1 0))) : ℂ) * M_mode.w (x.2 0) (x.1 0) α₀) *
        (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b.succ))) : ℂ) *
        fockPartialTerm M_mode α (euclidLaplace y) L (x.1 ∘ Fin.succ, x.2 ∘ Fin.succ) := by
  unfold fockPartialTerm
  rw [PartialPairing.partialCross_prependUnpaired, Fin.prod_univ_succ,
      ← (PartialPairing.measurePreserving_prependUnpairedParamEquiv L).integral_comp']
  · have h_w0 : M_mode.w (x.2 0) (x.1 0)
        ((Fin.cons α₀ α : Fin (j + 1) → ι) ((PartialPairing.prependUnpaired L).unpaired 0)) =
        M_mode.w (x.2 0) (x.1 0) α₀ := rfl
    have h_ws : (∏ b : Fin r, M_mode.w (x.2 b.succ) (x.1 b.succ)
        ((Fin.cons α₀ α : Fin (j + 1) → ι)
          ((PartialPairing.prependUnpaired L).unpaired b.succ))) =
        ∏ b : Fin r, M_mode.w (x.2 b.succ) (x.1 b.succ) (α (L.unpaired b)) := rfl
    have h_int : (∫ p_int : L.InternalChord → Fin 3 → ℝ,
        fockPartialIntWeight m C (Fin.cons α₀ α) (PartialPairing.prependUnpaired L)
          (PartialPairing.prependUnpairedParamEquiv L p_int) *
          euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))
            ((PartialPairing.prependUnpaired L).partialMomentum m
              (PartialPairing.prependUnpairedParamEquiv L p_int) x.1)) =
        ((Real.exp (-(ε * massShellEnergy m (x.1 0))) : ℂ) *
          (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b.succ))) : ℂ)) *
        ∫ p_int : L.InternalChord → Fin 3 → ℝ,
          fockPartialIntWeight m C α L p_int *
            euclidLaplace y (L.partialMomentum m p_int (x.1 ∘ Fin.succ)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p_int => ?_)
      dsimp only
      rw [fockPartialIntWeight_prependUnpaired, PartialPairing.partialMomentum_prependUnpaired,
          euclidLaplace_cons_timeVec_partialMomentum]
      have hp0 : (-massShellVec m (x.1 0)) 0 * ε = -(ε * massShellEnergy m (x.1 0)) := by
        simp [massShellVec]
        ring
      rw [hp0]
      dsimp only [Function.comp_apply]
      ring
    rw [h_w0, h_ws, h_int]
    dsimp only [Function.comp_apply]
    ring

lemma fockPartialTerm_prependPaired_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α₀ : ι) (α : Fin j → ι) {ε : ℝ} (hε : 0 < ε)
    {y : Fin j → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN j)
    (L' : PartialPairing j (r + 1)) (a₀ : Fin (r + 1))
    (x : FockSectorDom M_mode.ν r) :
    fockPartialTerm M_mode (Fin.cons α₀ α)
        (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
        (PartialPairing.prependPaired L' a₀) x =
      η ^ (a₀ : ℕ) *
        (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
        ∑ s₀ : Fin M_mode.ν,
          ∫ q₀ : Fin 3 → ℝ,
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              fockPartialTerm M_mode α (euclidLaplace y) L'
                (a₀.insertNth q₀ x.1, a₀.insertNth s₀ x.2) := by
  let y' : Fin (j + 1) → Fin 4 → ℝ :=
    Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))
  have hy'_pos : y' ∈ posOrderedEuclidN (j + 1) := by
    have hy_sh := timeShift_mem_posOrderedEuclidN j hy hε.le
    have h_eq : y' = osPrependPoint j (euclidTimeVec ε) (fun i => y i + euclidTimeVec ε) := by
      ext u μ
      refine Fin.cases (by rfl) (fun i => ?_) u
      simp [y', osPrependPoint, euclidTimeVec]
      split_ifs <;> ring
    rw [h_eq]
    exact osPrependPoint_mem_posOrderedEuclidN j (by simpa [euclidTimeVec] using hε) hy_sh
  have h_int_pair : Integrable
      (fun qp : (Fin 3 → ℝ) × (L'.InternalChord → Fin 3 → ℝ) =>
        fockPartialIntWeight m C (Fin.cons α₀ α) (PartialPairing.prependPaired L' a₀)
            (PartialPairing.prependPairedParamEquiv L' a₀ qp) *
          euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))
            ((PartialPairing.prependPaired L' a₀).partialMomentum m
              (PartialPairing.prependPairedParamEquiv L' a₀ qp) x.1))
      (volume.prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact ((PartialPairing.measurePreserving_prependPairedParamEquiv L' a₀).integrable_comp_emb
      (PartialPairing.prependPairedParamEquiv L' a₀).measurableEmbedding).mpr
      (integrable_fockPartialIntegrand hC (Fin.cons α₀ α)
        (partialMomentumBound_euclidLaplace hm hy'_pos)
        (PartialPairing.prependPaired L' a₀) x.1)
  unfold fockPartialTerm
  rw [PartialPairing.partialCross_prependPaired, pow_add, mul_comm (η ^ L'.partialCross),
      ← (PartialPairing.measurePreserving_prependPairedParamEquiv L' a₀).integral_comp',
      MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.integral_prod _ h_int_pair]
  have h_q_eval : ∀ q₀ : Fin 3 → ℝ,
      (∫ p_int : L'.InternalChord → Fin 3 → ℝ,
        fockPartialIntWeight m C (Fin.cons α₀ α) (PartialPairing.prependPaired L' a₀)
            (PartialPairing.prependPairedParamEquiv L' a₀ (q₀, p_int)) *
          euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))
            ((PartialPairing.prependPaired L' a₀).partialMomentum m
              (PartialPairing.prependPairedParamEquiv L' a₀ (q₀, p_int)) x.1)) =
      (massShellWeight m C ![α₀, α (L'.unpaired a₀)] q₀ *
        (Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) *
        (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ)) *
        ∫ p_int : L'.InternalChord → Fin 3 → ℝ,
          fockPartialIntWeight m C α L' p_int *
            euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1)) := by
    intro q₀
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p_int => ?_)
    dsimp only
    rw [fockPartialIntWeight_prependPaired, PartialPairing.partialMomentum_prependPaired,
        euclidLaplace_cons_timeVec_partialMomentum]
    have h_sum_e :
        (∑ a : Fin (r + 1),
          massShellEnergy m (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a)) =
        massShellEnergy m q₀ + ∑ b : Fin r, massShellEnergy m (x.1 b) := by
      rw [Fin.sum_univ_succAbove
        (fun a => massShellEnergy m (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a)) a₀,
        Fin.insertNth_apply_same]
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Fin.insertNth_apply_succAbove]
    have h_exp : (Real.exp ((massShellVec m q₀) 0 * ε) : ℂ) *
        (Real.exp (-(2 * ε * ∑ a : Fin (r + 1),
          massShellEnergy m (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a))) : ℂ) =
        (Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) *
          (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) := by
      rw [h_sum_e, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 2
      simp [massShellVec]
      ring
    calc (massShellWeight m C ![α₀, α (L'.unpaired a₀)] q₀ *
            fockPartialIntWeight m C α L' p_int) *
          ((Real.exp ((massShellVec m q₀) 0 * ε) : ℂ) *
            (Real.exp (-(2 * ε * ∑ a : Fin (r + 1),
              massShellEnergy m (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a))) : ℂ) *
            euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1)))
        = massShellWeight m C ![α₀, α (L'.unpaired a₀)] q₀ *
            ((Real.exp ((massShellVec m q₀) 0 * ε) : ℂ) *
              (Real.exp (-(2 * ε * ∑ a : Fin (r + 1),
                massShellEnergy m (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a))) : ℂ)) *
            (fockPartialIntWeight m C α L' p_int *
              euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1))) := by ring
      _ = _ := by rw [h_exp]; ring
  simp_rw [h_q_eval]
  have h_w_prod : ∀ (q₀ : Fin 3 → ℝ) (s₀ : Fin M_mode.ν),
      M_mode.w s₀ q₀ (α (L'.unpaired a₀)) *
        (∏ b : Fin r, M_mode.w (x.2 b) (x.1 b)
          ((Fin.cons (α := fun _ => ι) α₀ α)
            ((PartialPairing.prependPaired L' a₀).unpaired b))) =
      ∏ a : Fin (r + 1),
        M_mode.w (a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2 a)
          (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a) (α (L'.unpaired a)) := by
    intro q₀ s₀
    rw [Fin.prod_univ_succAbove _ a₀, Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    rfl
  have h_int_s : ∀ s₀ : Fin M_mode.ν, Integrable
      (fun q₀ : Fin 3 → ℝ =>
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          (η ^ L'.partialCross *
            (∏ a : Fin (r + 1),
              M_mode.w (a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2 a)
                (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a) (α (L'.unpaired a))) *
            ∫ p_int : L'.InternalChord → Fin 3 → ℝ,
              fockPartialIntWeight m C α L' p_int *
                euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1)))) volume := by
    intro s₀
    obtain ⟨B_L, _, hBL⟩ :=
      norm_fockPartialTerm_euclidLaplace_le_const hm M_mode hC α hy L'
    let C_c : ℝ := (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M * B_L
    have h_dom : Integrable
        (fun q₀ : Fin 3 → ℝ => C_c * Real.exp (-(ε * massShellEnergy m q₀))) volume :=
      (integrable_exp_neg_massShellEnergy hm hε).const_mul C_c
    have h_ins_meas : Measurable (fun q₀ : Fin 3 → ℝ =>
        (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1,
          a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2)) :=
      (measurable_pi_lambda _ fun a => by
        by_cases ha : a = a₀
        · subst ha
          simpa only [Fin.insertNth_apply_same] using measurable_id'
        · rcases Fin.exists_succAbove_eq ha with ⟨b, rfl⟩
          simpa only [Fin.insertNth_apply_succAbove] using measurable_const).prodMk measurable_const
    have h_meas : Measurable (fun q₀ : Fin 3 → ℝ =>
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          fockPartialTerm M_mode α (euclidLaplace y) L'
            (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1,
              a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2)) :=
      (((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul (continuous_massShellEnergy m)).neg))
          ).measurable).mul (measurable_conjMode M_mode s₀ α₀)).mul
        ((measurable_fockPartialTerm M_mode hC α
          (partialMomentumBound_euclidLaplace hm hy) L').comp h_ins_meas)
    refine h_dom.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun q₀ => ?_)
    change ‖((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
        fockPartialTerm M_mode α (euclidLaplace y) L'
          (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1,
            a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2)‖ ≤ _
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h_cm_nn : 0 ≤ (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) M_mode.hM
    calc Real.exp (-(ε * massShellEnergy m q₀)) * ‖conjMode M_mode s₀ q₀ α₀‖ *
          ‖fockPartialTerm M_mode α (euclidLaplace y) L'
            (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1,
              a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2)‖
        ≤ Real.exp (-(ε * massShellEnergy m q₀)) *
            ((∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M) * B_L :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (norm_conjMode_le M_mode s₀ q₀ α₀) (Real.exp_pos _).le)
            (hBL _) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le h_cm_nn)
      _ = C_c * Real.exp (-(ε * massShellEnergy m q₀)) := by dsimp [C_c]; ring
  rw [← MeasureTheory.integral_finsetSum Finset.univ fun s₀ _ => h_int_s s₀]
  have h_pull :
      (η ^ (a₀ : ℕ) * η ^ L'.partialCross *
        (∏ b : Fin r, M_mode.w (x.2 b) (x.1 b)
          ((Fin.cons (α := fun _ => ι) α₀ α)
            ((PartialPairing.prependPaired L' a₀).unpaired b))) *
        ∫ q₀ : Fin 3 → ℝ,
          (massShellWeight m C ![α₀, α (L'.unpaired a₀)] q₀ *
            (Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) *
            (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ)) *
          ∫ p_int : L'.InternalChord → Fin 3 → ℝ,
            fockPartialIntWeight m C α L' p_int *
              euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1))) =
      η ^ (a₀ : ℕ) * (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
        ∫ q₀ : Fin 3 → ℝ,
          ∑ s₀ : Fin M_mode.ν,
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              (η ^ L'.partialCross *
                (∏ a : Fin (r + 1),
                  M_mode.w (a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2 a)
                    (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a) (α (L'.unpaired a))) *
                ∫ p_int : L'.InternalChord → Fin 3 → ℝ,
                  fockPartialIntWeight m C α L' p_int *
                    euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1))) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q₀ => ?_)
    dsimp only
    calc (η ^ (a₀ : ℕ) * η ^ L'.partialCross *
            (∏ b : Fin r, M_mode.w (x.2 b) (x.1 b)
              ((Fin.cons (α := fun _ => ι) α₀ α)
                ((PartialPairing.prependPaired L' a₀).unpaired b)))) *
          ((massShellWeight m C ![α₀, α (L'.unpaired a₀)] q₀ *
            (Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) *
            (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ)) *
          ∫ p_int : L'.InternalChord → Fin 3 → ℝ,
            fockPartialIntWeight m C α L' p_int *
              euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1)))
        = ∑ s₀ : Fin M_mode.ν,
            (η ^ (a₀ : ℕ) *
              (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ)) *
              (((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                (η ^ L'.partialCross *
                  (∏ a : Fin (r + 1),
                    M_mode.w (a₀.insertNth (α := fun _ => Fin M_mode.ν) s₀ x.2 a)
                      (a₀.insertNth (α := fun _ => Fin 3 → ℝ) q₀ x.1 a) (α (L'.unpaired a))) *
                  ∫ p_int : L'.InternalChord → Fin 3 → ℝ,
                    fockPartialIntWeight m C α L' p_int *
                      euclidLaplace y (L'.partialMomentum m p_int (a₀.insertNth q₀ x.1)))) := by
          rw [massShellWeight_eq_sum_conjMode_mul_w M_mode q₀ α₀ (α (L'.unpaired a₀)),
              Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s₀ _ => ?_
          rw [← h_w_prod q₀ s₀]
          ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  exact h_pull

noncomputable def fockCreateOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (α₀ : ι) (ε : ℝ)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ)
    (r : ℕ) (x : FockSectorDom M_mode.ν (r + 1)) : ℂ :=
  (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) *
    ∑ p : Fin (r + 1),
      η ^ (p : ℕ) *
        ((Real.exp (-(ε * massShellEnergy m (x.1 p))) : ℂ) * M_mode.w (x.2 p) (x.1 p) α₀) *
        (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) : ℂ) *
        G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)

noncomputable def fockAnnihOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (α₀ : ι) (ε : ℝ)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ)
    (r : ℕ) (x : FockSectorDom M_mode.ν r) : ℂ :=
  (Real.sqrt (r + 1 : ℝ) : ℂ) *
    (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
    ∑ s₀ : Fin M_mode.ν,
      ∫ q₀ : Fin 3 → ℝ,
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          G (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)

lemma sqrt_factorial_succ_inv_eq (r : ℕ) :
    (((r + 1).factorial : ℝ).sqrt⁻¹ : ℝ) =
      (Real.sqrt (r + 1 : ℝ))⁻¹ * ((r.factorial : ℝ).sqrt)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Real.sqrt_mul (by positivity), mul_inv]

lemma sqrt_factorial_inv_eq_mul_succ (r : ℕ) :
    ((r.factorial : ℝ).sqrt⁻¹ : ℝ) =
      Real.sqrt (r + 1 : ℝ) * (((r + 1).factorial : ℝ).sqrt)⁻¹ := by
  rw [sqrt_factorial_succ_inv_eq, ← mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by positivity)), one_mul]

lemma symmSector_prependUnpaired_sum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    {j r : ℕ} (α₀ : ι) (α : Fin j → ι) (ε : ℝ) (y : Fin j → Fin 4 → ℝ)
    (x : FockSectorDom M_mode.ν (r + 1)) :
    ((((r + 1).factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
      (∑ π : Equiv.Perm (Fin (r + 1)), η ^ permInversions π *
        ∑ L : PartialPairing j r,
          fockPartialTerm M_mode (Fin.cons α₀ α)
            (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
            (PartialPairing.prependUnpaired L)
            (fockSectorPermEquiv M_mode.ν (r + 1) π x)) =
    fockCreateOp M_mode α₀ ε
      (fun r' => symmSector M_mode.ν r' η (fockRawSector M_mode r' α (euclidLaplace y)))
      r x := by
  rw [sqrt_factorial_succ_inv_eq r, Complex.ofReal_mul, mul_assoc]
  unfold fockCreateOp
  congr 1
  rw [← Equiv.sum_comp (createPermEquiv r), Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h_each_σ : ∀ σ : Equiv.Perm (Fin r),
      η ^ permInversions (createPermEquiv r (p, σ)) *
        (∑ L : PartialPairing j r,
          fockPartialTerm M_mode (Fin.cons α₀ α)
            (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
            (PartialPairing.prependUnpaired L)
            (fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x)) =
      (η ^ (p : ℕ) *
        ((Real.exp (-(ε * massShellEnergy m (x.1 p))) : ℂ) * M_mode.w (x.2 p) (x.1 p) α₀) *
        (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) : ℂ)) *
        (η ^ permInversions σ *
          fockRawSector M_mode r α (euclidLaplace y)
            (fockSectorPermEquiv M_mode.ν r σ (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove))) := by
    intro σ
    rw [eta_pow_permInversions_createPermEquiv M_mode.hη p σ]
    have h_sum_e :
        (∑ b : Fin r, massShellEnergy m
          ((fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x).1 b.succ)) =
        ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)) := by
      have h_comp : ∀ b : Fin r,
          (fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x).1 b.succ =
            x.1 (p.succAbove (σ b)) := by
        intro b
        simp
      simp_rw [h_comp]
      exact Equiv.sum_comp σ fun b => massShellEnergy m (x.1 (p.succAbove b))
    have h0_k : (fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x).1 0 =
        x.1 p := by simp
    have h0_s : (fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x).2 0 =
        x.2 p := by simp
    have h_tail :
        ((fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x).1 ∘ Fin.succ,
          (fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x).2 ∘ Fin.succ) =
        fockSectorPermEquiv M_mode.ν r σ (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove) := by
      ext b <;> simp
    have h_L : ∀ L : PartialPairing j r,
        fockPartialTerm M_mode (Fin.cons α₀ α)
          (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
          (PartialPairing.prependUnpaired L)
          (fockSectorPermEquiv M_mode.ν (r + 1) (createPermEquiv r (p, σ)) x) =
        (((Real.exp (-(ε * massShellEnergy m (x.1 p))) : ℂ) * M_mode.w (x.2 p) (x.1 p) α₀) *
          (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) : ℂ)) *
          fockPartialTerm M_mode α (euclidLaplace y) L
            (fockSectorPermEquiv M_mode.ν r σ (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)) := by
      intro L
      rw [fockPartialTerm_prependUnpaired_eq, h0_k, h0_s, h_sum_e, h_tail]
    simp_rw [h_L]
    rw [← Finset.mul_sum]
    unfold fockRawSector
    ring
  simp_rw [h_each_σ, ← Finset.mul_sum]
  unfold symmSector
  ring

lemma measurable_finCons_left {r : ℕ} (v : Fin r → Fin 3 → ℝ) :
    Measurable (fun q₀ : Fin 3 → ℝ => (Fin.cons q₀ v : Fin (r + 1) → Fin 3 → ℝ)) := by
  refine measurable_pi_lambda _ fun a => ?_
  refine Fin.cases ?_ (fun j => ?_) a
  · simpa only [Fin.cons_zero] using measurable_id'
  · simpa only [Fin.cons_succ] using measurable_const

lemma symmSector_prependPaired_sum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α₀ : ι) (α : Fin j → ι) {ε : ℝ} (hε : 0 < ε)
    {y : Fin j → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN j)
    (x : FockSectorDom M_mode.ν r) :
    (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
      (∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
        ∑ L' : PartialPairing j (r + 1), ∑ a₀ : Fin (r + 1),
          fockPartialTerm M_mode (Fin.cons α₀ α)
            (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
            (PartialPairing.prependPaired L' a₀)
            (fockSectorPermEquiv M_mode.ν r σ x)) =
    fockAnnihOp M_mode α₀ ε
      (fun r' => symmSector M_mode.ν r' η (fockRawSector M_mode r' α (euclidLaplace y)))
      r x := by
  have h_int_πL : ∀ (s₀ : Fin M_mode.ν) (π : Equiv.Perm (Fin (r + 1)))
      (L' : PartialPairing j (r + 1)),
      Integrable (fun q₀ : Fin 3 → ℝ =>
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          (η ^ permInversions π *
            fockPartialTerm M_mode α (euclidLaplace y) L'
              (fockSectorPermEquiv M_mode.ν (r + 1) π
                (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) volume := by
    intro s₀ π L'
    obtain ⟨B_L, _, hBL⟩ :=
      norm_fockPartialTerm_euclidLaplace_le_const hm M_mode hC α hy L'
    let C_c : ℝ := (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M * B_L
    have h_dom : Integrable
        (fun q₀ : Fin 3 → ℝ => C_c * Real.exp (-(ε * massShellEnergy m q₀))) volume :=
      (integrable_exp_neg_massShellEnergy hm hε).const_mul C_c
    have h_cons_meas : Measurable
        (fun q₀ : Fin 3 → ℝ =>
          ((Fin.cons q₀ x.1 : Fin (r + 1) → Fin 3 → ℝ),
            (Fin.cons s₀ x.2 : Fin (r + 1) → Fin M_mode.ν))) :=
      (measurable_finCons_left x.1).prodMk measurable_const
    have h_meas : Measurable (fun q₀ : Fin 3 → ℝ =>
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          (η ^ permInversions π *
            fockPartialTerm M_mode α (euclidLaplace y) L'
              (fockSectorPermEquiv M_mode.ν (r + 1) π
                (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) :=
      (((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul (continuous_massShellEnergy m)).neg))
          ).measurable).mul (measurable_conjMode M_mode s₀ α₀)).mul
        (measurable_const.mul
          ((measurable_fockPartialTerm M_mode hC α
            (partialMomentumBound_euclidLaplace hm hy) L').comp
            ((fockSectorPermEquiv M_mode.ν (r + 1) π).measurable.comp h_cons_meas)))
    refine h_dom.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun q₀ => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_eta_pow M_mode.hη, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h_cm_nn : 0 ≤ (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) M_mode.hM
    calc Real.exp (-(ε * massShellEnergy m q₀)) * ‖conjMode M_mode s₀ q₀ α₀‖ *
          ‖fockPartialTerm M_mode α (euclidLaplace y) L'
            (fockSectorPermEquiv M_mode.ν (r + 1) π (Fin.cons q₀ x.1, Fin.cons s₀ x.2))‖
        ≤ Real.exp (-(ε * massShellEnergy m q₀)) *
            ((∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M) * B_L :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (norm_conjMode_le M_mode s₀ q₀ α₀) (Real.exp_pos _).le)
            (hBL _) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le h_cm_nn)
      _ = C_c * Real.exp (-(ε * massShellEnergy m q₀)) := by dsimp [C_c]; ring
  have h_each : ∀ (σ : Equiv.Perm (Fin r)) (L' : PartialPairing j (r + 1))
      (a₀ : Fin (r + 1)),
      η ^ permInversions σ *
        fockPartialTerm M_mode (Fin.cons α₀ α)
          (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
          (PartialPairing.prependPaired L' a₀)
          (fockSectorPermEquiv M_mode.ν r σ x) =
      (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
        ∑ s₀ : Fin M_mode.ν,
          ∫ q₀ : Fin 3 → ℝ,
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              (η ^ permInversions (annihPermEquiv r (a₀, σ)) *
                fockPartialTerm M_mode α (euclidLaplace y) L'
                  (fockSectorPermEquiv M_mode.ν (r + 1) (annihPermEquiv r (a₀, σ))
                    (Fin.cons q₀ x.1, Fin.cons s₀ x.2))) := by
    intro σ L' a₀
    rw [fockPartialTerm_prependPaired_eq hm M_mode hC α₀ α hε hy L' a₀]
    have h_sum_e :
        (∑ b : Fin r, massShellEnergy m ((fockSectorPermEquiv M_mode.ν r σ x).1 b)) =
        ∑ b : Fin r, massShellEnergy m (x.1 b) :=
      Equiv.sum_comp σ fun b => massShellEnergy m (x.1 b)
    rw [h_sum_e]
    dsimp only [fockSectorPermEquiv_apply]
    have h_eta := (eta_pow_permInversions_annihPermEquiv M_mode.hη a₀ σ).symm
    have h_ins : ∀ (q₀ : Fin 3 → ℝ) (s₀ : Fin M_mode.ν),
        (a₀.insertNth q₀ (x.1 ∘ σ), a₀.insertNth s₀ (x.2 ∘ σ)) =
          fockSectorPermEquiv M_mode.ν (r + 1) (annihPermEquiv r (a₀, σ))
            (Fin.cons q₀ x.1, Fin.cons s₀ x.2) := by
      intro q₀ s₀
      exact Prod.ext (cons_comp_annihPermEquiv q₀ x.1 a₀ σ).symm
        (cons_comp_annihPermEquiv s₀ x.2 a₀ σ).symm
    let e_damp : ℂ := (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ)
    have h_s_eq :
        (η ^ permInversions σ *
          (η ^ (a₀ : ℕ) * e_damp *
            ∑ s₀ : Fin M_mode.ν,
              ∫ q₀ : Fin 3 → ℝ,
                ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                  fockPartialTerm M_mode α (euclidLaplace y) L'
                    (a₀.insertNth q₀ (x.1 ∘ σ), a₀.insertNth s₀ (x.2 ∘ σ)))) =
        e_damp *
          ∑ s₀ : Fin M_mode.ν,
            (η ^ permInversions (annihPermEquiv r (a₀, σ))) *
              ∫ q₀ : Fin 3 → ℝ,
                ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                  fockPartialTerm M_mode α (euclidLaplace y) L'
                    (fockSectorPermEquiv M_mode.ν (r + 1) (annihPermEquiv r (a₀, σ))
                      (Fin.cons q₀ x.1, Fin.cons s₀ x.2)) := by
      have h_mul_eta : η ^ permInversions σ * η ^ (a₀ : ℕ) =
          η ^ permInversions (annihPermEquiv r (a₀, σ)) := by
        rw [mul_comm, h_eta]
      calc _ = e_damp *
              ((η ^ permInversions σ * η ^ (a₀ : ℕ)) *
                ∑ s₀ : Fin M_mode.ν,
                  ∫ q₀ : Fin 3 → ℝ,
                    ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                      fockPartialTerm M_mode α (euclidLaplace y) L'
                        (a₀.insertNth q₀ (x.1 ∘ σ), a₀.insertNth s₀ (x.2 ∘ σ))) := by ring
        _ = _ := by
            rw [h_mul_eta, Finset.mul_sum]
            refine congrArg (e_damp * ·) (Finset.sum_congr rfl fun s₀ _ => ?_)
            refine congrArg (η ^ permInversions (annihPermEquiv r (a₀, σ)) * ·) ?_
            refine integral_congr_ae (Filter.Eventually.of_forall fun q₀ => ?_)
            dsimp only
            rw [h_ins q₀ s₀]
    change η ^ permInversions σ *
        (η ^ (a₀ : ℕ) * e_damp *
          ∑ s₀ : Fin M_mode.ν,
            ∫ q₀ : Fin 3 → ℝ,
              ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                fockPartialTerm M_mode α (euclidLaplace y) L'
                  (a₀.insertNth q₀ (x.1 ∘ σ), a₀.insertNth s₀ (x.2 ∘ σ))) = _
    rw [h_s_eq]
    refine congrArg (e_damp * ·) (Finset.sum_congr rfl fun s₀ _ => ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q₀ => ?_)
    dsimp only [fockSectorPermEquiv_apply]
    ring
  simp_rw [Finset.mul_sum, h_each, ← Finset.mul_sum]
  rw [sqrt_factorial_inv_eq_mul_succ r, Complex.ofReal_mul]
  unfold fockAnnihOp
  have h_sum_int_π : ∀ (s₀ : Fin M_mode.ν) (π : Equiv.Perm (Fin (r + 1))),
      (∑ L' : PartialPairing j (r + 1),
        ∫ q₀ : Fin 3 → ℝ,
          ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
            (η ^ permInversions π *
              fockPartialTerm M_mode α (euclidLaplace y) L'
                (fockSectorPermEquiv M_mode.ν (r + 1) π
                  (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) =
      ∫ q₀ : Fin 3 → ℝ,
        ∑ L' : PartialPairing j (r + 1),
          ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
            (η ^ permInversions π *
              fockPartialTerm M_mode α (euclidLaplace y) L'
                (fockSectorPermEquiv M_mode.ν (r + 1) π
                  (Fin.cons q₀ x.1, Fin.cons s₀ x.2))) :=
    fun s₀ π => (MeasureTheory.integral_finsetSum Finset.univ fun L' _ => h_int_πL s₀ π L').symm
  have h_reord :
      (∑ σ : Equiv.Perm (Fin r), ∑ L' : PartialPairing j (r + 1), ∑ a₀ : Fin (r + 1),
        ∑ s₀ : Fin M_mode.ν,
          ∫ q₀ : Fin 3 → ℝ,
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              (η ^ permInversions (annihPermEquiv r (a₀, σ)) *
                fockPartialTerm M_mode α (euclidLaplace y) L'
                  (fockSectorPermEquiv M_mode.ν (r + 1) (annihPermEquiv r (a₀, σ))
                    (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) =
      ∑ s₀ : Fin M_mode.ν,
        ∫ q₀ : Fin 3 → ℝ,
          ∑ π : Equiv.Perm (Fin (r + 1)), ∑ L' : PartialPairing j (r + 1),
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              (η ^ permInversions π *
                fockPartialTerm M_mode α (euclidLaplace y) L'
                  (fockSectorPermEquiv M_mode.ν (r + 1) π
                    (Fin.cons q₀ x.1, Fin.cons s₀ x.2))) := by
    conv_lhs =>
      arg 2; ext σ; rw [Finset.sum_comm]
      arg 2; ext a₀; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext a₀; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s₀ _ => ?_
    rw [← Fintype.sum_prod_type (f := fun ps : Fin (r + 1) × Equiv.Perm (Fin r) =>
      ∑ L' : PartialPairing j (r + 1),
        ∫ q₀ : Fin 3 → ℝ,
          ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
            (η ^ permInversions (annihPermEquiv r ps) *
              fockPartialTerm M_mode α (euclidLaplace y) L'
                (fockSectorPermEquiv M_mode.ν (r + 1) (annihPermEquiv r ps)
                  (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))),
      Equiv.sum_comp (annihPermEquiv r) (fun π =>
        ∑ L' : PartialPairing j (r + 1),
          ∫ q₀ : Fin 3 → ℝ,
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              (η ^ permInversions π *
                fockPartialTerm M_mode α (euclidLaplace y) L'
                  (fockSectorPermEquiv M_mode.ν (r + 1) π
                    (Fin.cons q₀ x.1, Fin.cons s₀ x.2))))]
    simp_rw [h_sum_int_π s₀]
    exact (MeasureTheory.integral_finsetSum Finset.univ fun π _ =>
      integrable_finsetSum Finset.univ fun L' _ => h_int_πL s₀ π L').symm
  rw [h_reord]
  have h_pull_f :
      (((Real.sqrt (r + 1 : ℝ) : ℂ) *
        ((((r + 1).factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ)) *
        ((Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
          ∑ s₀ : Fin M_mode.ν,
            ∫ q₀ : Fin 3 → ℝ,
              ∑ π : Equiv.Perm (Fin (r + 1)), ∑ L' : PartialPairing j (r + 1),
                ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                  (η ^ permInversions π *
                    fockPartialTerm M_mode α (euclidLaplace y) L'
                      (fockSectorPermEquiv M_mode.ν (r + 1) π
                        (Fin.cons q₀ x.1, Fin.cons s₀ x.2))))) =
      (Real.sqrt (r + 1 : ℝ) : ℂ) *
        (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
        ∑ s₀ : Fin M_mode.ν,
          ∫ q₀ : Fin 3 → ℝ,
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              symmSector M_mode.ν (r + 1) η
                (fockRawSector M_mode (r + 1) α (euclidLaplace y))
                (Fin.cons q₀ x.1, Fin.cons s₀ x.2) := by
    have h_s : ∀ s₀ : Fin M_mode.ν,
        ((((r + 1).factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
          (∫ q₀ : Fin 3 → ℝ,
            ∑ π : Equiv.Perm (Fin (r + 1)), ∑ L' : PartialPairing j (r + 1),
              ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                (η ^ permInversions π *
                  fockPartialTerm M_mode α (euclidLaplace y) L'
                    (fockSectorPermEquiv M_mode.ν (r + 1) π
                      (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) =
        ∫ q₀ : Fin 3 → ℝ,
          ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
            symmSector M_mode.ν (r + 1) η
              (fockRawSector M_mode (r + 1) α (euclidLaplace y))
              (Fin.cons q₀ x.1, Fin.cons s₀ x.2) := by
      intro s₀
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q₀ => ?_)
      dsimp only [symmSector, fockRawSector]
      simp_rw [← Finset.mul_sum]
      ring
    calc _ = (Real.sqrt (r + 1 : ℝ) : ℂ) *
            (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ) *
            ∑ s₀ : Fin M_mode.ν,
              ((((r + 1).factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
                ∫ q₀ : Fin 3 → ℝ,
                  ∑ π : Equiv.Perm (Fin (r + 1)), ∑ L' : PartialPairing j (r + 1),
                    ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
                      (η ^ permInversions π *
                        fockPartialTerm M_mode α (euclidLaplace y) L'
                          (fockSectorPermEquiv M_mode.ν (r + 1) π
                            (Fin.cons q₀ x.1, Fin.cons s₀ x.2))) := by
            rw [← Finset.mul_sum]
            ring
      _ = _ := by
          refine congrArg (_ * ·) (Finset.sum_congr rfl fun s₀ _ => h_s s₀)
  exact h_pull_f

lemma symmSector_prependShift_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j : ℕ} (α₀ : ι) (α : Fin j → ι) {ε : ℝ} (hε : 0 < ε)
    {y : Fin j → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN j)
    (x : FockSectorDom M_mode.ν 0) :
    symmSector M_mode.ν 0 η
        (fockRawSector M_mode 0 (Fin.cons α₀ α)
          (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))))
        x =
      fockAnnihOp M_mode α₀ ε
        (fun r' => symmSector M_mode.ν r' η (fockRawSector M_mode r' α (euclidLaplace y)))
        0 x := by
  have h_raw : ∀ z : FockSectorDom M_mode.ν 0,
      fockRawSector M_mode 0 (Fin.cons α₀ α)
          (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))) z =
        ∑ L' : PartialPairing j 1, ∑ a₀ : Fin 1,
          fockPartialTerm M_mode (Fin.cons α₀ α)
            (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
            (PartialPairing.prependPaired L' a₀) z := by
    intro z
    unfold fockRawSector
    rw [← Equiv.sum_comp (PartialPairing.partialPairingSuccZeroEquiv j), Fintype.sum_prod_type]
    rfl
  rw [← symmSector_prependPaired_sum_eq hm M_mode hC α₀ α hε hy x]
  unfold symmSector
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [h_raw]

lemma symmSector_prependShift_succ_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {j r : ℕ} (α₀ : ι) (α : Fin j → ι) {ε : ℝ} (hε : 0 < ε)
    {y : Fin j → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN j)
    (x : FockSectorDom M_mode.ν (r + 1)) :
    symmSector M_mode.ν (r + 1) η
        (fockRawSector M_mode (r + 1) (Fin.cons α₀ α)
          (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))))
        x =
      fockCreateOp M_mode α₀ ε
        (fun r' => symmSector M_mode.ν r' η (fockRawSector M_mode r' α (euclidLaplace y)))
        r x +
      fockAnnihOp M_mode α₀ ε
        (fun r' => symmSector M_mode.ν r' η (fockRawSector M_mode r' α (euclidLaplace y)))
        (r + 1) x := by
  have h_raw : ∀ z : FockSectorDom M_mode.ν (r + 1),
      fockRawSector M_mode (r + 1) (Fin.cons α₀ α)
          (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε)))) z =
        (∑ L : PartialPairing j r,
          fockPartialTerm M_mode (Fin.cons α₀ α)
            (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
            (PartialPairing.prependUnpaired L) z) +
        (∑ L' : PartialPairing j (r + 2), ∑ a₀ : Fin (r + 2),
          fockPartialTerm M_mode (Fin.cons α₀ α)
            (euclidLaplace (Fin.cons (euclidTimeVec ε) (fun i => y i + euclidTimeVec (2 * ε))))
            (PartialPairing.prependPaired L' a₀) z) := by
    intro z
    unfold fockRawSector
    rw [← Equiv.sum_comp (PartialPairing.partialPairingSuccSuccEquiv j r),
        Fintype.sum_sum_type, Fintype.sum_prod_type]
    rfl
  rw [← symmSector_prependUnpaired_sum_eq M_mode α₀ α ε y x,
      ← symmSector_prependPaired_sum_eq hm M_mode hC α₀ α hε hy x,
      ← mul_add]
  unfold symmSector
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [h_raw, mul_add]

lemma liftSectorToFock_zero (ν r : ℕ) :
    liftSectorToFock ν r 0 measurable_const MemLp.zero = 0 := by
  rw [Lp.ext_iff]
  filter_upwards [(memLp_sectorToOmega (ν := ν) (r := r) measurable_const MemLp.zero).coeFn_toLp,
    Lp.coeFn_zero ℂ 2 (fockMeasure ν)] with a ha h0
  unfold liftSectorToFock
  exact ha.trans (by
    rw [h0]
    rcases a with ⟨r', x⟩
    by_cases hr : r' = r <;> · simp [sectorToOmega, hr]; try rfl)

lemma liftSectorToFock_add {ν r : ℕ}
    {g₁ g₂ : FockSectorDom ν r → ℂ}
    (hg₁_m : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r))
    (hg₂_m : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r)) :
    liftSectorToFock ν r (g₁ + g₂) (hg₁_m.add hg₂_m) (hg₁.add hg₂) =
      liftSectorToFock ν r g₁ hg₁_m hg₁ + liftSectorToFock ν r g₂ hg₂_m hg₂ := by
  rw [Lp.ext_iff]
  filter_upwards [(memLp_sectorToOmega (hg₁_m.add hg₂_m) (hg₁.add hg₂)).coeFn_toLp,
    Lp.coeFn_add (liftSectorToFock ν r g₁ hg₁_m hg₁) (liftSectorToFock ν r g₂ hg₂_m hg₂),
    (memLp_sectorToOmega hg₁_m hg₁).coeFn_toLp,
    (memLp_sectorToOmega hg₂_m hg₂).coeFn_toLp] with a ha h_add ha₁ ha₂
  unfold liftSectorToFock at h_add ⊢
  rw [ha, h_add, Pi.add_apply, ha₁, ha₂]
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r <;> simp [sectorToOmega, hr]

lemma liftSectorToFock_smul {ν r : ℕ} (c : ℂ)
    {g : FockSectorDom ν r → ℂ}
    (hg_m : Measurable g) (hg : MemLp g 2 (fockSectorMeasure ν r)) :
    liftSectorToFock ν r ((fun _ => c) * g) (measurable_const.mul hg_m) (hg.const_mul c) =
      c • liftSectorToFock ν r g hg_m hg := by
  rw [Lp.ext_iff]
  filter_upwards [(memLp_sectorToOmega (measurable_const.mul hg_m) (hg.const_mul c)).coeFn_toLp,
    Lp.coeFn_smul c (liftSectorToFock ν r g hg_m hg),
    (memLp_sectorToOmega hg_m hg).coeFn_toLp] with a ha h_sm ha₁
  unfold liftSectorToFock at h_sm ⊢
  rw [ha, h_sm, Pi.smul_apply, smul_eq_mul, ha₁]
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r <;> simp [sectorToOmega, hr]

lemma liftSectorToFock_congr {ν r : ℕ}
    {g₁ g₂ : FockSectorDom ν r → ℂ}
    (hg₁_m : Measurable g₁) (hg₁ : MemLp g₁ 2 (fockSectorMeasure ν r))
    (hg₂_m : Measurable g₂) (hg₂ : MemLp g₂ 2 (fockSectorMeasure ν r))
    (h_eq : ∀ x, g₁ x = g₂ x) :
    liftSectorToFock ν r g₁ hg₁_m hg₁ = liftSectorToFock ν r g₂ hg₂_m hg₂ := by
  unfold liftSectorToFock
  refine MeasureTheory.MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun a => ?_)
  rcases a with ⟨r', x⟩
  by_cases hr : r' = r <;> simp [sectorToOmega, hr, h_eq]

lemma norm_sq_sum_liftSectorToFock {ν M : ℕ}
    (G : ∀ r : ℕ, FockSectorDom ν r → ℂ)
    (hG_m : ∀ r, Measurable (G r))
    (hG_lp : ∀ r, MemLp (G r) 2 (fockSectorMeasure ν r)) :
    ‖∑ r ∈ Finset.range M, liftSectorToFock ν r (G r) (hG_m r) (hG_lp r)‖ ^ 2 =
      ∑ r ∈ Finset.range M,
        ∫ x : FockSectorDom ν r, ‖G r x‖ ^ 2 ∂(fockSectorMeasure ν r) := by
  have h_diag : ∀ r₁ ∈ Finset.range M,
      ⟪liftSectorToFock ν r₁ (G r₁) (hG_m r₁) (hG_lp r₁),
        ∑ r₂ ∈ Finset.range M, liftSectorToFock ν r₂ (G r₂) (hG_m r₂) (hG_lp r₂)⟫_ℂ =
      (((∫ x : FockSectorDom ν r₁, ‖G r₁ x‖ ^ 2 ∂(fockSectorMeasure ν r₁) : ℝ) : ℂ)) := by
    intro r₁ hr₁
    rw [inner_sum (𝕜 := ℂ), Finset.sum_eq_single r₁]
    · rw [inner_liftSectorToFock_eq (hG_m r₁) (hG_lp r₁) (hG_m r₁) (hG_lp r₁)]
      have h_int_re : Integrable
          (fun x : FockSectorDom ν r₁ => ‖G r₁ x‖ ^ 2) (fockSectorMeasure ν r₁) :=
        (memLp_two_iff_integrable_sq_norm (hG_m r₁).aestronglyMeasurable).mp (hG_lp r₁)
      have h_ofR :
          (∫ x : FockSectorDom ν r₁, ((‖G r₁ x‖ ^ 2 : ℝ) : ℂ) ∂(fockSectorMeasure ν r₁)) =
            (((∫ x : FockSectorDom ν r₁, ‖G r₁ x‖ ^ 2 ∂(fockSectorMeasure ν r₁) : ℝ) : ℂ)) :=
        integral_ofReal
      rw [← h_ofR]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    · intro r₂ _ hne
      exact inner_liftSectorToFock_ne hne.symm (hG_m r₁) (hG_lp r₁) (hG_m r₂) (hG_lp r₂)
    · intro hnot
      exact False.elim (hnot hr₁)
  apply Complex.ofReal_injective
  have h_self :
      (((‖∑ r ∈ Finset.range M, liftSectorToFock ν r (G r) (hG_m r) (hG_lp r)‖ ^ 2 : ℝ) : ℂ)) =
        ⟪∑ r ∈ Finset.range M, liftSectorToFock ν r (G r) (hG_m r) (hG_lp r),
          ∑ r ∈ Finset.range M, liftSectorToFock ν r (G r) (hG_m r) (hG_lp r)⟫_ℂ := by
    simp
  rw [h_self, sum_inner (𝕜 := ℂ), Finset.sum_congr rfl h_diag, Complex.ofReal_sum]

noncomputable def fockConfigSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (A : OSConfig ι)
    (r : ℕ) (x : FockSectorDom M_mode.ν r) : ℂ :=
  symmSector M_mode.ν r η (fockRawSector M_mode r A.2.1 (euclidLaplace A.2.2.val)) x

lemma fockConfigSector_eq_zero_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (A : OSConfig ι)
    {r : ℕ} (hlt : A.1 < r) (x : FockSectorDom M_mode.ν r) :
    fockConfigSector M_mode A r x = 0 := by
  haveI : IsEmpty (PartialPairing A.1 r) := PartialPairing.isEmpty_of_lt hlt
  unfold fockConfigSector symmSector fockRawSector
  simp

lemma measurable_fockConfigSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (A : OSConfig ι) (r : ℕ) :
    Measurable (fockConfigSector M_mode A r) :=
  measurable_symmSector η
    (measurable_fockRawSector M_mode hC r A.2.1 (partialMomentumBound_euclidLaplace hm A.2.2.2))

lemma memLp_fockConfigSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (A : OSConfig ι) (r : ℕ) :
    MemLp (fockConfigSector M_mode A r) 2 (fockSectorMeasure M_mode.ν r) :=
  memLp_symmSector η
    (memLp_fockRawSector M_mode hC r A.2.1 (partialMomentumBound_euclidLaplace hm A.2.2.2))

noncomputable def fockSumSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    (r : ℕ) (x : FockSectorDom M_mode.ν r) : ℂ :=
  ∑ a ∈ S_fin, c a * fockConfigSector M_mode (cfg a) r x

lemma measurable_fockSumSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι) (r : ℕ) :
    Measurable (fockSumSector M_mode S_fin c cfg r) :=
  Finset.measurable_sum S_fin fun a _ =>
    measurable_const.mul (measurable_fockConfigSector hm M_mode hC (cfg a) r)

lemma memLp_fockSumSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι) (r : ℕ) :
    MemLp (fockSumSector M_mode S_fin c cfg r) 2 (fockSectorMeasure M_mode.ν r) :=
  memLp_finsetSum S_fin fun a _ =>
    (memLp_fockConfigSector hm M_mode hC (cfg a) r).const_mul (c a)

lemma fockSumSector_eq_zero_of_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    {r : ℕ} (hlt : ∀ a ∈ S_fin, (cfg a).1 < r) (x : FockSectorDom M_mode.ν r) :
    fockSumSector M_mode S_fin c cfg r x = 0 := by
  unfold fockSumSector
  exact Finset.sum_eq_zero fun a ha => by
    rw [fockConfigSector_eq_zero_of_lt M_mode (cfg a) (hlt a ha), mul_zero]

lemma sum_fockOSMap_eq_sum_liftSectorToFock {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    {N : ℕ} (hN : ∀ a ∈ S_fin, (cfg a).1 ≤ N) :
    (∑ a ∈ S_fin, c a • fockOSMap hm M_mode hC (cfg a)) =
      ∑ r ∈ Finset.range (N + 1),
        liftSectorToFock M_mode.ν r
          (fockSumSector M_mode S_fin c cfg r)
          (measurable_fockSumSector hm M_mode hC S_fin c cfg r)
          (memLp_fockSumSector hm M_mode hC S_fin c cfg r) := by
  classical
  have h_single : ∀ A : OSConfig ι, A.1 ≤ N →
      fockOSMap hm M_mode hC A =
        ∑ r ∈ Finset.range (N + 1),
          liftSectorToFock M_mode.ν r
            (fockConfigSector M_mode A r)
            (measurable_fockConfigSector hm M_mode hC A r)
            (memLp_fockConfigSector hm M_mode hC A r) := by
    intro A hA
    unfold fockOSMap fockMomentumVec
    refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hA)) fun r _ hr_not => ?_
    have hlt : A.1 < r := by
      rw [Finset.mem_range] at hr_not
      omega
    change liftSectorToFock M_mode.ν r (fockConfigSector M_mode A r)
      (measurable_fockConfigSector hm M_mode hC A r)
      (memLp_fockConfigSector hm M_mode hC A r) = 0
    exact (liftSectorToFock_congr (g₂ := 0) _ _
      measurable_const MemLp.zero
      (fockConfigSector_eq_zero_of_lt M_mode A hlt)).trans
      (liftSectorToFock_zero M_mode.ν r)
  have h_lift_sum : ∀ r : ℕ,
      liftSectorToFock M_mode.ν r
        (fockSumSector M_mode S_fin c cfg r)
        (measurable_fockSumSector hm M_mode hC S_fin c cfg r)
        (memLp_fockSumSector hm M_mode hC S_fin c cfg r) =
      ∑ a ∈ S_fin, c a •
        liftSectorToFock M_mode.ν r
          (fockConfigSector M_mode (cfg a) r)
          (measurable_fockConfigSector hm M_mode hC (cfg a) r)
          (memLp_fockConfigSector hm M_mode hC (cfg a) r) := by
    intro r
    clear h_single hN
    induction S_fin using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact (liftSectorToFock_congr (g₂ := 0) _ _
        measurable_const MemLp.zero
        (fun _ => Finset.sum_empty)).trans (liftSectorToFock_zero M_mode.ν r)
    | @insert a₀ s ha₀ ih =>
      rw [Finset.sum_insert ha₀, ← ih]
      have hm1 : Measurable
          ((fun _ : FockSectorDom M_mode.ν r => c a₀) *
            fockConfigSector M_mode (cfg a₀) r) :=
        measurable_const.mul (measurable_fockConfigSector hm M_mode hC (cfg a₀) r)
      have hlp1 : MemLp
          ((fun _ : FockSectorDom M_mode.ν r => c a₀) *
            fockConfigSector M_mode (cfg a₀) r) 2 (fockSectorMeasure M_mode.ν r) :=
        (memLp_fockConfigSector hm M_mode hC (cfg a₀) r).const_mul (c a₀)
      have h_eq : ∀ x, fockSumSector M_mode (insert a₀ s) c cfg r x =
          (((fun _ : FockSectorDom M_mode.ν r => c a₀) *
            fockConfigSector M_mode (cfg a₀) r) +
            fockSumSector M_mode s c cfg r) x := fun x => Finset.sum_insert ha₀
      rw [liftSectorToFock_congr _ _
          (hm1.add (measurable_fockSumSector hm M_mode hC s c cfg r))
          (hlp1.add (memLp_fockSumSector hm M_mode hC s c cfg r)) h_eq,
          liftSectorToFock_add hm1 hlp1
            (measurable_fockSumSector hm M_mode hC s c cfg r)
            (memLp_fockSumSector hm M_mode hC s c cfg r),
          liftSectorToFock_smul (c a₀)
            (measurable_fockConfigSector hm M_mode hC (cfg a₀) r)
            (memLp_fockConfigSector hm M_mode hC (cfg a₀) r)]
  have h_each : ∀ a ∈ S_fin,
      c a • fockOSMap hm M_mode hC (cfg a) =
        ∑ r ∈ Finset.range (N + 1),
          c a • liftSectorToFock M_mode.ν r
            (fockConfigSector M_mode (cfg a) r)
            (measurable_fockConfigSector hm M_mode hC (cfg a) r)
            (memLp_fockConfigSector hm M_mode hC (cfg a) r) := by
    intro a ha
    rw [h_single (cfg a) (hN a ha), Finset.smul_sum]
  rw [Finset.sum_congr rfl h_each, Finset.sum_comm]
  exact Finset.sum_congr rfl fun r _ => (h_lift_sum r).symm

lemma finset_sq_sum_le_card_mul_sum_sq {α_t : Type*} (s : Finset α_t) (f : α_t → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i ^ 2 := by
  have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h_exp : (∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2) =
      2 * ((s.card : ℝ) * ∑ i ∈ s, f i ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
    have h_pt : ∀ i ∈ s, (∑ j ∈ s, (f i - f j) ^ 2) =
        (s.card : ℝ) * f i ^ 2 - 2 * f i * (∑ j ∈ s, f j) + ∑ j ∈ s, f j ^ 2 := by
      intro i _
      have h_ij : ∀ j : α_t, (f i - f j) ^ 2 = f i ^ 2 - 2 * f i * f j + f j ^ 2 :=
        fun _ => by ring
      simp_rw [h_ij]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h_pt, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

lemma sq_integral_mul_le_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {u v : Ω → ℝ} (hu_m : Measurable u) (hv_m : Measurable v)
    (hu_nn : ∀ a, 0 ≤ u a) (hv_nn : ∀ a, 0 ≤ v a)
    (hu_sq : Integrable (fun a => u a ^ 2) μ)
    (hv_sq : Integrable (fun a => v a ^ 2) μ) :
    (∫ a, u a * v a ∂μ) ^ 2 ≤ (∫ a, u a ^ 2 ∂μ) * (∫ a, v a ^ 2 ∂μ) := by
  have hu_lp : MemLp u 2 μ :=
    (memLp_two_iff_integrable_sq_norm hu_m.aestronglyMeasurable).mpr
      (hu_sq.congr (Filter.Eventually.of_forall fun a => by
        dsimp only
        rw [Real.norm_of_nonneg (hu_nn a)]))
  have hv_lp : MemLp v 2 μ :=
    (memLp_two_iff_integrable_sq_norm hv_m.aestronglyMeasurable).mpr
      (hv_sq.congr (Filter.Eventually.of_forall fun a => by
        dsimp only
        rw [Real.norm_of_nonneg (hv_nn a)]))
  let x' : Lp ℝ 2 μ := hu_lp.toLp u
  let y' : Lp ℝ 2 μ := hv_lp.toLp v
  have h_xy : (∫ a, u a * v a ∂μ) = ⟪x', y'⟫_ℝ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu_lp.coeFn_toLp, hv_lp.coeFn_toLp] with a hxa hya
    dsimp [x', y']
    rw [hxa, hya, conj_trivial, mul_comm]
  have h_xx : (∫ a, u a ^ 2 ∂μ) = ‖x'‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hu_lp.coeFn_toLp] with a hxa
    dsimp [x']
    rw [hxa, conj_trivial, sq]
  have h_yy : (∫ a, v a ^ 2 ∂μ) = ‖y'‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hv_lp.coeFn_toLp] with a hya
    dsimp [y']
    rw [hya, conj_trivial, sq]
  have h_int_nn : 0 ≤ ∫ a, u a * v a ∂μ :=
    integral_nonneg fun a => mul_nonneg (hu_nn a) (hv_nn a)
  have h_cs : ∫ a, u a * v a ∂μ ≤ ‖x'‖ * ‖y'‖ := by
    rw [h_xy]
    exact real_inner_le_norm x' y'
  calc (∫ a, u a * v a ∂μ) ^ 2
      ≤ (‖x'‖ * ‖y'‖) ^ 2 := pow_le_pow_left₀ h_int_nn h_cs 2
    _ = ‖x'‖ ^ 2 * ‖y'‖ ^ 2 := mul_pow _ _ 2
    _ = (∫ a, u a ^ 2 ∂μ) * (∫ a, v a ^ 2 ∂μ) := by rw [h_xx, h_yy]

lemma integrable_fockSectorMeasure_iff_forall_spin {ν r : ℕ}
    {h : FockSectorDom ν r → ℝ} (hh_m : Measurable h) :
    Integrable h (fockSectorMeasure ν r) ↔
      ∀ s : Fin r → Fin ν, Integrable (fun k : Fin r → Fin 3 → ℝ => h (k, s)) volume := by
  have h_lint : (∫⁻ x : FockSectorDom ν r, ‖h x‖ₑ ∂(fockSectorMeasure ν r)) =
      ∑ s : Fin r → Fin ν, ∫⁻ k : Fin r → Fin 3 → ℝ, ‖h (k, s)‖ₑ ∂volume := by
    unfold fockSectorMeasure
    rw [lintegral_prod_symm _ hh_m.enorm.aemeasurable, lintegral_fintype]
    simp
  constructor
  · intro hh s
    refine ⟨(hh_m.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable, ?_⟩
    have h_fin := hh.hasFiniteIntegral
    unfold HasFiniteIntegral at h_fin ⊢
    rw [h_lint, ENNReal.sum_lt_top] at h_fin
    exact h_fin s (Finset.mem_univ s)
  · intro hs
    refine ⟨hh_m.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [h_lint, ENNReal.sum_lt_top]
    intro s _
    exact (hs s).hasFiniteIntegral

lemma integral_fockSectorMeasure_eq_sum_spin {ν r : ℕ}
    {h : FockSectorDom ν r → ℝ} (hh : Integrable h (fockSectorMeasure ν r)) :
    (∫ x : FockSectorDom ν r, h x ∂(fockSectorMeasure ν r)) =
      ∑ s : Fin r → Fin ν, ∫ k : Fin r → Fin 3 → ℝ, h (k, s) ∂volume := by
  unfold fockSectorMeasure at hh ⊢
  rw [integral_prod_symm _ hh, integral_fintype_count]

lemma sq_exp_neg_two_mul_sum_massShellEnergy_le {m : ℝ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) {r : ℕ} (k : Fin r → Fin 3 → ℝ) :
    (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (k b)))) ^ 2 ≤
      Real.exp (-(4 * ε * (r : ℝ) * m)) := by
  have h_sum : (r : ℝ) * m ≤ ∑ b : Fin r, massShellEnergy m (k b) := by
    calc (r : ℝ) * m = ∑ _b : Fin r, m := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ b : Fin r, massShellEnergy m (k b) :=
          Finset.sum_le_sum fun b _ => massShellEnergy_ge_mass hm (k b)
  rw [sq, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

noncomputable def conjModeBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) : ℝ :=
  (∑ α₁ : ι, ∑ c : ι, ‖S.C α₁ c‖) * M_mode.M

lemma conjModeBound_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) :
    0 ≤ conjModeBound M_mode :=
  mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) M_mode.hM

noncomputable def uCreate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (ε : ℝ)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ)
    (r : ℕ) (x : FockSectorDom M_mode.ν (r + 1)) : ℝ :=
  M_mode.M ^ 2 * Real.exp (-(4 * ε * (r : ℝ) * m)) *
    ∑ p : Fin (r + 1),
      Real.exp (-(2 * ε * massShellEnergy m (x.1 p))) *
        ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖ ^ 2

lemma norm_sq_fockCreateOp_le_uCreate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (α₀ : ι) {ε : ℝ} (hε : 0 < ε)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ)
    (r : ℕ) (x : FockSectorDom M_mode.ν (r + 1)) :
    ‖fockCreateOp M_mode α₀ ε G r x‖ ^ 2 ≤ uCreate M_mode ε G r x := by
  unfold fockCreateOp uCreate
  have hr_pos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have h_pref_sq : ‖(((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ)‖ ^ 2 = ((r : ℝ) + 1)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_pow,
        Real.sq_sqrt hr_pos.le]
  rw [norm_mul, mul_pow, h_pref_sq]
  let term : Fin (r + 1) → ℂ := fun p =>
    η ^ (p : ℕ) *
      ((Real.exp (-(ε * massShellEnergy m (x.1 p))) : ℂ) * M_mode.w (x.2 p) (x.1 p) α₀) *
      (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) : ℂ) *
      G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)
  have h_sum_sq : ‖∑ p : Fin (r + 1), term p‖ ^ 2 ≤
      ((r : ℝ) + 1) * ∑ p : Fin (r + 1), ‖term p‖ ^ 2 := by
    have h_tri := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ term) 2
    have h_cs := finset_sq_sum_le_card_mul_sum_sq Finset.univ (fun p => ‖term p‖)
    rw [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h_cs
    exact h_tri.trans h_cs
  have h_each : ∀ p : Fin (r + 1),
      ‖term p‖ ^ 2 ≤
        M_mode.M ^ 2 * Real.exp (-(4 * ε * (r : ℝ) * m)) *
          (Real.exp (-(2 * ε * massShellEnergy m (x.1 p))) *
            ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖ ^ 2) := by
    intro p
    dsimp [term]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_eta_pow M_mode.hη, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hw_sq : ‖M_mode.w (x.2 p) (x.1 p) α₀‖ ^ 2 ≤ M_mode.M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (M_mode.norm_w_le (x.2 p) (x.1 p) α₀) 2
    have he₁_sq : (Real.exp (-(ε * massShellEnergy m (x.1 p)))) ^ 2 =
        Real.exp (-(2 * ε * massShellEnergy m (x.1 p))) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have he₂_sq := sq_exp_neg_two_mul_sum_massShellEnergy_le hm hε (x.1 ∘ p.succAbove)
    calc (Real.exp (-(ε * massShellEnergy m (x.1 p))) * ‖M_mode.w (x.2 p) (x.1 p) α₀‖ *
            Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) *
            ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖) ^ 2
        = (Real.exp (-(ε * massShellEnergy m (x.1 p)))) ^ 2 *
            ‖M_mode.w (x.2 p) (x.1 p) α₀‖ ^ 2 *
            (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b))))) ^ 2 *
            ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖ ^ 2 := by ring
      _ ≤ Real.exp (-(2 * ε * massShellEnergy m (x.1 p))) * M_mode.M ^ 2 *
            Real.exp (-(4 * ε * (r : ℝ) * m)) *
            ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖ ^ 2 := by
          rw [he₁_sq]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hw_sq (Real.exp_pos _).le)
            he₂_sq (sq_nonneg _) (by positivity)
      _ = M_mode.M ^ 2 * Real.exp (-(4 * ε * (r : ℝ) * m)) *
            (Real.exp (-(2 * ε * massShellEnergy m (x.1 p))) *
              ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖ ^ 2) := by ring
  calc ((r : ℝ) + 1)⁻¹ * ‖∑ p : Fin (r + 1), term p‖ ^ 2
      ≤ ((r : ℝ) + 1)⁻¹ * (((r : ℝ) + 1) * ∑ p : Fin (r + 1), ‖term p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_sum_sq (by positivity)
    _ = ∑ p : Fin (r + 1), ‖term p‖ ^ 2 := inv_mul_cancel_left₀ hr_pos.ne' _
    _ ≤ ∑ p : Fin (r + 1),
          M_mode.M ^ 2 * Real.exp (-(4 * ε * (r : ℝ) * m)) *
            (Real.exp (-(2 * ε * massShellEnergy m (x.1 p))) *
              ‖G r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)‖ ^ 2) :=
        Finset.sum_le_sum fun p _ => h_each p
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma integrable_and_sum_spin_uCreate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) {ε : ℝ} (hε : 0 < ε)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ) (r : ℕ)
    (hG_m : Measurable (G r)) (hG_lp : MemLp (G r) 2 (fockSectorMeasure M_mode.ν r)) :
    (∀ s : Fin (r + 1) → Fin M_mode.ν,
      Integrable (fun k : Fin (r + 1) → Fin 3 → ℝ => uCreate M_mode ε G r (k, s)) volume) ∧
    (∑ s : Fin (r + 1) → Fin M_mode.ν,
      ∫ k : Fin (r + 1) → Fin 3 → ℝ, uCreate M_mode ε G r (k, s)) =
      ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
        ((M_mode.ν : ℝ) * M_mode.M ^ 2 *
          ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
        ∫ y : FockSectorDom M_mode.ν r, ‖G r y‖ ^ 2 ∂(fockSectorMeasure M_mode.ν r) := by
  have hG_sq_int : Integrable
      (fun y : FockSectorDom M_mode.ν r => ‖G r y‖ ^ 2) (fockSectorMeasure M_mode.ν r) :=
    (memLp_two_iff_integrable_sq_norm hG_m.aestronglyMeasurable).mp hG_lp
  have hG_sq_m : Measurable (fun y : FockSectorDom M_mode.ν r => ‖G r y‖ ^ 2) :=
    (hG_m.norm).pow_const 2
  have hG_spin : ∀ s' : Fin r → Fin M_mode.ν,
      Integrable (fun k' : Fin r → Fin 3 → ℝ => ‖G r (k', s')‖ ^ 2) volume :=
    (integrable_fockSectorMeasure_iff_forall_spin hG_sq_m).mp hG_sq_int
  have h_exp_int : Integrable
      (fun q₀ : Fin 3 → ℝ => Real.exp (-(2 * ε * massShellEnergy m q₀))) volume :=
    integrable_exp_neg_massShellEnergy hm (mul_pos two_pos hε)
  have h_p_int : ∀ (p : Fin (r + 1)) (s : Fin (r + 1) → Fin M_mode.ν),
      Integrable (fun k : Fin (r + 1) → Fin 3 → ℝ =>
        Real.exp (-(2 * ε * massShellEnergy m (k p))) *
          ‖G r (k ∘ p.succAbove, s ∘ p.succAbove)‖ ^ 2) volume := by
    intro p s
    let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => Fin 3 → ℝ) p).symm
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Fin 3 → ℝ) p).symm
    refine (mp.integrable_comp_emb e.measurableEmbedding).mp ?_
    have h_eq : ((fun k : Fin (r + 1) → Fin 3 → ℝ =>
        Real.exp (-(2 * ε * massShellEnergy m (k p))) *
          ‖G r (k ∘ p.succAbove, s ∘ p.succAbove)‖ ^ 2) ∘ ⇑e) =
        fun qk : (Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
          Real.exp (-(2 * ε * massShellEnergy m qk.1)) *
            ‖G r (qk.2, s ∘ p.succAbove)‖ ^ 2 := by
      ext ⟨q₀, k'⟩
      dsimp only [Function.comp_apply]
      have h1 : e (q₀, k') p = q₀ := by simp [e]
      have h2 : e (q₀, k') ∘ p.succAbove = k' := by ext b; simp [e]
      rw [h1, h2]
    change Integrable (((fun k : Fin (r + 1) → Fin 3 → ℝ =>
      Real.exp (-(2 * ε * massShellEnergy m (k p))) *
        ‖G r (k ∘ p.succAbove, s ∘ p.succAbove)‖ ^ 2) ∘ ⇑e)) (volume.prod volume)
    rw [h_eq]
    exact h_exp_int.smul_prod (hG_spin (s ∘ p.succAbove))
  have h_p_val : ∀ (p : Fin (r + 1)) (s : Fin (r + 1) → Fin M_mode.ν),
      (∫ k : Fin (r + 1) → Fin 3 → ℝ,
        Real.exp (-(2 * ε * massShellEnergy m (k p))) *
          ‖G r (k ∘ p.succAbove, s ∘ p.succAbove)‖ ^ 2) =
      (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
        ∫ k' : Fin r → Fin 3 → ℝ, ‖G r (k', s ∘ p.succAbove)‖ ^ 2 := by
    intro p s
    let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => Fin 3 → ℝ) p).symm
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Fin 3 → ℝ) p).symm
    rw [← mp.integral_comp']
    have h_eq : (fun qk : (Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
        Real.exp (-(2 * ε * massShellEnergy m (e qk p))) *
          ‖G r (e qk ∘ p.succAbove, s ∘ p.succAbove)‖ ^ 2) =
        fun qk => Real.exp (-(2 * ε * massShellEnergy m qk.1)) *
          ‖G r (qk.2, s ∘ p.succAbove)‖ ^ 2 := by
      ext ⟨q₀, k'⟩
      have h1 : e (q₀, k') p = q₀ := by simp [e]
      have h2 : e (q₀, k') ∘ p.succAbove = k' := by ext b; simp [e]
      rw [h1, h2]
    rw [h_eq, MeasureTheory.Measure.volume_eq_prod,
        MeasureTheory.integral_prod
          (fun qk : (Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
            Real.exp (-(2 * ε * massShellEnergy m qk.1)) *
              ‖G r (qk.2, s ∘ p.succAbove)‖ ^ 2)
          (h_exp_int.smul_prod (hG_spin (s ∘ p.succAbove)))]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
  refine ⟨fun s => ?_, ?_⟩
  · unfold uCreate
    exact (integrable_finsetSum Finset.univ fun p _ => h_p_int p s).const_mul _
  · have h_each_s : ∀ s : Fin (r + 1) → Fin M_mode.ν,
        (∫ k : Fin (r + 1) → Fin 3 → ℝ, uCreate M_mode ε G r (k, s)) =
          M_mode.M ^ 2 * Real.exp (-(4 * ε * (r : ℝ) * m)) *
            ∑ p : Fin (r + 1),
              (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
                ∫ k' : Fin r → Fin 3 → ℝ, ‖G r (k', s ∘ p.succAbove)‖ ^ 2 := by
      intro s
      unfold uCreate
      rw [integral_const_mul, MeasureTheory.integral_finsetSum Finset.univ fun p _ => h_p_int p s]
      refine congrArg (_ * ·) (Finset.sum_congr rfl fun p _ => h_p_val p s)
    simp_rw [h_each_s]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h_each_p : ∀ p : Fin (r + 1),
        (∑ s : Fin (r + 1) → Fin M_mode.ν,
          (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
            ∫ k' : Fin r → Fin 3 → ℝ, ‖G r (k', s ∘ p.succAbove)‖ ^ 2) =
        (M_mode.ν : ℝ) *
          (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
          ∫ y : FockSectorDom M_mode.ν r, ‖G r y‖ ^ 2 ∂(fockSectorMeasure M_mode.ν r) := by
      intro p
      let es := (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (r + 1) => Fin M_mode.ν) p).toEquiv.symm
      rw [← Equiv.sum_comp es, Fintype.sum_prod_type]
      have h_es : ∀ (s₀ : Fin M_mode.ν) (s' : Fin r → Fin M_mode.ν),
          es (s₀, s') ∘ p.succAbove = s' := by
        intro s₀ s'
        ext b
        simp [es]
      simp_rw [h_es]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum, ← integral_fockSectorMeasure_eq_sum_spin hG_sq_int]
      ring
    simp_rw [h_each_p]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
    ring

noncomputable def uAnnih {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (ε : ℝ)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ)
    (r : ℕ) (x : FockSectorDom M_mode.ν r) : ℝ :=
  ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
    ((M_mode.ν : ℝ) * conjModeBound M_mode ^ 2 *
      ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
    ∑ s₀ : Fin M_mode.ν,
      ∫ q₀ : Fin 3 → ℝ, ‖G (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)‖ ^ 2

lemma integrable_and_ae_le_uAnnih {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (α₀ : ι) {ε : ℝ} (hε : 0 < ε)
    (G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ) (r : ℕ)
    (hG_m : Measurable (G (r + 1)))
    (hG_lp : MemLp (G (r + 1)) 2 (fockSectorMeasure M_mode.ν (r + 1))) :
    (∀ s : Fin r → Fin M_mode.ν,
      Integrable (fun k : Fin r → Fin 3 → ℝ => uAnnih M_mode ε G r (k, s)) volume) ∧
    (∀ s : Fin r → Fin M_mode.ν, ∀ᵐ k : Fin r → Fin 3 → ℝ ∂volume,
      ‖fockAnnihOp M_mode α₀ ε G r (k, s)‖ ^ 2 ≤ uAnnih M_mode ε G r (k, s)) ∧
    (∑ s : Fin r → Fin M_mode.ν,
      ∫ k : Fin r → Fin 3 → ℝ, uAnnih M_mode ε G r (k, s)) =
      ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
        ((M_mode.ν : ℝ) * conjModeBound M_mode ^ 2 *
          ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
        ∫ y : FockSectorDom M_mode.ν (r + 1),
          ‖G (r + 1) y‖ ^ 2 ∂(fockSectorMeasure M_mode.ν (r + 1)) := by
  have hG_sq_int : Integrable
      (fun y : FockSectorDom M_mode.ν (r + 1) => ‖G (r + 1) y‖ ^ 2)
      (fockSectorMeasure M_mode.ν (r + 1)) :=
    (memLp_two_iff_integrable_sq_norm hG_m.aestronglyMeasurable).mp hG_lp
  have hG_sq_m : Measurable (fun y : FockSectorDom M_mode.ν (r + 1) => ‖G (r + 1) y‖ ^ 2) :=
    (hG_m.norm).pow_const 2
  have hG_spin : ∀ s_ext : Fin (r + 1) → Fin M_mode.ν,
      Integrable (fun k_ext : Fin (r + 1) → Fin 3 → ℝ =>
        ‖G (r + 1) (k_ext, s_ext)‖ ^ 2) volume :=
    (integrable_fockSectorMeasure_iff_forall_spin hG_sq_m).mp hG_sq_int
  let mp₀ := (volume_preserving_piFinSuccAbove (fun _ : Fin (r + 1) => Fin 3 → ℝ) 0).symm
  let e₀ := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Fin 3 → ℝ) 0).symm
  have he₀ : ∀ (q₀ : Fin 3 → ℝ) (k : Fin r → Fin 3 → ℝ), e₀ (q₀, k) = Fin.cons q₀ k := by
    intro q₀ k
    ext i
    refine Fin.cases ?_ ?_ i <;> simp [e₀]
  have h_prod : ∀ (s₀ : Fin M_mode.ν) (s : Fin r → Fin M_mode.ν),
      Integrable (fun qk : (Fin 3 → ℝ) × (Fin r → Fin 3 → ℝ) =>
        ‖G (r + 1) (Fin.cons qk.1 qk.2, Fin.cons s₀ s)‖ ^ 2) (volume.prod volume) := by
    intro s₀ s
    have hp := (mp₀.integrable_comp_emb e₀.measurableEmbedding).mpr (hG_spin (Fin.cons s₀ s))
    refine hp.congr (Filter.Eventually.of_forall fun ⟨q₀, k⟩ => ?_)
    change ‖G (r + 1) (e₀ (q₀, k), Fin.cons s₀ s)‖ ^ 2 =
      ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2
    rw [he₀]
  have h_right : ∀ (s₀ : Fin M_mode.ν) (s : Fin r → Fin M_mode.ν),
      Integrable (fun k : Fin r → Fin 3 → ℝ =>
        ∫ q₀ : Fin 3 → ℝ, ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2) volume :=
    fun s₀ s => (h_prod s₀ s).integral_prod_right
  have h_exp2 : Integrable
      (fun q₀ : Fin 3 → ℝ => Real.exp (-(2 * ε * massShellEnergy m q₀))) volume :=
    integrable_exp_neg_massShellEnergy hm (mul_pos two_pos hε)
  refine ⟨fun s => ?_, fun s => ?_, ?_⟩
  · unfold uAnnih
    exact (integrable_finsetSum Finset.univ fun s₀ _ => h_right s₀ s).const_mul _
  · have h_ae : ∀ᵐ k : Fin r → Fin 3 → ℝ ∂volume, ∀ s₀ : Fin M_mode.ν,
        Integrable (fun q₀ : Fin 3 → ℝ =>
          ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2) volume :=
      Filter.eventually_all.mpr fun s₀ =>
        ((integrable_prod_iff' (h_prod s₀ s).1).mp (h_prod s₀ s)).1
    filter_upwards [h_ae] with k hk
    unfold fockAnnihOp uAnnih
    have hr_nn : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
    have h_sqrt_sq : ‖(Real.sqrt (r + 1 : ℝ) : ℂ)‖ ^ 2 = (r : ℝ) + 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr_nn]
    have h_damp_sq :
        ‖(Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (k b))) : ℂ)‖ ^ 2 ≤
          Real.exp (-(4 * ε * (r : ℝ) * m)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact sq_exp_neg_two_mul_sum_massShellEnergy_le hm hε k
    let I_s : Fin M_mode.ν → ℂ := fun s₀ =>
      ∫ q₀ : Fin 3 → ℝ,
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)
    have h_I_sq : ∀ s₀ : Fin M_mode.ν,
        ‖I_s s₀‖ ^ 2 ≤
          (conjModeBound M_mode ^ 2 *
            ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
            ∫ q₀ : Fin 3 → ℝ, ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2 := by
      intro s₀
      let u : (Fin 3 → ℝ) → ℝ := fun q₀ =>
        conjModeBound M_mode * Real.exp (-(ε * massShellEnergy m q₀))
      let v : (Fin 3 → ℝ) → ℝ := fun q₀ =>
        ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖
      have hu_m : Measurable u :=
        measurable_const.mul
          (Real.continuous_exp.comp
            ((continuous_const.mul (continuous_massShellEnergy m)).neg)).measurable
      have h_cons_m : Measurable
          (fun q₀ : Fin 3 → ℝ =>
            ((Fin.cons q₀ k : Fin (r + 1) → Fin 3 → ℝ),
              (Fin.cons s₀ s : Fin (r + 1) → Fin M_mode.ν))) :=
        (measurable_finCons_left k).prodMk measurable_const
      have hv_m : Measurable v := (hG_m.comp h_cons_m).norm
      have hu_sq_eq : (fun q₀ : Fin 3 → ℝ => u q₀ ^ 2) =
          fun q₀ => conjModeBound M_mode ^ 2 * Real.exp (-(2 * ε * massShellEnergy m q₀)) := by
        ext q₀
        dsimp [u]
        rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
        ring_nf
      have hu_sq : Integrable (fun q₀ => u q₀ ^ 2) volume := by
        rw [hu_sq_eq]
        exact h_exp2.const_mul _
      have hv_sq : Integrable (fun q₀ => v q₀ ^ 2) volume := hk s₀
      have huv_int : Integrable (fun q₀ => u q₀ * v q₀) volume := by
        refine (hu_sq.add hv_sq).mono' (hu_m.mul hv_m).aestronglyMeasurable
          (Filter.Eventually.of_forall fun q₀ => ?_)
        have hu0 : 0 ≤ u q₀ := mul_nonneg (conjModeBound_nonneg M_mode) (Real.exp_pos _).le
        have hv0 : 0 ≤ v q₀ := norm_nonneg _
        rw [Real.norm_of_nonneg (mul_nonneg hu0 hv0)]
        change u q₀ * v q₀ ≤ u q₀ ^ 2 + v q₀ ^ 2
        nlinarith [sq_nonneg (u q₀ - v q₀), mul_nonneg hu0 hv0]
      have h_norm_le : ‖I_s s₀‖ ≤ ∫ q₀ : Fin 3 → ℝ, u q₀ * v q₀ := by
        refine (norm_integral_le_integral_norm _).trans ?_
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          huv_int (Filter.Eventually.of_forall fun q₀ => ?_)
        dsimp only [u, v]
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc Real.exp (-(ε * massShellEnergy m q₀)) * ‖conjMode M_mode s₀ q₀ α₀‖
            ≤ Real.exp (-(ε * massShellEnergy m q₀)) * conjModeBound M_mode :=
              mul_le_mul_of_nonneg_left (norm_conjMode_le M_mode s₀ q₀ α₀) (Real.exp_pos _).le
          _ = conjModeBound M_mode * Real.exp (-(ε * massShellEnergy m q₀)) := mul_comm _ _
      calc ‖I_s s₀‖ ^ 2
          ≤ (∫ q₀ : Fin 3 → ℝ, u q₀ * v q₀) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h_norm_le 2
        _ ≤ (∫ q₀ : Fin 3 → ℝ, u q₀ ^ 2) * ∫ q₀ : Fin 3 → ℝ, v q₀ ^ 2 :=
            sq_integral_mul_le_of_nonneg hu_m hv_m
              (fun _ => mul_nonneg (conjModeBound_nonneg M_mode) (Real.exp_pos _).le)
              (fun _ => norm_nonneg _) hu_sq hv_sq
        _ = (conjModeBound M_mode ^ 2 *
              ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
              ∫ q₀ : Fin 3 → ℝ, ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2 := by
            rw [hu_sq_eq, integral_const_mul]
    have h_sum_I : ‖∑ s₀ : Fin M_mode.ν, I_s s₀‖ ^ 2 ≤
        (M_mode.ν : ℝ) * ∑ s₀ : Fin M_mode.ν, ‖I_s s₀‖ ^ 2 := by
      have h_tri := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ I_s) 2
      have h_cs := finset_sq_sum_le_card_mul_sum_sq Finset.univ (fun s₀ => ‖I_s s₀‖)
      rw [Finset.card_univ, Fintype.card_fin] at h_cs
      exact h_tri.trans h_cs
    rw [norm_mul, norm_mul, mul_pow, mul_pow, h_sqrt_sq]
    calc ((r : ℝ) + 1) *
          ‖(Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (k b))) : ℂ)‖ ^ 2 *
          ‖∑ s₀ : Fin M_mode.ν, I_s s₀‖ ^ 2
        ≤ ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
            ((M_mode.ν : ℝ) * ∑ s₀ : Fin M_mode.ν, ‖I_s s₀‖ ^ 2) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left h_damp_sq hr_nn)
            h_sum_I (sq_nonneg _) (by positivity)
      _ ≤ ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
            ((M_mode.ν : ℝ) *
              ∑ s₀ : Fin M_mode.ν,
                (conjModeBound M_mode ^ 2 *
                  ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) *
                  ∫ q₀ : Fin 3 → ℝ, ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s₀ _ => h_I_sq s₀) (by positivity)
      _ = _ := by
          rw [← Finset.mul_sum]
          ring
  · let pref_a : ℝ := ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
      ((M_mode.ν : ℝ) * conjModeBound M_mode ^ 2 *
        ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀)))
    have h_each_s : ∀ s : Fin r → Fin M_mode.ν,
        (∫ k : Fin r → Fin 3 → ℝ, uAnnih M_mode ε G r (k, s)) =
          pref_a *
            ∑ s₀ : Fin M_mode.ν,
              ∫ k_ext : Fin (r + 1) → Fin 3 → ℝ,
                ‖G (r + 1) (k_ext, Fin.cons s₀ s)‖ ^ 2 := by
      intro s
      unfold uAnnih
      change (∫ k : Fin r → Fin 3 → ℝ,
        pref_a * ∑ s₀ : Fin M_mode.ν,
          ∫ q₀ : Fin 3 → ℝ, ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2) = _
      rw [integral_const_mul,
          MeasureTheory.integral_finsetSum Finset.univ fun s₀ _ => h_right s₀ s]
      refine congrArg (pref_a * ·) (Finset.sum_congr rfl fun s₀ _ => ?_)
      rw [← integral_prod_symm _ (h_prod s₀ s), ← mp₀.integral_comp']
      refine integral_congr_ae (Filter.Eventually.of_forall fun ⟨q₀, k⟩ => ?_)
      change ‖G (r + 1) (Fin.cons q₀ k, Fin.cons s₀ s)‖ ^ 2 =
        ‖G (r + 1) (e₀ (q₀, k), Fin.cons s₀ s)‖ ^ 2
      rw [he₀]
    simp_rw [h_each_s, ← Finset.mul_sum]
    refine congrArg (pref_a * ·) ?_
    rw [Finset.sum_comm]
    let es₀ := (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (r + 1) => Fin M_mode.ν) 0).toEquiv.symm
    have h_es₀ : ∀ (s₀ : Fin M_mode.ν) (s : Fin r → Fin M_mode.ν),
        Fin.cons s₀ s = es₀ (s₀, s) := by
      intro s₀ s
      ext i
      refine Fin.cases ?_ ?_ i <;>
        simp [es₀]
    simp_rw [h_es₀]
    rw [← Fintype.sum_prod_type (f := fun ps : Fin M_mode.ν × (Fin r → Fin M_mode.ν) =>
      ∫ k_ext : Fin (r + 1) → Fin 3 → ℝ, ‖G (r + 1) (k_ext, es₀ ps)‖ ^ 2),
      Equiv.sum_comp es₀ (fun s_ext =>
        ∫ k_ext : Fin (r + 1) → Fin 3 → ℝ, ‖G (r + 1) (k_ext, s_ext)‖ ^ 2),
      ← integral_fockSectorMeasure_eq_sum_spin hG_sq_int]

noncomputable def prependShiftConfig {ι : Type*} (α₀ : ι) (ε : ℝ) (hε : 0 < ε)
    (A : OSConfig ι) : OSConfig ι :=
  osFieldPrependConfig α₀ (euclidTimeVec ε + euclidSpatialVec 0)
    (time_pos_euclidTimeVec_add_spatial hε 0) (osConfigTimeShift ε hε.le A)

lemma osPrependShiftLM_zero_osBasisPre {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    (D : OSReflectionPositiveData R_rep S) (α₀ : ι) (ε : ℝ) (hε : 0 < ε)
    (A : OSConfig ι) :
    osPrependShiftLM D α₀ 0 ε hε (osBasisPre D A) =
      osBasisPre D (prependShiftConfig α₀ ε hε A) := by
  unfold osPrependShiftLM osTimeShiftLM osFieldPrependLM prependShiftConfig
  rw [LinearMap.comp_apply, osLiftConfigMap_osBasisPre, osLiftConfigMap_osBasisPre]

lemma prependShiftConfig_val {ι : Type*} (α₀ : ι) (ε : ℝ) (hε : 0 < ε)
    (A : OSConfig ι) :
    (prependShiftConfig α₀ ε hε A).2.2.val =
      Fin.cons (euclidTimeVec ε) (fun i => A.2.2.val i + euclidTimeVec (2 * ε)) := by
  have hx₀ : euclidTimeVec ε + euclidSpatialVec 0 = euclidTimeVec ε := by
    rw [euclidSpatialVec_zero, add_zero]
  change osPrependPoint A.1 (euclidTimeVec ε + euclidSpatialVec 0)
    (fun i => A.2.2.val i + euclidTimeVec ε) = _
  rw [hx₀]
  ext i μ
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [osPrependPoint, Fin.cons_succ, Pi.add_apply, euclidTimeVec]
    split_ifs <;> ring

lemma integrable_annih_fockConfigSector {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (α₀ : ι) {ε : ℝ} (hε : 0 < ε) (A : OSConfig ι) (r : ℕ)
    (x : FockSectorDom M_mode.ν r) (s₀ : Fin M_mode.ν) :
    Integrable (fun q₀ : Fin 3 → ℝ =>
      ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
        fockConfigSector M_mode A (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)) volume := by
  have h_πL : ∀ (π : Equiv.Perm (Fin (r + 1))) (L' : PartialPairing A.1 (r + 1)),
      Integrable (fun q₀ : Fin 3 → ℝ =>
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          (η ^ permInversions π *
            fockPartialTerm M_mode A.2.1 (euclidLaplace A.2.2.val) L'
              (fockSectorPermEquiv M_mode.ν (r + 1) π
                (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) volume := by
    intro π L'
    obtain ⟨B_L, _, hBL⟩ :=
      norm_fockPartialTerm_euclidLaplace_le_const hm M_mode hC A.2.1 A.2.2.2 L'
    let C_c : ℝ := conjModeBound M_mode * B_L
    have h_dom : Integrable
        (fun q₀ : Fin 3 → ℝ => C_c * Real.exp (-(ε * massShellEnergy m q₀))) volume :=
      (integrable_exp_neg_massShellEnergy hm hε).const_mul C_c
    have h_cons_meas : Measurable
        (fun q₀ : Fin 3 → ℝ =>
          ((Fin.cons q₀ x.1 : Fin (r + 1) → Fin 3 → ℝ),
            (Fin.cons s₀ x.2 : Fin (r + 1) → Fin M_mode.ν))) :=
      (measurable_finCons_left x.1).prodMk measurable_const
    have h_meas : Measurable (fun q₀ : Fin 3 → ℝ =>
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          (η ^ permInversions π *
            fockPartialTerm M_mode A.2.1 (euclidLaplace A.2.2.val) L'
              (fockSectorPermEquiv M_mode.ν (r + 1) π
                (Fin.cons q₀ x.1, Fin.cons s₀ x.2)))) :=
      (((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp ((continuous_const.mul (continuous_massShellEnergy m)).neg))
          ).measurable).mul (measurable_conjMode M_mode s₀ α₀)).mul
        (measurable_const.mul
          ((measurable_fockPartialTerm M_mode hC A.2.1
            (partialMomentumBound_euclidLaplace hm A.2.2.2) L').comp
            ((fockSectorPermEquiv M_mode.ν (r + 1) π).measurable.comp h_cons_meas)))
    refine h_dom.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun q₀ => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_eta_pow M_mode.hη, one_mul,
        Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-(ε * massShellEnergy m q₀)) * ‖conjMode M_mode s₀ q₀ α₀‖ *
          ‖fockPartialTerm M_mode A.2.1 (euclidLaplace A.2.2.val) L'
            (fockSectorPermEquiv M_mode.ν (r + 1) π (Fin.cons q₀ x.1, Fin.cons s₀ x.2))‖
        ≤ Real.exp (-(ε * massShellEnergy m q₀)) * conjModeBound M_mode * B_L :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (norm_conjMode_le M_mode s₀ q₀ α₀) (Real.exp_pos _).le)
            (hBL _) (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (conjModeBound_nonneg M_mode))
      _ = C_c * Real.exp (-(ε * massShellEnergy m q₀)) := by dsimp [C_c]; ring
  have h_eq : (fun q₀ : Fin 3 → ℝ =>
      ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
        fockConfigSector M_mode A (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)) =
      fun q₀ =>
        ((((r + 1).factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
          ∑ π : Equiv.Perm (Fin (r + 1)), ∑ L' : PartialPairing A.1 (r + 1),
            ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
              (η ^ permInversions π *
                fockPartialTerm M_mode A.2.1 (euclidLaplace A.2.2.val) L'
                  (fockSectorPermEquiv M_mode.ν (r + 1) π
                    (Fin.cons q₀ x.1, Fin.cons s₀ x.2))) := by
    ext q₀
    unfold fockConfigSector symmSector fockRawSector
    simp_rw [← Finset.mul_sum]
    ring
  rw [h_eq]
  exact (integrable_finsetSum Finset.univ fun π _ =>
    integrable_finsetSum Finset.univ fun L' _ => h_πL π L').const_mul _

lemma sum_fockCreateOp_fockConfigSector_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (α₀ : ι) (ε : ℝ)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    (r : ℕ) (x : FockSectorDom M_mode.ν (r + 1)) :
    (∑ a ∈ S_fin, c a *
      fockCreateOp M_mode α₀ ε (fockConfigSector M_mode (cfg a)) r x) =
      fockCreateOp M_mode α₀ ε (fockSumSector M_mode S_fin c cfg) r x := by
  unfold fockCreateOp fockSumSector
  have h_pt : ∀ a ∈ S_fin,
      c a * ((((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ p : Fin (r + 1),
          η ^ (p : ℕ) *
            ((Real.exp (-(ε * massShellEnergy m (x.1 p))) : ℂ) * M_mode.w (x.2 p) (x.1 p) α₀) *
            (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) : ℂ) *
            fockConfigSector M_mode (cfg a) r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)) =
      (((Real.sqrt (r + 1 : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ p : Fin (r + 1),
          (η ^ (p : ℕ) *
            ((Real.exp (-(ε * massShellEnergy m (x.1 p))) : ℂ) * M_mode.w (x.2 p) (x.1 p) α₀) *
            (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 (p.succAbove b)))) : ℂ)) *
            (c a * fockConfigSector M_mode (cfg a) r (x.1 ∘ p.succAbove, x.2 ∘ p.succAbove)) := by
    intro a _
    rw [← mul_assoc, mul_comm (c a), mul_assoc, Finset.mul_sum]
    refine congrArg (_ * ·) (Finset.sum_congr rfl fun p _ => ?_)
    ring
  rw [Finset.sum_congr rfl h_pt, ← Finset.mul_sum, Finset.sum_comm]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun p _ => ?_)
  rw [← Finset.mul_sum]

lemma sum_fockAnnihOp_fockConfigSector_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (α₀ : ι) {ε : ℝ} (hε : 0 < ε)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    (r : ℕ) (x : FockSectorDom M_mode.ν r) :
    (∑ a ∈ S_fin, c a *
      fockAnnihOp M_mode α₀ ε (fockConfigSector M_mode (cfg a)) r x) =
      fockAnnihOp M_mode α₀ ε (fockSumSector M_mode S_fin c cfg) r x := by
  unfold fockAnnihOp fockSumSector
  let pref : ℂ :=
    (Real.sqrt (r + 1 : ℝ) : ℂ) *
      (Real.exp (-(2 * ε * ∑ b : Fin r, massShellEnergy m (x.1 b))) : ℂ)
  change (∑ a ∈ S_fin, c a *
    (pref * ∑ s₀ : Fin M_mode.ν,
      ∫ q₀ : Fin 3 → ℝ,
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          fockConfigSector M_mode (cfg a) (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2))) =
    pref * ∑ s₀ : Fin M_mode.ν,
      ∫ q₀ : Fin 3 → ℝ,
        ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
          ∑ a ∈ S_fin, c a *
            fockConfigSector M_mode (cfg a) (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)
  have h_pt : ∀ a ∈ S_fin,
      c a * (pref * ∑ s₀ : Fin M_mode.ν,
        ∫ q₀ : Fin 3 → ℝ,
          ((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
            fockConfigSector M_mode (cfg a) (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)) =
      pref * ∑ s₀ : Fin M_mode.ν,
        ∫ q₀ : Fin 3 → ℝ,
          c a * (((Real.exp (-(ε * massShellEnergy m q₀)) : ℂ) * conjMode M_mode s₀ q₀ α₀) *
            fockConfigSector M_mode (cfg a) (r + 1) (Fin.cons q₀ x.1, Fin.cons s₀ x.2)) := by
    intro a _
    rw [← mul_assoc, mul_comm (c a), mul_assoc, Finset.mul_sum]
    refine congrArg (pref * ·) (Finset.sum_congr rfl fun s₀ _ => ?_)
    rw [← integral_const_mul]
  rw [Finset.sum_congr rfl h_pt, ← Finset.mul_sum, Finset.sum_comm]
  refine congrArg (pref * ·) (Finset.sum_congr rfl fun s₀ _ => ?_)
  rw [← MeasureTheory.integral_finsetSum S_fin fun a _ =>
    (integrable_annih_fockConfigSector hm M_mode hC α₀ hε (cfg a) r x s₀).const_mul (c a)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q₀ => ?_)
  dsimp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma fockSumSector_prependShiftConfig_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (α₀ : ι) {ε : ℝ} (hε : 0 < ε)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    (x : FockSectorDom M_mode.ν 0) :
    fockSumSector M_mode S_fin c (fun a => prependShiftConfig α₀ ε hε (cfg a)) 0 x =
      fockAnnihOp M_mode α₀ ε (fockSumSector M_mode S_fin c cfg) 0 x := by
  rw [← sum_fockAnnihOp_fockConfigSector_eq hm M_mode hC α₀ hε S_fin c cfg 0 x]
  unfold fockSumSector
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  unfold fockConfigSector
  rw [prependShiftConfig_val α₀ ε hε (cfg a)]
  exact symmSector_prependShift_zero_eq hm M_mode hC α₀ (cfg a).2.1 hε (cfg a).2.2.2 x

lemma fockSumSector_prependShiftConfig_succ_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (α₀ : ι) {ε : ℝ} (hε : 0 < ε)
    {κ : Type*} (S_fin : Finset κ) (c : κ → ℂ) (cfg : κ → OSConfig ι)
    (r : ℕ) (x : FockSectorDom M_mode.ν (r + 1)) :
    fockSumSector M_mode S_fin c (fun a => prependShiftConfig α₀ ε hε (cfg a)) (r + 1) x =
      fockCreateOp M_mode α₀ ε (fockSumSector M_mode S_fin c cfg) r x +
        fockAnnihOp M_mode α₀ ε (fockSumSector M_mode S_fin c cfg) (r + 1) x := by
  rw [← sum_fockCreateOp_fockConfigSector_eq M_mode α₀ ε S_fin c cfg r x,
      ← sum_fockAnnihOp_fockConfigSector_eq hm M_mode hC α₀ hε S_fin c cfg (r + 1) x,
      ← Finset.sum_add_distrib]
  unfold fockSumSector
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add]
  congr 1
  unfold fockConfigSector
  rw [prependShiftConfig_val α₀ ε hε (cfg a)]
  exact symmSector_prependShift_succ_eq hm M_mode hC α₀ (cfg a).2.1 hε (cfg a).2.2.2 x

lemma integral_exp_neg_two_mul_massShellEnergy_le {m : ℝ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) ≤
      (24 * (1 / m + 1) ^ 4 * ∫ p : Fin 3 → ℝ, ((1 + ‖p‖) ^ 4)⁻¹) *
        (1 + ε⁻¹) ^ 4 := by
  let c : ℝ := 2 * ε
  have hc : 0 < c := by positivity
  let K : ℝ := (1 / m + 1) / c
  have hK_nn : 0 ≤ K := by positivity
  have hc_inv : c⁻¹ ≤ 1 + ε⁻¹ := by
    have h1 : (2 * ε)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (by linarith)
    have h2 : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
    dsimp [c]
    linarith
  have hK_pow : K ^ 4 ≤ (1 / m + 1) ^ 4 * (1 + ε⁻¹) ^ 4 := by
    dsimp [K]
    rw [div_eq_mul_inv, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hc_inv 4) (by positivity)
  have h_pt : ∀ p : Fin 3 → ℝ,
      Real.exp (-(2 * ε * massShellEnergy m p)) ≤
        (24 * ((1 / m + 1) ^ 4 * (1 + ε⁻¹) ^ 4)) * ((1 + ‖p‖) ^ 4)⁻¹ := by
    intro p
    have hω_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
    have hcω_nn : 0 ≤ c * massShellEnergy m p := mul_nonneg hc.le hω_pos.le
    have h_lin : 1 + ‖p‖ ≤ K * (c * massShellEnergy m p) := by
      have h1 := one_add_norm_le_scale_massShellEnergy hm p
      have hK_eq : K * (c * massShellEnergy m p) =
          (1 / m + 1) * massShellEnergy m p := by
        dsimp [K]
        field_simp [hc.ne']
      linarith
    have h_pow : (1 + ‖p‖) ^ 4 ≤ K ^ 4 * (c * massShellEnergy m p) ^ 4 :=
      (pow_le_pow_left₀ (by positivity) h_lin 4).trans_eq (mul_pow _ _ 4)
    have h_exp_fac :
        (c * massShellEnergy m p) ^ 4 / (24 : ℝ) ≤
          Real.exp (c * massShellEnergy m p) := by
      simpa [Nat.factorial] using
        Real.pow_div_factorial_le_exp (c * massShellEnergy m p) hcω_nn 4
    have h_prod :
        (1 + ‖p‖) ^ 4 * Real.exp (-(c * massShellEnergy m p)) ≤ 24 * K ^ 4 := by
      calc (1 + ‖p‖) ^ 4 * Real.exp (-(c * massShellEnergy m p))
          ≤ (K ^ 4 * (c * massShellEnergy m p) ^ 4) *
              Real.exp (-(c * massShellEnergy m p)) :=
            mul_le_mul_of_nonneg_right h_pow (Real.exp_pos _).le
        _ = (24 * K ^ 4) * (((c * massShellEnergy m p) ^ 4 / 24) *
              Real.exp (-(c * massShellEnergy m p))) := by ring
        _ ≤ (24 * K ^ 4) *
              (Real.exp (c * massShellEnergy m p) *
                Real.exp (-(c * massShellEnergy m p))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h_exp_fac (Real.exp_pos _).le) (by positivity)
        _ = 24 * K ^ 4 := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have h_pos4 : 0 < (1 + ‖p‖) ^ 4 := by positivity
    have h_le_K : Real.exp (-(c * massShellEnergy m p)) ≤
        (24 * K ^ 4) * ((1 + ‖p‖) ^ 4)⁻¹ :=
      (le_mul_inv_iff₀' h_pos4).mpr h_prod
    exact h_le_K.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK_pow (by positivity)) (by positivity))
  calc (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀)))
      ≤ ∫ p : Fin 3 → ℝ,
          (24 * ((1 / m + 1) ^ 4 * (1 + ε⁻¹) ^ 4)) * ((1 + ‖p‖) ^ 4)⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (integrable_massShellDecay.const_mul _) (Filter.Eventually.of_forall h_pt)
    _ = (24 * (1 / m + 1) ^ 4 * ∫ p : Fin 3 → ℝ, ((1 + ‖p‖) ^ 4)⁻¹) *
          (1 + ε⁻¹) ^ 4 := by
        rw [integral_const_mul]
        ring

lemma succ_mul_exp_neg_four_le {m : ℝ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) ≤
      (1 + (4 * m)⁻¹) * (1 + ε⁻¹) := by
  let u : ℝ := 4 * ε * (r : ℝ) * m
  have hu_nn : 0 ≤ u := by positivity
  have h_u_le : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have h_prod : u * Real.exp (-u) ≤ 1 := by
    calc u * Real.exp (-u)
        ≤ Real.exp u * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right h_u_le (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h4εm : 0 < 4 * m * ε := by positivity
  have hr_le : (r : ℝ) * Real.exp (-u) ≤ (4 * m)⁻¹ * ε⁻¹ := by
    have h_mul : (4 * m * ε) * ((r : ℝ) * Real.exp (-u)) ≤
        (4 * m * ε) * ((4 * m)⁻¹ * ε⁻¹) := by
      have h_rhs : (4 * m * ε) * ((4 * m)⁻¹ * ε⁻¹) = 1 := by
        field_simp [hm.ne', hε.ne']
      have h_lhs : (4 * m * ε) * ((r : ℝ) * Real.exp (-u)) = u * Real.exp (-u) := by
        dsimp [u]
        ring
      rw [h_lhs, h_rhs]
      exact h_prod
    exact le_of_mul_le_mul_left h_mul h4εm
  have h1_le : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h_inv_m : 0 ≤ (4 * m)⁻¹ := inv_nonneg.mpr (by positivity)
  have h_inv_ε : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  calc ((r : ℝ) + 1) * Real.exp (-u)
      = (r : ℝ) * Real.exp (-u) + Real.exp (-u) := add_one_mul _ _
    _ ≤ (4 * m)⁻¹ * ε⁻¹ + 1 := add_le_add hr_le h1_le
    _ ≤ (1 + (4 * m)⁻¹) * (1 + ε⁻¹) := by nlinarith

lemma sum_range_le_four_mul_of_rec {N : ℕ} {J J' : ℕ → ℝ} {C_op : ℝ}
    (hCop : 0 ≤ C_op) (hJ_nn : ∀ r, 0 ≤ J r)
    (hJ_gt : ∀ s, N < s → J s = 0)
    (hJ'_zero : J' 0 ≤ 2 * C_op * J 1)
    (hJ'_succ : ∀ r, J' (r + 1) ≤ 2 * C_op * J r + 2 * C_op * J (r + 2)) :
    (∑ r ∈ Finset.range (N + 2), J' r) ≤ 4 * C_op * ∑ r ∈ Finset.range (N + 1), J r := by
  have hJ_N1 : J (N + 1) = 0 := hJ_gt (N + 1) (Nat.lt_succ_self N)
  have hJ_N2 : J (N + 2) = 0 := hJ_gt (N + 2) (by omega)
  have h_tail_sum :
      J 1 + (∑ r ∈ Finset.range (N + 1), J (r + 2)) ≤ ∑ r ∈ Finset.range (N + 1), J r := by
    have hs1 : J 1 + (∑ r ∈ Finset.range (N + 1), J (r + 2)) =
        ∑ r ∈ Finset.range (N + 2), J (r + 1) := by
      rw [Finset.sum_range_succ' (fun r => J (r + 1)) (N + 1), add_comm]
    have hs2 : (∑ r ∈ Finset.range (N + 2), J (r + 1)) + J 0 =
        ∑ r ∈ Finset.range (N + 3), J r :=
      (Finset.sum_range_succ' J (N + 2)).symm
    have hs3 : (∑ r ∈ Finset.range (N + 3), J r) = ∑ r ∈ Finset.range (N + 1), J r := by
      rw [Finset.sum_range_succ J (N + 2), Finset.sum_range_succ J (N + 1), hJ_N1, hJ_N2,
          add_zero, add_zero]
    linarith [hJ_nn 0]
  rw [Finset.sum_range_succ' J' (N + 1)]
  have h_rec_sum : (∑ r ∈ Finset.range (N + 1), J' (r + 1)) ≤
      (2 * C_op) * (∑ r ∈ Finset.range (N + 1), J r) +
        (2 * C_op) * ∑ r ∈ Finset.range (N + 1), J (r + 2) := by
    calc (∑ r ∈ Finset.range (N + 1), J' (r + 1))
        ≤ ∑ r ∈ Finset.range (N + 1), (2 * C_op * J r + 2 * C_op * J (r + 2)) :=
          Finset.sum_le_sum fun r _ => hJ'_succ r
      _ = (2 * C_op) * (∑ r ∈ Finset.range (N + 1), J r) +
            (2 * C_op) * ∑ r ∈ Finset.range (N + 1), J (r + 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h_mul_tail :
      (2 * C_op) * (J 1 + ∑ r ∈ Finset.range (N + 1), J (r + 2)) ≤
        (2 * C_op) * ∑ r ∈ Finset.range (N + 1), J r :=
    mul_le_mul_of_nonneg_left h_tail_sum (mul_nonneg zero_le_two hCop)
  linarith

lemma exists_wickMassShell_damped_const {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ C_op : ℝ, 0 ≤ C_op ∧
          C₀ ^ 2 * ((1 + ε⁻¹) ^ 3) ^ 2 = 4 * C_op ∧
          (∀ r : ℕ,
            ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
              ((M_mode.ν : ℝ) * M_mode.M ^ 2 *
                ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) ≤ C_op) ∧
          (∀ r : ℕ,
            ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
              ((M_mode.ν : ℝ) * conjModeBound M_mode ^ 2 *
                ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) ≤ C_op) := by
  obtain ⟨B_mode, hB_nn, hM_sq, hconj_sq⟩ :
      ∃ B_mode : ℝ, 0 ≤ B_mode ∧ M_mode.M ^ 2 ≤ B_mode ^ 2 ∧
        conjModeBound M_mode ^ 2 ≤ B_mode ^ 2 :=
    ⟨max M_mode.M (conjModeBound M_mode), le_trans M_mode.hM (le_max_left _ _),
      pow_le_pow_left₀ M_mode.hM (le_max_left _ _) 2,
      pow_le_pow_left₀ (conjModeBound_nonneg M_mode) (le_max_right _ _) 2⟩
  obtain ⟨C_I, hCI_nn, hI_le⟩ :
      ∃ C_I : ℝ, 0 ≤ C_I ∧ ∀ {ε : ℝ}, 0 < ε →
        (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) ≤
          C_I * (1 + ε⁻¹) ^ 4 :=
    ⟨24 * (1 / m + 1) ^ 4 * ∫ p : Fin 3 → ℝ, ((1 + ‖p‖) ^ 4)⁻¹,
      mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity),
      fun hε => integral_exp_neg_two_mul_massShellEnergy_le hm hε⟩
  obtain ⟨C_r, hCr_nn, hr_le⟩ :
      ∃ C_r : ℝ, 0 ≤ C_r ∧ ∀ {ε : ℝ}, 0 < ε → ∀ r : ℕ,
        ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) ≤ C_r * (1 + ε⁻¹) :=
    ⟨1 + (4 * m)⁻¹, by positivity, fun hε r => succ_mul_exp_neg_four_le hm hε r⟩
  let C_base : ℝ := C_r * ((M_mode.ν : ℝ) * B_mode ^ 2 * C_I)
  have hCb_nn : 0 ≤ C_base := by positivity
  refine ⟨Real.sqrt (4 * C_base), Real.sqrt_nonneg _, fun {ε} hε => ?_⟩
  refine ⟨C_base * (1 + ε⁻¹) ^ 6, by positivity, ?_, ?_, ?_⟩
  · rw [Real.sq_sqrt (mul_nonneg (by positivity) hCb_nn), ← pow_mul]
    ring
  · intro r
    have hI_nn : 0 ≤ ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀)) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have h1_ge : 1 ≤ 1 + ε⁻¹ := by linarith [inv_nonneg.mpr hε.le]
    have h_pow56 : (1 + ε⁻¹) ^ 5 ≤ (1 + ε⁻¹) ^ 6 := pow_le_pow_right₀ h1_ge (by decide)
    have h_mid : (M_mode.ν : ℝ) * M_mode.M ^ 2 *
        (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) ≤
        (M_mode.ν : ℝ) * B_mode ^ 2 * (C_I * (1 + ε⁻¹) ^ 4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hM_sq (Nat.cast_nonneg _))
        (hI_le hε) hI_nn (by positivity)
    calc ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
          ((M_mode.ν : ℝ) * M_mode.M ^ 2 *
            ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀)))
        ≤ (C_r * (1 + ε⁻¹)) *
            ((M_mode.ν : ℝ) * B_mode ^ 2 * (C_I * (1 + ε⁻¹) ^ 4)) :=
          mul_le_mul (hr_le hε r) h_mid (by positivity) (by positivity)
      _ = C_base * (1 + ε⁻¹) ^ 5 := by dsimp [C_base]; ring
      _ ≤ C_base * (1 + ε⁻¹) ^ 6 := mul_le_mul_of_nonneg_left h_pow56 hCb_nn
  · intro r
    have hI_nn : 0 ≤ ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀)) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    have h1_ge : 1 ≤ 1 + ε⁻¹ := by linarith [inv_nonneg.mpr hε.le]
    have h_pow56 : (1 + ε⁻¹) ^ 5 ≤ (1 + ε⁻¹) ^ 6 := pow_le_pow_right₀ h1_ge (by decide)
    have h_mid : (M_mode.ν : ℝ) * conjModeBound M_mode ^ 2 *
        (∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀))) ≤
        (M_mode.ν : ℝ) * B_mode ^ 2 * (C_I * (1 + ε⁻¹) ^ 4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hconj_sq (Nat.cast_nonneg _))
        (hI_le hε) hI_nn (by positivity)
    calc ((r : ℝ) + 1) * Real.exp (-(4 * ε * (r : ℝ) * m)) *
          ((M_mode.ν : ℝ) * conjModeBound M_mode ^ 2 *
            ∫ q₀ : Fin 3 → ℝ, Real.exp (-(2 * ε * massShellEnergy m q₀)))
        ≤ (C_r * (1 + ε⁻¹)) *
            ((M_mode.ν : ℝ) * B_mode ^ 2 * (C_I * (1 + ε⁻¹) ^ 4)) :=
          mul_le_mul (hr_le hε r) h_mid (by positivity) (by positivity)
      _ = C_base * (1 + ε⁻¹) ^ 5 := by dsimp [C_base]; ring
      _ ≤ C_base * (1 + ε⁻¹) ^ 6 := mul_le_mul_of_nonneg_left h_pow56 hCb_nn

theorem wickMassShellOSDampedFieldBounded_of_eq_on_orderedEuclidN
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (D : OSReflectionPositiveData R_rep S)
    (htrans : OSTranslationInvariant D.𝒮)
    (hD : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = wickMassShellS m hm η C hC n α x) :
    OSDampedFieldBounded D := by
  refine osDampedFieldBounded_of_zero D htrans ?_
  obtain ⟨C₀, hC₀_nn, hC₀_spec⟩ := exists_wickMassShell_damped_const hm M_mode
  refine ⟨C₀, 3, hC₀_nn, fun α₀ ε hε Ψ => ?_⟩
  obtain ⟨C_op, hCop_nn, hC₀_sq, h_pref_M, h_pref_conj⟩ := hC₀_spec hε
  have h_ker : ∀ A B : OSConfig ι,
      ⟪fockOSMap hm M_mode hC A, fockOSMap hm M_mode hC B⟫_ℂ = osKernel S D.𝒮 A B := by
    intro A B
    rw [osKernel_congr_of_eq_on_orderedEuclidN S hD A B]
    exact inner_fockOSMap_eq_osKernel hm M_mode hC hC_herm A B
  obtain ⟨S_fin, c, hΨ_exp⟩ :
      ∃ (S_fin : Finset (OSConfig ι)) (c : OSConfig ι → ℂ),
        Ψ = ∑ A ∈ S_fin, c A • osBasisPre D A :=
    ⟨Ψ.toFinsupp.support, Ψ.toFinsupp, by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
      rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ A ∈ S_fin, A.1 ≤ N :=
    ⟨S_fin.sup fun A => A.1, fun A hA => Finset.le_sup (f := fun B => B.1) hA⟩
  have hN' : ∀ A ∈ S_fin, (prependShiftConfig α₀ ε hε A).1 ≤ N + 1 :=
    fun A hA => Nat.succ_le_succ (hN A hA)
  have h_map_Ψ :
      wavepacketOSPreLM D (fockOSMap hm M_mode hC) Ψ =
        ∑ A ∈ S_fin, c A • fockOSMap hm M_mode hC (id A) := by
    conv_lhs => rw [hΨ_exp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [LinearMap.map_smul, wavepacketOSPreLM_osBasisPre]
    rfl
  have h_map_Ψ' :
      wavepacketOSPreLM D (fockOSMap hm M_mode hC) (osPrependShiftLM D α₀ 0 ε hε Ψ) =
        ∑ A ∈ S_fin, c A • fockOSMap hm M_mode hC (prependShiftConfig α₀ ε hε A) := by
    conv_lhs => rw [hΨ_exp]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [LinearMap.map_smul, LinearMap.map_smul,
        osPrependShiftLM_zero_osBasisPre, wavepacketOSPreLM_osBasisPre]
  let G : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ := fockSumSector M_mode S_fin c id
  let G' : ∀ r : ℕ, FockSectorDom M_mode.ν r → ℂ :=
    fockSumSector M_mode S_fin c (prependShiftConfig α₀ ε hε)
  obtain ⟨J, hJ_def⟩ :
      ∃ J : ℕ → ℝ, ∀ r, J r =
        ∫ x : FockSectorDom M_mode.ν r, ‖G r x‖ ^ 2 ∂(fockSectorMeasure M_mode.ν r) :=
    ⟨fun r => ∫ x, ‖G r x‖ ^ 2 ∂(fockSectorMeasure M_mode.ν r), fun _ => rfl⟩
  obtain ⟨J', hJ'_def⟩ :
      ∃ J' : ℕ → ℝ, ∀ r, J' r =
        ∫ x : FockSectorDom M_mode.ν r, ‖G' r x‖ ^ 2 ∂(fockSectorMeasure M_mode.ν r) :=
    ⟨fun r => ∫ x, ‖G' r x‖ ^ 2 ∂(fockSectorMeasure M_mode.ν r), fun _ => rfl⟩
  have hJ_nn : ∀ r : ℕ, 0 ≤ J r := fun r => by
    rw [hJ_def r]
    exact integral_nonneg fun _ => sq_nonneg _
  have hΨ_norm_sq : ‖Ψ‖ ^ 2 = ∑ r ∈ Finset.range (N + 1), J r := by
    rw [← norm_wavepacketOSPreLM D (fockOSMap hm M_mode hC) h_ker Ψ, h_map_Ψ,
        sum_fockOSMap_eq_sum_liftSectorToFock hm M_mode hC S_fin c id hN,
        norm_sq_sum_liftSectorToFock G
          (measurable_fockSumSector hm M_mode hC S_fin c id)
          (memLp_fockSumSector hm M_mode hC S_fin c id)]
    exact Finset.sum_congr rfl fun r _ => (hJ_def r).symm
  have hΨ'_norm_sq :
      ‖osPrependShiftLM D α₀ 0 ε hε Ψ‖ ^ 2 = ∑ r ∈ Finset.range (N + 2), J' r := by
    rw [← norm_wavepacketOSPreLM D (fockOSMap hm M_mode hC) h_ker
          (osPrependShiftLM D α₀ 0 ε hε Ψ), h_map_Ψ',
        sum_fockOSMap_eq_sum_liftSectorToFock hm M_mode hC S_fin c
          (prependShiftConfig α₀ ε hε) hN',
        norm_sq_sum_liftSectorToFock G'
          (measurable_fockSumSector hm M_mode hC S_fin c (prependShiftConfig α₀ ε hε))
          (memLp_fockSumSector hm M_mode hC S_fin c (prependShiftConfig α₀ ε hε))]
    exact Finset.sum_congr rfl fun r _ => (hJ'_def r).symm
  have hG'_int_spin : ∀ (r : ℕ) (s : Fin r → Fin M_mode.ν),
      Integrable (fun k : Fin r → Fin 3 → ℝ => ‖G' r (k, s)‖ ^ 2) volume := by
    intro r
    have h_m := ((measurable_fockSumSector hm M_mode hC S_fin c
      (prependShiftConfig α₀ ε hε) r).norm).pow_const 2
    have h_int := (memLp_two_iff_integrable_sq_norm
      (measurable_fockSumSector hm M_mode hC S_fin c
        (prependShiftConfig α₀ ε hε) r).aestronglyMeasurable).mp
      (memLp_fockSumSector hm M_mode hC S_fin c (prependShiftConfig α₀ ε hε) r)
    exact (integrable_fockSectorMeasure_iff_forall_spin h_m).mp h_int
  have hG'_sum_spin : ∀ r : ℕ,
      J' r = ∑ s : Fin r → Fin M_mode.ν, ∫ k : Fin r → Fin 3 → ℝ, ‖G' r (k, s)‖ ^ 2 := by
    intro r
    rw [hJ'_def r]
    exact integral_fockSectorMeasure_eq_sum_spin
      ((memLp_two_iff_integrable_sq_norm
        (measurable_fockSumSector hm M_mode hC S_fin c
          (prependShiftConfig α₀ ε hε) r).aestronglyMeasurable).mp
        (memLp_fockSumSector hm M_mode hC S_fin c (prependShiftConfig α₀ ε hε) r))
  have hJ'_zero : J' 0 ≤ 2 * C_op * J 1 := by
    obtain ⟨huA_int, huA_ae, huA_sum⟩ := integrable_and_ae_le_uAnnih hm M_mode α₀ hε G 0
      (measurable_fockSumSector hm M_mode hC S_fin c id 1)
      (memLp_fockSumSector hm M_mode hC S_fin c id 1)
    have h_le_sum : J' 0 ≤
        ∑ s : Fin 0 → Fin M_mode.ν, ∫ k : Fin 0 → Fin 3 → ℝ, uAnnih M_mode ε G 0 (k, s) := by
      rw [hG'_sum_spin 0]
      refine Finset.sum_le_sum fun s _ =>
        integral_mono_ae (hG'_int_spin 0 s) (huA_int s) ?_
      filter_upwards [huA_ae s] with k hk
      have h_eq0 := fockSumSector_prependShiftConfig_zero_eq hm M_mode hC α₀ hε S_fin c id (k, s)
      dsimp only [id_eq] at h_eq0
      change ‖fockSumSector M_mode S_fin c (prependShiftConfig α₀ ε hε) 0 (k, s)‖ ^ 2 ≤ _
      rwa [h_eq0]
    rw [huA_sum, ← hJ_def 1] at h_le_sum
    have h1 : J' 0 ≤ C_op * J 1 :=
      h_le_sum.trans (mul_le_mul_of_nonneg_right (h_pref_conj 0) (hJ_nn 1))
    linarith [mul_nonneg hCop_nn (hJ_nn 1)]
  have hJ'_succ : ∀ r : ℕ, J' (r + 1) ≤ 2 * C_op * J r + 2 * C_op * J (r + 2) := by
    intro r
    obtain ⟨huC_int, huC_sum⟩ := integrable_and_sum_spin_uCreate hm M_mode hε G r
      (measurable_fockSumSector hm M_mode hC S_fin c id r)
      (memLp_fockSumSector hm M_mode hC S_fin c id r)
    obtain ⟨huA_int, huA_ae, huA_sum⟩ := integrable_and_ae_le_uAnnih hm M_mode α₀ hε G (r + 1)
      (measurable_fockSumSector hm M_mode hC S_fin c id (r + 2))
      (memLp_fockSumSector hm M_mode hC S_fin c id (r + 2))
    have h_le_sum : J' (r + 1) ≤
        2 * (∑ s : Fin (r + 1) → Fin M_mode.ν,
          ∫ k : Fin (r + 1) → Fin 3 → ℝ, uCreate M_mode ε G r (k, s)) +
        2 * (∑ s : Fin (r + 1) → Fin M_mode.ν,
          ∫ k : Fin (r + 1) → Fin 3 → ℝ, uAnnih M_mode ε G (r + 1) (k, s)) := by
      rw [hG'_sum_spin (r + 1), Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [← integral_const_mul, ← integral_const_mul,
          ← integral_add ((huC_int s).const_mul 2) ((huA_int s).const_mul 2)]
      refine integral_mono_ae (hG'_int_spin (r + 1) s)
        (((huC_int s).const_mul 2).add ((huA_int s).const_mul 2)) ?_
      filter_upwards [huA_ae s] with k hk
      have h_eqs := fockSumSector_prependShiftConfig_succ_eq hm M_mode hC α₀ hε S_fin c id r (k, s)
      dsimp only [id_eq] at h_eqs
      change ‖fockSumSector M_mode S_fin c (prependShiftConfig α₀ ε hε) (r + 1) (k, s)‖ ^ 2 ≤ _
      rw [h_eqs]
      have h_tri := norm_add_le
        (fockCreateOp M_mode α₀ ε G r (k, s))
        (fockAnnihOp M_mode α₀ ε G (r + 1) (k, s))
      have h_sq2 : ‖fockCreateOp M_mode α₀ ε G r (k, s) +
          fockAnnihOp M_mode α₀ ε G (r + 1) (k, s)‖ ^ 2 ≤
          2 * ‖fockCreateOp M_mode α₀ ε G r (k, s)‖ ^ 2 +
            2 * ‖fockAnnihOp M_mode α₀ ε G (r + 1) (k, s)‖ ^ 2 := by
        have h_ab := pow_le_pow_left₀ (norm_nonneg _) h_tri 2
        nlinarith [sq_nonneg (‖fockCreateOp M_mode α₀ ε G r (k, s)‖ -
          ‖fockAnnihOp M_mode α₀ ε G (r + 1) (k, s)‖)]
      have hc_le := norm_sq_fockCreateOp_le_uCreate hm M_mode α₀ hε G r (k, s)
      linarith
    rw [huC_sum, huA_sum, ← hJ_def r, ← hJ_def (r + 2)] at h_le_sum
    have h_c_bd := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (h_pref_M r) (hJ_nn r)) zero_le_two
    have h_a_bd := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (h_pref_conj (r + 1)) (hJ_nn (r + 2))) zero_le_two
    linarith
  have hJ_gt : ∀ s : ℕ, N < s → J s = 0 := by
    intro s hs
    rw [hJ_def s]
    have h_zero : ∀ x : FockSectorDom M_mode.ν s, ‖G s x‖ ^ 2 = 0 := by
      intro x
      dsimp only [G]
      rw [fockSumSector_eq_zero_of_lt M_mode S_fin c id (fun A hA => lt_of_le_of_lt (hN A hA) hs)]
      simp
    simp_rw [h_zero]
    simp
  have h_sum_J' := sum_range_le_four_mul_of_rec hCop_nn hJ_nn hJ_gt hJ'_zero hJ'_succ
  have h_sq_goal :
      ‖osPrependShiftLM D α₀ 0 ε hε Ψ‖ ^ 2 ≤ (C₀ * (1 + ε⁻¹) ^ 3 * ‖Ψ‖) ^ 2 := by
    rw [hΨ'_norm_sq]
    have h_rhs_eq : (C₀ * (1 + ε⁻¹) ^ 3 * ‖Ψ‖) ^ 2 =
        4 * C_op * ∑ r ∈ Finset.range (N + 1), J r := by
      calc (C₀ * (1 + ε⁻¹) ^ 3 * ‖Ψ‖) ^ 2
          = C₀ ^ 2 * ((1 + ε⁻¹) ^ 3) ^ 2 * ‖Ψ‖ ^ 2 := by ring
        _ = 4 * C_op * ∑ r ∈ Finset.range (N + 1), J r := by
            rw [hC₀_sq, hΨ_norm_sq]
    rw [h_rhs_eq]
    exact h_sum_J'
  have h_rhs_nn : 0 ≤ C₀ * (1 + ε⁻¹) ^ 3 * ‖Ψ‖ := by positivity
  have h_lhs_nn : 0 ≤ ‖osPrependShiftLM D α₀ 0 ε hε Ψ‖ := norm_nonneg _
  nlinarith

theorem wickMassShellOSDampedFieldBounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSDampedFieldBounded
      (wickMassShellOSAxioms R_rep S hm M_mode hC hC_cov hC_herm hC_pct).toReflectionPositiveData :=
  wickMassShellOSDampedFieldBounded_of_eq_on_orderedEuclidN hm M_mode hC hC_herm
    (wickMassShellOSAxioms R_rep S hm M_mode hC hC_cov hC_herm hC_pct).toReflectionPositiveData
    (wickMassShellOSAxioms R_rep S hm M_mode hC hC_cov hC_herm hC_pct).os1_translation
    (fun _ _ _ _ => rfl)

theorem wickMassShellFullOSDampedFieldBounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι) (S : StarStructure R_rep)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R_rep S m η C) (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) = ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R_rep.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q) :
    OSDampedFieldBounded
      (wickMassShellFullEuclidOSAxioms R_rep S hm M_mode hC
        hC_cov hC_herm hC_pct).toOSAxioms.toReflectionPositiveData :=
  wickMassShellOSDampedFieldBounded_of_eq_on_orderedEuclidN hm M_mode hC hC_herm
    (wickMassShellFullEuclidOSAxioms R_rep S hm M_mode hC
      hC_cov hC_herm hC_pct).toOSAxioms.toReflectionPositiveData
    (wickMassShellFullEuclidOSAxioms R_rep S hm M_mode hC
      hC_cov hC_herm hC_pct).toOSAxioms.os1_translation
    (fun n α _x hx =>
      wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx)

theorem freeKGOSDampedFieldBounded {m : ℝ} (hm : 0 < m) :
    OSDampedFieldBounded (freeKGOSAxioms hm).toReflectionPositiveData :=
  wickMassShellOSDampedFieldBounded trivialRep trivialStarStructure hm
    (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeKGFullOSDampedFieldBounded {m : ℝ} (hm : 0 < m) :
    OSDampedFieldBounded (freeKGFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData :=
  wickMassShellFullOSDampedFieldBounded trivialRep trivialStarStructure hm
    (kgModeData hm) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (fun _ _ => by simp [massiveKGCoeff, trivialStarStructure])
    (fun _ _ => by simp [massiveKGCoeff, trivialRep])

theorem freeDiracOSDampedFieldBounded {m : ℝ} (hm : 0 < m) :
    OSDampedFieldBounded (freeDiracOSAxioms hm).toReflectionPositiveData :=
  wickMassShellOSDampedFieldBounded diracRep diracStarStructure hm
    (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

theorem freeDiracFullOSDampedFieldBounded {m : ℝ} (hm : 0 < m) :
    OSDampedFieldBounded (freeDiracFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData :=
  wickMassShellFullOSDampedFieldBounded diracRep diracStarStructure hm
    (diracModeData hm) (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m) (diracMassShellCoeff_herm m) (diracMassShellCoeff_pct m)

theorem wickMassShell_osReconstructedWightmanFamily_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R_rep S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hdamped : OSDampedFieldBounded hOS.toReflectionPositiveData)
    (hD : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = wickMassShellS m hm η C hC n α x) :
    osReconstructedWightmanFamily hOS hcluster hdamped = wickMassShellW m η C hC := by
  let T₁ := osReconstructedTubeExtensionData hOS hcluster hdamped
  let T₂ := wickMassShellOSTubeExtensionData R_rep hm η hC hC_cov
  rw [← osReconstructedTubeExtensionData_W_eq hOS hcluster hdamped,
      ← wickMassShellOSTubeExtensionData_W R_rep hm η hC hC_cov]
  refine wightman_eq_of_tubeExtension_eq T₁.E T₂.E fun n α z hz => ?_
  have hx₀ : euclidOrderedBasePoint n ∈ orderedEuclidN n :=
    euclidOrderedBasePoint_mem_orderedEuclidN n
  have h_ev : ∀ᶠ x in 𝓝 (euclidOrderedBasePoint n),
      T₁.E.H n α (wickEmbedN n x) = T₂.E.H n α (wickEmbedN n x) := by
    filter_upwards [(isOpen_orderedEuclidN n).mem_nhds hx₀] with x hx
    rw [OSTubeExtensionData.E_H, OSTubeExtensionData.E_H,
        ← T₁.schwinger_eq n α x hx, hD n α x hx, T₂.schwinger_eq n α x hx]
  exact analyticOn_forward_tube_eq_of_eventuallyEq_wickEmbedN n
    (T₁.E.analytic n α) (T₂.E.analytic n α) hx₀ h_ev hz

theorem freeKG_osReconstructedWightmanFamily_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily (freeKGOSAxioms hm) (freeKGOSTimeCluster hm)
      (freeKGOSDampedFieldBounded hm) = freeKGW m hm :=
  wickMassShell_osReconstructedWightmanFamily_eq hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (freeKGOSAxioms hm) (freeKGOSTimeCluster hm) (freeKGOSDampedFieldBounded hm)
    (fun _ _ _ _ => rfl)

theorem freeKGFull_osReconstructedWightmanFamily_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily (freeKGFullEuclidOSAxioms hm).toOSAxioms
      (freeKGFullOSTimeCluster hm) (freeKGFullOSDampedFieldBounded hm) = freeKGW m hm :=
  wickMassShell_osReconstructedWightmanFamily_eq hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (freeKGFullEuclidOSAxioms hm).toOSAxioms (freeKGFullOSTimeCluster hm)
    (freeKGFullOSDampedFieldBounded hm)
    (fun n α _x hx => freeKGFullS_eq_freeKGS_on_orderedEuclidN hm n α hx)

theorem freeDirac_osReconstructedWightmanFamily_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm)
      (freeDiracOSDampedFieldBounded hm) = freeDiracW m hm :=
  wickMassShell_osReconstructedWightmanFamily_eq hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)
    (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm) (freeDiracOSDampedFieldBounded hm)
    (fun _ _ _ _ => rfl)

theorem freeDiracFull_osReconstructedWightmanFamily_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily (freeDiracFullEuclidOSAxioms hm).toOSAxioms
      (freeDiracFullOSTimeCluster hm) (freeDiracFullOSDampedFieldBounded hm) =
      freeDiracW m hm :=
  wickMassShell_osReconstructedWightmanFamily_eq hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)
    (freeDiracFullEuclidOSAxioms hm).toOSAxioms (freeDiracFullOSTimeCluster hm)
    (freeDiracFullOSDampedFieldBounded hm)
    (fun n α _x hx => freeDiracFullS_eq_freeDiracS_on_orderedEuclidN hm n α hx)

theorem freeKG_pure_os_full_reconstruction {m : ℝ} (hm : 0 < m) :
    let hOS := freeKGOSAxioms hm
    let hcluster := freeKGOSTimeCluster hm
    let hdamped := freeKGOSDampedFieldBounded hm
    let hnorm := freeKGOSVacuumNormalized hm
    let T := osReconstructedTubeExtensionData hOS hcluster hdamped
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeKGW m hm ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeKGS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare trivialRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms trivialRep trivialStarStructure 1 P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = freeKGS m hm n α x) := by
  have hsyn := os_full_wightman_reconstruction (freeKGOSAxioms hm)
    (freeKGOSTimeCluster hm) (freeKGOSDampedFieldBounded hm) (freeKGOSVacuumNormalized hm)
  have hW : osReconstructedWightmanFamily (freeKGOSAxioms hm)
      (freeKGOSTimeCluster hm) (freeKGOSDampedFieldBounded hm) = freeKGW m hm :=
    freeKG_osReconstructedWightmanFamily_eq hm
  have hloc : LocalCommutativity 1
      (osReconstructedWightmanFamily (freeKGOSAxioms hm)
        (freeKGOSTimeCluster hm) (freeKGOSDampedFieldBounded hm)) := by
    rw [hW]
    exact freeKG_localCommutativity hm
  rcases hsyn with ⟨hG, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inl rfl) hloc with ⟨hFE, hperm⟩
  exact ⟨hG.trans hW, hschw, hvac, htr, hFE, hperm⟩

theorem freeDirac_pure_os_full_reconstruction {m : ℝ} (hm : 0 < m) :
    let hOS := freeDiracOSAxioms hm
    let hcluster := freeDiracOSTimeCluster hm
    let hdamped := freeDiracOSDampedFieldBounded hm
    let hnorm := freeDiracOSVacuumNormalized hm
    let T := osReconstructedTubeExtensionData hOS hcluster hdamped
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeDiracW m hm ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeDiracS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare diracRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms diracRep diracStarStructure (-1) P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = freeDiracS m hm n α x) := by
  have hsyn := os_full_wightman_reconstruction (freeDiracOSAxioms hm)
    (freeDiracOSTimeCluster hm) (freeDiracOSDampedFieldBounded hm)
    (freeDiracOSVacuumNormalized hm)
  have hW : osReconstructedWightmanFamily (freeDiracOSAxioms hm)
      (freeDiracOSTimeCluster hm) (freeDiracOSDampedFieldBounded hm) = freeDiracW m hm :=
    freeDirac_osReconstructedWightmanFamily_eq hm
  have hloc : LocalCommutativity (-1)
      (osReconstructedWightmanFamily (freeDiracOSAxioms hm)
        (freeDiracOSTimeCluster hm) (freeDiracOSDampedFieldBounded hm)) := by
    rw [hW]
    exact freeDirac_localCommutativity hm
  rcases hsyn with ⟨hG, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inr rfl) hloc with ⟨hFE, hperm⟩
  exact ⟨hG.trans hW, hschw, hvac, htr, hFE, hperm⟩

lemma card_chordPairing_le_factorial (n : ℕ) :
    Fintype.card (ChordPairing n) ≤ n.factorial := by
  have hinj : Function.Injective (fun P : ChordPairing n => P.mate) := by
    intro P Q h
    exact ChordPairing.ext h
  calc Fintype.card (ChordPairing n)
      ≤ Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_le_of_injective _ hinj
    _ = n.factorial := by simp [Fintype.card_perm]

lemma orderedEuclidN_time_le_of_le {n : ℕ} {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) {u v : Fin n} (huv : u ≤ v) :
    x u 0 ≤ x v 0 := by
  have haux : ∀ (d i : ℕ) (hid : i + d < n),
      x ⟨i, by omega⟩ 0 ≤ x ⟨i + d, hid⟩ 0 := by
    intro d
    induction d with
    | zero =>
      intro i hid
      exact le_refl _
    | succ d ih =>
      intro i hid
      have h1 : x ⟨i, by omega⟩ 0 ≤ x ⟨i + d, by omega⟩ 0 := ih i (by omega)
      have h2 : x ⟨i + d, by omega⟩ 0 < x ⟨i + d + 1, hid⟩ 0 := hx ⟨i + d, by omega⟩ hid
      exact h1.trans h2.le
  have h_eq : u.val + (v.val - u.val) = v.val := Nat.add_sub_of_le huv
  have h_lt : u.val + (v.val - u.val) < n := by
    rw [h_eq]
    exact v.isLt
  have h_le := haux (v.val - u.val) u.val h_lt
  have hv_fin : (⟨u.val + (v.val - u.val), h_lt⟩ : Fin n) = v := Fin.ext h_eq
  have hu_fin : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
  rwa [hv_fin, hu_fin] at h_le

theorem wickMassShellOSLinearGrowthCondition_of_eq_on_orderedEuclidN
    {ι : Type*} [Finite ι]
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : ‖η‖ ≤ 1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    {𝒮 : SchwingerFamily ι}
    (hD : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = wickMassShellS m hm η C hC n α x) :
    OSLinearGrowthCondition 𝒮 := by
  letI : Fintype ι := Fintype.ofFinite ι
  let C_α : (Fin 2 → ι) → ℝ := fun β =>
    Classical.choose (norm_massShellTwoPointH_two_le hm hC β)
  have hC_α : ∀ β : Fin 2 → ι,
      0 ≤ C_α β ∧ ∀ {w : Fin 2 → Fin 4 → ℂ}, w ∈ forward_tube_n 2 →
        ‖massShellTwoPointH m C 2 β w‖ ≤
          C_α β * (coneGap (diff_im 2 w 0 (by decide)))⁻¹ ^ 4 :=
    fun β => Classical.choose_spec (norm_massShellTwoPointH_two_le hm hC β)
  let A_lg : ℝ := 1 + ∑ β : Fin 2 → ι, C_α β
  have hsum_nn : 0 ≤ ∑ β : Fin 2 → ι, C_α β :=
    Finset.sum_nonneg fun β _ => (hC_α β).1
  have hA_ge : 1 ≤ A_lg := by
    dsimp only [A_lg]
    linarith
  have hC_le_A : ∀ β : Fin 2 → ι, C_α β ≤ A_lg := fun β => by
    have h1 : C_α β ≤ ∑ β' : Fin 2 → ι, C_α β' :=
      Finset.single_le_sum (fun β' _ => (hC_α β').1) (Finset.mem_univ β)
    dsimp only [A_lg]
    linarith
  refine ⟨1, A_lg, 4, zero_le_one, hA_ge, fun n α x hx => ?_⟩
  rw [hD n α x hx]
  change ‖wickMassShellH m η C n α (wickEmbedN n x)‖ ≤ _
  let z : Fin n → Fin 4 → ℂ := wickEmbedN n x
  have hz : z ∈ forward_tube_n n := wickEmbedN_mem_forward_tube_n n hx
  let f : Fin (n - 1) → ℝ := fun k =>
    (1 + (x ⟨k.val + 1, by omega⟩ 0 - x ⟨k.val, by omega⟩ 0)⁻¹) ^ 4
  have hf_ge_one : ∀ k : Fin (n - 1), 1 ≤ f k := fun k => by
    have hk : k.val < n - 1 := k.isLt
    have hdt : 0 < x ⟨k.val + 1, by omega⟩ 0 - x ⟨k.val, by omega⟩ 0 :=
      sub_pos.mpr (hx ⟨k.val, by omega⟩ (by dsimp; omega))
    have hbase : 1 ≤ 1 + (x ⟨k.val + 1, by omega⟩ 0 - x ⟨k.val, by omega⟩ 0)⁻¹ := by
      have hinv : 0 ≤ (x ⟨k.val + 1, by omega⟩ 0 - x ⟨k.val, by omega⟩ 0)⁻¹ :=
        inv_nonneg.mpr hdt.le
      linarith
    exact one_le_pow₀ hbase
  have h_term : ∀ P : ChordPairing n,
      ‖η ^ P.cross * ∏ c : P.Chord,
        massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖ ≤
      A_lg ^ n * ∏ k : Fin (n - 1), f k := fun P => by
    rw [norm_mul, norm_pow, norm_prod]
    have hη_pow : ‖η‖ ^ P.cross ≤ 1 := pow_le_one₀ (norm_nonneg η) hη
    let g : P.Chord → Fin (n - 1) := fun c =>
      ⟨c.1.val, by
        have hlt : c.1.val < (P.mate c.1).val := c.2
        have hlt2 : (P.mate c.1).val < n := (P.mate c.1).isLt
        omega⟩
    have hg_inj : Function.Injective g := by
      intro c₁ c₂ h
      exact Subtype.ext (Fin.ext (congrArg (fun u : Fin (n - 1) => u.val) h))
    have h_prod_le :
        (∏ c : P.Chord,
          ‖massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖) ≤
        ∏ c : P.Chord, (A_lg * f (g c)) := by
      refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun c _ => ?_
      have hzc : ![z c.1, z (P.mate c.1)] ∈ forward_tube_n 2 :=
        pair_mem_forward_tube_two hz c.2
      have h_diff_eq :
          diff_im 2 ![z c.1, z (P.mate c.1)] 0 (by decide) =
            euclidTimeVec (x (P.mate c.1) 0 - x c.1 0) := by
        ext μ
        fin_cases μ <;> simp [diff_im, diff_z, z, wickEmbed, euclidTimeVec]
      have h_gap_eq :
          coneGap (diff_im 2 ![z c.1, z (P.mate c.1)] 0 (by decide)) =
            x (P.mate c.1) 0 - x c.1 0 := by
        rw [h_diff_eq]
        simp [coneGap, euclidTimeVec]
      have hdt_step : 0 < x ⟨c.1.val + 1, by omega⟩ 0 - x ⟨c.1.val, by omega⟩ 0 :=
        sub_pos.mpr (hx c.1 (by
          have hlt : c.1.val < (P.mate c.1).val := c.2
          have hlt2 : (P.mate c.1).val < n := (P.mate c.1).isLt
          omega))
      have h_le_mate :
          x ⟨c.1.val + 1, by
            have hlt : c.1.val < (P.mate c.1).val := c.2
            have hlt2 : (P.mate c.1).val < n := (P.mate c.1).isLt
            omega⟩ 0 ≤ x (P.mate c.1) 0 := by
        refine orderedEuclidN_time_le_of_le hx ?_
        exact Nat.succ_le_of_lt c.2
      have hdt_le :
          x ⟨c.1.val + 1, by
            have hlt : c.1.val < (P.mate c.1).val := c.2
            have hlt2 : (P.mate c.1).val < n := (P.mate c.1).isLt
            omega⟩ 0 - x ⟨c.1.val, c.1.isLt⟩ 0 ≤ x (P.mate c.1) 0 - x c.1 0 := by
        have hc_eq : (⟨c.1.val, c.1.isLt⟩ : Fin n) = c.1 := Fin.ext rfl
        rw [hc_eq]
        linarith
      have hdt_pos : 0 < x (P.mate c.1) 0 - x c.1 0 := lt_of_lt_of_le hdt_step hdt_le
      have h_inv_le :
          (x (P.mate c.1) 0 - x c.1 0)⁻¹ ≤
            1 + (x ⟨(g c).val + 1, by omega⟩ 0 - x ⟨(g c).val, by omega⟩ 0)⁻¹ := by
        have h1 :
            (x (P.mate c.1) 0 - x c.1 0)⁻¹ ≤
              (x ⟨(g c).val + 1, by omega⟩ 0 - x ⟨(g c).val, by omega⟩ 0)⁻¹ :=
          inv_anti₀ hdt_step hdt_le
        linarith
      have h_pow_le :
          (coneGap (diff_im 2 ![z c.1, z (P.mate c.1)] 0 (by decide)))⁻¹ ^ 4 ≤ f (g c) := by
        rw [h_gap_eq]
        exact pow_le_pow_left₀ (inv_nonneg.mpr hdt_pos.le) h_inv_le 4
      exact ((hC_α ![α c.1, α (P.mate c.1)]).2 hzc).trans
        (mul_le_mul (hC_le_A _) h_pow_le (by positivity) (by linarith))
    have h_card_le : Fintype.card P.Chord ≤ n := by
      have h2 := P.two_mul_card_chord
      omega
    have hA_pow_le : A_lg ^ Fintype.card P.Chord ≤ A_lg ^ n :=
      pow_le_pow_right₀ hA_ge h_card_le
    have h_f_prod_le : (∏ c : P.Chord, f (g c)) ≤ ∏ k : Fin (n - 1), f k := by
      have h_img : ∏ k ∈ Finset.univ.image g, f k = ∏ c : P.Chord, f (g c) :=
        Finset.prod_image fun a _ b _ h => hg_inj h
      have h_sdiff : (∏ k ∈ Finset.univ \ Finset.univ.image g, f k) *
          (∏ k ∈ Finset.univ.image g, f k) = ∏ k : Fin (n - 1), f k :=
        Finset.prod_sdiff (Finset.subset_univ _)
      have h_ge1 : 1 ≤ ∏ k ∈ Finset.univ \ Finset.univ.image g, f k := by
        simpa using Finset.prod_le_prod (fun _ _ => zero_le_one) fun k _ => hf_ge_one k
      have h_nn : 0 ≤ ∏ k ∈ Finset.univ.image g, f k :=
        Finset.prod_nonneg fun k _ => zero_le_one.trans (hf_ge_one k)
      rw [← h_img, ← h_sdiff]
      nlinarith
    have h_prod_rhs :
        (∏ c : P.Chord, (A_lg * f (g c))) ≤ A_lg ^ n * ∏ k : Fin (n - 1), f k := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      exact mul_le_mul hA_pow_le h_f_prod_le
        (Finset.prod_nonneg fun c _ => (zero_le_one.trans (hf_ge_one (g c))))
        (pow_nonneg (zero_le_one.trans hA_ge) _)
    calc ‖η‖ ^ P.cross *
          (∏ c : P.Chord,
            ‖massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖)
        ≤ 1 * (A_lg ^ n * ∏ k : Fin (n - 1), f k) :=
          mul_le_mul hη_pow (h_prod_le.trans h_prod_rhs)
            (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = A_lg ^ n * ∏ k : Fin (n - 1), f k := one_mul _
  have h_sum_le :
      ‖wickMassShellH m η C n α z‖ ≤
        (Fintype.card (ChordPairing n) : ℝ) * (A_lg ^ n * ∏ k : Fin (n - 1), f k) := by
    unfold wickMassShellH
    refine (norm_sum_le Finset.univ _).trans ?_
    calc (∑ P : ChordPairing n,
            ‖η ^ P.cross * ∏ c : P.Chord,
              massShellTwoPointH m C 2 ![α c.1, α (P.mate c.1)] ![z c.1, z (P.mate c.1)]‖)
        ≤ ∑ _P : ChordPairing n, (A_lg ^ n * ∏ k : Fin (n - 1), f k) :=
          Finset.sum_le_sum fun P _ => h_term P
      _ = (Fintype.card (ChordPairing n) : ℝ) * (A_lg ^ n * ∏ k : Fin (n - 1), f k) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_card_real : (Fintype.card (ChordPairing n) : ℝ) ≤ (n.factorial : ℝ) ^ 4 := by
    have h1 : (Fintype.card (ChordPairing n) : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast card_chordPairing_le_factorial n
    have h2 : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have h3 : (n.factorial : ℝ) ≤ (n.factorial : ℝ) ^ 4 :=
      le_self_pow₀ h2 (by decide)
    exact h1.trans h3
  have h_rhs_nn : 0 ≤ A_lg ^ n * ∏ k : Fin (n - 1), f k :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hA_ge) _)
      (Finset.prod_nonneg fun k _ => zero_le_one.trans (hf_ge_one k))
  calc ‖wickMassShellH m η C n α z‖
      ≤ (Fintype.card (ChordPairing n) : ℝ) * (A_lg ^ n * ∏ k : Fin (n - 1), f k) := h_sum_le
    _ ≤ (n.factorial : ℝ) ^ 4 * (A_lg ^ n * ∏ k : Fin (n - 1), f k) :=
        mul_le_mul_of_nonneg_right h_card_real h_rhs_nn
    _ = 1 * A_lg ^ n * (n.factorial : ℝ) ^ 4 * ∏ k : Fin (n - 1), f k := by ring

theorem wickMassShellOSLinearGrowthCondition {ι : Type*} [Finite ι]
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : ‖η‖ ≤ 1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C) :
    OSLinearGrowthCondition (wickMassShellS m hm η C hC) :=
  wickMassShellOSLinearGrowthCondition_of_eq_on_orderedEuclidN hm hη hC
    (fun _ _ _ _ => rfl)

theorem wickMassShellFullOSLinearGrowthCondition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R_rep : HolomorphicLorentzRep ι)
    {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : ‖η‖ ≤ 1)
    {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ} (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q) :
    OSLinearGrowthCondition (wickMassShellFullS R_rep m hm η C hC) :=
  wickMassShellOSLinearGrowthCondition_of_eq_on_orderedEuclidN hm hη hC
    (fun n α _x hx =>
      wickMassShellFullS_eq_wickMassShellS_on_orderedEuclidN R_rep hm η hC hC_cov n α hx)

theorem freeKGOSLinearGrowthCondition {m : ℝ} (hm : 0 < m) :
    OSLinearGrowthCondition (freeKGS m hm) :=
  wickMassShellOSLinearGrowthCondition hm (by norm_num) (massiveKGCoeff_data hm)

theorem freeKGFullOSLinearGrowthCondition {m : ℝ} (hm : 0 < m) :
    OSLinearGrowthCondition (freeKGFullS m hm) :=
  wickMassShellFullOSLinearGrowthCondition trivialRep hm (by norm_num) (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])

theorem freeDiracOSLinearGrowthCondition {m : ℝ} (hm : 0 < m) :
    OSLinearGrowthCondition (freeDiracS m hm) :=
  wickMassShellOSLinearGrowthCondition hm (by norm_num) (diracMassShellCoeff_data hm)

theorem freeDiracFullOSLinearGrowthCondition {m : ℝ} (hm : 0 < m) :
    OSLinearGrowthCondition (freeDiracFullS m hm) :=
  wickMassShellFullOSLinearGrowthCondition diracRep hm (by norm_num)
    (diracMassShellCoeff_data hm) (diracMassShellCoeff_lorentz m)

theorem wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R_rep : HolomorphicLorentzRep ι} {S : StarStructure R_rep}
    {m : ℝ} (hm : 0 < m) {η_os η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (hC : MassShellCoeffData m C)
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R_rep.rep A (α i) (β i)) * C β q)
    {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R_rep S η_os 𝒮)
    (hlg : OSLinearGrowthCondition 𝒮)
    (hD : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = wickMassShellS m hm η C hC n α x) :
    osReconstructedWightmanFamily_of_linearGrowth hOS hlg =
      wickMassShellW m η C hC := by
  let T₁ := osReconstructedTubeExtensionData_of_linearGrowth hOS hlg
  let T₂ := wickMassShellOSTubeExtensionData R_rep hm η hC hC_cov
  rw [← osReconstructedTubeExtensionData_of_linearGrowth_W_eq hOS hlg,
      ← wickMassShellOSTubeExtensionData_W R_rep hm η hC hC_cov]
  refine wightman_eq_of_tubeExtension_eq T₁.E T₂.E fun n α z hz => ?_
  have hx₀ : euclidOrderedBasePoint n ∈ orderedEuclidN n :=
    euclidOrderedBasePoint_mem_orderedEuclidN n
  have h_ev : ∀ᶠ x in 𝓝 (euclidOrderedBasePoint n),
      T₁.E.H n α (wickEmbedN n x) = T₂.E.H n α (wickEmbedN n x) := by
    filter_upwards [(isOpen_orderedEuclidN n).mem_nhds hx₀] with x hx
    rw [OSTubeExtensionData.E_H, OSTubeExtensionData.E_H,
        ← T₁.schwinger_eq n α x hx, hD n α x hx, T₂.schwinger_eq n α x hx]
  exact analyticOn_forward_tube_eq_of_eventuallyEq_wickEmbedN n
    (T₁.E.analytic n α) (T₂.E.analytic n α) hx₀ h_ev hz

theorem freeKG_osReconstructedWightmanFamily_of_linearGrowth_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily_of_linearGrowth (freeKGOSAxioms hm)
      (freeKGOSLinearGrowthCondition hm) = freeKGW m hm :=
  wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (freeKGOSAxioms hm) (freeKGOSLinearGrowthCondition hm)
    (fun _ _ _ _ => rfl)

theorem freeKGFull_osReconstructedWightmanFamily_of_linearGrowth_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily_of_linearGrowth (freeKGFullEuclidOSAxioms hm).toOSAxioms
      (freeKGFullOSLinearGrowthCondition hm) = freeKGW m hm :=
  wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq hm (massiveKGCoeff_data hm)
    (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
    (freeKGFullEuclidOSAxioms hm).toOSAxioms
    (freeKGFullOSLinearGrowthCondition hm)
    (fun n α _x hx => freeKGFullS_eq_freeKGS_on_orderedEuclidN hm n α hx)

theorem freeDirac_osReconstructedWightmanFamily_of_linearGrowth_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily_of_linearGrowth (freeDiracOSAxioms hm)
      (freeDiracOSLinearGrowthCondition hm) = freeDiracW m hm :=
  wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)
    (freeDiracOSAxioms hm) (freeDiracOSLinearGrowthCondition hm)
    (fun _ _ _ _ => rfl)

theorem freeDiracFull_osReconstructedWightmanFamily_of_linearGrowth_eq {m : ℝ} (hm : 0 < m) :
    osReconstructedWightmanFamily_of_linearGrowth (freeDiracFullEuclidOSAxioms hm).toOSAxioms
      (freeDiracFullOSLinearGrowthCondition hm) = freeDiracW m hm :=
  wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq hm (diracMassShellCoeff_data hm)
    (diracMassShellCoeff_lorentz m)
    (freeDiracFullEuclidOSAxioms hm).toOSAxioms
    (freeDiracFullOSLinearGrowthCondition hm)
    (fun n α _x hx => freeDiracFullS_eq_freeDiracS_on_orderedEuclidN hm n α hx)

theorem freeKGS_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hOS : OSAxioms trivialRep trivialStarStructure η (freeKGS m hm)) :
    η = 1 := by
  have hlg : OSLinearGrowthCondition (freeKGS m hm) := freeKGOSLinearGrowthCondition hm
  have hW : osReconstructedWightmanFamily_of_linearGrowth hOS hlg = freeKGW m hm :=
    wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq hm (massiveKGCoeff_data hm)
      (fun _ _ _ => by simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply])
      hOS hlg (fun _ _ _ _ => rfl)
  have hsyn := os_wightman_reconstruction_of_linearGrowth hOS hlg
  exact hsyn.2.2.2.2.1.1 trivialRep_spinParity ⟨default, by
    rw [hW]
    exact freeKGW_twoPoint_ne_zero hm⟩

theorem freeDiracS_spin_statistics {m : ℝ} (hm : 0 < m) {η : ℂ}
    (hOS : OSAxioms diracRep diracStarStructure η (freeDiracS m hm)) :
    η = -1 := by
  have hlg : OSLinearGrowthCondition (freeDiracS m hm) := freeDiracOSLinearGrowthCondition hm
  have hW : osReconstructedWightmanFamily_of_linearGrowth hOS hlg = freeDiracW m hm :=
    wickMassShell_osReconstructedWightmanFamily_of_linearGrowth_eq hm (diracMassShellCoeff_data hm)
      (diracMassShellCoeff_lorentz m) hOS hlg (fun _ _ _ _ => rfl)
  have hsyn := os_wightman_reconstruction_of_linearGrowth hOS hlg
  rcases freeDiracW_twoPoint_nondegenerate hm with ⟨β, hβ⟩
  exact hsyn.2.2.2.2.1.1 diracRep_spinParity ⟨β, by
    rw [hW]
    exact hβ⟩

theorem freeKG_pure_os_full_reconstruction_of_linearGrowth {m : ℝ} (hm : 0 < m) :
    let hOS := freeKGOSAxioms hm
    let hcluster := freeKGOSTimeCluster hm
    let hlg := freeKGOSLinearGrowthCondition hm
    let hnorm := freeKGOSVacuumNormalized hm
    let T := osReconstructedTubeExtensionData_of_linearGrowth hOS hlg
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeKGW m hm ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeKGS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare trivialRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms trivialRep trivialStarStructure 1 P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = freeKGS m hm n α x) ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ nonCoincidentEuclidN n → P.permutedSchwinger n α x = freeKGFullS m hm n α x) := by
  have hsyn := os_full_wightman_reconstruction_of_linearGrowth (freeKGOSAxioms hm)
    (freeKGOSTimeCluster hm) (freeKGOSLinearGrowthCondition hm) (freeKGOSVacuumNormalized hm)
  have hW : osReconstructedWightmanFamily_of_linearGrowth (freeKGOSAxioms hm)
      (freeKGOSLinearGrowthCondition hm) = freeKGW m hm :=
    freeKG_osReconstructedWightmanFamily_of_linearGrowth_eq hm
  have hloc : LocalCommutativity 1
      (osReconstructedWightmanFamily_of_linearGrowth (freeKGOSAxioms hm)
        (freeKGOSLinearGrowthCondition hm)) := by
    rw [hW]
    exact freeKG_localCommutativity hm
  rcases hsyn with ⟨hG, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inl rfl) hloc with ⟨hFE, hperm⟩
  have hFE_kg := freeKGFullEuclidOSAxioms hm
  refine ⟨hG.trans hW, hschw, hvac, htr, hFE, hperm, fun n α x hx => ?_⟩
  exact fullEuclid_eq_of_eq_on_orderedEuclidN hFE.os1_rotation hFE.os3_permutation
    hFE_kg.os1_rotation hFE_kg.os3_permutation
    (fun β y hy => (hperm n β y hy).trans
      (freeKGFullS_eq_freeKGS_on_orderedEuclidN hm n β hy).symm) α hx

theorem freeDirac_pure_os_full_reconstruction_of_linearGrowth {m : ℝ} (hm : 0 < m) :
    let hOS := freeDiracOSAxioms hm
    let hcluster := freeDiracOSTimeCluster hm
    let hlg := freeDiracOSLinearGrowthCondition hm
    let hnorm := freeDiracOSVacuumNormalized hm
    let T := osReconstructedTubeExtensionData_of_linearGrowth hOS hlg
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeDiracW m hm ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeDiracS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare diracRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms diracRep diracStarStructure (-1) P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = freeDiracS m hm n α x) ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ nonCoincidentEuclidN n → P.permutedSchwinger n α x = freeDiracFullS m hm n α x) := by
  have hsyn := os_full_wightman_reconstruction_of_linearGrowth (freeDiracOSAxioms hm)
    (freeDiracOSTimeCluster hm) (freeDiracOSLinearGrowthCondition hm)
    (freeDiracOSVacuumNormalized hm)
  have hW : osReconstructedWightmanFamily_of_linearGrowth (freeDiracOSAxioms hm)
      (freeDiracOSLinearGrowthCondition hm) = freeDiracW m hm :=
    freeDirac_osReconstructedWightmanFamily_of_linearGrowth_eq hm
  have hloc : LocalCommutativity (-1)
      (osReconstructedWightmanFamily_of_linearGrowth (freeDiracOSAxioms hm)
        (freeDiracOSLinearGrowthCondition hm)) := by
    rw [hW]
    exact freeDirac_localCommutativity hm
  rcases hsyn with ⟨hG, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inr rfl) hloc with ⟨hFE, hperm⟩
  have hFE_dir := freeDiracFullEuclidOSAxioms hm
  refine ⟨hG.trans hW, hschw, hvac, htr, hFE, hperm, fun n α x hx => ?_⟩
  exact fullEuclid_eq_of_eq_on_orderedEuclidN hFE.os1_rotation hFE.os3_permutation
    hFE_dir.os1_rotation hFE_dir.os3_permutation
    (fun β y hy => (hperm n β y hy).trans
      (freeDiracFullS_eq_freeDiracS_on_orderedEuclidN hm n β hy).symm) α hx

theorem freeKG_euclidean_to_local_wightman_of_linearGrowth {m : ℝ} (hm : 0 < m) :
    let hFull := freeKGFullEuclidOSAxioms hm
    let hOS := hFull.toOSAxioms
    let hcluster := freeKGFullOSTimeCluster hm
    let hlg := freeKGFullOSLinearGrowthCondition hm
    let hnorm := freeKGFullS_vacuumNormalized hm
    let T := osReconstructedTubeExtensionData_of_linearGrowth hOS hlg
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeKGW m hm ∧
    LocalCommutativity 1 (freeKGW m hm) ∧
    PermSpacelikeLocality 1 (freeKGW m hm) ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeKGFullS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare trivialRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms trivialRep trivialStarStructure 1 P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (x : Fin n → Fin 4 → ℝ),
      x ∈ nonCoincidentEuclidN n → P.permutedSchwinger n α x = freeKGFullS m hm n α x) := by
  have hsyn := fullEuclid_os_generalWightman_reconstruction_of_linearGrowth
    (freeKGFullEuclidOSAxioms hm) (freeKGFullOSTimeCluster hm)
    (freeKGFullOSLinearGrowthCondition hm) (freeKGFullS_vacuumNormalized hm)
  have hW := freeKGFull_osReconstructedWightmanFamily_of_linearGrowth_eq hm
  rcases hsyn with ⟨hG, hloc, hperm_loc, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inl rfl) with ⟨hFE, hperm⟩
  have hW_eq := hG.trans hW
  rw [hW_eq] at hloc hperm_loc
  exact ⟨hW_eq, hloc, hperm_loc, hschw, hvac, htr, hFE, hperm⟩

theorem freeDirac_euclidean_to_local_wightman_of_linearGrowth {m : ℝ} (hm : 0 < m) :
    let hFull := freeDiracFullEuclidOSAxioms hm
    let hOS := hFull.toOSAxioms
    let hcluster := freeDiracFullOSTimeCluster hm
    let hlg := freeDiracFullOSLinearGrowthCondition hm
    let hnorm := freeDiracFullS_vacuumNormalized hm
    let T := osReconstructedTubeExtensionData_of_linearGrowth hOS hlg
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = freeDiracW m hm ∧
    LocalCommutativity (-1) (freeDiracW m hm) ∧
    PermSpacelikeLocality (-1) (freeDiracW m hm) ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → freeDiracFullS m hm n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare diracRep P.poincare) a (U Ψ)) ∧
    FullEuclidOSAxioms diracRep diracStarStructure (-1) P.permutedSchwinger ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ nonCoincidentEuclidN n → P.permutedSchwinger n α x = freeDiracFullS m hm n α x) := by
  have hsyn := fullEuclid_os_generalWightman_reconstruction_of_linearGrowth
    (freeDiracFullEuclidOSAxioms hm) (freeDiracFullOSTimeCluster hm)
    (freeDiracFullOSLinearGrowthCondition hm) (freeDiracFullS_vacuumNormalized hm)
  have hW := freeDiracFull_osReconstructedWightmanFamily_of_linearGrowth_eq hm
  rcases hsyn with ⟨hG, hloc, hperm_loc, hschw, hvac, htr, _, hfull⟩
  rcases hfull (Or.inr rfl) with ⟨hFE, hperm⟩
  have hW_eq := hG.trans hW
  rw [hW_eq] at hloc hperm_loc
  exact ⟨hW_eq, hloc, hperm_loc, hschw, hvac, htr, hFE, hperm⟩

theorem freeKG_grand_master {m : ℝ} (hm : 0 < m) :
    FullEuclidOSAxioms trivialRep trivialStarStructure 1 (freeKGFullS m hm) ∧
    OSAxioms trivialRep trivialStarStructure 1 (freeKGS m hm) ∧
    OSVacuumNormalized (freeKGFullS m hm) ∧
    OSVacuumNormalized (freeKGS m hm) ∧
    freeKGFullS m hm 2 default (equalTimeTwoPoint 1) ≠ 0 ∧
    (∀ {η : ℂ}, FullEuclidOSAxioms trivialRep trivialStarStructure η (freeKGFullS m hm) →
      η = 1) ∧
    (∀ {η : ℂ}, OSAxioms trivialRep trivialStarStructure η (freeKGS m hm) → η = 1) ∧
    (∀ {τ : ℝ} (hτ : 0 ≤ τ) (A B : OSConfig Unit),
      ‖osKernel trivialStarStructure (freeKGS m hm) A (osConfigTimeShift τ hτ B) -
          osKernel trivialStarStructure (freeKGS m hm) A (osVacuumConfig Unit) *
            osKernel trivialStarStructure (freeKGS m hm) (osVacuumConfig Unit) B‖ ≤
        ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) A‖ *
          ‖fockOSMap hm (kgModeData hm) (massiveKGCoeff_data hm) B‖ *
            Real.exp (-(m * τ))) ∧
    (freeKGOSHolomorphicSemigroup hm).IsWeaklyHolomorphic ∧
    (freeKGFullForwardConeOSReconstructedWightman hm).W = freeKGW m hm ∧
    (freeKGForwardConeOSReconstructedWightman hm).W = freeKGW m hm ∧
    (freeKGOSTubeExtensionData hm).W = freeKGW m hm ∧
    (freeKGFullOSTubeExtensionData hm).W = freeKGW m hm ∧
    (∀ {n : ℕ}, n ≤ 2 →
      osTwoPointWightmanFamily (freeKGOSAxioms hm) (freeKGOSTimeCluster hm)
        (freeKGS_positiveTimeTwoPointPowerBound hm) n = freeKGW m hm n) ∧
    OSDampedFieldBounded (freeKGOSAxioms hm).toReflectionPositiveData ∧
    OSDampedFieldBounded
      (freeKGFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData ∧
    osReconstructedWightmanFamily (freeKGOSAxioms hm) (freeKGOSTimeCluster hm)
      (freeKGOSDampedFieldBounded hm) = freeKGW m hm ∧
    osReconstructedWightmanFamily (freeKGFullEuclidOSAxioms hm).toOSAxioms
      (freeKGFullOSTimeCluster hm) (freeKGFullOSDampedFieldBounded hm) = freeKGW m hm ∧
    OSLinearGrowthCondition (freeKGS m hm) ∧
    OSLinearGrowthCondition (freeKGFullS m hm) ∧
    osReconstructedWightmanFamily_of_linearGrowth (freeKGOSAxioms hm)
      (freeKGOSLinearGrowthCondition hm) = freeKGW m hm ∧
    osReconstructedWightmanFamily_of_linearGrowth (freeKGFullEuclidOSAxioms hm).toOSAxioms
      (freeKGFullOSLinearGrowthCondition hm) = freeKGW m hm ∧
    Positivity trivialStarStructure (freeKGW m hm) ∧
    PoincareCovariant trivialRep (freeKGW m hm) ∧
    ForwardConeSpectrumCondition (freeKGW m hm) ∧
    LocalCommutativity 1 (freeKGW m hm) ∧
    PermSpacelikeLocality 1 (freeKGW m hm) ∧
    WeakLocality 1 (freeKGW m hm) ∧
    WightmanPCT 1 trivialRep (freeKGW m hm) ∧
    WightmanVacuumNormalized trivialStarStructure (freeKGW m hm) ∧
    (∀ {a : Fin 4 → ℝ}, a ≠ 0 → WightmanClusterAlong (freeKGWightmanAxioms hm).WData a) ∧
    WightmanVacuumUnique (freeKGWightmanAxioms hm).WData
      (freeKGWightmanAxioms hm).translationInvariant ∧
    (∀ {η : ℂ}, WeakLocality η (freeKGW m hm) → η = 1) ∧
    freeKGW m hm 2 default ≠ 0 ∧
    ¬ ZeroMomentumSpectrumCondition (freeKGW m hm) := by
  have h_rec :
      (wickTemperedSpectralMeasureFamily m hm 1 massiveKGCoeff
        (massiveKGCoeff_data hm)).toWightmanFamily = freeKGW m hm :=
    wickTemperedSpectralMeasureFamily_toWightmanFamily m hm 1 massiveKGCoeff
      (massiveKGCoeff_data hm)
  refine ⟨freeKGFullEuclidOSAxioms hm,
    freeKGOSAxioms hm,
    freeKGFullS_vacuumNormalized hm,
    freeKGOSVacuumNormalized hm,
    freeKGFullS_equalTime_ne_zero hm zero_lt_one,
    fun hOS => freeKGFullS_spin_statistics hm hOS,
    fun hOS => freeKGS_spin_statistics hm hOS,
    fun hτ A B => freeKGOS_exponential_cluster hm hτ A B,
    freeKGOSHolomorphicSemigroup_isWeaklyHolomorphic hm,
    ?_,
    ?_,
    freeKGOSTubeExtensionData_W hm,
    freeKGFullOSTubeExtensionData_W hm,
    fun hn => freeKG_two_point_os_eq_freeKGW hm hn,
    freeKGOSDampedFieldBounded hm,
    freeKGFullOSDampedFieldBounded hm,
    freeKG_osReconstructedWightmanFamily_eq hm,
    freeKGFull_osReconstructedWightmanFamily_eq hm,
    freeKGOSLinearGrowthCondition hm,
    freeKGFullOSLinearGrowthCondition hm,
    freeKG_osReconstructedWightmanFamily_of_linearGrowth_eq hm,
    freeKGFull_osReconstructedWightmanFamily_of_linearGrowth_eq hm,
    freeKGPositivity hm,
    freeKGPoincareCovariant hm,
    freeKG_forwardConeSpectrumCondition hm,
    freeKG_localCommutativity hm,
    freeKG_permSpacelikeLocality hm,
    freeKGWeakLocality hm,
    freeKGWightmanPCT hm,
    freeKGWightmanVacuumNormalized hm,
    fun ha => freeKGClusterAlong hm ha,
    freeKGVacuumUnique hm,
    fun hloc => freeKG_spin_statistics hm hloc,
    freeKGW_twoPoint_ne_zero hm,
    not_zeroMomentumSpectrumCondition_freeKGW hm⟩
  · unfold freeKGFullForwardConeOSReconstructedWightman
    rw [OSMeasureReconstructionData.toForwardConeOSReconstructedWightman_W]
    exact h_rec
  · unfold freeKGForwardConeOSReconstructedWightman
    rw [OSMeasureReconstructionData.toForwardConeOSReconstructedWightman_W]
    exact h_rec

theorem freeDirac_grand_master {m : ℝ} (hm : 0 < m) :
    FullEuclidOSAxioms diracRep diracStarStructure (-1) (freeDiracFullS m hm) ∧
    OSAxioms diracRep diracStarStructure (-1) (freeDiracS m hm) ∧
    OSVacuumNormalized (freeDiracFullS m hm) ∧
    OSVacuumNormalized (freeDiracS m hm) ∧
    (∃ β : Fin 2 → Fin 2 ⊕ Fin 2, freeDiracFullS m hm 2 β (equalTimeTwoPoint 1) ≠ 0) ∧
    (∀ {η : ℂ}, FullEuclidOSAxioms diracRep diracStarStructure η (freeDiracFullS m hm) →
      η = -1) ∧
    (∀ {η : ℂ}, OSAxioms diracRep diracStarStructure η (freeDiracS m hm) → η = -1) ∧
    (∀ {τ : ℝ} (hτ : 0 ≤ τ) (A B : OSConfig (Fin 2 ⊕ Fin 2)),
      ‖osKernel diracStarStructure (freeDiracS m hm) A (osConfigTimeShift τ hτ B) -
          osKernel diracStarStructure (freeDiracS m hm) A (osVacuumConfig (Fin 2 ⊕ Fin 2)) *
            osKernel diracStarStructure (freeDiracS m hm) (osVacuumConfig (Fin 2 ⊕ Fin 2)) B‖ ≤
        ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) A‖ *
          ‖fockOSMap hm (diracModeData hm) (diracMassShellCoeff_data hm) B‖ *
            Real.exp (-(m * τ))) ∧
    (freeDiracOSHolomorphicSemigroup hm).IsWeaklyHolomorphic ∧
    (freeDiracFullForwardConeOSReconstructedWightman hm).W = freeDiracW m hm ∧
    (freeDiracForwardConeOSReconstructedWightman hm).W = freeDiracW m hm ∧
    (freeDiracOSTubeExtensionData hm).W = freeDiracW m hm ∧
    (freeDiracFullOSTubeExtensionData hm).W = freeDiracW m hm ∧
    (∀ {n : ℕ}, n ≤ 2 →
      osTwoPointWightmanFamily (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm)
        (freeDiracS_positiveTimeTwoPointPowerBound hm) n = freeDiracW m hm n) ∧
    OSDampedFieldBounded (freeDiracOSAxioms hm).toReflectionPositiveData ∧
    OSDampedFieldBounded
      (freeDiracFullEuclidOSAxioms hm).toOSAxioms.toReflectionPositiveData ∧
    osReconstructedWightmanFamily (freeDiracOSAxioms hm) (freeDiracOSTimeCluster hm)
      (freeDiracOSDampedFieldBounded hm) = freeDiracW m hm ∧
    osReconstructedWightmanFamily (freeDiracFullEuclidOSAxioms hm).toOSAxioms
      (freeDiracFullOSTimeCluster hm) (freeDiracFullOSDampedFieldBounded hm) =
      freeDiracW m hm ∧
    OSLinearGrowthCondition (freeDiracS m hm) ∧
    OSLinearGrowthCondition (freeDiracFullS m hm) ∧
    osReconstructedWightmanFamily_of_linearGrowth (freeDiracOSAxioms hm)
      (freeDiracOSLinearGrowthCondition hm) = freeDiracW m hm ∧
    osReconstructedWightmanFamily_of_linearGrowth (freeDiracFullEuclidOSAxioms hm).toOSAxioms
      (freeDiracFullOSLinearGrowthCondition hm) = freeDiracW m hm ∧
    Positivity diracStarStructure (freeDiracW m hm) ∧
    PoincareCovariant diracRep (freeDiracW m hm) ∧
    ForwardConeSpectrumCondition (freeDiracW m hm) ∧
    LocalCommutativity (-1) (freeDiracW m hm) ∧
    PermSpacelikeLocality (-1) (freeDiracW m hm) ∧
    WeakLocality (-1) (freeDiracW m hm) ∧
    WightmanPCT (-1) diracRep (freeDiracW m hm) ∧
    WightmanVacuumNormalized diracStarStructure (freeDiracW m hm) ∧
    (∀ {a : Fin 4 → ℝ}, a ≠ 0 → WightmanClusterAlong (freeDiracWightmanAxioms hm).WData a) ∧
    WightmanVacuumUnique (freeDiracWightmanAxioms hm).WData
      (freeDiracWightmanAxioms hm).translationInvariant ∧
    (∀ {η : ℂ}, WeakLocality η (freeDiracW m hm) → η = -1) ∧
    (∃ β : Fin 2 → Fin 2 ⊕ Fin 2, freeDiracW m hm 2 β ≠ 0) ∧
    ¬ ZeroMomentumSpectrumCondition (freeDiracW m hm) := by
  have h_rec :
      (wickTemperedSpectralMeasureFamily m hm (-1) (diracMassShellCoeff m)
        (diracMassShellCoeff_data hm)).toWightmanFamily = freeDiracW m hm :=
    wickTemperedSpectralMeasureFamily_toWightmanFamily m hm (-1) (diracMassShellCoeff m)
      (diracMassShellCoeff_data hm)
  refine ⟨freeDiracFullEuclidOSAxioms hm,
    freeDiracOSAxioms hm,
    freeDiracFullS_vacuumNormalized hm,
    freeDiracOSVacuumNormalized hm,
    freeDiracFullS_equalTime_exists_ne_zero hm zero_lt_one,
    fun hOS => freeDiracFullS_spin_statistics hm hOS,
    fun hOS => freeDiracS_spin_statistics hm hOS,
    fun hτ A B => freeDiracOS_exponential_cluster hm hτ A B,
    freeDiracOSHolomorphicSemigroup_isWeaklyHolomorphic hm,
    ?_,
    ?_,
    freeDiracOSTubeExtensionData_W hm,
    freeDiracFullOSTubeExtensionData_W hm,
    fun hn => freeDirac_two_point_os_eq_freeDiracW hm hn,
    freeDiracOSDampedFieldBounded hm,
    freeDiracFullOSDampedFieldBounded hm,
    freeDirac_osReconstructedWightmanFamily_eq hm,
    freeDiracFull_osReconstructedWightmanFamily_eq hm,
    freeDiracOSLinearGrowthCondition hm,
    freeDiracFullOSLinearGrowthCondition hm,
    freeDirac_osReconstructedWightmanFamily_of_linearGrowth_eq hm,
    freeDiracFull_osReconstructedWightmanFamily_of_linearGrowth_eq hm,
    freeDiracPositivity hm,
    freeDiracPoincareCovariant hm,
    freeDirac_forwardConeSpectrumCondition hm,
    freeDirac_localCommutativity hm,
    freeDirac_permSpacelikeLocality hm,
    freeDiracWeakLocality hm,
    freeDiracWightmanPCT hm,
    freeDiracWightmanVacuumNormalized hm,
    fun ha => freeDiracClusterAlong hm ha,
    freeDiracVacuumUnique hm,
    fun hloc => freeDirac_spin_statistics hm hloc,
    freeDiracW_twoPoint_nondegenerate hm,
    not_zeroMomentumSpectrumCondition_freeDiracW hm⟩
  · unfold freeDiracFullForwardConeOSReconstructedWightman
    rw [OSMeasureReconstructionData.toForwardConeOSReconstructedWightman_W]
    exact h_rec
  · unfold freeDiracForwardConeOSReconstructedWightman
    rw [OSMeasureReconstructionData.toForwardConeOSReconstructedWightman_W]
    exact h_rec

end

end QFT
