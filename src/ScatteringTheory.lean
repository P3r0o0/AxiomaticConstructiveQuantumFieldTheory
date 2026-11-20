import WightmanBridge
import FreeFieldFock
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Normed.Operator.Extend

open scoped ComplexConjugate Topology BigOperators Matrix InnerProductSpace FourierTransform
open scoped ContDiff
open Geometry Geometry.MatrixAnalysis MeasureTheory Filter Complex Matrix

namespace QFT

noncomputable section

def velocityVec (m : ℝ) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (massShellEnergy m p)⁻¹ • p

@[simp]
lemma velocityVec_apply (m : ℝ) (p : Fin 3 → ℝ) (j : Fin 3) :
    velocityVec m p j = (massShellEnergy m p)⁻¹ * p j := rfl

lemma contDiff_massShellSpatialSq :
    ContDiff ℝ (⊤ : ℕ∞) massShellSpatialSq := by
  unfold massShellSpatialSq
  have hc : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (p j) ^ 2) :=
    fun j => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).contDiff).pow 2
  exact ((hc 0).add (hc 1)).add (hc 2)

lemma contDiff_massShellEnergy {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ (⊤ : ℕ∞) (massShellEnergy m) := by
  unfold massShellEnergy
  refine ContDiff.sqrt (contDiff_const.add contDiff_massShellSpatialSq) fun p => ?_
  have hpos : 0 < m ^ 2 + massShellSpatialSq p :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hm) (massShellSpatialSq_nonneg p)
  exact hpos.ne'

lemma contDiff_velocityVec {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityVec m) := by
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (massShellEnergy m p)⁻¹) :=
    (contDiff_massShellEnergy hm).inv fun p => (massShellEnergy_pos hm p).ne'
  exact hinv.smul contDiff_id

lemma sum_sq_velocityVec_eq {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    (∑ j : Fin 3, (velocityVec m p j) ^ 2) =
      massShellSpatialSq p / (massShellEnergy m p) ^ 2 := by
  have he_ne : massShellEnergy m p ≠ 0 := (massShellEnergy_pos hm p).ne'
  rw [Fin.sum_univ_three]
  unfold massShellSpatialSq velocityVec
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [he_ne]

lemma one_sub_sum_sq_velocityVec {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    1 - (∑ j : Fin 3, (velocityVec m p j) ^ 2) = m ^ 2 / (massShellEnergy m p) ^ 2 := by
  have he_ne : massShellEnergy m p ≠ 0 := (massShellEnergy_pos hm p).ne'
  rw [sum_sq_velocityVec_eq hm p]
  have hsq := massShellEnergy_sq m p
  field_simp [he_ne]
  linarith

lemma sum_sq_velocityVec_lt_one {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    ∑ j : Fin 3, (velocityVec m p j) ^ 2 < 1 := by
  have hdiff : 0 < 1 - ∑ j : Fin 3, (velocityVec m p j) ^ 2 := by
    rw [one_sub_sum_sq_velocityVec hm p]
    exact div_pos (sq_pos_of_pos hm) (sq_pos_of_pos (massShellEnergy_pos hm p))
  linarith

lemma abs_velocityVec_apply_lt_one {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) (j : Fin 3) :
    |velocityVec m p j| < 1 := by
  have h_sq_le : (velocityVec m p j) ^ 2 ≤ ∑ k : Fin 3, (velocityVec m p k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (velocityVec m p k)) (Finset.mem_univ j)
  have h_sq_lt : (velocityVec m p j) ^ 2 < 1 := h_sq_le.trans_lt (sum_sq_velocityVec_lt_one hm p)
  exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

lemma norm_velocityVec_lt_one {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    ‖velocityVec m p‖ < 1 := by
  have hnn : ‖velocityVec m p‖₊ < 1 := by
    rw [Pi.nnnorm_def, Finset.sup_lt_iff (by norm_num : (0 : NNReal) < 1)]
    intro j _
    exact_mod_cast abs_velocityVec_apply_lt_one hm p j
  exact_mod_cast hnn

lemma norm_velocityVec_le_one {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    ‖velocityVec m p‖ ≤ 1 :=
  (norm_velocityVec_lt_one hm p).le

lemma velocityVec_injective {m : ℝ} (hm : 0 < m) :
    Function.Injective (velocityVec m) := by
  intro p q hpq
  have he_p : 0 < massShellEnergy m p := massShellEnergy_pos hm p
  have he_q : 0 < massShellEnergy m q := massShellEnergy_pos hm q
  have h_inv_sq : m ^ 2 / (massShellEnergy m p) ^ 2 = m ^ 2 / (massShellEnergy m q) ^ 2 := by
    rw [← one_sub_sum_sq_velocityVec hm p, ← one_sub_sum_sq_velocityVec hm q, hpq]
  have hm_sq_ne : m ^ 2 ≠ 0 := (sq_pos_of_pos hm).ne'
  have h_eq_sq : (massShellEnergy m p) ^ 2 = (massShellEnergy m q) ^ 2 := by
    have hinv : ((massShellEnergy m p) ^ 2)⁻¹ = ((massShellEnergy m q) ^ 2)⁻¹ := by
      simpa [div_eq_mul_inv, hm_sq_ne] using h_inv_sq
    exact inv_injective hinv
  have h_eq_e : massShellEnergy m p = massShellEnergy m q := by
    nlinarith [he_p, he_q]
  calc p = (massShellEnergy m p) • velocityVec m p := by
        dsimp [velocityVec]
        rw [smul_smul, mul_inv_cancel₀ he_p.ne', one_smul]
    _ = (massShellEnergy m q) • velocityVec m q := by rw [h_eq_e, hpq]
    _ = q := by
        dsimp [velocityVec]
        rw [smul_smul, mul_inv_cancel₀ he_q.ne', one_smul]

structure SmoothWavepacket where
  amp : (Fin 3 → ℝ) → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) amp
  compactSupport : HasCompactSupport amp

def velocitySupport (m : ℝ) (f : SmoothWavepacket) : Set (Fin 3 → ℝ) :=
  velocityVec m '' tsupport f.amp

lemma isCompact_velocitySupport {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) :
    IsCompact (velocitySupport m f) :=
  f.compactSupport.isCompact.image (contDiff_velocityVec hm).continuous

lemma exists_velocitySupport_norm_bound {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) :
    ∃ vmax : ℝ, 0 ≤ vmax ∧ vmax < 1 ∧ ∀ v ∈ velocitySupport m f, ‖v‖ ≤ vmax := by
  by_cases hne : (velocitySupport m f).Nonempty
  · obtain ⟨v₀, hv₀, hv₀_max⟩ :=
      (isCompact_velocitySupport hm f).exists_isMaxOn hne continuous_norm.continuousOn
    obtain ⟨p₀, _, rfl⟩ := hv₀
    refine ⟨‖velocityVec m p₀‖, norm_nonneg _, norm_velocityVec_lt_one hm p₀, ?_⟩
    intro v hv
    exact hv₀_max hv
  · refine ⟨0, le_rfl, zero_lt_one, fun v hv => False.elim (hne ⟨v, hv⟩)⟩

def VelocityDisjoint (m : ℝ) (f₁ f₂ : SmoothWavepacket) : Prop :=
  Disjoint (velocitySupport m f₁) (velocitySupport m f₂)

lemma velocityDisjoint_iff_tsupport_disjoint {m : ℝ} (hm : 0 < m) (f₁ f₂ : SmoothWavepacket) :
    VelocityDisjoint m f₁ f₂ ↔ Disjoint (tsupport f₁.amp) (tsupport f₂.amp) :=
  Set.disjoint_image_iff (velocityVec_injective hm)

lemma exists_pos_sep_of_velocityDisjoint {m : ℝ} (hm : 0 < m)
    {f₁ f₂ : SmoothWavepacket} (hdisj : VelocityDisjoint m f₁ f₂) :
    ∃ d_sep : ℝ, 0 < d_sep ∧
      ∀ v₁ ∈ velocitySupport m f₁, ∀ v₂ ∈ velocitySupport m f₂, d_sep ≤ ‖v₁ - v₂‖ := by
  by_cases h1 : (velocitySupport m f₁).Nonempty
  · by_cases h2 : (velocitySupport m f₂).Nonempty
    · have hc_prod : IsCompact (velocitySupport m f₁ ×ˢ velocitySupport m f₂) :=
        (isCompact_velocitySupport hm f₁).prod (isCompact_velocitySupport hm f₂)
      have hne_prod : (velocitySupport m f₁ ×ˢ velocitySupport m f₂).Nonempty := h1.prod h2
      let distFn : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ := fun q => ‖q.1 - q.2‖
      have hcont : Continuous distFn :=
        continuous_norm.comp (continuous_fst.sub continuous_snd)
      obtain ⟨q₀, hq₀, hq₀_min⟩ := hc_prod.exists_isMinOn hne_prod hcont.continuousOn
      have hpos : 0 < distFn q₀ := by
        refine lt_of_le_of_ne (norm_nonneg _) ?_
        intro hz
        have heq : q₀.1 = q₀.2 := sub_eq_zero.mp (norm_eq_zero.mp hz.symm)
        have hmem1 : q₀.1 ∈ velocitySupport m f₁ := hq₀.1
        have hmem2 : q₀.1 ∈ velocitySupport m f₂ := heq ▸ hq₀.2
        exact Set.disjoint_left.mp hdisj hmem1 hmem2
      refine ⟨distFn q₀, hpos, fun v₁ hv₁ v₂ hv₂ => ?_⟩
      have hmem : (v₁, v₂) ∈ velocitySupport m f₁ ×ˢ velocitySupport m f₂ := ⟨hv₁, hv₂⟩
      exact hq₀_min hmem
    · refine ⟨1, zero_lt_one, fun _ _ v₂ hv₂ => ?_⟩
      exact (h2 ⟨v₂, hv₂⟩).elim
  · refine ⟨1, zero_lt_one, fun v₁ hv₁ _ _ => ?_⟩
    exact (h1 ⟨v₁, hv₁⟩).elim

noncomputable def bumpWavepacket (c : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r) : SmoothWavepacket where
  amp x := ((({ rIn := r, rOut := 2 * r, rIn_pos := hr, rIn_lt_rOut := by linarith } :
    ContDiffBump c) x : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp
    ({ rIn := r, rOut := 2 * r, rIn_pos := hr, rIn_lt_rOut := by linarith } :
      ContDiffBump c).contDiff
  compactSupport :=
    ({ rIn := r, rOut := 2 * r, rIn_pos := hr, rIn_lt_rOut := by linarith } :
      ContDiffBump c).hasCompactSupport.comp_left Complex.ofReal_zero

@[simp]
lemma bumpWavepacket_apply_center (c : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r) :
    (bumpWavepacket c r hr).amp c = 1 := by
  let b : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  have hb : b c = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self hr.le)
  dsimp [bumpWavepacket]
  change ((b c : ℝ) : ℂ) = 1
  rw [hb]
  simp

lemma tsupport_bumpWavepacket_subset (c : Fin 3 → ℝ) (r : ℝ) (hr : 0 < r) :
    tsupport (bumpWavepacket c r hr).amp ⊆ Metric.closedBall c (2 * r) := by
  let b : ContDiffBump c := ⟨r, 2 * r, hr, by linarith⟩
  have hsub : Function.support (bumpWavepacket c r hr).amp ⊆ Metric.closedBall c (2 * r) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hnot
    rw [Metric.mem_closedBall, not_le] at hnot
    have hz : b x = 0 := ContDiffBump.zero_of_le_dist b hnot.le
    exact hx (by dsimp [bumpWavepacket]; rw [hz]; simp)
  exact closure_minimal hsub Metric.isClosed_closedBall

def massShellGapDelta (m M : ℝ) : ℝ :=
  min (m ^ 2) (M ^ 2 - m ^ 2) / 4

lemma massShellGapDelta_pos {m M : ℝ} (hm : 0 < m) (hM : m < M) :
    0 < massShellGapDelta m M := by
  have hm2 : 0 < m ^ 2 := sq_pos_of_pos hm
  have hM2 : 0 < M ^ 2 - m ^ 2 := by nlinarith
  unfold massShellGapDelta
  positivity

lemma massShellGapDelta_four_le_sub {m M : ℝ} :
    4 * massShellGapDelta m M ≤ M ^ 2 - m ^ 2 := by
  unfold massShellGapDelta
  linarith [min_le_right (m ^ 2) (M ^ 2 - m ^ 2)]

lemma massShellGapDelta_four_le_sq {m M : ℝ} :
    4 * massShellGapDelta m M ≤ m ^ 2 := by
  unfold massShellGapDelta
  linarith [min_le_left (m ^ 2) (M ^ 2 - m ^ 2)]

def posEnergyStep (m q0 : ℝ) : ℝ :=
  Real.smoothTransition ((4 / m) * q0 - 1)

lemma contDiff_posEnergyStep (m : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (posEnergyStep m) := by
  unfold posEnergyStep
  refine (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp ?_
  exact ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma posEnergyStep_nonneg (m q0 : ℝ) : 0 ≤ posEnergyStep m q0 :=
  Real.smoothTransition.nonneg _

lemma posEnergyStep_le_one (m q0 : ℝ) : posEnergyStep m q0 ≤ 1 :=
  Real.smoothTransition.le_one _

lemma posEnergyStep_eq_one_of_ge {m q0 : ℝ} (hm : 0 < m) (hq : m / 2 ≤ q0) :
    posEnergyStep m q0 = 1 := by
  unfold posEnergyStep
  refine Real.smoothTransition.one_of_one_le ?_
  have h1 : 2 ≤ (4 / m) * q0 := by
    have h_mul := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 4 / m)
    have h_eq : (4 / m) * (m / 2) = 2 := by
      field_simp [hm.ne']
      norm_num
    linarith
  linarith

lemma posEnergyStep_eq_zero_of_le {m q0 : ℝ} (hm : 0 < m) (hq : q0 ≤ m / 4) :
    posEnergyStep m q0 = 0 := by
  unfold posEnergyStep
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h1 : (4 / m) * q0 ≤ 1 := by
    have h_mul := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 4 / m)
    have h_eq : (4 / m) * (m / 4) = 1 := by field_simp [hm.ne']
    linarith
  linarith

def massSqBump (m M : ℝ) (hm : 0 < m) (hM : m < M) : ContDiffBump (m ^ 2) where
  rIn := massShellGapDelta m M
  rOut := 2 * massShellGapDelta m M
  rIn_pos := massShellGapDelta_pos hm hM
  rIn_lt_rOut := by linarith [massShellGapDelta_pos hm hM]

def massShellCutoff (m M : ℝ) (hm : 0 < m) (hM : m < M) (q : Fin 4 → ℝ) : ℝ :=
  posEnergyStep m (q 0) * massSqBump m M hm hM (minkowskiInner q q)

lemma contDiff_minkowskiInner_self :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => minkowskiInner q q) := by
  have hc : ∀ μ : Fin 4, ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q μ) :=
    fun μ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).contDiff
  have heq : (fun q : Fin 4 → ℝ => minkowskiInner q q) =
      fun q => q 0 * q 0 - q 1 * q 1 - q 2 * q 2 - q 3 * q 3 := by
    ext q
    rw [minkowskiInner_explicit]
  rw [heq]
  exact ((((hc 0).mul (hc 0)).sub ((hc 1).mul (hc 1))).sub
    ((hc 2).mul (hc 2))).sub ((hc 3).mul (hc 3))

lemma contDiff_massShellCutoff (m M : ℝ) (hm : 0 < m) (hM : m < M) :
    ContDiff ℝ (⊤ : ℕ∞) (massShellCutoff m M hm hM) := by
  unfold massShellCutoff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => posEnergyStep m (q 0)) :=
    (contDiff_posEnergyStep m).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Fin 4 → ℝ => massSqBump m M hm hM (minkowskiInner q q)) :=
    (massSqBump m M hm hM).contDiff.comp contDiff_minkowskiInner_self
  exact h1.mul h2

lemma massShellCutoff_nonneg (m M : ℝ) (hm : 0 < m) (hM : m < M) (q : Fin 4 → ℝ) :
    0 ≤ massShellCutoff m M hm hM q :=
  mul_nonneg (posEnergyStep_nonneg m (q 0)) (massSqBump m M hm hM).nonneg

lemma massShellCutoff_le_one (m M : ℝ) (hm : 0 < m) (hM : m < M) (q : Fin 4 → ℝ) :
    massShellCutoff m M hm hM q ≤ 1 :=
  mul_le_one₀ (posEnergyStep_le_one m (q 0)) (massSqBump m M hm hM).nonneg
    (massSqBump m M hm hM).le_one

lemma massShellCutoff_massShellVec (m M : ℝ) (hm : 0 < m) (hM : m < M) (k : Fin 3 → ℝ) :
    massShellCutoff m M hm hM (massShellVec m k) = 1 := by
  unfold massShellCutoff
  have h0 : m / 2 ≤ massShellVec m k 0 := by
    change m / 2 ≤ massShellEnergy m k
    linarith [massShellEnergy_ge_mass hm k]
  have hs1 : posEnergyStep m (massShellVec m k 0) = 1 := posEnergyStep_eq_one_of_ge hm h0
  have hs2 : massSqBump m M hm hM (minkowskiInner (massShellVec m k) (massShellVec m k)) = 1 := by
    rw [minkowskiInner_massShellVec_self]
    exact (massSqBump m M hm hM).one_of_mem_closedBall
      (Metric.mem_closedBall_self (massShellGapDelta_pos hm hM).le)
  rw [hs1, hs2, mul_one]

lemma massShellCutoff_eq_zero_of_le (m M : ℝ) (hm : 0 < m) (hM : m < M)
    {q : Fin 4 → ℝ} (hq : q 0 ≤ m / 4) :
    massShellCutoff m M hm hM q = 0 := by
  unfold massShellCutoff
  rw [posEnergyStep_eq_zero_of_le hm hq, zero_mul]

lemma massShellCutoff_eq_zero_of_ge_threshold (m M : ℝ) (hm : 0 < m) (hM : m < M)
    {q : Fin 4 → ℝ} (hq : M ^ 2 ≤ minkowskiInner q q) :
    massShellCutoff m M hm hM q = 0 := by
  unfold massShellCutoff
  have hdist : (massSqBump m M hm hM).rOut ≤ dist (minkowskiInner q q) (m ^ 2) := by
    have hd := massShellGapDelta_four_le_sub (m := m) (M := M)
    have hpos := massShellGapDelta_pos hm hM
    change 2 * massShellGapDelta m M ≤ |minkowskiInner q q - m ^ 2|
    have hnonneg : 0 ≤ minkowskiInner q q - m ^ 2 := by nlinarith
    rw [abs_of_nonneg hnonneg]
    linarith
  rw [ContDiffBump.zero_of_le_dist _ hdist, mul_zero]

lemma massShellCutoff_support_bounds {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {q : Fin 4 → ℝ} (hq : massShellCutoff m M hm hM q ≠ 0) :
    m / 4 < q 0 ∧
      |minkowskiInner q q - m ^ 2| ≤ 2 * massShellGapDelta m M ∧
      minkowskiInner q q < M ^ 2 := by
  have h0 : m / 4 < q 0 := by
    by_contra hnot
    exact hq (massShellCutoff_eq_zero_of_le m M hm hM (not_lt.mp hnot))
  have h_bump : massSqBump m M hm hM (minkowskiInner q q) ≠ 0 := by
    intro hb
    exact hq (by unfold massShellCutoff; rw [hb, mul_zero])
  have h_lt : dist (minkowskiInner q q) (m ^ 2) < 2 * massShellGapDelta m M := by
    by_contra hnot
    exact h_bump (ContDiffBump.zero_of_le_dist _ (not_lt.mp hnot))
  have h_abs : |minkowskiInner q q - m ^ 2| < 2 * massShellGapDelta m M := by
    simpa [Real.dist_eq] using h_lt
  have h_sub := massShellGapDelta_four_le_sub (m := m) (M := M)
  have h_pos := massShellGapDelta_pos hm hM
  have h_lt_M : minkowskiInner q q < M ^ 2 := by
    have := abs_lt.mp h_abs
    linarith
  exact ⟨h0, h_abs.le, h_lt_M⟩

lemma massShellCutoff_eq_one_near_massShell {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {q : Fin 4 → ℝ} (hq0 : m / 2 ≤ q 0)
    (hq_sq : |minkowskiInner q q - m ^ 2| ≤ massShellGapDelta m M) :
    massShellCutoff m M hm hM q = 1 := by
  unfold massShellCutoff
  have h1 : posEnergyStep m (q 0) = 1 := posEnergyStep_eq_one_of_ge hm hq0
  have h2 : massSqBump m M hm hM (minkowskiInner q q) = 1 := by
    refine (massSqBump m M hm hM).one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hq_sq
  rw [h1, h2, mul_one]

def timeModMomAmp (m : ℝ) (base : (Fin 4 → ℝ) → ℂ) (t : ℝ) (q : Fin 4 → ℝ) : ℂ :=
  base q * Complex.exp (Complex.I * (((q 0 - massShellEnergy m (spatialPart q)) * t : ℝ) : ℂ))

lemma contDiff_spatialPart : ContDiff ℝ (⊤ : ℕ∞) spatialPart := by
  refine contDiff_pi.mpr fun j => ?_
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j.succ).contDiff

lemma contDiff_timeModMomAmp {m : ℝ} (hm : 0 < m) {base : (Fin 4 → ℝ) → ℂ}
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (timeModMomAmp m base t) := by
  unfold timeModMomAmp
  have hc0 : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff
  have hce : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => massShellEnergy m (spatialPart q)) :=
    (contDiff_massShellEnergy hm).comp contDiff_spatialPart
  have hph : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Fin 4 → ℝ => (q 0 - massShellEnergy m (spatialPart q)) * t) :=
    (hc0.sub hce).mul contDiff_const
  exact h_sm.mul (Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hph)))

lemma hasCompactSupport_timeModMomAmp (m : ℝ) {base : (Fin 4 → ℝ) → ℂ}
    (h_supp : HasCompactSupport base) (t : ℝ) :
    HasCompactSupport (timeModMomAmp m base t) := by
  change HasCompactSupport (fun q : Fin 4 → ℝ => base q *
    Complex.exp (Complex.I * (((q 0 - massShellEnergy m (spatialPart q)) * t : ℝ) : ℂ)))
  exact h_supp.mul_right

lemma tsupport_timeModMomAmp_subset (m : ℝ) (base : (Fin 4 → ℝ) → ℂ) (t : ℝ) :
    tsupport (timeModMomAmp m base t) ⊆ tsupport base := by
  refine tsupport_mul_subset_left

lemma norm_timeModMomAmp (m : ℝ) (base : (Fin 4 → ℝ) → ℂ) (t : ℝ) (q : Fin 4 → ℝ) :
    ‖timeModMomAmp m base t q‖ = ‖base q‖ := by
  unfold timeModMomAmp
  have h_im : Complex.I * (((q 0 - massShellEnergy m (spatialPart q)) * t : ℝ) : ℂ) =
      (((q 0 - massShellEnergy m (spatialPart q)) * t : ℝ) : ℂ) * Complex.I := by
    ring
  rw [norm_mul, h_im, Complex.norm_exp_ofReal_mul_I, mul_one]

def momNegArgCLE : (Fin 1 → Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) where
  toFun p := -(p 0)
  invFun q _ := -q
  left_inv p := by
    ext i μ
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp
  right_inv q := by
    ext μ
    simp
  map_add' p₁ p₂ := by
    ext μ
    simp
    ring
  map_smul' c p := by simp [smul_neg]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
lemma momNegArgCLE_apply (p : Fin 1 → Fin 4 → ℝ) :
    momNegArgCLE p = -(p 0) := rfl

@[simp]
lemma momNegArgCLE_symm_apply (q : Fin 4 → ℝ) (i : Fin 1) :
    momNegArgCLE.symm q i = -q := rfl

def timeModMomSchwartz (m : ℝ) (hm : 0 < m) (base : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (h_supp : HasCompactSupport base) (t : ℝ) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  ((hasCompactSupport_timeModMomAmp m h_supp t).comp_homeomorph
      momNegArgCLE.toHomeomorph).toSchwartzMap
    ((contDiff_timeModMomAmp hm h_sm t).comp momNegArgCLE.contDiff)

@[simp]
lemma timeModMomSchwartz_apply (m : ℝ) (hm : 0 < m) (base : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (h_supp : HasCompactSupport base) (t : ℝ)
    (p : Fin 1 → Fin 4 → ℝ) :
    timeModMomSchwartz m hm base h_sm h_supp t p = timeModMomAmp m base t (-(p 0)) := rfl

def timeModTestFn (m : ℝ) (hm : 0 < m) (base : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (h_supp : HasCompactSupport base) (t : ℝ) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  invMinkowskiFourierCLM 1 (timeModMomSchwartz m hm base h_sm h_supp t)

lemma minkowskiFourier_timeModTestFn (m : ℝ) (hm : 0 < m) (base : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (h_supp : HasCompactSupport base) (t : ℝ)
    (q : Fin 4 → ℝ) :
    minkowskiFourier (timeModTestFn m hm base h_sm h_supp t) (fun _ => -q) =
      timeModMomAmp m base t q := by
  unfold timeModTestFn
  rw [minkowskiFourier_invMinkowskiFourierCLM_one, timeModMomSchwartz_apply]
  simp

def haagRuelleBaseAmp (m M : ℝ) (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket)
    (q : Fin 4 → ℝ) : ℂ :=
  f.amp (spatialPart q) * (massShellCutoff m M hm hM q : ℂ)

def haagRuelleDerivBaseAmp (m M : ℝ) (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket)
    (q : Fin 4 → ℝ) : ℂ :=
  (Complex.I * ((q 0 - massShellEnergy m (spatialPart q) : ℝ) : ℂ)) *
    haagRuelleBaseAmp m M hm hM f q

lemma contDiff_haagRuelleBaseAmp (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) :
    ContDiff ℝ (⊤ : ℕ∞) (haagRuelleBaseAmp m M hm hM f) :=
  (f.smooth.comp contDiff_spatialPart).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_massShellCutoff m M hm hM))

lemma contDiff_haagRuelleDerivBaseAmp (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) :
    ContDiff ℝ (⊤ : ℕ∞) (haagRuelleDerivBaseAmp m M hm hM f) := by
  unfold haagRuelleDerivBaseAmp
  have hc0 : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff
  have hce : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => massShellEnergy m (spatialPart q)) :=
    (contDiff_massShellEnergy hm).comp contDiff_spatialPart
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hc0.sub hce))).mul
    (contDiff_haagRuelleBaseAmp m M hm hM f)

lemma hasCompactSupport_haagRuelleBaseAmp (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) :
    HasCompactSupport (haagRuelleBaseAmp m M hm hM f) := by
  obtain ⟨Rf, hRf⟩ := Metric.isBounded_iff_subset_ball (0 : Fin 3 → ℝ) |>.mp
    f.compactSupport.isCompact.isBounded
  let Rf' : ℝ := max Rf 0
  let R0 : ℝ := Real.sqrt (M ^ 2 + 3 * Rf' ^ 2)
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin 4 → ℝ) (max R0 Rf')) fun q hq => ?_
  rw [Function.mem_support] at hq
  have hf_ne : f.amp (spatialPart q) ≠ 0 := by
    intro hz
    exact hq (by unfold haagRuelleBaseAmp; rw [hz, zero_mul])
  have hc_ne : massShellCutoff m M hm hM q ≠ 0 := by
    intro hz
    exact hq (by unfold haagRuelleBaseAmp; rw [hz]; simp)
  have hsp_norm : ‖spatialPart q‖ ≤ Rf' := by
    have hmem : spatialPart q ∈ tsupport f.amp := subset_tsupport _ (Function.mem_support.mpr hf_ne)
    have hball : dist (spatialPart q) 0 < Rf := hRf hmem
    rw [dist_zero_right] at hball
    exact hball.le.trans (le_max_left _ _)
  have hsp_sq : ∀ j : Fin 3, (spatialPart q j) ^ 2 ≤ Rf' ^ 2 := by
    intro j
    have h1 : |spatialPart q j| ≤ ‖spatialPart q‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (spatialPart q) j
    have h2 : |spatialPart q j| ≤ Rf' := h1.trans hsp_norm
    nlinarith [sq_abs (spatialPart q j), abs_nonneg (spatialPart q j)]
  obtain ⟨hq0_pos, _, hq_lt_M⟩ := massShellCutoff_support_bounds hm hM hc_ne
  have hq0_nonneg : 0 ≤ q 0 := by linarith
  have hq0_sq : (q 0) ^ 2 ≤ M ^ 2 + 3 * Rf' ^ 2 := by
    have hm_exp : minkowskiInner q q =
        (q 0) ^ 2 - (spatialPart q 0) ^ 2 - (spatialPart q 1) ^ 2 - (spatialPart q 2) ^ 2 := by
      rw [minkowskiInner_explicit]
      simp [spatialPart]
      ring
    linarith [hsp_sq 0, hsp_sq 1, hsp_sq 2]
  have hq0_le : |q 0| ≤ R0 := by
    rw [abs_of_nonneg hq0_nonneg]
    calc q 0 = Real.sqrt ((q 0) ^ 2) := (Real.sqrt_sq hq0_nonneg).symm
      _ ≤ Real.sqrt (M ^ 2 + 3 * Rf' ^ 2) := Real.sqrt_le_sqrt hq0_sq
  rw [Metric.mem_closedBall, dist_zero_right,
      pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ max R0 Rf')]
  intro μ
  fin_cases μ
  · simpa [Real.norm_eq_abs] using hq0_le.trans (le_max_left _ _)
  · have h_j := (norm_le_pi_norm (spatialPart q) 0).trans hsp_norm
    exact h_j.trans (le_max_right _ _)
  · have h_j := (norm_le_pi_norm (spatialPart q) 1).trans hsp_norm
    exact h_j.trans (le_max_right _ _)
  · have h_j := (norm_le_pi_norm (spatialPart q) 2).trans hsp_norm
    exact h_j.trans (le_max_right _ _)

lemma hasCompactSupport_haagRuelleDerivBaseAmp (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) :
    HasCompactSupport (haagRuelleDerivBaseAmp m M hm hM f) := by
  change HasCompactSupport (fun q : Fin 4 → ℝ =>
    (Complex.I * ((q 0 - massShellEnergy m (spatialPart q) : ℝ) : ℂ)) *
      haagRuelleBaseAmp m M hm hM f q)
  exact (hasCompactSupport_haagRuelleBaseAmp m M hm hM f).mul_left

lemma tsupport_haagRuelleBaseAmp_spatialPart_subset (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) :
    spatialPart '' tsupport (haagRuelleBaseAmp m M hm hM f) ⊆ tsupport f.amp := by
  rintro _ ⟨q, hq, rfl⟩
  have hsub : tsupport (haagRuelleBaseAmp m M hm hM f) ⊆
      tsupport (fun q' => f.amp (spatialPart q')) := tsupport_mul_subset_left
  exact tsupport_comp_subset_preimage f.amp contDiff_spatialPart.continuous (hsub hq)

lemma tsupport_haagRuelleDerivBaseAmp_subset (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) :
    tsupport (haagRuelleDerivBaseAmp m M hm hM f) ⊆
      tsupport (haagRuelleBaseAmp m M hm hM f) :=
  tsupport_mul_subset_right

def haagRuelleTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModTestFn m hm (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) t

def haagRuelleDerivTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModTestFn m hm (haagRuelleDerivBaseAmp m M hm hM f)
    (contDiff_haagRuelleDerivBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleDerivBaseAmp m M hm hM f) t

lemma minkowskiFourier_haagRuelleTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (t : ℝ) (q : Fin 4 → ℝ) :
    minkowskiFourier (haagRuelleTestFn m M hm hM f t) (fun _ => -q) =
      timeModMomAmp m (haagRuelleBaseAmp m M hm hM f) t q :=
  minkowskiFourier_timeModTestFn m hm (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) t q

lemma minkowskiFourier_haagRuelleTestFn_massShell (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (t : ℝ) (k : Fin 3 → ℝ) :
    minkowskiFourier (haagRuelleTestFn m M hm hM f t) (fun _ => -massShellVec m k) = f.amp k := by
  rw [minkowskiFourier_haagRuelleTestFn]
  unfold timeModMomAmp haagRuelleBaseAmp
  have hsp : spatialPart (massShellVec m k) = k := by
    ext j
    fin_cases j <;> rfl
  have h0 : massShellVec m k 0 = massShellEnergy m k := rfl
  rw [hsp, h0, sub_self, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      massShellCutoff_massShellVec m M hm hM k]
  simp

lemma minkowskiFourier_haagRuelleDerivTestFn_massShell (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (t : ℝ) (k : Fin 3 → ℝ) :
    minkowskiFourier (haagRuelleDerivTestFn m M hm hM f t) (fun _ => -massShellVec m k) = 0 := by
  unfold haagRuelleDerivTestFn
  rw [minkowskiFourier_timeModTestFn]
  unfold timeModMomAmp haagRuelleDerivBaseAmp
  have hsp : spatialPart (massShellVec m k) = k := by
    ext j
    fin_cases j <;> rfl
  have h0 : massShellVec m k 0 = massShellEnergy m k := rfl
  rw [hsp, h0, sub_self]
  simp

lemma norm_exp_ofReal_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp (((θ : ℝ) : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  let φ : ℝ → ℂ := fun u => Complex.exp (((u : ℝ) : ℂ) * Complex.I)
  have hderiv : ∀ u : ℝ, HasDerivAt φ (Complex.exp (((u : ℝ) : ℂ) * Complex.I) * Complex.I) u := by
    intro u
    have h_in : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ) * Complex.I) (1 * Complex.I) u :=
      (Complex.ofRealCLM.hasFDerivAt (x := u)).hasDerivAt.mul_const Complex.I
    refine ((Complex.hasDerivAt_exp (((u : ℝ) : ℂ) * Complex.I)).scomp u h_in).congr_deriv ?_
    ring
  have hbd := (convex_univ : Convex ℝ Set.univ).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (hderiv u).differentiableAt)
    (fun u _ => by
      rw [(hderiv u).deriv, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one])
    (Set.mem_univ 0) (Set.mem_univ θ)
  have h0 : φ 0 = 1 := by simp [φ]
  rw [h0, one_mul, Real.norm_eq_abs, sub_zero] at hbd
  exact hbd

lemma deriv_diffQuoKernel {h : ℝ} (hh : h ≠ 0) (a : ℝ) :
    HasDerivAt
      (fun u : ℝ => ((h⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)) - 1) -
        Complex.I * (u : ℂ))
      (Complex.I * (Complex.exp (Complex.I * ((h * a : ℝ) : ℂ)) - 1)) a := by
  have h_re : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 a :=
    Complex.ofRealCLM.hasFDerivAt (x := a) |>.hasDerivAt
  have h_arg : HasDerivAt (fun u : ℝ => Complex.I * ((h : ℂ) * (u : ℂ)))
      (Complex.I * ((h : ℂ) * 1)) a := by
    simpa using (h_re.const_mul (h : ℂ)).const_mul Complex.I
  have h_exp : HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)))
      (Complex.exp (Complex.I * ((h * a : ℝ) : ℂ)) * (Complex.I * ((h : ℂ) * 1))) a := by
    have h_eq : (fun u : ℝ => Complex.exp (Complex.I * ((h * u : ℝ) : ℂ))) =
        Complex.exp ∘ fun u : ℝ => Complex.I * ((h : ℂ) * (u : ℂ)) := by
      ext u
      simp [Complex.ofReal_mul]
    rw [h_eq]
    have he := (Complex.hasDerivAt_exp (Complex.I * ((h : ℂ) * (a : ℂ)))).scomp a h_arg
    refine he.congr_deriv ?_
    rw [Complex.ofReal_mul]
    ring
  have h_sub := ((h_exp.sub_const 1).const_mul ((h⁻¹ : ℝ) : ℂ)).sub (h_re.const_mul Complex.I)
  refine h_sub.congr_deriv ?_
  have hh_c : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  simp only [Complex.ofReal_inv]
  field_simp [hh_c]

lemma iteratedDeriv_const_mul_exp_mul (c d : ℂ) (n : ℕ) (a : ℝ) :
    iteratedDeriv n (fun u : ℝ => c * Complex.exp ((u : ℂ) * d)) a =
      c * d ^ n * Complex.exp ((a : ℂ) * d) := by
  induction n generalizing c a with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have h_fn : deriv (fun v : ℝ => c * Complex.exp ((v : ℂ) * d)) =
        fun u : ℝ => (c * d) * Complex.exp ((u : ℂ) * d) := by
      ext u
      have h_in : HasDerivAt (fun v : ℝ => (v : ℂ) * d) (1 * d) u :=
        (Complex.ofRealCLM.hasFDerivAt (x := u)).hasDerivAt.mul_const d
      have hd := ((Complex.hasDerivAt_exp ((u : ℂ) * d)).scomp u h_in).const_mul c
      change deriv (fun y : ℝ => c * (Complex.exp ∘ fun v : ℝ => (v : ℂ) * d) y) u = _
      rw [hd.deriv]
      ring
    rw [h_fn, ih (c * d) a, pow_succ']
    ring

lemma norm_iteratedDeriv_diffQuoKernel_le {h : ℝ} (hh : h ≠ 0) (hh1 : |h| ≤ 1)
    (i : ℕ) (a : ℝ) :
    ‖iteratedDeriv i
      (fun u : ℝ => ((h⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)) - 1) -
        Complex.I * (u : ℂ)) a‖ ≤ |h| * (a ^ 2 + |a| + 1) := by
  let g : ℝ → ℂ := fun u =>
    ((h⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)) - 1) - Complex.I * (u : ℂ)
  have hdiff : ∀ u : ℝ, DifferentiableAt ℝ g u :=
    fun u => (deriv_diffQuoKernel hh u).differentiableAt
  have hg_deriv : ∀ u : ℝ, deriv g u =
      Complex.I * (Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)) - 1) :=
    fun u => (deriv_diffQuoKernel hh u).deriv
  have h1_le : ∀ u : ℝ, ‖deriv g u‖ ≤ |h| * |u| := by
    intro u
    rw [hg_deriv u, norm_mul, Complex.norm_I, one_mul]
    have h_eq : Complex.I * ((h * u : ℝ) : ℂ) = (((h * u : ℝ) : ℂ)) * Complex.I := by ring
    rw [h_eq]
    calc ‖Complex.exp (((h * u : ℝ) : ℂ) * Complex.I) - 1‖ ≤ |h * u| :=
          norm_exp_ofReal_mul_I_sub_one_le (h * u)
      _ = |h| * |u| := abs_mul h u
  rcases i with _ | _ | n
  · rw [iteratedDeriv_zero]
    have hbd := (convex_uIcc 0 a).norm_image_sub_le_of_norm_deriv_le
      (fun u _ => hdiff u)
      (fun u hu => by
        have hu_le : |u| ≤ |a| := by
          rcases Set.mem_uIcc.mp hu with ⟨h0, h1⟩ | ⟨h0, h1⟩
          · rw [abs_of_nonneg h0]
            exact h1.trans (le_abs_self a)
          · rw [abs_of_nonpos h1]
            exact (neg_le_neg h0).trans (neg_le_abs a)
        calc ‖deriv g u‖ ≤ |h| * |u| := h1_le u
          _ ≤ |h| * |a| := mul_le_mul_of_nonneg_left hu_le (abs_nonneg h))
      Set.left_mem_uIcc Set.right_mem_uIcc
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0, sub_zero, Real.norm_eq_abs, sub_zero] at hbd
    have h_sq : |h| * |a| * |a| = |h| * a ^ 2 := by
      rw [mul_assoc, ← sq, sq_abs]
    rw [h_sq] at hbd
    exact hbd.trans (mul_le_mul_of_nonneg_left
      (by linarith [abs_nonneg a]) (abs_nonneg h))
  · rw [iteratedDeriv_one]
    exact (h1_le a).trans (mul_le_mul_of_nonneg_left
      (by linarith [sq_nonneg a]) (abs_nonneg h))
  · change ‖iteratedDeriv (n + 2) g a‖ ≤ _
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hg'_eq : deriv g = fun u : ℝ => Complex.I * Complex.exp ((u : ℂ) * (Complex.I * (h : ℂ))) -
        Complex.I := by
      ext u
      rw [hg_deriv u, mul_sub, mul_one, Complex.ofReal_mul]
      ring_nf
    have hg''_eq : deriv (deriv g) = fun u : ℝ =>
        (Complex.I * (Complex.I * (h : ℂ))) * Complex.exp ((u : ℂ) * (Complex.I * (h : ℂ))) := by
      ext u
      rw [hg'_eq]
      have h_in : HasDerivAt (fun v : ℝ => (v : ℂ) * (Complex.I * (h : ℂ)))
          (1 * (Complex.I * (h : ℂ))) u :=
        (Complex.ofRealCLM.hasFDerivAt (x := u)).hasDerivAt.mul_const (Complex.I * (h : ℂ))
      have hd :=
        (((Complex.hasDerivAt_exp ((u : ℂ) * (Complex.I * (h : ℂ)))).scomp u h_in).const_mul
          Complex.I).sub_const Complex.I
      change deriv (fun x : ℝ => Complex.I *
        (Complex.exp ∘ fun v : ℝ => (v : ℂ) * (Complex.I * (h : ℂ))) x - Complex.I) u = _
      rw [hd.deriv]
      ring
    rw [hg''_eq, iteratedDeriv_const_mul_exp_mul]
    have h_norm_e : ‖Complex.exp ((a : ℂ) * (Complex.I * (h : ℂ)))‖ = 1 := by
      have heq : (a : ℂ) * (Complex.I * (h : ℂ)) = (((a * h : ℝ) : ℂ)) * Complex.I := by
        push_cast; ring
      rw [heq, Complex.norm_exp_ofReal_mul_I]
    simp only [norm_mul, norm_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      h_norm_e, mul_one, ← pow_succ']
    have h_pow : |h| ^ (n + 1) ≤ |h| := by
      calc |h| ^ (n + 1) = |h| * |h| ^ n := by rw [pow_succ']
        _ ≤ |h| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg h) hh1) (abs_nonneg h)
        _ = |h| := mul_one _
    exact h_pow.trans (le_mul_of_one_le_right (abs_nonneg h)
      (by linarith [sq_nonneg a, abs_nonneg a]))

lemma contDiff_diffQuoKernel (h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ =>
      ((h⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)) - 1) -
        Complex.I * (u : ℂ)) := by
  have hc_u : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (u : ℂ)) := Complex.ofRealCLM.contDiff
  have h_arg : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Complex.I * (((h : ℂ) * (u : ℂ)))) :=
    contDiff_const.mul (contDiff_const.mul hc_u)
  simp_rw [Complex.ofReal_mul]
  exact (contDiff_const.mul ((Complex.contDiff_exp.comp h_arg).sub contDiff_const)).sub
    (contDiff_const.mul hc_u)

theorem tendsto_timeModTestFn_deriv {m : ℝ} (hm : 0 < m)
    {base : (Fin 4 → ℝ) → ℂ} (h_sm : ContDiff ℝ (⊤ : ℕ∞) base)
    (h_supp : HasCompactSupport base) (t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ • (timeModTestFn m hm base h_sm h_supp (t + h) -
          timeModTestFn m hm base h_sm h_supp t))
      (𝓝[≠] 0)
      (𝓝 (timeModTestFn m hm
        (fun q => (Complex.I * ((q 0 - massShellEnergy m (spatialPart q) : ℝ) : ℂ)) * base q)
        (by
          have hc0 : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q 0) :=
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff
          have hce : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => massShellEnergy m (spatialPart q)) :=
            (contDiff_massShellEnergy hm).comp contDiff_spatialPart
          exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hc0.sub hce))).mul h_sm)
        (h_supp.mul_left) t)) := by
  let base' : (Fin 4 → ℝ) → ℂ :=
    fun q => (Complex.I * ((q 0 - massShellEnergy m (spatialPart q) : ℝ) : ℂ)) * base q
  have h_sm' : ContDiff ℝ (⊤ : ℕ∞) base' := by
    have hc0 : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q 0) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).contDiff
    have hce : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => massShellEnergy m (spatialPart q)) :=
      (contDiff_massShellEnergy hm).comp contDiff_spatialPart
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hc0.sub hce))).mul h_sm
  have h_supp' : HasCompactSupport base' := h_supp.mul_left
  let M : ℝ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    timeModMomSchwartz m hm base h_sm h_supp
  let Md : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    timeModMomSchwartz m hm base' h_sm' h_supp' t
  have h_mom_tend : Tendsto (fun h : ℝ => h⁻¹ • (M (t + h) - M t) - Md) (𝓝[≠] 0) (𝓝 0) := by
    rw [(schwartz_withSeminorms ℝ (Fin 1 → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0]
    rintro ⟨l, k⟩ ε hε
    let K_p : Set (Fin 1 → Fin 4 → ℝ) := momNegArgCLE.symm '' tsupport base
    have hK_comp : IsCompact K_p := h_supp.isCompact.image momNegArgCLE.symm.continuous
    obtain ⟨R_m, hRm_sub⟩ := Metric.isBounded_iff_subset_ball (0 : Fin 1 → Fin 4 → ℝ) |>.mp
      hK_comp.isBounded
    let R : ℝ := max R_m 1
    have hR_pos : 0 < R := by positivity
    let B_m : Set (Fin 1 → Fin 4 → ℝ) := Metric.closedBall 0 R
    have hB_comp : IsCompact B_m := isCompact_closedBall 0 R
    have hB_ne : B_m.Nonempty := ⟨0, Metric.mem_closedBall_self hR_pos.le⟩
    let a_fn : (Fin 1 → Fin 4 → ℝ) → ℝ :=
      fun p => -(p 0 0) - massShellEnergy m (spatialPart (-(p 0)))
    have ha_cd : ContDiff ℝ (⊤ : ℕ∞) a_fn := by
      let h_proj0 : (Fin 1 → Fin 4 → ℝ) →L[ℝ] ℝ :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 4 → ℝ) 0)
      have hc0 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => -(p 0 0)) :=
        h_proj0.contDiff.neg
      have hce : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : Fin 1 → Fin 4 → ℝ => massShellEnergy m (spatialPart (-(p 0)))) :=
        (contDiff_massShellEnergy hm).comp (contDiff_spatialPart.comp momNegArgCLE.contDiff)
      exact hc0.sub hce
    obtain ⟨p_a, _, hp_a⟩ := hB_comp.exists_isMaxOn hB_ne
      (continuous_abs.comp ha_cd.continuous).continuousOn
    let A_max : ℝ := |a_fn p_a| ^ 2 + |a_fn p_a| + 1
    have hD_exists : ∃ D : ℝ, 1 ≤ D ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ k → ∀ p ∈ B_m, ‖iteratedFDeriv ℝ i a_fn p‖ ≤ D ^ i := by
      have h_each : ∀ i : Fin (k + 1), ∃ M_i : ℝ, 0 ≤ M_i ∧
          ∀ p ∈ B_m, ‖iteratedFDeriv ℝ i.val a_fn p‖ ≤ M_i := by
        intro i
        have hc_i : Continuous (iteratedFDeriv ℝ i.val a_fn) :=
          ha_cd.continuous_iteratedFDeriv (mod_cast le_top)
        obtain ⟨p_i, _, hp_i⟩ := hB_comp.exists_isMaxOn hB_ne
          (continuous_norm.comp hc_i).continuousOn
        exact ⟨‖iteratedFDeriv ℝ i.val a_fn p_i‖, norm_nonneg _, fun p hp => hp_i hp⟩
      choose M_fn hM_nn hM_le using h_each
      have hsum_nn : 0 ≤ ∑ j : Fin (k + 1), M_fn j := Finset.sum_nonneg (fun j _ => hM_nn j)
      let D : ℝ := 1 + ∑ i : Fin (k + 1), M_fn i
      have hD1 : 1 ≤ D := by dsimp [D]; linarith
      refine ⟨D, hD1, fun i hi1 hik p hp => ?_⟩
      let fi : Fin (k + 1) := ⟨i, Nat.lt_succ_of_le hik⟩
      have h1 : ‖iteratedFDeriv ℝ i a_fn p‖ ≤ M_fn fi := hM_le fi p hp
      have h2 : M_fn fi ≤ D := by
        have h_single : M_fn fi ≤ ∑ j : Fin (k + 1), M_fn j :=
          Finset.single_le_sum (fun j _ => hM_nn j) (Finset.mem_univ fi)
        dsimp [D]
        linarith
      have h3 : D ≤ D ^ i := by
        calc D = D ^ 1 := (pow_one D).symm
          _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1
      exact h1.trans (h2.trans h3)
    obtain ⟨D, hD1, hD_le⟩ := hD_exists
    let C_k : ℝ := ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * SchwartzMap.seminorm ℝ l (k - j) (M t) *
        ((Nat.factorial j : ℝ) * A_max * D ^ j)
    let K_all : ℝ := max C_k 1
    have hK_pos : 0 < K_all := by positivity
    have h_bd : ∀ {h : ℝ}, h ≠ 0 → |h| ≤ 1 →
        SchwartzMap.seminorm ℝ l k (h⁻¹ • (M (t + h) - M t) - Md) ≤ K_all * |h| := by
      intro h hh hh1
      refine SchwartzMap.seminorm_le_bound ℝ l k _ (mul_nonneg hK_pos.le (abs_nonneg h)) fun p => ?_
      by_cases hp_in : ‖p‖ ≤ R
      · have hpB : p ∈ B_m := by simpa [B_m, Metric.mem_closedBall, dist_zero_right] using hp_in
        let g_h : ℝ → ℂ := fun u =>
          ((h⁻¹ : ℝ) : ℂ) * (Complex.exp (Complex.I * ((h * u : ℝ) : ℂ)) - 1) -
            Complex.I * (u : ℂ)
        have h_eq : ((h⁻¹ • (M (t + h) - M t) - Md : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
              (Fin 1 → Fin 4 → ℝ) → ℂ) =
            fun q => (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) q * g_h (a_fn q) := by
          ext q
          simp only [_root_.sub_apply, _root_.smul_apply, M, Md, timeModMomSchwartz_apply,
            timeModMomAmp, base', a_fn, g_h, Complex.real_smul]
          have h0_eq : (-q 0) 0 = -(q 0 0) := rfl
          change ((h⁻¹ : ℝ) : ℂ) * (base (-q 0) * Complex.exp _ -
              base (-q 0) * Complex.exp _) - _ = _
          rw [h0_eq]
          simp only [Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add,
            mul_add, Complex.exp_add]
          ring_nf
        rw [h_eq]
        have hM_cd : ContDiff ℝ k (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) := (M t).smooth k
        have hg_cd : ContDiff ℝ k (g_h ∘ a_fn) :=
          ((contDiff_diffQuoKernel h).comp ha_cd).of_le (mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
        have h_mul_le := norm_iteratedFDeriv_mul_le hM_cd hg_cd p le_rfl
        have hg_comp_bd : ∀ j ≤ k, ‖iteratedFDeriv ℝ j (g_h ∘ a_fn) p‖ ≤
            ((Nat.factorial j : ℝ) * (|h| * A_max) * D ^ j) := by
          intro j hjk
          refine norm_iteratedFDeriv_comp_le (contDiff_diffQuoKernel h) ha_cd
            (mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) p ?_ ?_
          · intro i _
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
            have hi1 := norm_iteratedDeriv_diffQuoKernel_le hh hh1 i (a_fn p)
            have ha_le : |a_fn p| ≤ |a_fn p_a| := hp_a hpB
            have hpoly_le : (a_fn p) ^ 2 + |a_fn p| + 1 ≤ A_max := by
              have hsq : (a_fn p) ^ 2 ≤ |a_fn p_a| ^ 2 := by
                rw [← sq_abs (a_fn p)]
                exact pow_le_pow_left₀ (abs_nonneg _) ha_le 2
              dsimp [A_max]
              linarith
            exact hi1.trans (mul_le_mul_of_nonneg_left hpoly_le (abs_nonneg h))
          · intro i hi1 hij
            exact hD_le i hi1 (hij.trans hjk) p hpB
        calc ‖p‖ ^ l * ‖iteratedFDeriv ℝ k (fun q => (M t q) * g_h (a_fn q)) p‖
            ≤ ‖p‖ ^ l * ∑ j ∈ Finset.range (k + 1),
                (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) p‖ *
                  ‖iteratedFDeriv ℝ (k - j) (g_h ∘ a_fn) p‖ :=
              mul_le_mul_of_nonneg_left h_mul_le (pow_nonneg (norm_nonneg _) l)
          _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
                (‖p‖ ^ l * ‖iteratedFDeriv ℝ j (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) p‖) *
                  ‖iteratedFDeriv ℝ (k - j) (g_h ∘ a_fn) p‖ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring
          _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
                (‖p‖ ^ l * ‖iteratedFDeriv ℝ (k - j) (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) p‖) *
                  ‖iteratedFDeriv ℝ j (g_h ∘ a_fn) p‖ := by
              have h_ref := Finset.sum_range_reflect
                (fun j => (k.choose j : ℝ) *
                  (‖p‖ ^ l * ‖iteratedFDeriv ℝ (k - j) (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) p‖) *
                  ‖iteratedFDeriv ℝ j (g_h ∘ a_fn) p‖) (k + 1)
              refine le_of_eq ?_
              rw [← h_ref]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hk_sub : k + 1 - 1 - j = k - j := by omega
              rw [hk_sub, Nat.sub_sub_self hj_le, Nat.choose_symm hj_le]
          _ ≤ ∑ j ∈ Finset.range (k + 1),
                (k.choose j : ℝ) * SchwartzMap.seminorm ℝ l (k - j) (M t) *
                  ((Nat.factorial j : ℝ) * (|h| * A_max) * D ^ j) := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hM_sem := (M t).le_seminorm ℝ l (k - j) p
              have h_prod := mul_le_mul hM_sem (hg_comp_bd j hj_le) (norm_nonneg _)
                (apply_nonneg _ _)
              calc (k.choose j : ℝ) *
                    (‖p‖ ^ l * ‖iteratedFDeriv ℝ (k - j) (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) p‖) *
                      ‖iteratedFDeriv ℝ j (g_h ∘ a_fn) p‖
                  = (k.choose j : ℝ) *
                      ((‖p‖ ^ l * ‖iteratedFDeriv ℝ (k - j) (M t : (Fin 1 → Fin 4 → ℝ) → ℂ) p‖) *
                        ‖iteratedFDeriv ℝ j (g_h ∘ a_fn) p‖) := by ring
                _ ≤ (k.choose j : ℝ) *
                      (SchwartzMap.seminorm ℝ l (k - j) (M t) *
                        ((Nat.factorial j : ℝ) * (|h| * A_max) * D ^ j)) :=
                    mul_le_mul_of_nonneg_left h_prod (Nat.cast_nonneg _)
                _ = _ := by ring
          _ = C_k * |h| := by
              dsimp [C_k]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ => by ring
          _ ≤ K_all * |h| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg h)
      · have hp_gt : R < ‖p‖ := lt_of_not_ge hp_in
        have h_ev0 : (((h⁻¹ • (M (t + h) - M t) - Md : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
              (Fin 1 → Fin 4 → ℝ) → ℂ)) =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
          filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hp_gt] with q hq
          have hq_not_base : -(q 0) ∉ tsupport base := by
            intro hmem
            have hqK : q ∈ K_p := ⟨-(q 0), hmem, by
              ext i ν
              rw [Subsingleton.elim i 0]
              change -(-(q 0) ν) = q 0 ν
              ring⟩
            have hq_lt := hRm_sub hqK
            rw [Metric.mem_ball, dist_zero_right] at hq_lt
            have : R_m ≤ R := le_max_left _ _
            linarith
          have hb0 : base (-(q 0)) = 0 := image_eq_zero_of_notMem_tsupport hq_not_base
          simp only [_root_.sub_apply, _root_.smul_apply, M, Md, timeModMomSchwartz_apply,
            timeModMomAmp, base', hb0, zero_mul, mul_zero, sub_zero, smul_zero]
        have h_id0 : iteratedFDeriv ℝ k
            (((h⁻¹ • (M (t + h) - M t) - Md : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
              (Fin 1 → Fin 4 → ℝ) → ℂ)) p = 0 := by
          rw [(h_ev0.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
          simp
        rw [h_id0, norm_zero, mul_zero]
        exact mul_nonneg hK_pos.le (abs_nonneg h)
    let δ : ℝ := min 1 (ε / (2 * K_all))
    have hδ_pos : 0 < δ := by positivity
    have h_nhds : Metric.ball (0 : ℝ) δ ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ_pos)
    refine Filter.mem_of_superset (Filter.inter_mem h_nhds self_mem_nhdsWithin) ?_
    rintro h ⟨hh_ball, hh_ne⟩
    have hh_abs : |h| < δ := by
      simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hh_ball
    have hh1 : |h| ≤ 1 := (hh_abs.le).trans (min_le_left _ _)
    dsimp only [Set.mem_setOf_eq]
    rw [SchwartzMap.schwartzSeminormFamily_apply, sub_zero]
    calc SchwartzMap.seminorm ℝ l k (h⁻¹ • (M (t + h) - M t) - Md)
        ≤ K_all * |h| := h_bd hh_ne hh1
      _ < K_all * (ε / (2 * K_all)) := mul_lt_mul_of_pos_left
          (hh_abs.trans_le (min_le_right _ _)) hK_pos
      _ = ε / 2 := by field_simp [hK_pos.ne']
      _ < ε := half_lt_self hε
  have h_mom_lim : Tendsto (fun h : ℝ => h⁻¹ • (M (t + h) - M t)) (𝓝[≠] 0) (𝓝 Md) := by
    rw [← tendsto_sub_nhds_zero_iff]
    exact h_mom_tend
  have h_inv_lim := ((invMinkowskiFourierCLM 1).continuous.tendsto Md).comp h_mom_lim
  refine h_inv_lim.congr fun h => ?_
  dsimp [Function.comp_def, M, Md, timeModTestFn]
  have h1 : (invMinkowskiFourierCLM 1) (h⁻¹ • (M (t + h) - M t)) =
      h⁻¹ • (invMinkowskiFourierCLM 1) (M (t + h) - M t) :=
    ((invMinkowskiFourierCLM 1).restrictScalars ℝ).map_smul h⁻¹ _
  rw [h1, map_sub]

theorem tendsto_haagRuelleTestFn_timeDeriv (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (t : ℝ) :
    Tendsto
      (fun h : ℝ => h⁻¹ • (haagRuelleTestFn m M hm hM f (t + h) - haagRuelleTestFn m M hm hM f t))
      (𝓝[≠] 0)
      (𝓝 (haagRuelleDerivTestFn m M hm hM f t)) :=
  tendsto_timeModTestFn_deriv hm (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) t

lemma invMinkowskiFourierCLM_one_apply
    (G : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (x : Fin 1 → Fin 4 → ℝ) :
    (invMinkowskiFourierCLM 1 G) x =
      (((2 * Real.pi)⁻¹ ^ 4 : ℝ) : ℂ) *
        ∫ q : Fin 4 → ℝ, G (fun _ => -q) *
          Complex.exp (-(Complex.I * (minkowskiInner q (x 0) : ℂ))) := by
  let e1 := (piSpaceEquiv 1).symm.trans (minkowskiFlipEquiv 1)
  let e2 := (posScaledMomentumEquivN 1).trans (piSpaceEquiv 1)
  let V := EuclideanSpace ℝ (Fin 1 × Fin 4)
  let ψ : SchwartzMap V ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e2.symm G
  have h_val : (invMinkowskiFourierCLM 1 G) x =
      (FourierTransform.fourier (ψ : V → ℂ)) (-piSpaceEquiv 1 (minkowskiFlipFun 1 x)) := by
    change ((schwartzCompCLE e1).symm
      ((schwartzFourierCLE V).symm ((schwartzCompCLE e2).symm G))) x = _
    have h_s1 : ∀ (φ : SchwartzMap V ℂ), ((schwartzCompCLE e1).symm φ) x = φ (e1.symm x) :=
      fun _ => rfl
    rw [h_s1]
    have h_e1 : e1.symm x = piSpaceEquiv 1 (minkowskiFlipFun 1 x) := by
      simp [e1, minkowskiFlipEquiv]
    rw [h_e1]
    have h_four : ∀ u : V, (((schwartzFourierCLE V).symm ψ : SchwartzMap V ℂ) : V → ℂ) u =
        𝓕 (ψ : V → ℂ) (-u) := by
      intro u
      change ((SchwartzMap.fourierTransformCLM ℂ ψ : SchwartzMap V ℂ) : V → ℂ) (-u) = _
      rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
    exact h_four _
  rw [h_val, Real.fourier_eq]
  have h_inner_eq : ∀ w : V,
      -inner ℝ w (-piSpaceEquiv 1 (minkowskiFlipFun 1 x)) =
        inner ℝ (piSpaceEquiv 1 (minkowskiFlipFun 1 x)) w := by
    intro w
    rw [inner_neg_right, neg_neg, real_inner_comm]
  have h_eq1 : (∫ w : V, Real.fourierChar (-inner ℝ w (-piSpaceEquiv 1 (minkowskiFlipFun 1 x))) •
        ψ w) =
      ∫ q' : Fin 1 → Fin 4 → ℝ,
        G ((2 * Real.pi) • q') *
          Complex.exp (2 * Real.pi * Complex.I *
            (∑ k : Fin 1, minkowskiInner (q' k) (x k) : ℝ)) := by
    have h_mp := measurePreserving_piSpaceEquiv_n 1
    have h_emb : MeasurableEmbedding (piSpaceEquiv 1) :=
      (piSpaceEquiv 1).toHomeomorph.measurableEmbedding
    rw [← MeasurePreserving.integral_comp h_mp h_emb]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q' => ?_)
    dsimp only
    rw [h_inner_eq, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    have h_psi : ψ (piSpaceEquiv 1 q') = G ((2 * Real.pi) • q') := rfl
    rw [h_psi]
    congr 1
    rw [inner_piSpaceEquiv_minkowskiFlip_n 1 q' x]
    push_cast
    ring_nf
  rw [h_eq1]
  have h_smul_int : (∫ q' : Fin 1 → Fin 4 → ℝ,
        G ((2 * Real.pi) • q') *
          Complex.exp (2 * Real.pi * Complex.I *
            (∑ k : Fin 1, minkowskiInner (q' k) (x k) : ℝ))) =
      (((2 * Real.pi)⁻¹ ^ 4 : ℝ) : ℂ) *
        ∫ p : Fin 1 → Fin 4 → ℝ,
          G p * Complex.exp (Complex.I * (minkowskiInner (p 0) (x 0) : ℂ)) := by
    let H : (Fin 1 → Fin 4 → ℝ) → ℂ := fun p =>
      G p * Complex.exp (Complex.I * (minkowskiInner (p 0) (x 0) : ℂ))
    have h_H_eq : (fun q' : Fin 1 → Fin 4 → ℝ =>
          G ((2 * Real.pi) • q') *
            Complex.exp (2 * Real.pi * Complex.I *
              (∑ k : Fin 1, minkowskiInner (q' k) (x k) : ℝ))) =
        fun q' => H ((2 * Real.pi) • q') := by
      ext q'
      dsimp [H]
      congr 2
      rw [Fin.sum_univ_one]
      simp only [minkowskiInner_explicit, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [h_H_eq]
    have h_sc := Measure.integral_comp_smul_of_nonneg (μ := volume) H (2 * Real.pi)
      (hR := (by positivity : 0 ≤ 2 * Real.pi))
    have h_finrank : Module.finrank ℝ (Fin 1 → Fin 4 → ℝ) = 4 := by
      rw [(piSpaceEquiv 1).toLinearEquiv.finrank_eq]
      simp
    rw [h_finrank] at h_sc
    rw [h_sc]
    simp only [Complex.real_smul, inv_pow]
    push_cast
    rfl
  rw [h_smul_int]
  congr 1
  have h_neg : (∫ p : Fin 1 → Fin 4 → ℝ,
        G p * Complex.exp (Complex.I * (minkowskiInner (p 0) (x 0) : ℂ))) =
      ∫ p : Fin 1 → Fin 4 → ℝ,
        G (-p) * Complex.exp (Complex.I * (minkowskiInner ((-p) 0) (x 0) : ℂ)) :=
    (integral_neg_eq_self (μ := volume)
      (fun p : Fin 1 → Fin 4 → ℝ =>
        G p * Complex.exp (Complex.I * (minkowskiInner (p 0) (x 0) : ℂ)))).symm
  rw [h_neg]
  let eu := (MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ)).symm
  have h_mp := (volume_preserving_funUnique (Fin 1) (Fin 4 → ℝ)).symm
  refine Eq.trans (h_mp.integral_comp eu.measurableEmbedding
    (fun p : Fin 1 → Fin 4 → ℝ =>
      G (-p) * Complex.exp (Complex.I * (minkowskiInner ((-p) 0) (x 0) : ℂ)))).symm ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  have h_eu_val : ((MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ)).symm q) =
      fun _ : Fin 1 => q := rfl
  rw [h_eu_val]
  have h_m : minkowskiInner (-q) (x 0) = -minkowskiInner q (x 0) := by
    simp only [minkowskiInner_explicit, Pi.neg_apply]
    ring
  congr 1
  change Complex.exp (Complex.I * (minkowskiInner (-q) (x 0) : ℂ)) =
    Complex.exp (-(Complex.I * (minkowskiInner q (x 0) : ℂ)))
  rw [h_m]
  simp only [Complex.ofReal_neg, mul_neg]

def minkMetricSign : Fin 4 → ℝ
  | 0 => 1
  | _ => -1

lemma minkowskiInner_single_right (q : Fin 4 → ℝ) (μ : Fin 4) :
    minkowskiInner q (Pi.single μ 1) = minkMetricSign μ * q μ := by
  rw [minkowskiInner_explicit]
  fin_cases μ <;> simp [minkMetricSign]

def momCoordBaseStep (μ : Fin 4) (base : (Fin 4 → ℝ) → ℂ) (q : Fin 4 → ℝ) : ℂ :=
  (-Complex.I * ((minkMetricSign μ * q μ : ℝ) : ℂ)) * base q

lemma contDiff_momCoordBaseStep (μ : Fin 4) {base : (Fin 4 → ℝ) → ℂ}
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) :
    ContDiff ℝ (⊤ : ℕ∞) (momCoordBaseStep μ base) := by
  unfold momCoordBaseStep
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q μ) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).contDiff
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hq))).mul h_sm

lemma hasCompactSupport_momCoordBaseStep (μ : Fin 4) {base : (Fin 4 → ℝ) → ℂ}
    (h_supp : HasCompactSupport base) :
    HasCompactSupport (momCoordBaseStep μ base) := by
  change HasCompactSupport
    (fun q : Fin 4 → ℝ => (-Complex.I * ((minkMetricSign μ * q μ : ℝ) : ℂ)) * base q)
  exact h_supp.mul_left

lemma tsupport_momCoordBaseStep_subset (μ : Fin 4) (base : (Fin 4 → ℝ) → ℂ) :
    tsupport (momCoordBaseStep μ base) ⊆ tsupport base :=
  tsupport_mul_subset_right

def momCoordBase (α : List (Fin 4)) (base : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  α.foldl (fun acc μ => momCoordBaseStep μ acc) base

lemma contDiff_momCoordBase (α : List (Fin 4)) {base : (Fin 4 → ℝ) → ℂ}
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) :
    ContDiff ℝ (⊤ : ℕ∞) (momCoordBase α base) := by
  induction α generalizing base with
  | nil => exact h_sm
  | cons μ α ih => exact ih (contDiff_momCoordBaseStep μ h_sm)

lemma hasCompactSupport_momCoordBase (α : List (Fin 4)) {base : (Fin 4 → ℝ) → ℂ}
    (h_supp : HasCompactSupport base) :
    HasCompactSupport (momCoordBase α base) := by
  induction α generalizing base with
  | nil => exact h_supp
  | cons μ α ih => exact ih (hasCompactSupport_momCoordBaseStep μ h_supp)

lemma tsupport_momCoordBase_subset (α : List (Fin 4)) (base : (Fin 4 → ℝ) → ℂ) :
    tsupport (momCoordBase α base) ⊆ tsupport base := by
  induction α generalizing base with
  | nil => exact Set.Subset.rfl
  | cons μ α ih => exact (ih _).trans (tsupport_momCoordBaseStep_subset μ base)

def iterMinkCoordDeriv (α : List (Fin 4)) (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  α.foldl (fun acc μ => schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) acc) g

lemma schwartzDirDerivCLM_single_timeModTestFn {m : ℝ} (hm : 0 < m)
    {base : (Fin 4 → ℝ) → ℂ} (h_sm : ContDiff ℝ (⊤ : ℕ∞) base)
    (h_supp : HasCompactSupport base) (t : ℝ) (μ : Fin 4) :
    schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) (timeModTestFn m hm base h_sm h_supp t) =
      timeModTestFn m hm (momCoordBaseStep μ base) (contDiff_momCoordBaseStep μ h_sm)
        (hasCompactSupport_momCoordBaseStep μ h_supp) t := by
  apply minkowskiFourier_injective
  intro p
  have hp_eq : p = fun _ : Fin 1 => -(-(p 0)) := by
    ext i ν
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp
  rw [hp_eq, minkowskiFourier_schwartzDirDerivCLM, minkowskiFourier_timeModTestFn,
      minkowskiFourier_timeModTestFn]
  unfold timeModMomAmp momCoordBaseStep
  rw [Fin.sum_univ_one]
  have hs0 : minkSingleVec 1 0 μ 0 = Pi.single μ 1 := by
    ext ν
    simp [minkSingleVec]
  rw [hs0]
  have hm_neg2 : minkowskiInner (-(-(p 0))) (Pi.single μ 1) =
      -(minkowskiInner (-(p 0)) (Pi.single μ 1)) := by
    simp [minkowskiInner_explicit]
    ring
  rw [hm_neg2, minkowskiInner_single_right]
  push_cast
  ring

lemma iterMinkCoordDeriv_timeModTestFn {m : ℝ} (hm : 0 < m) (α : List (Fin 4))
    {base : (Fin 4 → ℝ) → ℂ} (h_sm : ContDiff ℝ (⊤ : ℕ∞) base)
    (h_supp : HasCompactSupport base) (t : ℝ) :
    iterMinkCoordDeriv α (timeModTestFn m hm base h_sm h_supp t) =
      timeModTestFn m hm (momCoordBase α base) (contDiff_momCoordBase α h_sm)
        (hasCompactSupport_momCoordBase α h_supp) t := by
  induction α generalizing base with
  | nil => rfl
  | cons μ α ih =>
    unfold iterMinkCoordDeriv momCoordBase
    simp only [List.foldl_cons]
    rw [schwartzDirDerivCLM_single_timeModTestFn]
    exact ih (contDiff_momCoordBaseStep μ h_sm) (hasCompactSupport_momCoordBaseStep μ h_supp)

lemma vec_one_eq_sum_minkSingleVec (v : Fin 1 → Fin 4 → ℝ) :
    v = ∑ μ : Fin 4, (v 0 μ) • minkSingleVec 1 0 μ := by
  ext i ν
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rw [Finset.sum_apply, Finset.sum_apply]
  have h_ite : (∑ μ : Fin 4, (v 0 μ • minkSingleVec 1 0 μ) 0 ν) =
      ∑ μ : Fin 4, if μ = ν then v 0 ν else 0 := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, minkSingleVec_apply, ↓reduceIte]
    by_cases hμ : ν = μ
    · subst hμ; simp
    · have hμ' : μ ≠ ν := fun h => hμ h.symm
      simp [hμ, hμ']
  rw [h_ite, Finset.sum_ite_eq']
  simp

lemma natCast_le_top_enat_coe (i : ℕ) :
    (i : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

lemma top_enat_coe_add_one_le :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  rw [← WithTop.coe_one, ← WithTop.coe_add]
  exact WithTop.coe_le_coe.mpr le_top

lemma norm_iteratedFDeriv_apply_le_sum_iterMinkCoordDeriv
    (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : ℕ)
    (x : Fin 1 → Fin 4 → ℝ) (m_v : Fin k → (Fin 1 → Fin 4 → ℝ)) :
    ‖iteratedFDeriv ℝ k (g : (Fin 1 → Fin 4 → ℝ) → ℂ) x m_v‖ ≤
      (∑ α : Fin k → Fin 4, ‖(iterMinkCoordDeriv (List.ofFn α) g) x‖) *
        ∏ i : Fin k, ‖m_v i‖ := by
  induction k generalizing g with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    have h_list : ∀ α : Fin 0 → Fin 4, List.ofFn α = [] := fun α => by simp
    rw [Finset.univ_unique, Finset.sum_singleton, h_list]
    simp [iterMinkCoordDeriv]
  | succ k ih =>
    rw [iteratedFDeriv_succ_apply_right]
    let v : Fin 1 → Fin 4 → ℝ := m_v (Fin.last k)
    let L_v : ((Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.apply ℝ ℂ v
    have h_comm : (iteratedFDeriv ℝ k (fderiv ℝ (g : (Fin 1 → Fin 4 → ℝ) → ℂ)) x
          (Fin.init m_v)) v =
        iteratedFDeriv ℝ k (L_v ∘ fderiv ℝ (g : (Fin 1 → Fin 4 → ℝ) → ℂ)) x
          (Fin.init m_v) := by
      have h_fcd : ContDiff ℝ (k : ℕ) (fderiv ℝ (g : (Fin 1 → Fin 4 → ℝ) → ℂ)) :=
        ((g.smooth (k + 1)).fderiv_right (by simp))
      change L_v _ = _
      rw [L_v.iteratedFDeriv_comp_left h_fcd.contDiffAt le_rfl]
      rfl
    rw [h_comm]
    have h_lin_fn : (L_v ∘ fderiv ℝ (g : (Fin 1 → Fin 4 → ℝ) → ℂ)) =
        fun y : Fin 1 → Fin 4 → ℝ => ∑ μ : Fin 4, (v 0 μ) •
          ((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
            (Fin 1 → Fin 4 → ℝ) → ℂ) y) := by
      ext y
      simp only [Function.comp_def, L_v, ContinuousLinearMap.apply_apply]
      conv_lhs => rw [vec_one_eq_sum_minkSingleVec v]
      rw [map_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [map_smul, schwartzDirDerivCLM_apply]
    have h_diff_each : ∀ μ : Fin 4, ContDiff ℝ k
        (fun y : Fin 1 → Fin 4 → ℝ => (v 0 μ) •
          ((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
            (Fin 1 → Fin 4 → ℝ) → ℂ) y)) := by
      intro μ
      exact ContDiff.const_smul (v 0 μ)
        (((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g).smooth (⊤ : ℕ∞)).of_le
          (natCast_le_top_enat_coe k))
    have h_sum_eval : iteratedFDeriv ℝ k (L_v ∘ fderiv ℝ (g : (Fin 1 → Fin 4 → ℝ) → ℂ)) x =
        ∑ μ : Fin 4, iteratedFDeriv ℝ k
          (fun y : Fin 1 → Fin 4 → ℝ => (v 0 μ) •
            ((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
              (Fin 1 → Fin 4 → ℝ) → ℂ) y)) x := by
      rw [h_lin_fn, iteratedFDeriv_sum (fun μ _ => h_diff_each μ), Finset.sum_apply]
    rw [h_sum_eval]
    simp only [_root_.sum_apply]
    calc ‖∑ μ : Fin 4, iteratedFDeriv ℝ k
            (fun y => (v 0 μ) • ((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
              (Fin 1 → Fin 4 → ℝ) → ℂ) y)) x (Fin.init m_v)‖
        ≤ ∑ μ : Fin 4, ‖iteratedFDeriv ℝ k
            (fun y => (v 0 μ) • ((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
              (Fin 1 → Fin 4 → ℝ) → ℂ) y)) x (Fin.init m_v)‖ := norm_sum_le _ _
      _ = ∑ μ : Fin 4, |v 0 μ| *
            ‖iteratedFDeriv ℝ k
              (schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
                (Fin 1 → Fin 4 → ℝ) → ℂ) x (Fin.init m_v)‖ := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            have h_cd_mu : ContDiffAt ℝ k
                ((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g :
                  (Fin 1 → Fin 4 → ℝ) → ℂ)) x :=
              (((schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g).smooth (⊤ : ℕ∞)).of_le
                (natCast_le_top_enat_coe k)).contDiffAt
            change ‖iteratedFDeriv ℝ k ((v 0 μ) • (schwartzDirDerivCLM 1
              (minkSingleVec 1 0 μ) g : (Fin 1 → Fin 4 → ℝ) → ℂ)) x (Fin.init m_v)‖ = _
            rw [iteratedFDeriv_const_smul_apply h_cd_mu, _root_.smul_apply,
              norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ μ : Fin 4, ‖v‖ *
            ((∑ β : Fin k → Fin 4,
              ‖(iterMinkCoordDeriv (List.ofFn β)
                (schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g)) x‖) *
              ∏ i : Fin k, ‖Fin.init m_v i‖) := by
            refine Finset.sum_le_sum fun μ _ => ?_
            have hv0 : |v 0 μ| ≤ ‖v‖ :=
              (Real.norm_eq_abs (v 0 μ) ▸ norm_le_pi_norm (v 0) μ).trans (norm_le_pi_norm v 0)
            exact mul_le_mul hv0
              (ih (schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g) (Fin.init m_v))
              (norm_nonneg _) (norm_nonneg v)
      _ = (∑ μ : Fin 4, ∑ β : Fin k → Fin 4,
            ‖(iterMinkCoordDeriv (μ :: List.ofFn β) g) x‖) *
            ((∏ i : Fin k, ‖Fin.init m_v i‖) * ‖v‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [Finset.sum_mul]
            have h_fold : ∀ β : Fin k → Fin 4,
                iterMinkCoordDeriv (μ :: List.ofFn β) g =
                  iterMinkCoordDeriv (List.ofFn β)
                    (schwartzDirDerivCLM 1 (minkSingleVec 1 0 μ) g) :=
              fun _ => rfl
            simp_rw [h_fold]
            rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun β _ => by ring
      _ = (∑ α : Fin (k + 1) → Fin 4, ‖(iterMinkCoordDeriv (List.ofFn α) g) x‖) *
            ∏ i : Fin (k + 1), ‖m_v i‖ := by
            have h_prod : (∏ i : Fin k, ‖Fin.init m_v i‖) * ‖v‖ = ∏ i : Fin (k + 1), ‖m_v i‖ := by
              rw [Fin.prod_univ_castSucc]
              rfl
            have h_sum_eq : (∑ α : Fin (k + 1) → Fin 4,
                  ‖(iterMinkCoordDeriv (List.ofFn α) g) x‖) =
                ∑ μ : Fin 4, ∑ β : Fin k → Fin 4,
                  ‖(iterMinkCoordDeriv (μ :: List.ofFn β) g) x‖ := by
              rw [← Fintype.sum_prod_type']
              refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 4)).symm _ _
                fun α => ?_
              have h_cons : List.ofFn α = List.ofFn (Fin.cons (α 0) (fun i => α i.succ)) := by
                congr 1
                ext i
                refine Fin.cases rfl (fun j => rfl) i
              rw [h_cons, List.ofFn_succ]
              rfl
            rw [h_prod, h_sum_eq]

lemma norm_iteratedFDeriv_le_sum_iterMinkCoordDeriv
    (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : ℕ) (x : Fin 1 → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ k (g : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ ≤
      ∑ α : Fin k → Fin 4, ‖(iterMinkCoordDeriv (List.ofFn α) g) x‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun m_v => norm_iteratedFDeriv_apply_le_sum_iterMinkCoordDeriv g k x m_v

lemma exists_smoothCutoff_compact_nhd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K₀ : Set E) (hK₀ : IsCompact K₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ q : E, 0 ≤ b q ∧ b q ≤ 1) ∧
      (∀ q ∈ K₀, b q = 1) ∧
      (∀ q ∈ tsupport b, ∃ c ∈ K₀, dist q c ≤ 2 * δ / 3) := by
  classical
  have hcov : K₀ ⊆ ⋃ c : K₀, Metric.ball c.1 (δ / 3) :=
    fun p hp => Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (by positivity)⟩
  obtain ⟨s, hs_cov⟩ := hK₀.elim_finite_subcover
    (fun c : K₀ => Metric.ball c.1 (δ / 3)) (fun _ => Metric.isOpen_ball) hcov
  let mkBump : ContDiffBump (0 : E) := ⟨δ / 3, 2 * δ / 3, by positivity, by linarith⟩
  let bumpAt : E → E → ℝ := fun c q => mkBump (q - c)
  have h_bump_cd : ∀ c : E, ContDiff ℝ (⊤ : ℕ∞) (bumpAt c) := fun c =>
    mkBump.contDiff.comp (contDiff_id.sub contDiff_const)
  let b : E → ℝ := fun q => 1 - ∏ c ∈ s, (1 - bumpAt c.1 q)
  have h_prod_cd : ∀ s' : Finset K₀,
      ContDiff ℝ (⊤ : ℕ∞) (fun q : E => ∏ c ∈ s', (1 - bumpAt c.1 q)) := by
    intro s'
    induction s' using Finset.induction_on with
    | empty => simpa using contDiff_const
    | @insert a s'' ha ih =>
      have h_eq : (fun q : E => ∏ c ∈ insert a s'', (1 - bumpAt c.1 q)) =
          fun q => (1 - bumpAt a.1 q) * ∏ c ∈ s'', (1 - bumpAt c.1 q) := by
        ext q
        exact Finset.prod_insert ha
      rw [h_eq]
      exact (contDiff_const.sub (h_bump_cd a.1)).mul ih
  have h_b_cd : ContDiff ℝ (⊤ : ℕ∞) b := contDiff_const.sub (h_prod_cd s)
  have h_b_bounds : ∀ q : E, 0 ≤ b q ∧ b q ≤ 1 := by
    intro q
    have h_factor_nn : ∀ c ∈ s, 0 ≤ 1 - bumpAt c.1 q := fun c _ => by
      linarith [mkBump.le_one (x := q - c.1)]
    have h_factor_le : ∀ c ∈ s, 1 - bumpAt c.1 q ≤ 1 := fun c _ => by
      linarith [mkBump.nonneg (x := q - c.1)]
    have h_prod_nn : 0 ≤ ∏ c ∈ s, (1 - bumpAt c.1 q) := Finset.prod_nonneg h_factor_nn
    have h_prod_le : (∏ c ∈ s, (1 - bumpAt c.1 q)) ≤ 1 := Finset.prod_le_one h_factor_nn h_factor_le
    exact ⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩
  have h_b_one : ∀ q ∈ K₀, b q = 1 := by
    intro q hq
    have hq_u := hs_cov hq
    simp only [Set.mem_iUnion, exists_prop] at hq_u
    rcases hq_u with ⟨c, hc_s, hq_ball⟩
    have hc_one : bumpAt c.1 q = 1 := by
      refine mkBump.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
      exact hq_ball.le
    have h_prod0 : (∏ c' ∈ s, (1 - bumpAt c'.1 q)) = 0 :=
      Finset.prod_eq_zero hc_s (by rw [hc_one, sub_self])
    dsimp [b]
    rw [h_prod0, sub_zero]
  let K_ext : Set E := ⋃ c ∈ s, Metric.closedBall c.1 (2 * δ / 3)
  have hK_ext_compact : IsCompact K_ext :=
    s.isCompact_biUnion fun c _ => isCompact_closedBall c.1 (2 * δ / 3)
  have hK_ext_closed : IsClosed K_ext := hK_ext_compact.isClosed
  have h_supp_sub : Function.support b ⊆ K_ext := by
    intro q hq
    by_contra hnot
    have h_all : ∀ c ∈ s, bumpAt c.1 q = 0 := by
      intro c hc
      have h_nb : q ∉ Metric.closedBall c.1 (2 * δ / 3) :=
        fun hmem => hnot (Set.mem_biUnion hc hmem)
      rw [Metric.mem_closedBall, not_le] at h_nb
      refine mkBump.zero_of_le_dist ?_
      rw [dist_zero_right, ← dist_eq_norm]
      exact h_nb.le
    have h_prod1 : (∏ c ∈ s, (1 - bumpAt c.1 q)) = 1 :=
      Finset.prod_eq_one fun c hc => by rw [h_all c hc, sub_zero]
    exact hq (by dsimp [b]; rw [h_prod1, sub_self])
  have h_tsupp_sub : tsupport b ⊆ K_ext := closure_minimal h_supp_sub hK_ext_closed
  have h_b_supp : HasCompactSupport b :=
    HasCompactSupport.of_support_subset_isCompact hK_ext_compact h_supp_sub
  refine ⟨b, h_b_cd, h_b_supp, h_b_bounds, h_b_one, fun q hq => ?_⟩
  have hmem := h_tsupp_sub hq
  simp only [K_ext, Set.mem_iUnion, exists_prop] at hmem
  rcases hmem with ⟨c, _, hq_ball⟩
  exact ⟨c.1, c.2, hq_ball⟩

def hrPhase (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (q : Fin 4 → ℝ) : ℝ :=
  minkowskiInner q x0 - (q 0 - massShellEnergy m (spatialPart q)) * t

def expHrPhase (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (q : Fin 4 → ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (hrPhase m x0 t q : ℂ)))

lemma norm_expHrPhase (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (q : Fin 4 → ℝ) :
    ‖expHrPhase m x0 t q‖ = 1 := by
  unfold expHrPhase
  have h_eq : -(Complex.I * (hrPhase m x0 t q : ℂ)) =
      ((-hrPhase m x0 t q : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h_eq]
  exact Complex.norm_exp_ofReal_mul_I _

lemma contDiff_hrPhase {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (hrPhase m x0 t) := by
  unfold hrPhase
  have hc : ∀ μ : Fin 4, ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => q μ) :=
    fun μ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).contDiff
  have hmink : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => minkowskiInner q x0) := by
    have heq : (fun q : Fin 4 → ℝ => minkowskiInner q x0) =
        fun q => q 0 * x0 0 - q 1 * x0 1 - q 2 * x0 2 - q 3 * x0 3 := by
      ext q
      rw [minkowskiInner_explicit]
    rw [heq]
    exact ((((hc 0).mul contDiff_const).sub ((hc 1).mul contDiff_const)).sub
      ((hc 2).mul contDiff_const)).sub ((hc 3).mul contDiff_const)
  have hce : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => massShellEnergy m (spatialPart q)) :=
    (contDiff_massShellEnergy hm).comp contDiff_spatialPart
  exact hmink.sub (((hc 0).sub hce).mul contDiff_const)

lemma contDiff_expHrPhase {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (expHrPhase m x0 t) := by
  unfold expHrPhase
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_hrPhase hm x0 t))).neg)

lemma timeModTestFn_apply (m : ℝ) (hm : 0 < m) (u : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u) (t : ℝ)
    (x : Fin 1 → Fin 4 → ℝ) :
    (timeModTestFn m hm u h_sm h_supp t) x =
      (((2 * Real.pi)⁻¹ ^ 4 : ℝ) : ℂ) *
        ∫ q : Fin 4 → ℝ, u q * expHrPhase m (x 0) t q := by
  unfold timeModTestFn
  rw [invMinkowskiFourierCLM_one_apply]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  dsimp only
  rw [timeModMomSchwartz_apply]
  simp only [neg_neg, timeModMomAmp, expHrPhase, hrPhase, mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

def hrPhaseGrad (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) : Fin 4 → (Fin 4 → ℝ) → ℝ
  | 0, _ => x0 0 - t
  | 1, q => velocityVec m (spatialPart q) 0 * t - x0 1
  | 2, q => velocityVec m (spatialPart q) 1 * t - x0 2
  | 3, q => velocityVec m (spatialPart q) 2 * t - x0 3

def spacetimeScale (x0 : Fin 4 → ℝ) (t : ℝ) : ℝ :=
  1 + |t| + |x0 0| + ‖spatialPart x0‖

lemma one_le_spacetimeScale (x0 : Fin 4 → ℝ) (t : ℝ) :
    1 ≤ spacetimeScale x0 t := by
  unfold spacetimeScale
  linarith [abs_nonneg t, abs_nonneg (x0 0), norm_nonneg (spatialPart x0)]

lemma spacetimeScale_pos (x0 : Fin 4 → ℝ) (t : ℝ) :
    0 < spacetimeScale x0 t :=
  lt_of_lt_of_le zero_lt_one (one_le_spacetimeScale x0 t)

def normPhaseGrad (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (μ : Fin 4) (q : Fin 4 → ℝ) : ℝ :=
  (spacetimeScale x0 t)⁻¹ * hrPhaseGrad m x0 t μ q

lemma hrPhaseGrad_eq_scale_mul_normPhaseGrad (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ)
    (μ : Fin 4) (q : Fin 4 → ℝ) :
    hrPhaseGrad m x0 t μ q = spacetimeScale x0 t * normPhaseGrad m x0 t μ q := by
  unfold normPhaseGrad
  have hs : spacetimeScale x0 t ≠ 0 := (spacetimeScale_pos x0 t).ne'
  field_simp [hs]

lemma abs_hrPhaseGrad_le_spacetimeScale {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    (μ : Fin 4) (q : Fin 4 → ℝ) :
    |hrPhaseGrad m x0 t μ q| ≤ spacetimeScale x0 t := by
  unfold spacetimeScale
  fin_cases μ
  · change |x0 0 - t| ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖
    calc |x0 0 - t| ≤ |x0 0| + |t| := abs_sub _ _
      _ ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖ := by linarith [norm_nonneg (spatialPart x0)]
  · change |velocityVec m (spatialPart q) 0 * t - x0 1| ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖
    have hv : |velocityVec m (spatialPart q) 0| ≤ 1 :=
      (abs_velocityVec_apply_lt_one hm (spatialPart q) 0).le
    have hx : |x0 1| ≤ ‖spatialPart x0‖ := by
      simpa [Real.norm_eq_abs, spatialPart] using norm_le_pi_norm (spatialPart x0) 0
    calc |velocityVec m (spatialPart q) 0 * t - x0 1|
        ≤ |velocityVec m (spatialPart q) 0 * t| + |x0 1| := abs_sub _ _
      _ = |velocityVec m (spatialPart q) 0| * |t| + |x0 1| := by rw [abs_mul]
      _ ≤ 1 * |t| + ‖spatialPart x0‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hv (abs_nonneg t)) hx
      _ ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖ := by linarith [abs_nonneg (x0 0)]
  · change |velocityVec m (spatialPart q) 1 * t - x0 2| ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖
    have hv : |velocityVec m (spatialPart q) 1| ≤ 1 :=
      (abs_velocityVec_apply_lt_one hm (spatialPart q) 1).le
    have hx : |x0 2| ≤ ‖spatialPart x0‖ := by
      simpa [Real.norm_eq_abs, spatialPart] using norm_le_pi_norm (spatialPart x0) 1
    calc |velocityVec m (spatialPart q) 1 * t - x0 2|
        ≤ |velocityVec m (spatialPart q) 1 * t| + |x0 2| := abs_sub _ _
      _ = |velocityVec m (spatialPart q) 1| * |t| + |x0 2| := by rw [abs_mul]
      _ ≤ 1 * |t| + ‖spatialPart x0‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hv (abs_nonneg t)) hx
      _ ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖ := by linarith [abs_nonneg (x0 0)]
  · change |velocityVec m (spatialPart q) 2 * t - x0 3| ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖
    have hv : |velocityVec m (spatialPart q) 2| ≤ 1 :=
      (abs_velocityVec_apply_lt_one hm (spatialPart q) 2).le
    have hx : |x0 3| ≤ ‖spatialPart x0‖ := by
      simpa [Real.norm_eq_abs, spatialPart] using norm_le_pi_norm (spatialPart x0) 2
    calc |velocityVec m (spatialPart q) 2 * t - x0 3|
        ≤ |velocityVec m (spatialPart q) 2 * t| + |x0 3| := abs_sub _ _
      _ = |velocityVec m (spatialPart q) 2| * |t| + |x0 3| := by rw [abs_mul]
      _ ≤ 1 * |t| + ‖spatialPart x0‖ :=
          add_le_add (mul_le_mul_of_nonneg_right hv (abs_nonneg t)) hx
      _ ≤ 1 + |t| + |x0 0| + ‖spatialPart x0‖ := by linarith [abs_nonneg (x0 0)]

lemma abs_normPhaseGrad_le_one {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    (μ : Fin 4) (q : Fin 4 → ℝ) :
    |normPhaseGrad m x0 t μ q| ≤ 1 := by
  unfold normPhaseGrad
  have hs : 0 < spacetimeScale x0 t := spacetimeScale_pos x0 t
  rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_le_one₀ hs]
  exact abs_hrPhaseGrad_le_spacetimeScale hm x0 t μ q

lemma contDiff_normPhaseGrad {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ) (μ : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (normPhaseGrad m x0 t μ) := by
  unfold normPhaseGrad
  refine contDiff_const.mul ?_
  fin_cases μ
  · exact contDiff_const
  · exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff.comp
      ((contDiff_velocityVec hm).comp contDiff_spatialPart)).mul contDiff_const).sub contDiff_const
  · exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).contDiff.comp
      ((contDiff_velocityVec hm).comp contDiff_spatialPart)).mul contDiff_const).sub contDiff_const
  · exact (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).contDiff.comp
      ((contDiff_velocityVec hm).comp contDiff_spatialPart)).mul contDiff_const).sub contDiff_const

lemma hasDerivAt_hrPhase_single {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    (μ : Fin 4) (q : Fin 4 → ℝ) :
    HasDerivAt (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single μ 1))
      (hrPhaseGrad m x0 t μ q) 0 := by
  fin_cases μ
  · change HasDerivAt (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 0 1))
      (hrPhaseGrad m x0 t 0 q) 0
    have h_eq : (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 0 1)) =
        fun s => hrPhase m x0 t q + s * (x0 0 - t) := by
      ext s
      have hsp : spatialPart (q + s • Pi.single 0 1) = spatialPart q := by
        ext j
        fin_cases j <;> simp [spatialPart]
      unfold hrPhase
      rw [hsp, minkowskiInner_explicit, minkowskiInner_explicit]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.isValue,
        ↓reduceIte, Fin.reduceEq, mul_zero, add_zero, mul_one]
      ring
    rw [h_eq]
    dsimp [hrPhaseGrad]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (x0 0 - t)).const_add (hrPhase m x0 t q)
  · change HasDerivAt (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 1 1))
      (hrPhaseGrad m x0 t 1 q) 0
    have hsp : ∀ s : ℝ, spatialPart (q + s • Pi.single 1 1) =
        spatialPart q + s • Pi.single 0 1 := by
      intro s
      ext j
      fin_cases j <;> simp [spatialPart]
    have h_line : HasDerivAt (fun s : ℝ => spatialPart q + s • Pi.single (0 : Fin 3) (1 : ℝ))
        (Pi.single (0 : Fin 3) (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (0 : Fin 3) (1 : ℝ))).const_add
        (spatialPart q)
    have h_mf : HasFDerivAt (massShellEnergy m) (massShellEnergyDerivCLM m (spatialPart q))
        (spatialPart q + (0 : ℝ) • Pi.single (0 : Fin 3) 1) := by
      simpa using hasFDerivAt_massShellEnergy hm (spatialPart q)
    have h_en := h_mf.comp_hasDerivAt 0 h_line
    have hd_en : massShellEnergyDerivCLM m (spatialPart q) (Pi.single 0 1) =
        velocityVec m (spatialPart q) 0 := by
      simp [massShellEnergyDerivCLM, velocityVec, spatialPart]
    rw [hd_en] at h_en
    have h_eq : (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 1 1)) =
        fun s => (minkowskiInner q x0 - q 0 * t) +
          (t * massShellEnergy m (spatialPart q + s • Pi.single 0 1) - s * x0 1) := by
      ext s
      unfold hrPhase
      rw [hsp s, minkowskiInner_explicit]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.isValue,
        Fin.reduceEq, ↓reduceIte, mul_zero, add_zero, mul_one]
      rw [minkowskiInner_explicit]
      ring
    rw [h_eq]
    have hd_all := ((h_en.const_mul t).sub ((hasDerivAt_id (0 : ℝ)).mul_const (x0 1))).const_add
      (minkowskiInner q x0 - q 0 * t)
    refine hd_all.congr_deriv ?_
    change t * velocityVec m (spatialPart q) 0 - 1 * x0 1 = hrPhaseGrad m x0 t 1 q
    dsimp [hrPhaseGrad]
    ring
  · change HasDerivAt (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 2 1))
      (hrPhaseGrad m x0 t 2 q) 0
    have hsp : ∀ s : ℝ, spatialPart (q + s • Pi.single 2 1) =
        spatialPart q + s • Pi.single 1 1 := by
      intro s
      ext j
      fin_cases j <;> simp [spatialPart]
    have h_line : HasDerivAt (fun s : ℝ => spatialPart q + s • Pi.single (1 : Fin 3) (1 : ℝ))
        (Pi.single (1 : Fin 3) (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (1 : Fin 3) (1 : ℝ))).const_add
        (spatialPart q)
    have h_mf : HasFDerivAt (massShellEnergy m) (massShellEnergyDerivCLM m (spatialPart q))
        (spatialPart q + (0 : ℝ) • Pi.single (1 : Fin 3) 1) := by
      simpa using hasFDerivAt_massShellEnergy hm (spatialPart q)
    have h_en := h_mf.comp_hasDerivAt 0 h_line
    have hd_en : massShellEnergyDerivCLM m (spatialPart q) (Pi.single 1 1) =
        velocityVec m (spatialPart q) 1 := by
      simp [massShellEnergyDerivCLM, velocityVec, spatialPart]
    rw [hd_en] at h_en
    have h_eq : (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 2 1)) =
        fun s => (minkowskiInner q x0 - q 0 * t) +
          (t * massShellEnergy m (spatialPart q + s • Pi.single 1 1) - s * x0 2) := by
      ext s
      unfold hrPhase
      rw [hsp s, minkowskiInner_explicit]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.isValue,
        Fin.reduceEq, ↓reduceIte, mul_zero, add_zero, mul_one]
      rw [minkowskiInner_explicit]
      ring
    rw [h_eq]
    have hd_all := ((h_en.const_mul t).sub ((hasDerivAt_id (0 : ℝ)).mul_const (x0 2))).const_add
      (minkowskiInner q x0 - q 0 * t)
    refine hd_all.congr_deriv ?_
    change t * velocityVec m (spatialPart q) 1 - 1 * x0 2 = hrPhaseGrad m x0 t 2 q
    dsimp [hrPhaseGrad]
    ring
  · change HasDerivAt (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 3 1))
      (hrPhaseGrad m x0 t 3 q) 0
    have hsp : ∀ s : ℝ, spatialPart (q + s • Pi.single 3 1) =
        spatialPart q + s • Pi.single 2 1 := by
      intro s
      ext j
      fin_cases j <;> simp [spatialPart]
    have h_line : HasDerivAt (fun s : ℝ => spatialPart q + s • Pi.single (2 : Fin 3) (1 : ℝ))
        (Pi.single (2 : Fin 3) (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single (2 : Fin 3) (1 : ℝ))).const_add
        (spatialPart q)
    have h_mf : HasFDerivAt (massShellEnergy m) (massShellEnergyDerivCLM m (spatialPart q))
        (spatialPart q + (0 : ℝ) • Pi.single (2 : Fin 3) 1) := by
      simpa using hasFDerivAt_massShellEnergy hm (spatialPart q)
    have h_en := h_mf.comp_hasDerivAt 0 h_line
    have hd_en : massShellEnergyDerivCLM m (spatialPart q) (Pi.single 2 1) =
        velocityVec m (spatialPart q) 2 := by
      simp [massShellEnergyDerivCLM, velocityVec, spatialPart]
    rw [hd_en] at h_en
    have h_eq : (fun s : ℝ => hrPhase m x0 t (q + s • Pi.single 3 1)) =
        fun s => (minkowskiInner q x0 - q 0 * t) +
          (t * massShellEnergy m (spatialPart q + s • Pi.single 2 1) - s * x0 3) := by
      ext s
      unfold hrPhase
      rw [hsp s, minkowskiInner_explicit]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Fin.isValue,
        Fin.reduceEq, ↓reduceIte, mul_zero, add_zero, mul_one]
      rw [minkowskiInner_explicit]
      ring
    rw [h_eq]
    have hd_all := ((h_en.const_mul t).sub ((hasDerivAt_id (0 : ℝ)).mul_const (x0 3))).const_add
      (minkowskiInner q x0 - q 0 * t)
    refine hd_all.congr_deriv ?_
    change t * velocityVec m (spatialPart q) 2 - 1 * x0 3 = hrPhaseGrad m x0 t 3 q
    dsimp [hrPhaseGrad]
    ring

def smoothClampPos (c y : ℝ) : ℝ :=
  Real.smoothTransition ((2 / c) * y - 1) * y +
    (1 - Real.smoothTransition ((2 / c) * y - 1)) * (c / 2)

def smoothInv (c y : ℝ) : ℝ :=
  (smoothClampPos c y)⁻¹

lemma contDiff_smoothClampPos (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothClampPos c) := by
  unfold smoothClampPos
  have htr : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Real.smoothTransition ((2 / c) * y - 1)) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact (htr.mul contDiff_id).add ((contDiff_const.sub htr).mul contDiff_const)

lemma half_le_smoothClampPos {c : ℝ} (hc : 0 < c) (y : ℝ) :
    c / 2 ≤ smoothClampPos c y := by
  unfold smoothClampPos
  set w : ℝ := Real.smoothTransition ((2 / c) * y - 1)
  have hw0 : 0 ≤ w := Real.smoothTransition.nonneg _
  have hw1 : w ≤ 1 := Real.smoothTransition.le_one _
  by_cases hy : y ≤ c / 2
  · have harg : (2 / c) * y - 1 ≤ 0 := by
      have h1 : (2 / c) * y ≤ (2 / c) * (c / 2) :=
        mul_le_mul_of_nonneg_left hy (by positivity)
      have h2 : (2 / c) * (c / 2) = 1 := by field_simp [hc.ne']
      linarith
    have hw_z : w = 0 := Real.smoothTransition.zero_of_nonpos harg
    rw [hw_z]
    ring_nf
    exact le_rfl
  · have hy' : c / 2 ≤ y := (not_le.mp hy).le
    calc c / 2 = w * (c / 2) + (1 - w) * (c / 2) := by ring
      _ ≤ w * y + (1 - w) * (c / 2) := by
          linarith [mul_le_mul_of_nonneg_left hy' hw0]

lemma contDiff_smoothInv {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothInv c) := by
  unfold smoothInv
  refine (contDiff_smoothClampPos c).inv fun y => ?_
  have hpos : 0 < c / 2 := half_pos hc
  exact (hpos.trans_le (half_le_smoothClampPos hc y)).ne'

lemma smoothInv_eq_inv_of_le {c y : ℝ} (hc : 0 < c) (hy : c ≤ y) :
    smoothInv c y = y⁻¹ := by
  unfold smoothInv smoothClampPos
  have harg : 1 ≤ (2 / c) * y - 1 := by
    have h1 : (2 / c) * c ≤ (2 / c) * y := mul_le_mul_of_nonneg_left hy (by positivity)
    have h2 : (2 / c) * c = 2 := by field_simp [hc.ne']
    linarith
  rw [Real.smoothTransition.one_of_one_le harg]
  ring_nf

def regDenom (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (b_K : (Fin 4 → ℝ) → ℝ)
    (q : Fin 4 → ℝ) : ℝ :=
  (∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2) + (1 - b_K q) ^ 2

lemma contDiff_regDenom {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K) :
    ContDiff ℝ (⊤ : ℕ∞) (regDenom m x0 t b_K) := by
  unfold regDenom
  have h0 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Fin 4 → ℝ => ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2) := by
    simp_rw [Fin.sum_univ_four]
    exact ((((contDiff_normPhaseGrad hm x0 t 0).pow 2).add
      ((contDiff_normPhaseGrad hm x0 t 1).pow 2)).add
      ((contDiff_normPhaseGrad hm x0 t 2).pow 2)).add
      ((contDiff_normPhaseGrad hm x0 t 3).pow 2)
  exact h0.add ((contDiff_const.sub hb_cd).pow 2)

lemma regDenom_bounds {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_bd : ∀ q, 0 ≤ b_K q ∧ b_K q ≤ 1)
    {c₀ : ℝ}
    (h_nonstat : ∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2)
    (q : Fin 4 → ℝ) :
    min (c₀ ^ 2) (1 / 4) ≤ regDenom m x0 t b_K q ∧ regDenom m x0 t b_K q ≤ 5 := by
  have h_top : regDenom m x0 t b_K q ≤ 5 := by
    unfold regDenom
    have h_each : ∀ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2 ≤ 1 := fun μ => by
      have ha := abs_normPhaseGrad_le_one hm x0 t μ q
      rw [← sq_abs]
      nlinarith [abs_nonneg (normPhaseGrad m x0 t μ q)]
    have h_sum : ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2 ≤ 4 := by
      have := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => h_each μ)
      simpa using this
    have hb_sq : (1 - b_K q) ^ 2 ≤ 1 := by
      rcases hb_bd q with ⟨h0, h1⟩
      nlinarith
    linarith
  have h_bot : min (c₀ ^ 2) (1 / 4) ≤ regDenom m x0 t b_K q := by
    unfold regDenom
    by_cases hbq : b_K q ≤ 1 / 2
    · have h1 : (1 / 4 : ℝ) ≤ (1 - b_K q) ^ 2 := by nlinarith
      have h2 : 0 ≤ ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact (min_le_right _ _).trans (by linarith)
    · have hbq_pos : 0 < b_K q := by linarith [not_le.mp hbq]
      have hq_mem : q ∈ tsupport b_K := subset_tsupport _ (Function.mem_support.mpr hbq_pos.ne')
      have h_ns := h_nonstat q hq_mem
      exact (min_le_left _ _).trans (le_add_of_le_of_nonneg h_ns (sq_nonneg _))
  exact ⟨h_bot, h_top⟩

def ibpCoeff (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (b_K : (Fin 4 → ℝ) → ℝ)
    (c_min : ℝ) (μ : Fin 4) (q : Fin 4 → ℝ) : ℝ :=
  normPhaseGrad m x0 t μ q * smoothInv c_min (regDenom m x0 t b_K q)

def normIBPOp (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ) (b_K : (Fin 4 → ℝ) → ℝ)
    (c_min : ℝ) (v : (Fin 4 → ℝ) → ℂ) (q : Fin 4 → ℝ) : ℂ :=
  ∑ μ : Fin 4, fderiv ℝ (fun q' => ((ibpCoeff m x0 t b_K c_min μ q' : ℝ) : ℂ) * v q') q
    (Pi.single μ 1)

lemma contDiff_ibpCoeff {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K)
    {c_min : ℝ} (hc_min : 0 < c_min) (μ : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (ibpCoeff m x0 t b_K c_min μ) := by
  unfold ibpCoeff
  exact (contDiff_normPhaseGrad hm x0 t μ).mul
    ((contDiff_smoothInv hc_min).comp (contDiff_regDenom hm x0 t hb_cd))

lemma contDiff_normIBPOp {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K)
    {c_min : ℝ} (hc_min : 0 < c_min) {v : (Fin 4 → ℝ) → ℂ} (hv_cd : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞) (normIBPOp m x0 t b_K c_min v) := by
  unfold normIBPOp
  have h_each : ∀ μ : Fin 4, ContDiff ℝ (⊤ : ℕ∞) (fun q =>
      fderiv ℝ (fun q' => ((ibpCoeff m x0 t b_K c_min μ q' : ℝ) : ℂ) * v q') q
        (Pi.single μ 1)) := by
    intro μ
    have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun q' : Fin 4 → ℝ =>
        ((ibpCoeff m x0 t b_K c_min μ q' : ℝ) : ℂ) * v q') :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_ibpCoeff hm x0 t hb_cd hc_min μ)).mul hv_cd
    exact (ContinuousLinearMap.apply ℝ ℂ (Pi.single μ (1 : ℝ))).contDiff.comp
      (hprod.fderiv_right top_enat_coe_add_one_le)
  simp_rw [Fin.sum_univ_four]
  exact (((h_each 0).add (h_each 1)).add (h_each 2)).add (h_each 3)

lemma tsupport_normIBPOp_subset (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ)
    (b_K : (Fin 4 → ℝ) → ℝ) (c_min : ℝ) (v : (Fin 4 → ℝ) → ℂ) :
    tsupport (normIBPOp m x0 t b_K c_min v) ⊆ tsupport v := by
  refine closure_minimal ?_ isClosed_closure
  intro q hq
  rw [Function.mem_support] at hq
  by_contra hnot
  have h_ev0 : v =ᶠ[𝓝 q] (fun _ => (0 : ℂ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hnot
  have h_all0 : ∀ μ : Fin 4,
      fderiv ℝ (fun q' => ((ibpCoeff m x0 t b_K c_min μ q' : ℝ) : ℂ) * v q') q
        (Pi.single μ 1) = 0 := by
    intro μ
    have h_fev : (fun q' : Fin 4 → ℝ => ((ibpCoeff m x0 t b_K c_min μ q' : ℝ) : ℂ) * v q') =ᶠ[𝓝 q]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [h_ev0] with q' hq'
      rw [hq', mul_zero]
    rw [h_fev.fderiv_eq]
    simp
  exact hq (by unfold normIBPOp; simp [h_all0])

lemma hasCompactSupport_normIBPOp (m : ℝ) (x0 : Fin 4 → ℝ) (t : ℝ)
    (b_K : (Fin 4 → ℝ) → ℝ) (c_min : ℝ) {v : (Fin 4 → ℝ) → ℂ}
    (hv_supp : HasCompactSupport v) :
    HasCompactSupport (normIBPOp m x0 t b_K c_min v) := by
  refine HasCompactSupport.of_support_subset_isCompact hv_supp.isCompact ?_
  exact subset_tsupport _ |>.trans (tsupport_normIBPOp_subset m x0 t b_K c_min v)

lemma integral_hrPhase_ibp_coord {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    (μ : Fin 4) {F : (Fin 4 → ℝ) → ℂ} (hF_cd : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF_supp : HasCompactSupport F) :
    (∫ q : Fin 4 → ℝ,
      (fderiv ℝ F q (Pi.single μ 1) +
        F q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ))) *
        expHrPhase m x0 t q) = 0 := by
  let e_μ : Fin 4 → ℝ := Pi.single μ 1
  let G : (Fin 4 → ℝ) → ℂ := fun q => F q * expHrPhase m x0 t q
  let φ : ℝ → ℂ := fun s => ∫ q : Fin 4 → ℝ, G (q + s • e_μ)
  have hφ_const : ∀ s : ℝ, φ s = φ 0 := fun s => by
    dsimp [φ]
    rw [MeasureTheory.integral_add_right_eq_self G (s • e_μ)]
    simp
  have hd_const : HasDerivAt φ 0 0 :=
    (hasDerivAt_const (0 : ℝ) (φ 0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hφ_const)
  let H_der : (Fin 4 → ℝ) → ℂ := fun q =>
    (fderiv ℝ F q e_μ + F q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ))) *
      expHrPhase m x0 t q
  obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_ball (0 : Fin 4 → ℝ) |>.mp
    hF_supp.isCompact.isBounded
  let R' : ℝ := max R 0
  let B_big : Set (Fin 4 → ℝ) := Metric.closedBall 0 (R' + 1)
  have hB_comp : IsCompact B_big := isCompact_closedBall 0 (R' + 1)
  have hB_ne : B_big.Nonempty := ⟨0, Metric.mem_closedBall_self (by positivity)⟩
  have hG_cd : ContDiff ℝ (⊤ : ℕ∞) G := hF_cd.mul (contDiff_expHrPhase hm x0 t)
  have hF'_cd : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => fderiv ℝ F q e_μ) :=
    (ContinuousLinearMap.apply ℝ ℂ e_μ).contDiff.comp (hF_cd.fderiv_right top_enat_coe_add_one_le)
  have hH_cd : ContDiff ℝ (⊤ : ℕ∞) H_der := by
    have h_gr : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => hrPhaseGrad m x0 t μ q) := by
      have h_eq : (fun q => hrPhaseGrad m x0 t μ q) =
          fun q => spacetimeScale x0 t * normPhaseGrad m x0 t μ q :=
        funext (hrPhaseGrad_eq_scale_mul_normPhaseGrad m x0 t μ)
      rw [h_eq]
      exact contDiff_const.mul (contDiff_normPhaseGrad hm x0 t μ)
    exact (hF'_cd.add (hF_cd.mul (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp h_gr)))).mul (contDiff_expHrPhase hm x0 t)
  obtain ⟨q_max, _, hq_max⟩ := hB_comp.exists_isMaxOn hB_ne
    (continuous_norm.comp hH_cd.continuous).continuousOn
  let M_bd : ℝ := ‖H_der q_max‖
  have hM_nn : 0 ≤ M_bd := norm_nonneg _
  let bound : (Fin 4 → ℝ) → ℝ := Set.indicator B_big (fun _ => M_bd)
  have h_bound_int : Integrable bound volume :=
    (integrableOn_const (hs := hB_comp.measure_lt_top.ne)).integrable_indicator
      measurableSet_closedBall
  have h_nhds : Set.Ioo (-1 / 2 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hG_supp : HasCompactSupport G := hF_supp.mul_right
  have hd_int : HasDerivAt φ (∫ q : Fin 4 → ℝ, H_der q) 0 := by
    have hd0 : (∫ q : Fin 4 → ℝ, H_der q) = ∫ q : Fin 4 → ℝ, H_der (q + (0 : ℝ) • e_μ) := by
      simp
    rw [hd0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℝ)
      (F := fun s q => G (q + s • e_μ)) (F' := fun s q => H_der (q + s • e_μ))
      (bound := bound) h_nhds ?_ ?_ ?_ ?_ h_bound_int ?_).2
    · filter_upwards [h_nhds] with s _
      exact (hG_cd.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · simpa using hG_cd.continuous.integrable_of_hasCompactSupport hG_supp
    · simp only [zero_smul, add_zero]
      exact hH_cd.continuous.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun q s hs => ?_
      have hs_abs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have he_norm : ‖e_μ‖ ≤ 1 := by
        dsimp [e_μ]
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro ν
        by_cases hν : ν = μ <;> simp [hν]
      by_cases hq_mem : q ∈ B_big
      · simp only [bound, Set.indicator_of_mem hq_mem]
        by_cases h_in : q + s • e_μ ∈ B_big
        · exact hq_max h_in
        · have h_not_supp : q + s • e_μ ∉ tsupport F := by
            intro hm
            have hb := hR hm
            rw [Metric.mem_ball, dist_zero_right] at hb
            exact h_in (Metric.mem_closedBall.mpr
              (by rw [dist_zero_right]; exact hb.le.trans (by linarith [le_max_left R 0])))
          have h_ev0 : F =ᶠ[𝓝 (q + s • e_μ)] (fun _ => (0 : ℂ)) :=
            notMem_tsupport_iff_eventuallyEq.mp h_not_supp
          have hF0 : F (q + s • e_μ) = 0 := h_ev0.self_of_nhds
          have hdF0 : fderiv ℝ F (q + s • e_μ) = 0 := by rw [h_ev0.fderiv_eq]; simp
          have hH0 : H_der (q + s • e_μ) = 0 := by simp [H_der, hF0, hdF0]
          rw [hH0, norm_zero]
          exact hM_nn
      · simp only [bound, Set.indicator_of_notMem hq_mem]
        have hq_gt : R' + 1 < ‖q‖ := by
          by_contra hle
          exact hq_mem (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact not_lt.mp hle))
        have h_qs_gt : R' < ‖q + s • e_μ‖ := by
          have htri := norm_le_add_norm_add q (s • e_μ)
          have hsn : ‖s • e_μ‖ ≤ 1 / 2 := by
            rw [norm_smul, Real.norm_eq_abs]
            calc |s| * ‖e_μ‖ ≤ (1 / 2) * 1 :=
                  mul_le_mul hs_abs he_norm (norm_nonneg _) (by norm_num)
              _ = 1 / 2 := mul_one _
          linarith
        have h_not_supp : q + s • e_μ ∉ tsupport F := by
          intro hm
          have hb := hR hm
          rw [Metric.mem_ball, dist_zero_right] at hb
          have := le_max_left R 0
          linarith
        have h_ev0 : F =ᶠ[𝓝 (q + s • e_μ)] (fun _ => (0 : ℂ)) :=
          notMem_tsupport_iff_eventuallyEq.mp h_not_supp
        have hF0 : F (q + s • e_μ) = 0 := h_ev0.self_of_nhds
        have hdF0 : fderiv ℝ F (q + s • e_μ) = 0 := by rw [h_ev0.fderiv_eq]; simp
        have hH0 : H_der (q + s • e_μ) = 0 := by simp [H_der, hF0, hdF0]
        rw [hH0, norm_zero]
    · refine Filter.Eventually.of_forall fun q s _ => ?_
      have h_line : HasDerivAt (fun u : ℝ => q + u • e_μ) e_μ s := by
        simpa using ((hasDerivAt_id s).smul_const e_μ).const_add q
      have h_F_u : HasDerivAt (fun u : ℝ => F (q + u • e_μ))
          (fderiv ℝ F (q + s • e_μ) e_μ) s :=
        (hF_cd.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt s h_line
      have h_ph_u : HasDerivAt (fun u : ℝ => hrPhase m x0 t (q + u • e_μ))
          (hrPhaseGrad m x0 t μ (q + s • e_μ)) s := by
        let tr : ℝ → ℝ := fun v => v - s
        have h_sh : HasDerivAt tr 1 s := by
          simpa [tr] using (hasDerivAt_id s).sub_const s
        have h_ph0 : HasDerivAt
            (fun v : ℝ => hrPhase m x0 t ((q + s • e_μ) + v • Pi.single μ 1))
            (hrPhaseGrad m x0 t μ (q + s • e_μ)) (tr s) := by
          simpa [tr, sub_self] using hasDerivAt_hrPhase_single hm x0 t μ (q + s • e_μ)
        have hc := h_ph0.comp s h_sh
        have h_eq : ((fun v => hrPhase m x0 t ((q + s • e_μ) + v • Pi.single μ 1)) ∘ tr) =
            fun u => hrPhase m x0 t (q + u • e_μ) := by
          ext u
          dsimp [Function.comp_def, tr, e_μ]
          congr 1
          rw [sub_smul]
          abel
        rw [h_eq, mul_one] at hc
        exact hc
      have h_arg_u := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s h_ph_u).const_mul
        Complex.I).neg
      have h_exp_u : HasDerivAt (fun u : ℝ => expHrPhase m x0 t (q + u • e_μ))
          (expHrPhase m x0 t (q + s • e_μ) *
            (-(Complex.I * ((hrPhaseGrad m x0 t μ (q + s • e_μ) : ℝ) : ℂ)))) s := by
        have h_raw := (Complex.hasDerivAt_exp _).scomp s h_arg_u
        refine h_raw.congr_deriv ?_
        rw [smul_eq_mul, mul_comm]
        simp only [expHrPhase, Function.comp_def, Pi.neg_apply, Complex.ofRealCLM_apply]
      refine (h_F_u.mul h_exp_u).congr_deriv ?_
      dsimp [H_der]
      ring
  exact (hd_int.unique hd_const).trans rfl

lemma integral_hrPhase_ibp_step {m : ℝ} (hm : 0 < m) (x0 : Fin 4 → ℝ) (t : ℝ)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K)
    (hb_bd : ∀ q, 0 ≤ b_K q ∧ b_K q ≤ 1)
    {c₀ c_min : ℝ} (hc₀ : 0 < c₀) (hc_min_def : c_min = min (c₀ ^ 2) (1 / 4))
    (h_nonstat : ∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2)
    {v : (Fin 4 → ℝ) → ℂ} (hv_cd : ContDiff ℝ (⊤ : ℕ∞) v) (hv_supp : HasCompactSupport v)
    (hv_one : ∀ q ∈ tsupport v, b_K q = 1) :
    (∫ q : Fin 4 → ℝ, v q * expHrPhase m x0 t q) =
      (-Complex.I * ((spacetimeScale x0 t)⁻¹ : ℂ)) *
        ∫ q : Fin 4 → ℝ, normIBPOp m x0 t b_K c_min v q * expHrPhase m x0 t q := by
  have hc_min_pos : 0 < c_min := by rw [hc_min_def]; positivity
  let F : Fin 4 → (Fin 4 → ℝ) → ℂ := fun μ q =>
    ((ibpCoeff m x0 t b_K c_min μ q : ℝ) : ℂ) * v q
  have hF_cd : ∀ μ : Fin 4, ContDiff ℝ (⊤ : ℕ∞) (F μ) := fun μ =>
    (Complex.ofRealCLM.contDiff.comp (contDiff_ibpCoeff hm x0 t hb_cd hc_min_pos μ)).mul hv_cd
  have hF_supp : ∀ μ : Fin 4, HasCompactSupport (F μ) := fun μ => hv_supp.mul_left
  have h_sum_zero : (∑ μ : Fin 4, ∫ q : Fin 4 → ℝ,
      (fderiv ℝ (F μ) q (Pi.single μ 1) +
        F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ))) *
        expHrPhase m x0 t q) = 0 :=
    Finset.sum_eq_zero fun μ _ => integral_hrPhase_ibp_coord hm x0 t μ (hF_cd μ) (hF_supp μ)
  have h_pt_id : ∀ q : Fin 4 → ℝ,
      (∑ μ : Fin 4,
        (fderiv ℝ (F μ) q (Pi.single μ 1) +
          F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ))) *
          expHrPhase m x0 t q) =
      normIBPOp m x0 t b_K c_min v q * expHrPhase m x0 t q -
        Complex.I * ((spacetimeScale x0 t : ℝ) : ℂ) * (v q * expHrPhase m x0 t q) := by
    intro q
    rw [Finset.sum_congr rfl fun μ _ => add_mul _ _ _]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    have h_n : (∑ μ : Fin 4, fderiv ℝ (F μ) q (Pi.single μ 1)) =
        normIBPOp m x0 t b_K c_min v q := rfl
    rw [h_n]
    by_cases hqv : q ∈ tsupport v
    · have hbq : b_K q = 1 := hv_one q hqv
      have hreg_ge : c_min ≤ regDenom m x0 t b_K q := by
        rw [hc_min_def]
        exact (regDenom_bounds hm x0 t hb_bd h_nonstat q).1
      have h_inv_eq : smoothInv c_min (regDenom m x0 t b_K q) =
          (∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2)⁻¹ := by
        rw [smoothInv_eq_inv_of_le hc_min_pos hreg_ge]
        unfold regDenom
        rw [hbq, sub_self, zero_pow two_ne_zero, add_zero]
      have hsum_nz : ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2 ≠ 0 := by
        have h_pos : 0 < regDenom m x0 t b_K q := hc_min_pos.trans_le hreg_ge
        have h_eq : regDenom m x0 t b_K q = ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2 := by
          unfold regDenom; rw [hbq, sub_self, zero_pow two_ne_zero, add_zero]
        linarith
      have h_alg : (∑ μ : Fin 4, ((ibpCoeff m x0 t b_K c_min μ q : ℝ) : ℂ) *
            ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ)) = ((spacetimeScale x0 t : ℝ) : ℂ) := by
        have h_each : ∀ μ : Fin 4,
            ((ibpCoeff m x0 t b_K c_min μ q : ℝ) : ℂ) * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ) =
              ((spacetimeScale x0 t : ℝ) : ℂ) *
                (((normPhaseGrad m x0 t μ q) ^ 2 *
                  (∑ ν : Fin 4, (normPhaseGrad m x0 t ν q) ^ 2)⁻¹ : ℝ) : ℂ) := by
          intro μ
          dsimp [ibpCoeff]
          rw [h_inv_eq, hrPhaseGrad_eq_scale_mul_normPhaseGrad m x0 t μ q]
          push_cast
          ring
        rw [Finset.sum_congr rfl fun μ _ => h_each μ, ← Finset.mul_sum]
        have h_real : (∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2 *
            (∑ ν : Fin 4, (normPhaseGrad m x0 t ν q) ^ 2)⁻¹) = 1 := by
          rw [← Finset.sum_mul, mul_inv_cancel₀ hsum_nz]
        rw [← Complex.ofReal_sum, h_real, Complex.ofReal_one, mul_one]
      have h_lhs : (∑ μ : Fin 4, F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ)) *
            expHrPhase m x0 t q) =
          -(Complex.I * ((spacetimeScale x0 t : ℝ) : ℂ) * (v q * expHrPhase m x0 t q)) := by
        have h_term : ∀ μ : Fin 4,
            F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ)) * expHrPhase m x0 t q =
              (-(Complex.I * (v q * expHrPhase m x0 t q))) *
                (((ibpCoeff m x0 t b_K c_min μ q : ℝ) : ℂ) *
                  ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ)) := by
          intro μ
          dsimp [F]
          ring
        rw [Finset.sum_congr rfl fun μ _ => h_term μ, ← Finset.mul_sum, h_alg]
        ring
      rw [h_lhs, sub_eq_add_neg]
    · have hv0 : v q = 0 := image_eq_zero_of_notMem_tsupport hqv
      have hz1 : (∑ μ : Fin 4, F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ)) *
          expHrPhase m x0 t q) = 0 := by
        simp [F, hv0]
      have hz2 : -(Complex.I * ((spacetimeScale x0 t : ℝ) : ℂ) * (v q * expHrPhase m x0 t q)) =
          0 := by
        simp [hv0]
      rw [hz1, sub_eq_add_neg, hz2]
  have h_int_F : ∀ μ : Fin 4, Integrable (fun q : Fin 4 → ℝ =>
      fderiv ℝ (F μ) q (Pi.single μ 1) * expHrPhase m x0 t q) volume := by
    intro μ
    have h_df : ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ (F μ) q (Pi.single μ 1)) :=
      ((hF_cd μ).fderiv_right top_enat_coe_add_one_le).clm_apply contDiff_const
    have h_cd : ContDiff ℝ (⊤ : ℕ∞) (fun q =>
        fderiv ℝ (F μ) q (Pi.single μ 1) * expHrPhase m x0 t q) :=
      h_df.mul (contDiff_expHrPhase hm x0 t)
    have h_supp : HasCompactSupport (fun q => fderiv ℝ (F μ) q (Pi.single μ 1)) := by
      refine HasCompactSupport.of_support_subset_isCompact (hF_supp μ).isCompact ?_
      intro q hq
      rw [Function.mem_support] at hq
      by_contra hnot
      have hev := notMem_tsupport_iff_eventuallyEq.mp hnot
      have hz : fderiv ℝ (F μ) q = 0 := by rw [hev.fderiv_eq]; simp
      exact hq (by rw [hz]; simp)
    exact h_cd.continuous.integrable_of_hasCompactSupport h_supp.mul_right
  have h_int_v : Integrable (fun q : Fin 4 → ℝ => v q * expHrPhase m x0 t q) volume :=
    (hv_cd.mul (contDiff_expHrPhase hm x0 t)).continuous.integrable_of_hasCompactSupport
      hv_supp.mul_right
  have h_int_ibp : Integrable (fun q : Fin 4 → ℝ =>
      normIBPOp m x0 t b_K c_min v q * expHrPhase m x0 t q) volume :=
    ((contDiff_normIBPOp hm x0 t hb_cd hc_min_pos hv_cd).mul
      (contDiff_expHrPhase hm x0 t)).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_normIBPOp m x0 t b_K c_min hv_supp).mul_right
  have h_int_diff : (∫ q : Fin 4 → ℝ,
      normIBPOp m x0 t b_K c_min v q * expHrPhase m x0 t q) -
      Complex.I * ((spacetimeScale x0 t : ℝ) : ℂ) *
        ∫ q : Fin 4 → ℝ, v q * expHrPhase m x0 t q = 0 := by
    rw [← integral_const_mul, ← integral_sub h_int_ibp (h_int_v.const_mul _)]
    have h_int_each : ∀ μ ∈ Finset.univ, Integrable (fun q : Fin 4 → ℝ =>
        (fderiv ℝ (F μ) q (Pi.single μ 1) +
          F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ))) *
          expHrPhase m x0 t q) volume := by
      intro μ _
      have h_cd : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ =>
          (fderiv ℝ (F μ) q (Pi.single μ 1) +
            F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ))) *
            expHrPhase m x0 t q) := by
        have h_gr : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 4 → ℝ => hrPhaseGrad m x0 t μ q) := by
          have heq : (fun q => hrPhaseGrad m x0 t μ q) =
              fun q => spacetimeScale x0 t * normPhaseGrad m x0 t μ q :=
            funext (hrPhaseGrad_eq_scale_mul_normPhaseGrad m x0 t μ)
          rw [heq]
          exact contDiff_const.mul (contDiff_normPhaseGrad hm x0 t μ)
        have h_df : ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ (F μ) q (Pi.single μ 1)) :=
          ((hF_cd μ).fderiv_right top_enat_coe_add_one_le).clm_apply contDiff_const
        exact (h_df.add ((hF_cd μ).mul (contDiff_const.mul
          (Complex.ofRealCLM.contDiff.comp h_gr)))).mul (contDiff_expHrPhase hm x0 t)
      have h_supp : HasCompactSupport (fun q : Fin 4 → ℝ =>
          (fderiv ℝ (F μ) q (Pi.single μ 1) +
            F μ q * (-Complex.I * ((hrPhaseGrad m x0 t μ q : ℝ) : ℂ)))) := by
        refine HasCompactSupport.of_support_subset_isCompact (hF_supp μ).isCompact ?_
        intro q hq
        rw [Function.mem_support] at hq
        by_contra hnot
        have hev := notMem_tsupport_iff_eventuallyEq.mp hnot
        have hz1 : F μ q = 0 := hev.self_of_nhds
        have hz2 : fderiv ℝ (F μ) q = 0 := by rw [hev.fderiv_eq]; simp
        exact hq (by simp [hz1, hz2])
      exact h_cd.continuous.integrable_of_hasCompactSupport h_supp.mul_right
    rw [← integral_finsetSum _ h_int_each] at h_sum_zero
    rw [← h_sum_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => (h_pt_id q).symm)
  have h_eq_mul : Complex.I * ((spacetimeScale x0 t : ℝ) : ℂ) *
      ∫ q : Fin 4 → ℝ, v q * expHrPhase m x0 t q =
      ∫ q : Fin 4 → ℝ, normIBPOp m x0 t b_K c_min v q * expHrPhase m x0 t q :=
    (sub_eq_zero.mp h_int_diff).symm
  have hs_ne : ((spacetimeScale x0 t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (spacetimeScale_pos x0 t).ne'
  calc (∫ q : Fin 4 → ℝ, v q * expHrPhase m x0 t q)
      = (-Complex.I * ((spacetimeScale x0 t)⁻¹ : ℂ)) *
          (Complex.I * ((spacetimeScale x0 t : ℝ) : ℂ) *
            ∫ q : Fin 4 → ℝ, v q * expHrPhase m x0 t q) := by
          field_simp [hs_ne]
          simp [Complex.I_sq]
    _ = (-Complex.I * ((spacetimeScale x0 t)⁻¹ : ℂ)) *
          ∫ q : Fin 4 → ℝ, normIBPOp m x0 t b_K c_min v q * expHrPhase m x0 t q := by
          rw [h_eq_mul]

lemma exists_uniform_ibpCoeff_deriv_bound {m : ℝ} (hm : 0 < m)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K)
    (hb_bd : ∀ q, 0 ≤ b_K q ∧ b_K q ≤ 1)
    {c₀ c_min : ℝ} (hc₀ : 0 < c₀) (hc_min_def : c_min = min (c₀ ^ 2) (1 / 4))
    (R_b : ℝ) (hRb : 0 ≤ R_b) (M : ℕ) :
    ∃ K_c : ℝ, 0 ≤ K_c ∧
      ∀ (x0 : Fin 4 → ℝ) (t : ℝ),
        (∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2) →
        ∀ (μ : Fin 4) (i : ℕ), i ≤ M → ∀ q ∈ Metric.closedBall (0 : Fin 4 → ℝ) R_b,
          ‖iteratedFDeriv ℝ i (fun q' => (ibpCoeff m x0 t b_K c_min μ q' : ℂ)) q‖ ≤ K_c := by
  have hc_min_pos : 0 < c_min := by rw [hc_min_def]; positivity
  let B : Set (Fin 4 → ℝ) := Metric.closedBall 0 R_b
  have hB_comp : IsCompact B := isCompact_closedBall 0 R_b
  have hB_ne : B.Nonempty := ⟨0, Metric.mem_closedBall_self hRb⟩
  let v_fn : Fin 3 → (Fin 4 → ℝ) → ℝ := fun j q => velocityVec m (spatialPart q) j
  have hv_cd : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (v_fn j) := fun j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).contDiff.comp
      ((contDiff_velocityVec hm).comp contDiff_spatialPart)
  have h_v_bd : ∀ (j : Fin 3) (i : Fin (M + 1)), ∃ M_v : ℝ, 0 ≤ M_v ∧
      ∀ q ∈ B, ‖iteratedFDeriv ℝ i.val (v_fn j) q‖ ≤ M_v := by
    intro j i
    have hc : Continuous (iteratedFDeriv ℝ i.val (v_fn j)) :=
      (hv_cd j).continuous_iteratedFDeriv (mod_cast le_top)
    obtain ⟨q₀, _, hq₀⟩ := hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn
    exact ⟨‖iteratedFDeriv ℝ i.val (v_fn j) q₀‖, norm_nonneg _, fun q hq => hq₀ hq⟩
  choose M_v hMv_nn hMv_le using h_v_bd
  let M_np : ℝ := 1 + ∑ j : Fin 3, ∑ i : Fin (M + 1), M_v j i
  have hMnp_nn : 0 ≤ M_np := by
    have : 0 ≤ ∑ j : Fin 3, ∑ i : Fin (M + 1), M_v j i :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hMv_nn j i
    dsimp [M_np]
    linarith
  have hMnp_one : 1 ≤ M_np := by
    have : 0 ≤ ∑ j : Fin 3, ∑ i : Fin (M + 1), M_v j i :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => hMv_nn j i
    dsimp [M_np]
    linarith
  have h_np_bd : ∀ (x0 : Fin 4 → ℝ) (t : ℝ) (μ : Fin 4) (i : ℕ), i ≤ M →
      ∀ q ∈ B, ‖iteratedFDeriv ℝ i (normPhaseGrad m x0 t μ) q‖ ≤ M_np := by
    intro x0 t μ i hiM q hq
    rcases i with _ | r
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (abs_normPhaseGrad_le_one hm x0 t μ q).trans hMnp_one
    · have h_step : ∀ (j : Fin 3),
          ‖iteratedFDeriv ℝ (r + 1) (normPhaseGrad m x0 t j.succ) q‖ ≤ M_np := by
        intro j
        let α_sc : ℝ := (spacetimeScale x0 t)⁻¹ * t
        have hα_abs : |α_sc| ≤ 1 := by
          dsimp [α_sc]
          have hs : 0 < spacetimeScale x0 t := spacetimeScale_pos x0 t
          have ht_le : |t| ≤ spacetimeScale x0 t := by
            unfold spacetimeScale
            linarith [abs_nonneg (x0 0), norm_nonneg (spatialPart x0)]
          rw [abs_mul, abs_inv, abs_of_pos hs, inv_mul_le_one₀ hs]
          exact ht_le
        have h_eq : normPhaseGrad m x0 t j.succ =
            fun q' => α_sc • v_fn j q' - ((spacetimeScale x0 t)⁻¹ * x0 j.succ) := by
          ext q'
          fin_cases j <;> (simp [normPhaseGrad, hrPhaseGrad, v_fn, α_sc, smul_eq_mul]; ring)
        have h_lin_eq : iteratedFDeriv ℝ (r + 1) (normPhaseGrad m x0 t j.succ) q =
            iteratedFDeriv ℝ (r + 1) (α_sc • v_fn j) q := by
          rw [h_eq]
          change iteratedFDeriv ℝ (r + 1)
              ((α_sc • v_fn j) - (fun _ => ((spacetimeScale x0 t)⁻¹ * x0 j.succ))) q =
            iteratedFDeriv ℝ (r + 1) (α_sc • v_fn j) q
          have h_cd_sm : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (α_sc • v_fn j) :=
            (contDiff_const.smul (hv_cd j)).of_le (natCast_le_top_enat_coe (r + 1))
          rw [iteratedFDeriv_sub_apply h_cd_sm.contDiffAt contDiff_const.contDiffAt,
            iteratedFDeriv_const_succ, sub_zero]
        rw [h_lin_eq, iteratedFDeriv_const_smul_apply
          (((hv_cd j).of_le (natCast_le_top_enat_coe (r + 1))).contDiffAt),
          norm_smul, Real.norm_eq_abs]
        let fr : Fin (M + 1) := ⟨r + 1, Nat.lt_succ_of_le hiM⟩
        have h1 : ‖iteratedFDeriv ℝ (r + 1) (v_fn j) q‖ ≤ M_v j fr := hMv_le j fr q hq
        have h2 : M_v j fr ≤ M_np := by
          have h_s1 : M_v j fr ≤ ∑ i' : Fin (M + 1), M_v j i' :=
            Finset.single_le_sum (fun i' _ => hMv_nn j i') (Finset.mem_univ fr)
          have h_s2 : (∑ i' : Fin (M + 1), M_v j i') ≤
              ∑ j' : Fin 3, ∑ i' : Fin (M + 1), M_v j' i' :=
            Finset.single_le_sum
              (fun j' _ => Finset.sum_nonneg fun i' _ => hMv_nn j' i') (Finset.mem_univ j)
          dsimp [M_np]
          linarith
        calc |α_sc| * ‖iteratedFDeriv ℝ (r + 1) (v_fn j) q‖
            ≤ 1 * M_np := mul_le_mul hα_abs (h1.trans h2) (norm_nonneg _) zero_le_one
          _ = M_np := one_mul _
      fin_cases μ
      · change ‖iteratedFDeriv ℝ (r + 1) (normPhaseGrad m x0 t 0) q‖ ≤ M_np
        have h_eq : normPhaseGrad m x0 t 0 = fun _ => (spacetimeScale x0 t)⁻¹ * (x0 0 - t) := rfl
        rw [h_eq, iteratedFDeriv_const_succ, norm_zero]
        exact hMnp_nn
      · exact h_step 0
      · exact h_step 1
      · exact h_step 2
  let M_b : Fin (M + 1) → ℝ := fun i =>
    let hc : Continuous (iteratedFDeriv ℝ i.val (fun q' : Fin 4 → ℝ => 1 - b_K q')) :=
      (contDiff_const.sub hb_cd).continuous_iteratedFDeriv (natCast_le_top_enat_coe i.val)
    ‖iteratedFDeriv ℝ i.val (fun q' : Fin 4 → ℝ => 1 - b_K q')
      ((hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn).choose)‖
  have hMb_le : ∀ (i : ℕ) (hi : i ≤ M) (q : Fin 4 → ℝ), q ∈ B →
      ‖iteratedFDeriv ℝ i (fun q' : Fin 4 → ℝ => 1 - b_K q') q‖ ≤
        M_b ⟨i, Nat.lt_succ_of_le hi⟩ := by
    intro i hi q hq
    let hc : Continuous (iteratedFDeriv ℝ i (fun q' : Fin 4 → ℝ => 1 - b_K q')) :=
      (contDiff_const.sub hb_cd).continuous_iteratedFDeriv (natCast_le_top_enat_coe i)
    exact (hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn).choose_spec.2 hq
  let M_b_max : ℝ := ∑ i : Fin (M + 1), M_b i
  have hMb_all : ∀ i ≤ M, ∀ q ∈ B,
      ‖iteratedFDeriv ℝ i (fun q' : Fin 4 → ℝ => 1 - b_K q') q‖ ≤ M_b_max := by
    intro i hi q hq
    refine (hMb_le i hi q hq).trans ?_
    exact Finset.single_le_sum (fun (j : Fin (M + 1)) _ => (norm_nonneg _ : 0 ≤ M_b j))
      (Finset.mem_univ (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (M + 1)))
  let B_pow : ℝ := ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np * M_np
  let B_oneb : ℝ := ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_b_max * M_b_max
  let D_reg : ℝ := 1 + 4 * (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np ^ 2) +
    (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_b_max ^ 2)
  have hD_reg_one : 1 ≤ D_reg := by
    have h1 : 0 ≤ ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np ^ 2 :=
      Finset.sum_nonneg fun j _ => by positivity
    have h2 : 0 ≤ ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_b_max ^ 2 :=
      Finset.sum_nonneg fun j _ => by positivity
    dsimp [D_reg]
    linarith
  have h_reg_bd : ∀ (x0 : Fin 4 → ℝ) (t : ℝ) (i : ℕ), i ≤ M → ∀ q ∈ B,
      ‖iteratedFDeriv ℝ i (regDenom m x0 t b_K) q‖ ≤ D_reg := by
    intro x0 t i hi q hq
    have h_sq_np : ∀ μ : Fin 4,
        ‖iteratedFDeriv ℝ i (fun q' => (normPhaseGrad m x0 t μ q') ^ 2) q‖ ≤
          ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np ^ 2 := by
      intro μ
      have h_mul : (fun q' => (normPhaseGrad m x0 t μ q') ^ 2) =
          fun q' => normPhaseGrad m x0 t μ q' * normPhaseGrad m x0 t μ q' := by
        ext q'; ring
      rw [h_mul]
      have hl := norm_iteratedFDeriv_mul_le (contDiff_normPhaseGrad hm x0 t μ)
        (contDiff_normPhaseGrad hm x0 t μ) q (natCast_le_top_enat_coe i)
      refine hl.trans ?_
      have h_sum1 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j (normPhaseGrad m x0 t μ) q‖ *
              ‖iteratedFDeriv ℝ (i - j) (normPhaseGrad m x0 t μ) q‖) ≤
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_np ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj_le : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h_p := mul_le_mul (h_np_bd x0 t μ j (hj_le.trans hi) q hq)
          (h_np_bd x0 t μ (i - j) ((Nat.sub_le i j).trans hi) q hq)
          (norm_nonneg _) hMnp_nn
        calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (normPhaseGrad m x0 t μ) q‖ *
              ‖iteratedFDeriv ℝ (i - j) (normPhaseGrad m x0 t μ) q‖
            = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (normPhaseGrad m x0 t μ) q‖ *
                ‖iteratedFDeriv ℝ (i - j) (normPhaseGrad m x0 t μ) q‖) := by ring
          _ ≤ (i.choose j : ℝ) * (M_np * M_np) :=
              mul_le_mul_of_nonneg_left h_p (Nat.cast_nonneg _)
          _ = (i.choose j : ℝ) * M_np ^ 2 := by ring
      refine h_sum1.trans ?_
      have h_choose_le : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) ≤ (M.choose j : ℝ) := by
        intro j _
        exact Nat.cast_le.mpr (Nat.choose_le_choose j hi)
      calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_np ^ 2)
          ≤ ∑ j ∈ Finset.range (i + 1), (M.choose j : ℝ) * M_np ^ 2 :=
            Finset.sum_le_sum fun j hj =>
              mul_le_mul_of_nonneg_right (h_choose_le j hj) (sq_nonneg _)
        _ ≤ ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.succ_le_succ hi)) (fun _ _ _ => by positivity)
    have h_sq_b : ‖iteratedFDeriv ℝ i (fun q' => (1 - b_K q') ^ 2) q‖ ≤
        ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_b_max ^ 2 := by
      have h_mul : (fun q' => (1 - b_K q') ^ 2) = fun q' => (1 - b_K q') * (1 - b_K q') := by
        ext q'; ring
      rw [h_mul]
      have hl := norm_iteratedFDeriv_mul_le ((contDiff_const (c := (1 : ℝ))).sub hb_cd)
        ((contDiff_const (c := (1 : ℝ))).sub hb_cd) q (natCast_le_top_enat_coe i)
      refine hl.trans ?_
      have h_Mb_nn : 0 ≤ M_b_max := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have h_sum1 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j (fun q' => 1 - b_K q') q‖ *
              ‖iteratedFDeriv ℝ (i - j) (fun q' => 1 - b_K q') q‖) ≤
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_b_max ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj_le : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h_p := mul_le_mul (hMb_all j (hj_le.trans hi) q hq)
          (hMb_all (i - j) ((Nat.sub_le i j).trans hi) q hq) (norm_nonneg _) h_Mb_nn
        calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun q' => 1 - b_K q') q‖ *
              ‖iteratedFDeriv ℝ (i - j) (fun q' => 1 - b_K q') q‖
            = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (fun q' => 1 - b_K q') q‖ *
                ‖iteratedFDeriv ℝ (i - j) (fun q' => 1 - b_K q') q‖) := by ring
          _ ≤ (i.choose j : ℝ) * (M_b_max * M_b_max) :=
              mul_le_mul_of_nonneg_left h_p (Nat.cast_nonneg _)
          _ = (i.choose j : ℝ) * M_b_max ^ 2 := by ring
      refine h_sum1.trans ?_
      calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_b_max ^ 2)
          ≤ ∑ j ∈ Finset.range (i + 1), (M.choose j : ℝ) * M_b_max ^ 2 :=
            Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr (Nat.choose_le_choose j hi)) (sq_nonneg _)
        _ ≤ ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_b_max ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_mono (Nat.succ_le_succ hi)) (fun _ _ _ => by positivity)
    have h_add_reg : iteratedFDeriv ℝ i (regDenom m x0 t b_K) q =
        iteratedFDeriv ℝ i (fun q' => ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q') ^ 2) q +
          iteratedFDeriv ℝ i (fun q' => (1 - b_K q') ^ 2) q := by
      have h_cd1 : ContDiff ℝ i (fun q' : Fin 4 → ℝ =>
          ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q') ^ 2) := by
        simp_rw [Fin.sum_univ_four]
        exact (((((contDiff_normPhaseGrad hm x0 t 0).pow 2).add
          ((contDiff_normPhaseGrad hm x0 t 1).pow 2)).add
          ((contDiff_normPhaseGrad hm x0 t 2).pow 2)).add
          ((contDiff_normPhaseGrad hm x0 t 3).pow 2)).of_le (natCast_le_top_enat_coe i)
      have h_cd2 : ContDiff ℝ i (fun q' : Fin 4 → ℝ => (1 - b_K q') ^ 2) :=
        ((contDiff_const.sub hb_cd).pow 2).of_le (natCast_le_top_enat_coe i)
      exact iteratedFDeriv_add_apply h_cd1.contDiffAt h_cd2.contDiffAt
    have h_sum_sq : iteratedFDeriv ℝ i
        (fun q' : Fin 4 → ℝ => ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q') ^ 2) q =
        ∑ μ : Fin 4, iteratedFDeriv ℝ i (fun q' => (normPhaseGrad m x0 t μ q') ^ 2) q := by
      have h_each : ∀ μ : Fin 4,
          ContDiff ℝ i (fun q' : Fin 4 → ℝ => (normPhaseGrad m x0 t μ q') ^ 2) :=
        fun μ => ((contDiff_normPhaseGrad hm x0 t μ).pow 2).of_le (natCast_le_top_enat_coe i)
      rw [iteratedFDeriv_sum (fun μ _ => h_each μ), Finset.sum_apply]
    rw [h_add_reg]
    calc ‖iteratedFDeriv ℝ i (fun q' => ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q') ^ 2) q +
            iteratedFDeriv ℝ i (fun q' => (1 - b_K q') ^ 2) q‖
        ≤ ‖iteratedFDeriv ℝ i (fun q' => ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q') ^ 2) q‖ +
            ‖iteratedFDeriv ℝ i (fun q' => (1 - b_K q') ^ 2) q‖ := norm_add_le _ _
      _ ≤ (∑ μ : Fin 4, ‖iteratedFDeriv ℝ i (fun q' => (normPhaseGrad m x0 t μ q') ^ 2) q‖) +
            ‖iteratedFDeriv ℝ i (fun q' => (1 - b_K q') ^ 2) q‖ := by
          rw [h_sum_sq]
          linarith [norm_sum_le Finset.univ
            (fun μ => iteratedFDeriv ℝ i (fun q' => (normPhaseGrad m x0 t μ q') ^ 2) q)]
      _ ≤ 4 * (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np ^ 2) +
            (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_b_max ^ 2) := by
          have h4 := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => h_sq_np μ)
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h4
          exact add_le_add h4 h_sq_b
      _ ≤ D_reg := by dsimp [D_reg]; linarith
  let K_si_each : Fin (M + 1) → ℝ := fun r =>
    let hc : Continuous (iteratedFDeriv ℝ r.val (smoothInv c_min)) :=
      (contDiff_smoothInv hc_min_pos).continuous_iteratedFDeriv (natCast_le_top_enat_coe r.val)
    ‖iteratedFDeriv ℝ r.val (smoothInv c_min)
      (((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 5)).exists_isMaxOn
        ⟨0, by norm_num, by norm_num⟩ (continuous_norm.comp hc).continuousOn).choose)‖
  let K_si : ℝ := ∑ r : Fin (M + 1), K_si_each r
  have hKsi_nn : 0 ≤ K_si := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKsi_le : ∀ r ≤ M, ∀ y ∈ Set.Icc (0 : ℝ) 5,
      ‖iteratedFDeriv ℝ r (smoothInv c_min) y‖ ≤ K_si := by
    intro r hr y hy
    let hc : Continuous (iteratedFDeriv ℝ r (smoothInv c_min)) :=
      (contDiff_smoothInv hc_min_pos).continuous_iteratedFDeriv (natCast_le_top_enat_coe r)
    have h1 : ‖iteratedFDeriv ℝ r (smoothInv c_min) y‖ ≤ K_si_each ⟨r, Nat.lt_succ_of_le hr⟩ :=
      ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 5)).exists_isMaxOn
        ⟨0, by norm_num, by norm_num⟩ (continuous_norm.comp hc).continuousOn).choose_spec.2 hy
    exact h1.trans (Finset.single_le_sum
      (fun (r' : Fin (M + 1)) _ => (norm_nonneg _ : 0 ≤ K_si_each r'))
      (Finset.mem_univ (⟨r, Nat.lt_succ_of_le hr⟩ : Fin (M + 1))))
  let M_si_comp : ℝ := (Nat.factorial M : ℝ) * K_si * D_reg ^ M
  have hMsi_nn : 0 ≤ M_si_comp :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKsi_nn) (pow_nonneg (by linarith) _)
  let K_c : ℝ := ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * M_np * M_si_comp
  refine ⟨K_c, Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hMnp_nn) hMsi_nn,
    fun x0 t h_ns μ i hiM q hq => ?_⟩
  have h_si_bd : ∀ j ≤ i, ‖iteratedFDeriv ℝ j
      (fun q' => smoothInv c_min (regDenom m x0 t b_K q')) q‖ ≤ M_si_comp := by
    intro j hji
    have hjM : j ≤ M := hji.trans hiM
    have h_comp := norm_iteratedFDeriv_comp_le (contDiff_smoothInv hc_min_pos)
      (contDiff_regDenom hm x0 t hb_cd) (natCast_le_top_enat_coe j) q
      (fun r hr => by
        have hrb := regDenom_bounds hm x0 t hb_bd h_ns q
        have h0_le : 0 ≤ regDenom m x0 t b_K q :=
          le_trans (le_min (sq_nonneg c₀) (by norm_num)) hrb.1
        exact hKsi_le r (hr.trans hjM) _ ⟨h0_le, hrb.2⟩)
      (fun r hr1 hrj => by
        have hD_pow : D_reg ≤ D_reg ^ r := by
          calc D_reg = D_reg ^ 1 := (pow_one D_reg).symm
            _ ≤ D_reg ^ r := pow_le_pow_right₀ hD_reg_one hr1
        exact (h_reg_bd x0 t r (hrj.trans hjM) q hq).trans hD_pow)
    refine h_comp.trans ?_
    have h_fac : (Nat.factorial j : ℝ) ≤ (Nat.factorial M : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le hjM)
    have h_pow : D_reg ^ j ≤ D_reg ^ M := pow_le_pow_right₀ hD_reg_one hjM
    exact mul_le_mul (mul_le_mul h_fac le_rfl hKsi_nn (Nat.cast_nonneg _)) h_pow
      (by positivity) (by positivity)
  have h_re_bd : ‖iteratedFDeriv ℝ i (ibpCoeff m x0 t b_K c_min μ) q‖ ≤ K_c := by
    unfold ibpCoeff
    have hl := norm_iteratedFDeriv_mul_le (contDiff_normPhaseGrad hm x0 t μ)
      ((contDiff_smoothInv hc_min_pos).comp (contDiff_regDenom hm x0 t hb_cd)) q
      (natCast_le_top_enat_coe i)
    refine hl.trans ?_
    have h_s1 : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (normPhaseGrad m x0 t μ) q‖ *
            ‖iteratedFDeriv ℝ (i - j) (fun q' => smoothInv c_min (regDenom m x0 t b_K q')) q‖) ≤
        ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_np * M_si_comp := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 := h_np_bd x0 t μ j (hji.trans hiM) q hq
      have h2 := h_si_bd (i - j) (Nat.sub_le i j)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMnp_nn)
    refine h_s1.trans ?_
    calc (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_np * M_si_comp)
        ≤ ∑ j ∈ Finset.range (i + 1), (M.choose j : ℝ) * M_np * M_si_comp :=
          Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_choose j hiM)) hMnp_nn)
              hMsi_nn
      _ ≤ K_c := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.succ_le_succ hiM)) (fun _ _ _ => mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) hMnp_nn) hMsi_nn)
  have h_ofReal := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
    ((contDiff_ibpCoeff hm x0 t hb_cd hc_min_pos μ).of_le
      (natCast_le_top_enat_coe i)).contDiffAt le_rfl (x := q)
  have h_clm_le : ‖Complex.ofRealCLM‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun r => by
      simp [Complex.norm_real]
  calc ‖iteratedFDeriv ℝ i (fun q' => (ibpCoeff m x0 t b_K c_min μ q' : ℂ)) q‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ i (ibpCoeff m x0 t b_K c_min μ) q‖ := h_ofReal
    _ ≤ 1 * K_c := mul_le_mul h_clm_le h_re_bd (norm_nonneg _) zero_le_one
    _ = K_c := one_mul _

lemma norm_iterated_normIBPOp_step {m : ℝ} (hm : 0 < m)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K)
    {c_min K_c : ℝ} (hc_min : 0 < c_min) (hKc : 0 ≤ K_c) (R_b : ℝ) (M : ℕ) (x0 : Fin 4 → ℝ) (t : ℝ)
    (h_ibp_bd : ∀ (μ : Fin 4) (i : ℕ), i ≤ M + 1 → ∀ q ∈ Metric.closedBall (0 : Fin 4 → ℝ) R_b,
      ‖iteratedFDeriv ℝ i (fun q' => (ibpCoeff m x0 t b_K c_min μ q' : ℂ)) q‖ ≤ K_c)
    {v : (Fin 4 → ℝ) → ℂ} (hv_cd : ContDiff ℝ (⊤ : ℕ∞) v) {A : ℝ} (hA : 0 ≤ A)
    (hv_bd : ∀ j ≤ M + 1, ∀ q ∈ Metric.closedBall (0 : Fin 4 → ℝ) R_b,
      ‖iteratedFDeriv ℝ j v q‖ ≤ A) :
    ∀ j ≤ M, ∀ q ∈ Metric.closedBall (0 : Fin 4 → ℝ) R_b,
      ‖iteratedFDeriv ℝ j (normIBPOp m x0 t b_K c_min v) q‖ ≤
        4 * (∑ a ∈ Finset.range (M + 2), ((M + 1).choose a : ℝ) * K_c * A) := by
  intro j hjM q hq
  have h_each : ∀ μ : Fin 4, ‖iteratedFDeriv ℝ j (fun q' =>
      fderiv ℝ (fun q'' => ((ibpCoeff m x0 t b_K c_min μ q'' : ℝ) : ℂ) * v q'') q'
        (Pi.single μ 1)) q‖ ≤
      ∑ a ∈ Finset.range (M + 2), ((M + 1).choose a : ℝ) * K_c * A := by
    intro μ
    let w : (Fin 4 → ℝ) → ℂ := fun q'' => ((ibpCoeff m x0 t b_K c_min μ q'' : ℝ) : ℂ) * v q''
    have hw_cd : ContDiff ℝ (⊤ : ℕ∞) w :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_ibpCoeff hm x0 t hb_cd hc_min μ)).mul hv_cd
    let L_μ : ((Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ (Pi.single μ 1)
    have hL_norm : ‖L_μ‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun φ => ?_
      change ‖φ (Pi.single μ 1)‖ ≤ 1 * ‖φ‖
      rw [one_mul]
      have h_single_le : ‖(Pi.single μ (1 : ℝ) : Fin 4 → ℝ)‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro ν
        by_cases hν : ν = μ <;> simp [hν]
      exact (φ.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg φ) h_single_le)
    have h1 := L_μ.norm_iteratedFDeriv_comp_left
      (hw_cd.fderiv_right top_enat_coe_add_one_le).contDiffAt (natCast_le_top_enat_coe j) (x := q)
    have h2 : ‖iteratedFDeriv ℝ j (fderiv ℝ w) q‖ = ‖iteratedFDeriv ℝ (j + 1) w q‖ :=
      norm_iteratedFDeriv_fderiv
    have h_clm : ‖iteratedFDeriv ℝ j (fun q' => fderiv ℝ w q' (Pi.single μ 1)) q‖ ≤
        ‖iteratedFDeriv ℝ (j + 1) w q‖ := by
      calc ‖iteratedFDeriv ℝ j (fun q' => fderiv ℝ w q' (Pi.single μ 1)) q‖
          ≤ ‖L_μ‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ w) q‖ := h1
        _ ≤ 1 * ‖iteratedFDeriv ℝ (j + 1) w q‖ := by
            rw [h2]
            exact mul_le_mul_of_nonneg_right hL_norm (norm_nonneg _)
        _ = ‖iteratedFDeriv ℝ (j + 1) w q‖ := one_mul _
    refine h_clm.trans ?_
    have hm_le := norm_iteratedFDeriv_mul_le
      (Complex.ofRealCLM.contDiff.comp (contDiff_ibpCoeff hm x0 t hb_cd hc_min μ))
      hv_cd q (natCast_le_top_enat_coe (j + 1))
    refine hm_le.trans ?_
    have h_s1 : (∑ a ∈ Finset.range (j + 2), ((j + 1).choose a : ℝ) *
          ‖iteratedFDeriv ℝ a (fun q' => ((ibpCoeff m x0 t b_K c_min μ q' : ℝ) : ℂ)) q‖ *
            ‖iteratedFDeriv ℝ (j + 1 - a) v q‖) ≤
        ∑ a ∈ Finset.range (j + 2), ((j + 1).choose a : ℝ) * K_c * A := by
      refine Finset.sum_le_sum fun a ha => ?_
      have ha_le : a ≤ j + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have ha_M : a ≤ M + 1 := ha_le.trans (Nat.succ_le_succ hjM)
      have hsub_M : j + 1 - a ≤ M + 1 := (Nat.sub_le (j + 1) a).trans (Nat.succ_le_succ hjM)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (h_ibp_bd μ a ha_M q hq) (Nat.cast_nonneg _))
        (hv_bd (j + 1 - a) hsub_M q hq) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hKc)
    refine h_s1.trans ?_
    calc (∑ a ∈ Finset.range (j + 2), ((j + 1).choose a : ℝ) * K_c * A)
        ≤ ∑ a ∈ Finset.range (j + 2), ((M + 1).choose a : ℝ) * K_c * A :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (Nat.cast_le.mpr (Nat.choose_le_choose a (Nat.succ_le_succ hjM))) hKc) hA
      _ ≤ ∑ a ∈ Finset.range (M + 2), ((M + 1).choose a : ℝ) * K_c * A :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.succ_le_succ (Nat.succ_le_succ hjM)))
            (fun _ _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hKc) hA)
  have h_sum_ibp : iteratedFDeriv ℝ j (normIBPOp m x0 t b_K c_min v) q =
      ∑ μ : Fin 4, iteratedFDeriv ℝ j (fun q' =>
        fderiv ℝ (fun q'' => ((ibpCoeff m x0 t b_K c_min μ q'' : ℝ) : ℂ) * v q'') q'
          (Pi.single μ 1)) q := by
    have h_cd_each : ∀ μ : Fin 4, ContDiff ℝ j (fun q' =>
        fderiv ℝ (fun q'' => ((ibpCoeff m x0 t b_K c_min μ q'' : ℝ) : ℂ) * v q'') q'
          (Pi.single μ 1)) := by
      intro μ
      have hw_cd : ContDiff ℝ (⊤ : ℕ∞) (fun q'' =>
          ((ibpCoeff m x0 t b_K c_min μ q'' : ℝ) : ℂ) * v q'') :=
        (Complex.ofRealCLM.contDiff.comp (contDiff_ibpCoeff hm x0 t hb_cd hc_min μ)).mul hv_cd
      exact ((ContinuousLinearMap.apply ℝ ℂ (Pi.single μ (1 : ℝ))).contDiff.comp
        (hw_cd.fderiv_right top_enat_coe_add_one_le)).of_le (natCast_le_top_enat_coe j)
    unfold normIBPOp
    rw [iteratedFDeriv_sum (fun μ _ => h_cd_each μ), Finset.sum_apply]
  rw [h_sum_ibp]
  refine (norm_sum_le _ _).trans ?_
  have h4 := Finset.sum_le_sum (fun μ (_ : μ ∈ Finset.univ) => h_each μ)
  simpa [Finset.sum_const, nsmul_eq_mul] using h4

lemma norm_timeModTestFn_mul_spacetimeScale_pow_le {m : ℝ} (hm : 0 < m)
    (u : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    {b_K : (Fin 4 → ℝ) → ℝ} (hb_cd : ContDiff ℝ (⊤ : ℕ∞) b_K)
    (hb_bd : ∀ q, 0 ≤ b_K q ∧ b_K q ≤ 1) (hb_one : ∀ q ∈ tsupport u, b_K q = 1)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (N : ℕ) :
    ∃ C_N : ℝ, 0 ≤ C_N ∧
      ∀ (x : Fin 1 → Fin 4 → ℝ) (t : ℝ),
        (∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m (x 0) t μ q) ^ 2) →
        ‖(timeModTestFn m hm u h_sm h_supp t) x‖ * (spacetimeScale (x 0) t) ^ N ≤ C_N := by
  let c_min : ℝ := min (c₀ ^ 2) (1 / 4)
  have hc_min_pos : 0 < c_min := by dsimp [c_min]; positivity
  obtain ⟨R₀, hR₀⟩ := Metric.isBounded_iff_subset_ball (0 : Fin 4 → ℝ) |>.mp
    h_supp.isCompact.isBounded
  let R_b : ℝ := max R₀ 1
  have hRb_pos : 0 < R_b := by positivity
  let B : Set (Fin 4 → ℝ) := Metric.closedBall 0 R_b
  have hB_comp : IsCompact B := isCompact_closedBall 0 R_b
  have hB_ne : B.Nonempty := ⟨0, Metric.mem_closedBall_self hRb_pos.le⟩
  have hu_sub_B : tsupport u ⊆ B := fun q hq => by
    have hb := hR₀ hq
    rw [Metric.mem_ball, dist_zero_right] at hb
    exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hb.le.trans (le_max_left _ _))
  obtain ⟨K_c, hKc_nn, hKc_bd⟩ := exists_uniform_ibpCoeff_deriv_bound hm hb_cd hb_bd hc₀
    (rfl : c_min = min (c₀ ^ 2) (1 / 4)) R_b hRb_pos.le N
  let A_fn : Fin (N + 1) → ℝ := fun j =>
    have hc : Continuous (iteratedFDeriv ℝ j.val u) :=
      h_sm.continuous_iteratedFDeriv (natCast_le_top_enat_coe j.val)
    ‖iteratedFDeriv ℝ j.val u
      ((hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn).choose)‖
  let A₀ : ℝ := ∑ j : Fin (N + 1), A_fn j
  have hA₀_nn : 0 ≤ A₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hu_bd : ∀ j ≤ N, ∀ q ∈ B, ‖iteratedFDeriv ℝ j u q‖ ≤ A₀ := by
    intro j hjN q hq
    have hc : Continuous (iteratedFDeriv ℝ j u) :=
      h_sm.continuous_iteratedFDeriv (natCast_le_top_enat_coe j)
    have h1 : ‖iteratedFDeriv ℝ j u q‖ ≤ A_fn ⟨j, Nat.lt_succ_of_le hjN⟩ :=
      (hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn).choose_spec.2 hq
    exact h1.trans (Finset.single_le_sum
      (fun (j' : Fin (N + 1)) _ => (norm_nonneg _ : 0 ≤ A_fn j'))
      (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hjN⟩ : Fin (N + 1))))
  have h_cd_iter : ∀ (n : ℕ) (y0 : Fin 4 → ℝ) (s : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) (((normIBPOp m y0 s b_K c_min)^[n]) u) := by
    intro n y0 s
    induction n with
    | zero => exact h_sm
    | succ n' ihn =>
      rw [Function.iterate_succ_apply']
      exact contDiff_normIBPOp hm y0 s hb_cd hc_min_pos ihn
  have h_supp_iter : ∀ (n : ℕ) (y0 : Fin 4 → ℝ) (s : ℝ),
      HasCompactSupport (((normIBPOp m y0 s b_K c_min)^[n]) u) := by
    intro n y0 s
    induction n with
    | zero => exact h_supp
    | succ n' ihn =>
      rw [Function.iterate_succ_apply']
      exact hasCompactSupport_normIBPOp m y0 s b_K c_min ihn
  have h_tsupp_iter : ∀ (n : ℕ) (y0 : Fin 4 → ℝ) (s : ℝ),
      tsupport (((normIBPOp m y0 s b_K c_min)^[n]) u) ⊆ tsupport u := by
    intro n y0 s
    induction n with
    | zero => exact Set.Subset.rfl
    | succ n' ihn =>
      rw [Function.iterate_succ_apply']
      exact (tsupport_normIBPOp_subset m y0 s b_K c_min _).trans ihn
  have h_ind_bd : ∀ k : ℕ, k ≤ N → ∃ A_k : ℝ, 0 ≤ A_k ∧
      ∀ (x0 : Fin 4 → ℝ) (t : ℝ),
        (∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m x0 t μ q) ^ 2) →
        ∀ j ≤ N - k, ∀ q ∈ B,
          ‖iteratedFDeriv ℝ j (((normIBPOp m x0 t b_K c_min)^[k]) u) q‖ ≤ A_k := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨A₀, hA₀_nn, fun _ _ _ j hj q hq => hu_bd j (by simpa using hj) q hq⟩
    | succ k ih =>
      intro hkN
      obtain ⟨A_k, hAk_nn, hAk_bd⟩ := ih (Nat.le_of_succ_le hkN)
      let M_s : ℕ := N - (k + 1)
      let A_next : ℝ := 4 * (∑ a ∈ Finset.range (M_s + 2), ((M_s + 1).choose a : ℝ) * K_c * A_k)
      refine ⟨A_next, by positivity, fun x0 t h_ns j hj q hq => ?_⟩
      have h_sub_eq : M_s + 1 = N - k := by dsimp [M_s]; omega
      have h_step := norm_iterated_normIBPOp_step hm hb_cd hc_min_pos hKc_nn R_b M_s x0 t
        (fun μ i hi q' hq' => hKc_bd x0 t h_ns μ i
          (by rw [h_sub_eq] at hi; exact hi.trans (Nat.sub_le N k)) q' hq')
        (h_cd_iter k x0 t) hAk_nn
        (fun i hi q' hq' => hAk_bd x0 t h_ns i (by rw [h_sub_eq] at hi; exact hi) q' hq')
      rw [Function.iterate_succ_apply']
      exact h_step j hj q hq
  obtain ⟨A_N, hAN_nn, hAN_bd⟩ := h_ind_bd N le_rfl
  let C_N : ℝ := ((2 * Real.pi)⁻¹ ^ 4) * (A_N * (volume : Measure (Fin 4 → ℝ)).real B)
  refine ⟨C_N, by positivity, fun x t h_ns => ?_⟩
  have h_ibp_iter : ∀ k : ℕ,
      (∫ q : Fin 4 → ℝ, u q * expHrPhase m (x 0) t q) =
        (-Complex.I * ((spacetimeScale (x 0) t)⁻¹ : ℂ)) ^ k *
          ∫ q : Fin 4 → ℝ, (((normIBPOp m (x 0) t b_K c_min)^[k]) u) q *
            expHrPhase m (x 0) t q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, pow_succ]
      have h_one_k : ∀ q ∈ tsupport (((normIBPOp m (x 0) t b_K c_min)^[k]) u), b_K q = 1 :=
        fun q hq => hb_one q (h_tsupp_iter k (x 0) t hq)
      rw [integral_hrPhase_ibp_step hm (x 0) t hb_cd hb_bd hc₀ (c_min := c_min) rfl h_ns
        (h_cd_iter k (x 0) t) (h_supp_iter k (x 0) t) h_one_k]
      rw [Function.iterate_succ_apply']
      ring
  have h_tsupp_N : tsupport (((normIBPOp m (x 0) t b_K c_min)^[N]) u) ⊆ B :=
    (h_tsupp_iter N (x 0) t).trans hu_sub_B
  have h_int_N_le :
      ‖∫ q : Fin 4 → ℝ, (((normIBPOp m (x 0) t b_K c_min)^[N]) u) q *
          expHrPhase m (x 0) t q‖ ≤ A_N * (volume : Measure (Fin 4 → ℝ)).real B := by
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun q hq => by
      have hnot : q ∉ tsupport (((normIBPOp m (x 0) t b_K c_min)^[N]) u) :=
        fun hm => hq (h_tsupp_N hm)
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]]
    refine MeasureTheory.norm_setIntegral_le_of_norm_le_const hB_comp.measure_lt_top fun q hq => ?_
    rw [norm_mul, norm_expHrPhase, mul_one]
    simpa [norm_iteratedFDeriv_zero] using hAN_bd (x 0) t h_ns 0 (by simp) q hq
  rw [timeModTestFn_apply, h_ibp_iter N, norm_mul, norm_mul, norm_pow, norm_mul,
    norm_neg, Complex.norm_I, one_mul]
  have hs_pos : 0 < spacetimeScale (x 0) t := spacetimeScale_pos (x 0) t
  have hsc_norm : ‖((spacetimeScale (x 0) t : ℝ) : ℂ)⁻¹‖ = (spacetimeScale (x 0) t)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hs_pos.le)]
  have hpi_norm : ‖(((2 * Real.pi)⁻¹ ^ 4 : ℝ) : ℂ)‖ = (2 * Real.pi)⁻¹ ^ 4 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hsc_norm, hpi_norm]
  calc (2 * Real.pi)⁻¹ ^ 4 * (((spacetimeScale (x 0) t)⁻¹) ^ N *
          ‖∫ q : Fin 4 → ℝ, (((normIBPOp m (x 0) t b_K c_min)^[N]) u) q *
            expHrPhase m (x 0) t q‖) *
        spacetimeScale (x 0) t ^ N
      = (2 * Real.pi)⁻¹ ^ 4 *
          ‖∫ q : Fin 4 → ℝ, (((normIBPOp m (x 0) t b_K c_min)^[N]) u) q *
            expHrPhase m (x 0) t q‖ *
          ((spacetimeScale (x 0) t)⁻¹ * spacetimeScale (x 0) t) ^ N := by ring
    _ = (2 * Real.pi)⁻¹ ^ 4 *
          ‖∫ q : Fin 4 → ℝ, (((normIBPOp m (x 0) t b_K c_min)^[N]) u) q *
            expHrPhase m (x 0) t q‖ := by
        rw [inv_mul_cancel₀ hs_pos.ne', one_pow, mul_one]
    _ ≤ (2 * Real.pi)⁻¹ ^ 4 * (A_N * (volume : Measure (Fin 4 → ℝ)).real B) :=
        mul_le_mul_of_nonneg_left h_int_N_le (by positivity)

def velocityFatSet (m : ℝ) (f : SmoothWavepacket) (r : ℝ) : Set (Fin 3 → ℝ) :=
  (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 + p.2) ''
    ((velocitySupport m f) ×ˢ Metric.closedBall (0 : Fin 3 → ℝ) (r / 2))

lemma isCompact_velocityFatSet {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) (r : ℝ) :
    IsCompact (velocityFatSet m f r) :=
  ((isCompact_velocitySupport hm f).prod (isCompact_closedBall 0 (r / 2))).image
    (continuous_fst.add continuous_snd)

lemma exists_global_iteratedFDeriv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} (hg_cd : ContDiff ℝ (⊤ : ℕ∞) g) (hg_supp : HasCompactSupport g) (j : ℕ) :
    ∃ B_j : ℝ, 0 ≤ B_j ∧ ∀ x : E, ‖iteratedFDeriv ℝ j g x‖ ≤ B_j := by
  by_cases hne : (tsupport g).Nonempty
  · have hc : Continuous (iteratedFDeriv ℝ j g) :=
      hg_cd.continuous_iteratedFDeriv (natCast_le_top_enat_coe j)
    obtain ⟨x₀, _, hx₀⟩ := hg_supp.isCompact.exists_isMaxOn hne
      (continuous_norm.comp hc).continuousOn
    refine ⟨‖iteratedFDeriv ℝ j g x₀‖, norm_nonneg _, fun x => ?_⟩
    by_cases hx : x ∈ tsupport g
    · exact hx₀ hx
    · have h_ev : g =ᶠ[𝓝 x] (fun _ => (0 : F)) := notMem_tsupport_iff_eventuallyEq.mp hx
      have h0 : iteratedFDeriv ℝ j g x = 0 := by
        rw [(h_ev.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
        simp
      rw [h0, norm_zero]
      exact norm_nonneg _
  · refine ⟨0, le_rfl, fun x => ?_⟩
    have hx : x ∉ tsupport g := fun h => hne ⟨x, h⟩
    have h_ev : g =ᶠ[𝓝 x] (fun _ => (0 : F)) := notMem_tsupport_iff_eventuallyEq.mp hx
    have h0 : iteratedFDeriv ℝ j g x = 0 := by
      rw [(h_ev.iteratedFDeriv (𝕜 := ℝ) j).self_of_nhds]
      simp
    rw [h0, norm_zero]

lemma exists_uniform_affine_comp_deriv_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} (hg_cd : ContDiff ℝ (⊤ : ℕ∞) g) (hg_supp : HasCompactSupport g)
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (j : ℕ) :
    ∃ B_j : ℝ, 0 ≤ B_j ∧ ∀ (s : ℝ) (c : F) (x : E),
      |s| ≤ 1 → ‖iteratedFDeriv ℝ j (fun y : E => g ((s • L) y + c)) x‖ ≤ B_j := by
  have h_raw : ∀ i : ℕ, ∃ A_i : ℝ, 0 ≤ A_i ∧ ∀ y : F, ‖iteratedFDeriv ℝ i g y‖ ≤ A_i :=
    fun i => exists_global_iteratedFDeriv_bound hg_cd hg_supp i
  choose A hA_nn hA_le using h_raw
  let C_g : ℝ := ∑ i : Fin (j + 1), A i.val
  have hCg_nn : 0 ≤ C_g := Finset.sum_nonneg fun i _ => hA_nn i.val
  let B_j : ℝ := (Nat.factorial j : ℝ) * C_g
  refine ⟨B_j, mul_nonneg (Nat.cast_nonneg _) hCg_nn, fun s c x hs => ?_⟩
  let T : E →L[ℝ] F := s • L
  let h : E → F := fun y => T y + c
  have hh_cd : ContDiff ℝ (⊤ : ℕ∞) h := T.contDiff.add contDiff_const
  have hh_fderiv : fderiv ℝ h = fun _ => T := by
    ext y v
    have hd0 := (T.hasFDerivAt (x := y)).add (hasFDerivAt_const c y)
    have h_fn : h = (⇑T + fun _ => c) := rfl
    rw [h_fn, (hd0.congr_fderiv (add_zero T)).fderiv]
  have h_comp := norm_iteratedFDeriv_comp_le hg_cd hh_cd (natCast_le_top_enat_coe j) x
    (fun i hi => by
      have hi1 := hA_le i (h x)
      exact hi1.trans (Finset.single_le_sum (fun (r : Fin (j + 1)) _ => hA_nn r.val)
        (Finset.mem_univ (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (j + 1)))))
    (fun i hi1 _ => by
      rw [one_pow]
      rcases i with _ | _ | r
      · omega
      · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero, hh_fderiv]
        calc ‖T‖ = |s| * ‖L‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ 1 * 1 := mul_le_mul hs hL (norm_nonneg _) zero_le_one
          _ = 1 := mul_one _
      · change ‖iteratedFDeriv ℝ ((r + 1) + 1) h x‖ ≤ 1
        rw [← norm_iteratedFDeriv_fderiv, hh_fderiv, iteratedFDeriv_const_succ, norm_zero]
        exact zero_le_one)
  refine h_comp.trans ?_
  rw [one_pow, mul_one]

def velSetCutoff (m : ℝ) (f : SmoothWavepacket) {hm : 0 < m} (r : ℝ) (hr : 0 < r) :
    (Fin 3 → ℝ) → ℝ :=
  (exists_smoothCutoff_compact_nhd (velocityFatSet m f r) (isCompact_velocityFatSet hm f r)
    (by positivity : 0 < r / 2)).choose

lemma contDiff_velSetCutoff {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (velSetCutoff m f (hm := hm) r hr) :=
  (exists_smoothCutoff_compact_nhd (velocityFatSet m f r) (isCompact_velocityFatSet hm f r)
    (by positivity : 0 < r / 2)).choose_spec.1

lemma hasCompactSupport_velSetCutoff {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (velSetCutoff m f (hm := hm) r hr) :=
  (exists_smoothCutoff_compact_nhd (velocityFatSet m f r) (isCompact_velocityFatSet hm f r)
    (by positivity : 0 < r / 2)).choose_spec.2.1

lemma velSetCutoff_bounds {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (w : Fin 3 → ℝ) :
    0 ≤ velSetCutoff m f (hm := hm) r hr w ∧ velSetCutoff m f (hm := hm) r hr w ≤ 1 :=
  (exists_smoothCutoff_compact_nhd (velocityFatSet m f r) (isCompact_velocityFatSet hm f r)
    (by positivity : 0 < r / 2)).choose_spec.2.2.1 w

lemma velSetCutoff_eq_one_of_dist {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) {w v : Fin 3 → ℝ} (hv : v ∈ velocitySupport m f)
    (hw : ‖w - v‖ ≤ r / 2) :
    velSetCutoff m f (hm := hm) r hr w = 1 := by
  have hw_fat : w ∈ velocityFatSet m f r := by
    refine ⟨(v, w - v), ⟨hv, ?_⟩, by simp⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw
  exact (exists_smoothCutoff_compact_nhd (velocityFatSet m f r) (isCompact_velocityFatSet hm f r)
    (by positivity : 0 < r / 2)).choose_spec.2.2.2.1 w hw_fat

lemma tsupport_velSetCutoff_subset {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) {w : Fin 3 → ℝ} (hw : w ∈ tsupport (velSetCutoff m f (hm := hm) r hr)) :
    ∃ v ∈ velocitySupport m f, ‖w - v‖ ≤ 5 * r / 6 := by
  have hspec := (exists_smoothCutoff_compact_nhd (velocityFatSet m f r)
    (isCompact_velocityFatSet hm f r) (by positivity : 0 < r / 2)).choose_spec.2.2.2.2 w hw
  rcases hspec with ⟨c, hc_fat, hc_dist⟩
  rcases hc_fat with ⟨⟨v, u⟩, ⟨hv, hu⟩, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  rw [dist_eq_norm] at hc_dist
  refine ⟨v, hv, ?_⟩
  calc ‖w - v‖ = ‖(w - (v + u)) + u‖ := by congr 1; abel
    _ ≤ ‖w - (v + u)‖ + ‖u‖ := norm_add_le _ _
    _ ≤ 2 * (r / 2) / 3 + r / 2 := add_le_add hc_dist hu
    _ = 5 * r / 6 := by ring

def timeWindowBump (r : ℝ) (hr : 0 < r) : ℝ → ℝ :=
  ({ rIn := r / 2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith } :
    ContDiffBump (0 : ℝ))

lemma contDiff_timeWindowBump (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (timeWindowBump r hr) :=
  ({ rIn := r / 2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith } :
    ContDiffBump (0 : ℝ)).contDiff

lemma hasCompactSupport_timeWindowBump (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (timeWindowBump r hr) :=
  ({ rIn := r / 2, rOut := r, rIn_pos := by positivity, rIn_lt_rOut := by linarith } :
    ContDiffBump (0 : ℝ)).hasCompactSupport

lemma timeWindowBump_eq_one_of_le (r : ℝ) (hr : 0 < r) {s : ℝ} (hs : |s| ≤ r / 2) :
    timeWindowBump r hr s = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hmem : s ∈ Metric.closedBall (0 : ℝ) b.rIn := by
    simpa [b, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hs
  exact b.one_of_mem_closedBall hmem

lemma tsupport_timeWindowBump_subset (r : ℝ) (hr : 0 < r) {s : ℝ}
    (hs : s ∈ tsupport (timeWindowBump r hr)) : |s| ≤ r := by
  by_contra hnot
  rw [not_le] at hnot
  let b : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have h_ev : timeWindowBump r hr =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_lt continuous_const continuous_abs |>.mem_nhds hnot] with u hu
    refine b.zero_of_le_dist ?_
    simpa [b, dist_zero_right, Real.norm_eq_abs] using hu.le
  exact notMem_tsupport_iff_eventuallyEq.mpr h_ev hs

def signedInvScale (t : ℝ) : ℝ :=
  if |t| < 1 then 1 else t⁻¹

lemma abs_signedInvScale_le_one (t : ℝ) : |signedInvScale t| ≤ 1 := by
  unfold signedInvScale
  split_ifs with h
  · simp
  · have ht1 : 1 ≤ |t| := not_lt.mp h
    rw [abs_inv]
    exact inv_le_one_of_one_le₀ ht1

lemma signedInvScale_ne_zero (t : ℝ) : signedInvScale t ≠ 0 := by
  unfold signedInvScale
  split_ifs with h
  · exact one_ne_zero
  · have ht : |t| ≠ 0 := by linarith [not_lt.mp h]
    exact inv_ne_zero (abs_ne_zero.mp ht)

def invTimeScale (t : ℝ) : ℝ :=
  (max |t| 1)⁻¹

lemma invTimeScale_pos (t : ℝ) : 0 < invTimeScale t := by
  unfold invTimeScale
  have : 1 ≤ max |t| 1 := le_max_right _ _
  positivity

lemma invTimeScale_le_one (t : ℝ) : invTimeScale t ≤ 1 := by
  unfold invTimeScale
  exact inv_le_one_of_one_le₀ (le_max_right _ _)

def timeCoordCLM : (Fin 1 → Fin 4 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 4 → ℝ) 0)

@[simp]
lemma timeCoordCLM_apply (x : Fin 1 → Fin 4 → ℝ) :
    timeCoordCLM x = x 0 0 := rfl

lemma norm_timeCoordCLM_le_one : ‖timeCoordCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [timeCoordCLM_apply, Real.norm_eq_abs, one_mul]
  exact (Real.norm_eq_abs (x 0 0) ▸ norm_le_pi_norm (x 0) 0).trans (norm_le_pi_norm x 0)

def spatialCoordCLM : (Fin 1 → Fin 4 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun j : Fin 3 =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j.succ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => Fin 4 → ℝ) 0)

@[simp]
lemma spatialCoordCLM_apply (x : Fin 1 → Fin 4 → ℝ) :
    spatialCoordCLM x = spatialPart (x 0) := rfl

lemma norm_spatialCoordCLM_le_one : ‖spatialCoordCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, spatialCoordCLM_apply, pi_norm_le_iff_of_nonneg (norm_nonneg x)]
  intro j
  exact (norm_le_pi_norm (x 0) j.succ).trans (norm_le_pi_norm x 0)

def velocityConeCutoff (m : ℝ) (hm : 0 < m) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (x : Fin 1 → Fin 4 → ℝ) : ℝ :=
  timeWindowBump r hr (invTimeScale t * (timeCoordCLM x - t)) *
    velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM x)

lemma contDiff_velocityConeCutoff {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityConeCutoff m hm f r hr t) := by
  unfold velocityConeCutoff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin 1 → Fin 4 → ℝ =>
      timeWindowBump r hr (invTimeScale t * (timeCoordCLM x - t))) :=
    (contDiff_timeWindowBump r hr).comp
      (contDiff_const.mul (timeCoordCLM.contDiff.sub contDiff_const))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin 1 → Fin 4 → ℝ =>
      velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM x)) :=
    (contDiff_velSetCutoff hm f r hr).comp
      (ContDiff.const_smul (signedInvScale t) spatialCoordCLM.contDiff)
  exact h1.mul h2

lemma tsupport_velocityConeCutoff_bounds {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) {x : Fin 1 → Fin 4 → ℝ}
    (hx : x ∈ tsupport (velocityConeCutoff m hm f r hr t)) :
    |invTimeScale t * (x 0 0 - t)| ≤ r ∧
      ∃ v ∈ velocitySupport m f, ‖signedInvScale t • spatialPart (x 0) - v‖ ≤ 5 * r / 6 := by
  have h_sub1 : tsupport (velocityConeCutoff m hm f r hr t) ⊆
      tsupport (fun y : Fin 1 → Fin 4 → ℝ =>
        timeWindowBump r hr (invTimeScale t * (timeCoordCLM y - t))) := by
    refine closure_minimal ?_ isClosed_closure
    intro y hy
    rw [Function.mem_support] at hy
    refine subset_tsupport _ (Function.mem_support.mpr ?_)
    intro h0
    exact hy (by unfold velocityConeCutoff; rw [h0, zero_mul])
  have h_sub2 : tsupport (velocityConeCutoff m hm f r hr t) ⊆
      tsupport (fun y : Fin 1 → Fin 4 → ℝ =>
        velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM y)) := by
    refine closure_minimal ?_ isClosed_closure
    intro y hy
    rw [Function.mem_support] at hy
    refine subset_tsupport _ (Function.mem_support.mpr ?_)
    intro h0
    exact hy (by unfold velocityConeCutoff; rw [h0, mul_zero])
  have h1 : (fun y : Fin 1 → Fin 4 → ℝ => invTimeScale t * (timeCoordCLM y - t)) x ∈
      tsupport (timeWindowBump r hr) :=
    tsupport_comp_subset_preimage (timeWindowBump r hr)
      (continuous_const.mul (timeCoordCLM.continuous.sub continuous_const)) (h_sub1 hx)
  have h2 : (fun y : Fin 1 → Fin 4 → ℝ => signedInvScale t • spatialCoordCLM y) x ∈
      tsupport (velSetCutoff m f (hm := hm) r hr) :=
    tsupport_comp_subset_preimage (velSetCutoff m f (hm := hm) r hr)
      (spatialCoordCLM.continuous.const_smul (signedInvScale t)) (h_sub2 hx)
  exact ⟨tsupport_timeWindowBump_subset r hr h1, tsupport_velSetCutoff_subset hm f r hr h2⟩

lemma hasCompactSupport_velocityConeCutoff {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    HasCompactSupport (velocityConeCutoff m hm f r hr t) := by
  let R_c : ℝ := max (|t| + r * max |t| 1) (max |t| 1 * (1 + r))
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Fin 1 → Fin 4 → ℝ) R_c) fun x hx => ?_
  obtain ⟨ht_bd, v, hv, hv_bd⟩ :=
    tsupport_velocityConeCutoff_bounds hm f r hr t (subset_tsupport _ hx)
  have h_max_pos : 0 < max |t| 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hx0_bd : |x 0 0| ≤ |t| + r * max |t| 1 := by
    have hinv : invTimeScale t * |x 0 0 - t| ≤ r := by
      rwa [invTimeScale, abs_mul, abs_inv, abs_of_pos h_max_pos] at ht_bd
    have hdiff : |x 0 0 - t| ≤ r * max |t| 1 := by
      have hm1 := mul_le_mul_of_nonneg_left hinv h_max_pos.le
      dsimp only [invTimeScale] at hm1
      rw [← mul_assoc, mul_inv_cancel₀ h_max_pos.ne', one_mul] at hm1
      linarith
    have htri : |x 0 0| ≤ |x 0 0 - t| + |t| := by
      simpa using abs_add_le (x 0 0 - t) t
    linarith
  have hxsp_bd : ‖spatialPart (x 0)‖ ≤ max |t| 1 * (1 + r) := by
    obtain ⟨vmax, _, hvmax_lt, hv_norm⟩ := exists_velocitySupport_norm_bound hm f
    have hv_le : ‖v‖ ≤ 1 := (hv_norm v hv).trans hvmax_lt.le
    have h_sv : ‖signedInvScale t • spatialPart (x 0)‖ ≤ 1 + r := by
      calc ‖signedInvScale t • spatialPart (x 0)‖
          = ‖(signedInvScale t • spatialPart (x 0) - v) + v‖ := by congr 1; abel
        _ ≤ ‖signedInvScale t • spatialPart (x 0) - v‖ + ‖v‖ := norm_add_le _ _
        _ ≤ 5 * r / 6 + 1 := add_le_add hv_bd hv_le
        _ ≤ 1 + r := by linarith
    have hs_nz := signedInvScale_ne_zero t
    have h_eq : spatialPart (x 0) =
        (signedInvScale t)⁻¹ • (signedInvScale t • spatialPart (x 0)) := by
      rw [smul_smul, inv_mul_cancel₀ hs_nz, one_smul]
    rw [h_eq, norm_smul, Real.norm_eq_abs]
    have h_inv_le : |(signedInvScale t)⁻¹| ≤ max |t| 1 := by
      unfold signedInvScale
      split_ifs with ht
      · simp
      · simp only [inv_inv, le_max_left]
    exact mul_le_mul h_inv_le h_sv (norm_nonneg _) h_max_pos.le
  rw [Metric.mem_closedBall, dist_zero_right,
    pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ R_c)]
  intro i
  rw [Subsingleton.elim i 0, pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ R_c)]
  intro μ
  fin_cases μ
  · exact (Real.norm_eq_abs (x 0 0)).symm ▸ hx0_bd.trans (le_max_left _ _)
  · exact (norm_le_pi_norm (spatialPart (x 0)) 0).trans (hxsp_bd.trans (le_max_right _ _))
  · exact (norm_le_pi_norm (spatialPart (x 0)) 1).trans (hxsp_bd.trans (le_max_right _ _))
  · exact (norm_le_pi_norm (spatialPart (x 0)) 2).trans (hxsp_bd.trans (le_max_right _ _))

lemma tsupport_velocityConeCutoff_large_time {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) {t : ℝ} (ht : 1 ≤ |t|) {x : Fin 1 → Fin 4 → ℝ}
    (hx : x ∈ tsupport (velocityConeCutoff m hm f r hr t)) :
    |x 0 0 - t| ≤ r * |t| ∧
      ∃ v ∈ velocitySupport m f, ‖spatialPart (x 0) - t • v‖ ≤ r * |t| := by
  obtain ⟨ht_bd, v, hv, hv_bd⟩ := tsupport_velocityConeCutoff_bounds hm f r hr t hx
  have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have hmax_eq : max |t| 1 = |t| := max_eq_left ht
  have ht1 : |x 0 0 - t| ≤ r * |t| := by
    rw [invTimeScale, hmax_eq, abs_mul, abs_inv, abs_of_pos ht_pos] at ht_bd
    have h1 := mul_le_mul_of_nonneg_left ht_bd ht_pos.le
    rw [← mul_assoc, mul_inv_cancel₀ ht_pos.ne', one_mul] at h1
    linarith
  have hs_eq : signedInvScale t = t⁻¹ := if_neg (not_lt.mpr ht)
  have ht_nz : t ≠ 0 := abs_pos.mp ht_pos
  have hsp : ‖spatialPart (x 0) - t • v‖ ≤ r * |t| := by
    have h_id : spatialPart (x 0) - t • v = t • (signedInvScale t • spatialPart (x 0) - v) := by
      rw [smul_sub, smul_smul, hs_eq, mul_inv_cancel₀ ht_nz, one_smul]
    rw [h_id, norm_smul, Real.norm_eq_abs]
    have h2 := mul_le_mul_of_nonneg_left hv_bd ht_pos.le
    calc |t| * ‖signedInvScale t • spatialPart (x 0) - v‖ ≤ |t| * (5 * r / 6) := h2
      _ ≤ r * |t| := by nlinarith [ht_pos]
  exact ⟨ht1, v, hv, hsp⟩

lemma velocityConeCutoff_eventually_one_interior {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) {t : ℝ} (ht : 1 ≤ |t|) {x : Fin 1 → Fin 4 → ℝ}
    (hxt : |x 0 0 - t| < (r / 4) * |t|)
    (hxsp : ∃ v ∈ velocitySupport m f, ‖spatialPart (x 0) - t • v‖ < (r / 4) * |t|) :
    velocityConeCutoff m hm f r hr t =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  rcases hxsp with ⟨v, hv, hxv⟩
  have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have ht_nz : t ≠ 0 := abs_pos.mp ht_pos
  have hs_eq : signedInvScale t = t⁻¹ := if_neg (not_lt.mpr ht)
  have hmax_eq : max |t| 1 = |t| := max_eq_left ht
  let U1 : Set (Fin 1 → Fin 4 → ℝ) :=
    { y : Fin 1 → Fin 4 → ℝ | |invTimeScale t * (timeCoordCLM y - t)| < r / 2 }
  let U2 : Set (Fin 1 → Fin 4 → ℝ) :=
    { y : Fin 1 → Fin 4 → ℝ | ‖signedInvScale t • spatialCoordCLM y - v‖ < r / 2 }
  have hf1_open : IsOpen U1 := isOpen_lt
    (continuous_abs.comp (continuous_const.mul (timeCoordCLM.continuous.sub continuous_const)))
    continuous_const
  have hf2_open : IsOpen U2 := isOpen_lt
    (continuous_norm.comp
      ((spatialCoordCLM.continuous.const_smul (signedInvScale t)).sub continuous_const))
    continuous_const
  have hx1 : x ∈ U1 := by
    simp only [U1, Set.mem_setOf_eq, timeCoordCLM_apply, invTimeScale, hmax_eq, abs_mul, abs_inv,
      abs_of_pos ht_pos]
    calc |t|⁻¹ * |x 0 0 - t| < |t|⁻¹ * ((r / 4) * |t|) :=
          mul_lt_mul_of_pos_left hxt (inv_pos.mpr ht_pos)
      _ = r / 4 := by field_simp [ht_pos.ne']
      _ < r / 2 := by linarith
  have hx2 : x ∈ U2 := by
    simp only [U2, Set.mem_setOf_eq, spatialCoordCLM_apply]
    have h_id : signedInvScale t • spatialPart (x 0) - v =
        t⁻¹ • (spatialPart (x 0) - t • v) := by
      rw [smul_sub, hs_eq, smul_smul, inv_mul_cancel₀ ht_nz, one_smul]
    rw [h_id, norm_smul, Real.norm_eq_abs, abs_inv]
    calc |t|⁻¹ * ‖spatialPart (x 0) - t • v‖ < |t|⁻¹ * ((r / 4) * |t|) :=
          mul_lt_mul_of_pos_left hxv (inv_pos.mpr ht_pos)
      _ = r / 4 := by field_simp [ht_pos.ne']
      _ < r / 2 := by linarith
  filter_upwards [hf1_open.mem_nhds hx1, hf2_open.mem_nhds hx2] with y hy1 hy2
  unfold velocityConeCutoff
  rw [timeWindowBump_eq_one_of_le r hr hy1.le, velSetCutoff_eq_one_of_dist hm f r hr hv hy2.le,
    mul_one]

lemma exists_uniform_velocityConeCutoff_deriv_bound {m : ℝ} (hm : 0 < m)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (j : ℕ) :
    ∃ B_j : ℝ, 0 ≤ B_j ∧ ∀ (t : ℝ) (x : Fin 1 → Fin 4 → ℝ),
      ‖iteratedFDeriv ℝ j (fun y : Fin 1 → Fin 4 → ℝ =>
        (velocityConeCutoff m hm f r hr t y : ℂ)) x‖ ≤ B_j := by
  have h1_bd : ∀ i : ℕ, ∃ A_i : ℝ, 0 ≤ A_i ∧ ∀ (t : ℝ) (x : Fin 1 → Fin 4 → ℝ),
      ‖iteratedFDeriv ℝ i (fun y : Fin 1 → Fin 4 → ℝ =>
        timeWindowBump r hr (invTimeScale t * (timeCoordCLM y - t))) x‖ ≤ A_i := by
    intro i
    obtain ⟨A_i, hAi_nn, hAi⟩ := exists_uniform_affine_comp_deriv_bound
      (contDiff_timeWindowBump r hr) (hasCompactSupport_timeWindowBump r hr)
      timeCoordCLM norm_timeCoordCLM_le_one i
    refine ⟨A_i, hAi_nn, fun t x => ?_⟩
    have h_abs : |invTimeScale t| ≤ 1 := by
      rw [abs_of_pos (invTimeScale_pos t)]
      exact invTimeScale_le_one t
    have h_eq : (fun y : Fin 1 → Fin 4 → ℝ =>
          timeWindowBump r hr (invTimeScale t * (timeCoordCLM y - t))) =
        fun y => timeWindowBump r hr
          ((invTimeScale t • timeCoordCLM) y + -(invTimeScale t * t)) := by
      ext y
      simp only [_root_.smul_apply, smul_eq_mul]
      ring_nf
    rw [h_eq]
    exact hAi (invTimeScale t) (-(invTimeScale t * t)) x h_abs
  have h2_bd : ∀ i : ℕ, ∃ C_i : ℝ, 0 ≤ C_i ∧ ∀ (t : ℝ) (x : Fin 1 → Fin 4 → ℝ),
      ‖iteratedFDeriv ℝ i (fun y : Fin 1 → Fin 4 → ℝ =>
        velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM y)) x‖ ≤ C_i := by
    intro i
    obtain ⟨C_i, hCi_nn, hCi⟩ := exists_uniform_affine_comp_deriv_bound
      (contDiff_velSetCutoff hm f r hr) (hasCompactSupport_velSetCutoff hm f r hr)
      spatialCoordCLM norm_spatialCoordCLM_le_one i
    refine ⟨C_i, hCi_nn, fun t x => ?_⟩
    have h_eq : (fun y : Fin 1 → Fin 4 → ℝ =>
          velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM y)) =
        fun y => velSetCutoff m f (hm := hm) r hr ((signedInvScale t • spatialCoordCLM) y + 0) := by
      ext y
      simp
    rw [h_eq]
    exact hCi (signedInvScale t) 0 x (abs_signedInvScale_le_one t)
  choose A hA_nn hA_le using h1_bd
  choose C hC_nn hC_le using h2_bd
  let B_j : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A i * C (j - i)
  have hBj_nn : 0 ≤ B_j := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA_nn i)) (hC_nn (j - i))
  refine ⟨B_j, hBj_nn, fun t x => ?_⟩
  have h1_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin 1 → Fin 4 → ℝ =>
      timeWindowBump r hr (invTimeScale t * (timeCoordCLM y - t))) :=
    (contDiff_timeWindowBump r hr).comp
      (contDiff_const.mul (timeCoordCLM.contDiff.sub contDiff_const))
  have h2_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin 1 → Fin 4 → ℝ =>
      velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM y)) :=
    (contDiff_velSetCutoff hm f r hr).comp
      (ContDiff.const_smul (signedInvScale t) spatialCoordCLM.contDiff)
  have h_re : ‖iteratedFDeriv ℝ j (velocityConeCutoff m hm f r hr t) x‖ ≤ B_j := by
    have h_un : velocityConeCutoff m hm f r hr t = fun y =>
        timeWindowBump r hr (invTimeScale t * (timeCoordCLM y - t)) *
          velSetCutoff m f (hm := hm) r hr (signedInvScale t • spatialCoordCLM y) := rfl
    rw [h_un]
    refine (norm_iteratedFDeriv_mul_le h1_cd h2_cd x (natCast_le_top_enat_coe j)).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hA_le i t x) (Nat.cast_nonneg _))
      (hC_le (j - i) t x) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA_nn i))
  have h_ofReal := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
    ((contDiff_velocityConeCutoff hm f r hr t).of_le (natCast_le_top_enat_coe j)).contDiffAt
    le_rfl (x := x)
  have h_clm_le : ‖Complex.ofRealCLM‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by simp [Complex.norm_real]
  calc ‖iteratedFDeriv ℝ j (fun y : Fin 1 → Fin 4 → ℝ =>
          (velocityConeCutoff m hm f r hr t y : ℂ)) x‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (velocityConeCutoff m hm f r hr t) x‖ :=
        h_ofReal
    _ ≤ 1 * B_j := mul_le_mul h_clm_le h_re (norm_nonneg _) zero_le_one
    _ = B_j := one_mul _

lemma norm_mulBounded_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : E → ℂ} (hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ)
    (B : ℕ → ℝ) (hB_nn : ∀ j, 0 ≤ B j) (hB_bd : ∀ j (x : E), ‖iteratedFDeriv ℝ j χ x‖ ≤ B j)
    (g : SchwartzMap E ℂ) (l k : ℕ) (x : E) :
    ‖x‖ ^ l * ‖iteratedFDeriv ℝ k (fun y : E => χ y * g y) x‖ ≤
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * SchwartzMap.seminorm ℝ l (k - j) g := by
  have hm := norm_iteratedFDeriv_mul_le (hχ_cd.of_le (natCast_le_top_enat_coe k))
    ((g.smooth (⊤ : ℕ∞)).of_le (natCast_le_top_enat_coe k)) x le_rfl
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ k (fun y : E => χ y * g y) x‖
      ≤ ‖x‖ ^ l * ∑ j ∈ Finset.range (k + 1),
          (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j χ x‖ *
            ‖iteratedFDeriv ℝ (k - j) (g : E → ℂ) x‖ :=
        mul_le_mul_of_nonneg_left hm (pow_nonneg (norm_nonneg _) l)
    _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j χ x‖ *
          (‖x‖ ^ l * ‖iteratedFDeriv ℝ (k - j) (g : E → ℂ) x‖) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j *
          SchwartzMap.seminorm ℝ l (k - j) g := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := mul_le_mul_of_nonneg_left (hB_bd j x) (Nat.cast_nonneg (k.choose j))
        have h2 := g.le_seminorm ℝ l (k - j) x
        exact mul_le_mul h1 h2 (mul_nonneg (pow_nonneg (norm_nonneg _) l) (norm_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (hB_nn j))

def mulBoundedCutoffSchwartz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℂ) (hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ)
    (B : ℕ → ℝ) (hB_nn : ∀ j, 0 ≤ B j) (hB_bd : ∀ j (x : E), ‖iteratedFDeriv ℝ j χ x‖ ≤ B j)
    (g : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun x := χ x * g x
  smooth' := hχ_cd.mul (g.smooth (⊤ : ℕ∞))
  decay' l k :=
    ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * SchwartzMap.seminorm ℝ l (k - j) g,
      fun x => norm_mulBounded_le hχ_cd B hB_nn hB_bd g l k x⟩

@[simp]
lemma mulBoundedCutoffSchwartz_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℂ) (hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ)
    (B : ℕ → ℝ) (hB_nn : ∀ j, 0 ≤ B j) (hB_bd : ∀ j (x : E), ‖iteratedFDeriv ℝ j χ x‖ ≤ B j)
    (g : SchwartzMap E ℂ) (x : E) :
    mulBoundedCutoffSchwartz χ hχ_cd B hB_nn hB_bd g x = χ x * g x := rfl

lemma seminorm_mulBoundedCutoffSchwartz_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : E → ℂ) (hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ)
    (B : ℕ → ℝ) (hB_nn : ∀ j, 0 ≤ B j) (hB_bd : ∀ j (x : E), ‖iteratedFDeriv ℝ j χ x‖ ≤ B j)
    (g : SchwartzMap E ℂ) (l k : ℕ) :
    SchwartzMap.seminorm ℝ l k (mulBoundedCutoffSchwartz χ hχ_cd B hB_nn hB_bd g) ≤
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * SchwartzMap.seminorm ℝ l (k - j) g := by
  refine SchwartzMap.seminorm_le_bound ℝ l k _ ?_ fun x =>
    norm_mulBounded_le hχ_cd B hB_nn hB_bd g l k x
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB_nn j)) (apply_nonneg _ _)

def coneDerivBoundFn (m : ℝ) (hm : 0 < m) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r)
    (j : ℕ) : ℝ :=
  (exists_uniform_velocityConeCutoff_deriv_bound hm f r hr j).choose

lemma coneDerivBoundFn_nonneg {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (j : ℕ) : 0 ≤ coneDerivBoundFn m hm f r hr j :=
  (exists_uniform_velocityConeCutoff_deriv_bound hm f r hr j).choose_spec.1

lemma coneDerivBoundFn_spec {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (j : ℕ) (t : ℝ) (x : Fin 1 → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : Fin 1 → Fin 4 → ℝ =>
      (velocityConeCutoff m hm f r hr t y : ℂ)) x‖ ≤ coneDerivBoundFn m hm f r hr j :=
  (exists_uniform_velocityConeCutoff_deriv_bound hm f r hr j).choose_spec.2 t x

def timeModCoreTestFn (m : ℝ) (hm : 0 < m) (f : SmoothWavepacket)
    (u : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  mulBoundedCutoffSchwartz
    (fun y => (velocityConeCutoff m hm f r hr t y : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_velocityConeCutoff hm f r hr t))
    (coneDerivBoundFn m hm f r hr)
    (coneDerivBoundFn_nonneg hm f r hr)
    (fun j x => coneDerivBoundFn_spec hm f r hr j t x)
    (timeModTestFn m hm u h_sm h_supp t)

def timeModTailTestFn (m : ℝ) (hm : 0 < m) (f : SmoothWavepacket)
    (u : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModTestFn m hm u h_sm h_supp t - timeModCoreTestFn m hm f u h_sm h_supp r hr t

def haagRuelleCoreTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModCoreTestFn m hm f (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) r hr t

def haagRuelleTailTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModTailTestFn m hm f (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) r hr t

def haagRuelleDerivCoreTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModCoreTestFn m hm f (haagRuelleDerivBaseAmp m M hm hM f)
    (contDiff_haagRuelleDerivBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleDerivBaseAmp m M hm hM f) r hr t

def haagRuelleDerivTailTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket)
    (r : ℝ) (hr : 0 < r) (t : ℝ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  timeModTailTestFn m hm f (haagRuelleDerivBaseAmp m M hm hM f)
    (contDiff_haagRuelleDerivBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleDerivBaseAmp m M hm hM f) r hr t

lemma haagRuelleTestFn_eq_core_add_tail (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    haagRuelleTestFn m M hm hM f t =
      haagRuelleCoreTestFn m M hm hM f r hr t +
        haagRuelleTailTestFn m M hm hM f r hr t := by
  unfold haagRuelleTailTestFn timeModTailTestFn haagRuelleCoreTestFn haagRuelleTestFn
  abel

lemma haagRuelleDerivTestFn_eq_core_add_tail (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    haagRuelleDerivTestFn m M hm hM f t =
      haagRuelleDerivCoreTestFn m M hm hM f r hr t +
        haagRuelleDerivTailTestFn m M hm hM f r hr t := by
  unfold haagRuelleDerivTailTestFn timeModTailTestFn haagRuelleDerivCoreTestFn haagRuelleDerivTestFn
  abel

lemma tsupport_timeModCoreTestFn_subset {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (u : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    tsupport ((timeModCoreTestFn m hm f u h_sm h_supp r hr t : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
        (Fin 1 → Fin 4 → ℝ) → ℂ) ⊆
      tsupport (velocityConeCutoff m hm f r hr t) := by
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  rw [Function.mem_support] at hx
  refine subset_tsupport _ (Function.mem_support.mpr ?_)
  intro h0
  exact hx (by simp [timeModCoreTestFn, mulBoundedCutoffSchwartz_apply, h0])

lemma hasCompactSupport_timeModCoreTestFn {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket)
    (u : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    HasCompactSupport (timeModCoreTestFn m hm f u h_sm h_supp r hr t :
      (Fin 1 → Fin 4 → ℝ) → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_velocityConeCutoff hm f r hr t).isCompact ?_
  exact (subset_tsupport _).trans (tsupport_timeModCoreTestFn_subset hm f u h_sm h_supp r hr t)

lemma hasCompactSupport_haagRuelleCoreTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    HasCompactSupport (haagRuelleCoreTestFn m M hm hM f r hr t : (Fin 1 → Fin 4 → ℝ) → ℂ) :=
  hasCompactSupport_timeModCoreTestFn hm f _ _ _ r hr t

lemma hasCompactSupport_haagRuelleDerivCoreTestFn (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    HasCompactSupport (haagRuelleDerivCoreTestFn m M hm hM f r hr t :
      (Fin 1 → Fin 4 → ℝ) → ℂ) :=
  hasCompactSupport_timeModCoreTestFn hm f _ _ _ r hr t

lemma schwartzSeminorm_timeModMomSchwartz_poly_growth {m : ℝ} (hm : 0 < m)
    (base : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (h_supp : HasCompactSupport base)
    (l k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (timeModMomSchwartz m hm base h_sm h_supp t) ≤
        C * (1 + |t|) ^ k := by
  let K_p : Set (Fin 1 → Fin 4 → ℝ) := momNegArgCLE.symm '' tsupport base
  have hK_comp : IsCompact K_p := h_supp.isCompact.image momNegArgCLE.symm.continuous
  obtain ⟨R_m, hRm_sub⟩ := Metric.isBounded_iff_subset_ball (0 : Fin 1 → Fin 4 → ℝ) |>.mp
    hK_comp.isBounded
  let R : ℝ := max R_m 1
  have hR_pos : 0 < R := by positivity
  let B_m : Set (Fin 1 → Fin 4 → ℝ) := Metric.closedBall 0 R
  have hB_comp : IsCompact B_m := isCompact_closedBall 0 R
  have hB_ne : B_m.Nonempty := ⟨0, Metric.mem_closedBall_self hR_pos.le⟩
  let base_p : (Fin 1 → Fin 4 → ℝ) → ℂ := fun p => base (-(p 0))
  have hbp_cd : ContDiff ℝ (⊤ : ℕ∞) base_p := h_sm.comp momNegArgCLE.contDiff
  have h_bp_bd : ∀ j : Fin (k + 1), ∃ M_b : ℝ, 0 ≤ M_b ∧ ∀ p ∈ B_m,
      ‖iteratedFDeriv ℝ j.val base_p p‖ ≤ M_b := by
    intro j
    have hc : Continuous (iteratedFDeriv ℝ j.val base_p) :=
      hbp_cd.continuous_iteratedFDeriv (natCast_le_top_enat_coe j.val)
    obtain ⟨p₀, _, hp₀⟩ := hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn
    exact ⟨‖iteratedFDeriv ℝ j.val base_p p₀‖, norm_nonneg _, fun p hp => hp₀ hp⟩
  choose M_b hMb_nn hMb_le using h_bp_bd
  let M_b_all : ℝ := ∑ j : Fin (k + 1), M_b j
  have hMb_all_nn : 0 ≤ M_b_all := Finset.sum_nonneg fun j _ => hMb_nn j
  let a_fn : (Fin 1 → Fin 4 → ℝ) → ℝ := fun p => -p 0 0 - massShellEnergy m (spatialPart (-p 0))
  have ha_cd : ContDiff ℝ (⊤ : ℕ∞) a_fn := by
    have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => -p 0 0) :=
      (-((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) 0).comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin 1 => Fin 4 → ℝ) 0))).contDiff
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => spatialPart (-p 0)) :=
      contDiff_spatialPart.comp momNegArgCLE.contDiff
    exact h0.sub ((contDiff_massShellEnergy hm).comp h1)
  have h_Da : ∃ D : ℝ, 1 ≤ D ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k →
      ∀ p ∈ B_m, ‖iteratedFDeriv ℝ i a_fn p‖ ≤ D ^ i := by
    have h_each : ∀ i : Fin (k + 1), ∃ D_i : ℝ, 0 ≤ D_i ∧
        ∀ p ∈ B_m, ‖iteratedFDeriv ℝ i.val a_fn p‖ ≤ D_i := by
      intro i
      have hc : Continuous (iteratedFDeriv ℝ i.val a_fn) :=
        ha_cd.continuous_iteratedFDeriv (natCast_le_top_enat_coe i.val)
      obtain ⟨p₀, _, hp₀⟩ := hB_comp.exists_isMaxOn hB_ne (continuous_norm.comp hc).continuousOn
      exact ⟨‖iteratedFDeriv ℝ i.val a_fn p₀‖, norm_nonneg _, fun p hp => hp₀ hp⟩
    choose D_fn hD_nn hD_spec using h_each
    let D : ℝ := 1 + ∑ i : Fin (k + 1), D_fn i
    have hD1 : 1 ≤ D := by
      have : 0 ≤ ∑ i : Fin (k + 1), D_fn i := Finset.sum_nonneg fun i _ => hD_nn i
      dsimp [D]
      linarith
    refine ⟨D, hD1, fun i hi1 hik p hp => ?_⟩
    have hi_lt : i < k + 1 := Nat.lt_succ_of_le hik
    have h_term : D_fn ⟨i, hi_lt⟩ ≤ D := by
      have h_le := Finset.single_le_sum (fun j _ => hD_nn j)
        (Finset.mem_univ (⟨i, hi_lt⟩ : Fin (k + 1)))
      dsimp [D]
      linarith
    have h_pow : D ≤ D ^ i := by
      calc D = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ i := pow_le_pow_right₀ hD1 hi1
    exact (hD_spec ⟨i, hi_lt⟩ p hp).trans (h_term.trans h_pow)
  obtain ⟨D, hD1, hD_le⟩ := h_Da
  let C_e : ℝ := (Nat.factorial k : ℝ) * D ^ k
  have hCe_nn : 0 ≤ C_e := by positivity
  let C : ℝ := R ^ l * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M_b_all * C_e
  have hC_nn : 0 ≤ C := by
    have : 0 ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * M_b_all * C_e :=
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hMb_all_nn) hCe_nn
    exact mul_nonneg (pow_nonneg hR_pos.le l) this
  refine ⟨C, hC_nn, fun t => ?_⟩
  refine SchwartzMap.seminorm_le_bound ℝ l k _
    (mul_nonneg hC_nn (pow_nonneg (by positivity) k)) fun p => ?_
  by_cases hp_in : ‖p‖ ≤ R
  · have hpB : p ∈ B_m := by simpa [B_m, Metric.mem_closedBall, dist_zero_right] using hp_in
    let g_t : ℝ → ℂ := fun u => Complex.exp ((u : ℂ) * (Complex.I * (t : ℂ)))
    have hg_cd : ContDiff ℝ (⊤ : ℕ∞) g_t :=
      Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
    have h_mom_eq : (timeModMomSchwartz m hm base h_sm h_supp t :
          (Fin 1 → Fin 4 → ℝ) → ℂ) = fun q => base_p q * (g_t ∘ a_fn) q := by
      ext q
      simp only [timeModMomSchwartz_apply, timeModMomAmp, base_p, Function.comp_def, g_t, a_fn]
      congr 2
      have h0_eq : (-q 0) 0 = -(q 0 0) := rfl
      rw [h0_eq]
      push_cast
      ring
    rw [h_mom_eq]
    have h_mul := norm_iteratedFDeriv_mul_le hbp_cd (hg_cd.comp ha_cd) p (natCast_le_top_enat_coe k)
    have h_exp_bd : ∀ j ≤ k, ‖iteratedFDeriv ℝ j (g_t ∘ a_fn) p‖ ≤ C_e * (1 + |t|) ^ k := by
      intro j hjk
      have hc_gt : ‖iteratedFDeriv ℝ j (g_t ∘ a_fn) p‖ ≤
          (Nat.factorial j : ℝ) * (1 + |t|) ^ j * D ^ j := by
        refine norm_iteratedFDeriv_comp_le hg_cd ha_cd (natCast_le_top_enat_coe j) p ?_ ?_
        · intro i hij
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
          have h_id : g_t = fun u : ℝ =>
              (1 : ℂ) * Complex.exp ((u : ℂ) * (Complex.I * (t : ℂ))) := by
            ext u; rw [one_mul]
          rw [h_id, iteratedDeriv_const_mul_exp_mul]
          have h_norm_e : ‖Complex.exp ((a_fn p : ℂ) * (Complex.I * (t : ℂ)))‖ = 1 := by
            have heq : (a_fn p : ℂ) * (Complex.I * (t : ℂ)) =
                (((a_fn p * t : ℝ) : ℂ)) * Complex.I := by
              push_cast; ring
            rw [heq, Complex.norm_exp_ofReal_mul_I]
          rw [norm_mul, one_mul, norm_pow, h_norm_e, mul_one, norm_mul, Complex.norm_I, one_mul,
            Complex.norm_real, Real.norm_eq_abs]
          have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
          calc |t| ^ i ≤ (1 + |t|) ^ i := pow_le_pow_left₀ (abs_nonneg t) (by linarith) i
            _ ≤ (1 + |t|) ^ j := pow_le_pow_right₀ ht1 hij
        · intro i hi1 hij
          exact hD_le i hi1 (hij.trans hjk) p hpB
      refine hc_gt.trans ?_
      have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
      have h_fac : (Nat.factorial j : ℝ) ≤ (Nat.factorial k : ℝ) :=
        Nat.cast_le.mpr (Nat.factorial_le hjk)
      have h_pow_D : D ^ j ≤ D ^ k := pow_le_pow_right₀ hD1 hjk
      have h_pow_t : (1 + |t|) ^ j ≤ (1 + |t|) ^ k := pow_le_pow_right₀ ht1 hjk
      calc (Nat.factorial j : ℝ) * (1 + |t|) ^ j * D ^ j
          = ((Nat.factorial j : ℝ) * D ^ j) * (1 + |t|) ^ j := by ring
        _ ≤ ((Nat.factorial k : ℝ) * D ^ k) * (1 + |t|) ^ k :=
            mul_le_mul (mul_le_mul h_fac h_pow_D (by positivity) (Nat.cast_nonneg _))
              h_pow_t (by positivity) (by positivity)
        _ = C_e * (1 + |t|) ^ k := rfl
    have hp_pow : ‖p‖ ^ l ≤ R ^ l := pow_le_pow_left₀ (norm_nonneg _) hp_in l
    calc ‖p‖ ^ l * ‖iteratedFDeriv ℝ k (fun q => base_p q * (g_t ∘ a_fn) q) p‖
        ≤ R ^ l * ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j base_p p‖ *
              ‖iteratedFDeriv ℝ (k - j) (g_t ∘ a_fn) p‖ :=
          mul_le_mul hp_pow h_mul (norm_nonneg _) (pow_nonneg hR_pos.le l)
      _ ≤ R ^ l * ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * M_b_all * (C_e * (1 + |t|) ^ k) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_)
            (pow_nonneg hR_pos.le l)
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have hb_le : ‖iteratedFDeriv ℝ j base_p p‖ ≤ M_b_all := by
            refine (hMb_le ⟨j, Nat.lt_succ_of_le hjk⟩ p hpB).trans ?_
            exact Finset.single_le_sum (fun (j' : Fin (k + 1)) _ => hMb_nn j')
              (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hjk⟩ : Fin (k + 1)))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb_le (Nat.cast_nonneg _))
            (h_exp_bd (k - j) (Nat.sub_le k j)) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) hMb_all_nn)
      _ = C * (1 + |t|) ^ k := by
          dsimp [C]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
  · have hp_gt : R < ‖p‖ := lt_of_not_ge hp_in
    have h_ev0 : (timeModMomSchwartz m hm base h_sm h_supp t :
        (Fin 1 → Fin 4 → ℝ) → ℂ) =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hp_gt] with q hq
      have hq_not : -(q 0) ∉ tsupport base := by
        intro hmem
        have hqK : q ∈ K_p := ⟨-(q 0), hmem, by
          ext i ν
          rw [Subsingleton.elim i 0]
          change -(-(q 0) ν) = q 0 ν
          ring⟩
        have hq_lt := hRm_sub hqK
        rw [Metric.mem_ball, dist_zero_right] at hq_lt
        have : R_m ≤ R := le_max_left _ _
        linarith
      simp only [timeModMomSchwartz_apply, timeModMomAmp,
        image_eq_zero_of_notMem_tsupport hq_not, zero_mul]
    have h_id0 : iteratedFDeriv ℝ k
        (timeModMomSchwartz m hm base h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) p = 0 := by
      rw [(h_ev0.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
      simp
    rw [h_id0, norm_zero, mul_zero]
    exact mul_nonneg hC_nn (pow_nonneg (by positivity) k)

lemma schwartzSeminorm_timeModTestFn_poly_growth {m : ℝ} (hm : 0 < m)
    (base : (Fin 4 → ℝ) → ℂ) (h_sm : ContDiff ℝ (⊤ : ℕ∞) base) (h_supp : HasCompactSupport base)
    (l k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (timeModTestFn m hm base h_sm h_supp t) ≤ C * (1 + |t|) ^ K := by
  have h_with := schwartz_withSeminorms ℝ (Fin 1 → Fin 4 → ℝ) ℂ
  let T_real := (invMinkowskiFourierCLM 1).toLinearMap.restrictScalars ℝ
  let q_sem : Seminorm ℝ (SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :=
    (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ (l, k)).comp T_real
  have hq_cont : Continuous q_sem :=
    (h_with.continuous_seminorm (l, k)).comp (invMinkowskiFourierCLM 1).continuous
  obtain ⟨s, C₀, _, hq_le⟩ := Seminorm.bound_of_continuous h_with q_sem hq_cont
  have h_mom : ∀ p : ℕ × ℕ, ∃ C_p : ℝ, 0 ≤ C_p ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ p.1 p.2 (timeModMomSchwartz m hm base h_sm h_supp t) ≤
        C_p * (1 + |t|) ^ p.2 := fun p =>
    schwartzSeminorm_timeModMomSchwartz_poly_growth hm base h_sm h_supp p.1 p.2
  choose C_p hCp_nn hCp_bd using h_mom
  let K : ℕ := s.sup Prod.snd
  let C_sup : ℝ := ∑ p ∈ s, C_p p
  have hCsup_nn : 0 ≤ C_sup := Finset.sum_nonneg fun p _ => hCp_nn p
  refine ⟨(C₀ : ℝ) * C_sup, K, mul_nonneg (NNReal.coe_nonneg _) hCsup_nn, fun t => ?_⟩
  have h_eval : SchwartzMap.seminorm ℝ l k (timeModTestFn m hm base h_sm h_supp t) ≤
      (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ))
        (timeModMomSchwartz m hm base h_sm h_supp t) := by
    have h_le := hq_le (timeModMomSchwartz m hm base h_sm h_supp t)
    exact le_trans h_le (le_of_eq (NNReal.smul_def _ _))
  have h_sup_le : (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ))
      (timeModMomSchwartz m hm base h_sm h_supp t) ≤ C_sup * (1 + |t|) ^ K := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg hCsup_nn (pow_nonneg (by positivity) K))
      fun p hp => ?_
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    have hpK : p.2 ≤ K := Finset.le_sup hp
    have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hCp_sum : C_p p ≤ C_sup := Finset.single_le_sum (fun p' _ => hCp_nn p') hp
    exact (hCp_bd p t).trans
      (mul_le_mul hCp_sum (pow_le_pow_right₀ ht1 hpK) (pow_nonneg (by positivity) _) hCsup_nn)
  calc SchwartzMap.seminorm ℝ l k (timeModTestFn m hm base h_sm h_supp t)
      ≤ (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ))
          (timeModMomSchwartz m hm base h_sm h_supp t) := h_eval
    _ ≤ (C₀ : ℝ) * (C_sup * (1 + |t|) ^ K) :=
        mul_le_mul_of_nonneg_left h_sup_le (NNReal.coe_nonneg _)
    _ = ((C₀ : ℝ) * C_sup) * (1 + |t|) ^ K := by ring

lemma schwartzSeminorm_timeModCoreTestFn_poly_growth {m : ℝ} (hm : 0 < m)
    (f : SmoothWavepacket) (u : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    (r : ℝ) (hr : 0 < r) (l k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (timeModCoreTestFn m hm f u h_sm h_supp r hr t) ≤
        C * (1 + |t|) ^ K := by
  have h_full : ∀ j : Fin (k + 1), ∃ (C_j : ℝ) (K_j : ℕ), 0 ≤ C_j ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l (k - j.val) (timeModTestFn m hm u h_sm h_supp t) ≤
        C_j * (1 + |t|) ^ K_j := fun j =>
    schwartzSeminorm_timeModTestFn_poly_growth hm u h_sm h_supp l (k - j.val)
  choose C_j K_j hCj_nn hCj_bd using h_full
  let K : ℕ := Finset.univ.sup K_j
  let C : ℝ := ∑ j : Fin (k + 1),
    (k.choose j.val : ℝ) * coneDerivBoundFn m hm f r hr j.val * C_j j
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (coneDerivBoundFn_nonneg hm f r hr j.val))
      (hCj_nn j)
  refine ⟨C, K, hC_nn, fun t => ?_⟩
  have h_mul := seminorm_mulBoundedCutoffSchwartz_le
    (fun y => (velocityConeCutoff m hm f r hr t y : ℂ))
    (Complex.ofRealCLM.contDiff.comp (contDiff_velocityConeCutoff hm f r hr t))
    (coneDerivBoundFn m hm f r hr)
    (coneDerivBoundFn_nonneg hm f r hr)
    (fun j x => coneDerivBoundFn_spec hm f r hr j t x)
    (timeModTestFn m hm u h_sm h_supp t) l k
  refine h_mul.trans ?_
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * coneDerivBoundFn m hm f r hr j *
          SchwartzMap.seminorm ℝ l (k - j) (timeModTestFn m hm u h_sm h_supp t))
      = ∑ j : Fin (k + 1), (k.choose j.val : ℝ) * coneDerivBoundFn m hm f r hr j.val *
          SchwartzMap.seminorm ℝ l (k - j.val) (timeModTestFn m hm u h_sm h_supp t) := by
          rw [← Fin.sum_univ_eq_sum_range]
    _ ≤ ∑ j : Fin (k + 1),
          ((k.choose j.val : ℝ) * coneDerivBoundFn m hm f r hr j.val * C_j j) *
            (1 + |t|) ^ K := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hjK : K_j j ≤ K := Finset.le_sup (Finset.mem_univ j)
          have hbd := (hCj_bd j t).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 hjK) (hCj_nn j))
          calc (k.choose j.val : ℝ) * coneDerivBoundFn m hm f r hr j.val *
                SchwartzMap.seminorm ℝ l (k - j.val) (timeModTestFn m hm u h_sm h_supp t)
              ≤ (k.choose j.val : ℝ) * coneDerivBoundFn m hm f r hr j.val *
                  (C_j j * (1 + |t|) ^ K) :=
                mul_le_mul_of_nonneg_left hbd
                  (mul_nonneg (Nat.cast_nonneg _) (coneDerivBoundFn_nonneg hm f r hr j.val))
            _ = _ := by ring
    _ = C * (1 + |t|) ^ K := by rw [← Finset.sum_mul]

lemma schwartzSeminorm_haagRuelleTestFn_poly_growth (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (l k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (haagRuelleTestFn m M hm hM f t) ≤ C * (1 + |t|) ^ K :=
  schwartzSeminorm_timeModTestFn_poly_growth hm (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) l k

lemma schwartzSeminorm_haagRuelleDerivTestFn_poly_growth (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (l k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (haagRuelleDerivTestFn m M hm hM f t) ≤ C * (1 + |t|) ^ K :=
  schwartzSeminorm_timeModTestFn_poly_growth hm (haagRuelleDerivBaseAmp m M hm hM f)
    (contDiff_haagRuelleDerivBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleDerivBaseAmp m M hm hM f) l k

lemma schwartzSeminorm_haagRuelleCoreTestFn_poly_growth (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (l k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (haagRuelleCoreTestFn m M hm hM f r hr t) ≤
        C * (1 + |t|) ^ K :=
  schwartzSeminorm_timeModCoreTestFn_poly_growth hm f (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f) r hr l k

lemma schwartzSeminorm_haagRuelleDerivCoreTestFn_poly_growth (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (l k : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (haagRuelleDerivCoreTestFn m M hm hM f r hr t) ≤
        C * (1 + |t|) ^ K :=
  schwartzSeminorm_timeModCoreTestFn_poly_growth hm f (haagRuelleDerivBaseAmp m M hm hM f)
    (contDiff_haagRuelleDerivBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleDerivBaseAmp m M hm hM f) r hr l k

lemma norm_le_spacetimeScale (x : Fin 1 → Fin 4 → ℝ) (t : ℝ) :
    ‖x‖ ≤ spacetimeScale (x 0) t := by
  have hs := (spacetimeScale_pos (x 0) t).le
  rw [pi_norm_le_iff_of_nonneg hs]
  intro i
  rw [Subsingleton.elim i 0, pi_norm_le_iff_of_nonneg hs]
  intro μ
  fin_cases μ
  · change ‖x 0 0‖ ≤ spacetimeScale (x 0) t
    unfold spacetimeScale
    rw [Real.norm_eq_abs]
    linarith [abs_nonneg t, norm_nonneg (spatialPart (x 0))]
  · change ‖x 0 1‖ ≤ spacetimeScale (x 0) t
    unfold spacetimeScale
    have h0 : ‖x 0 1‖ ≤ ‖spatialPart (x 0)‖ := norm_le_pi_norm (spatialPart (x 0)) 0
    linarith [abs_nonneg t, abs_nonneg (x 0 0)]
  · change ‖x 0 2‖ ≤ spacetimeScale (x 0) t
    unfold spacetimeScale
    have h1 : ‖x 0 2‖ ≤ ‖spatialPart (x 0)‖ := norm_le_pi_norm (spatialPart (x 0)) 1
    linarith [abs_nonneg t, abs_nonneg (x 0 0)]
  · change ‖x 0 3‖ ≤ spacetimeScale (x 0) t
    unfold spacetimeScale
    have h2 : ‖x 0 3‖ ≤ ‖spatialPart (x 0)‖ := norm_le_pi_norm (spatialPart (x 0)) 2
    linarith [abs_nonneg t, abs_nonneg (x 0 0)]

lemma one_add_abs_le_spacetimeScale (x : Fin 1 → Fin 4 → ℝ) (t : ℝ) :
    1 + |t| ≤ spacetimeScale (x 0) t := by
  unfold spacetimeScale
  linarith [abs_nonneg (x 0 0), norm_nonneg (spatialPart (x 0))]

lemma sum_sq_fin3_ge_pi_norm_sq (w : Fin 3 → ℝ) :
    ‖w‖ ^ 2 ≤ w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
  have h_nn : 0 ≤ w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by positivity
  have h_le : ‖w‖ ≤ Real.sqrt (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro j
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    fin_cases j
    · change w 0 ^ 2 ≤ _; linarith [sq_nonneg (w 1), sq_nonneg (w 2)]
    · change w 1 ^ 2 ≤ _; linarith [sq_nonneg (w 0), sq_nonneg (w 2)]
    · change w 2 ^ 2 ≤ _; linarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  calc ‖w‖ ^ 2 ≤ (Real.sqrt (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_le 2
    _ = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := Real.sq_sqrt h_nn

theorem schwartzSeminorm_timeModTailTestFn_rapid_decay {m : ℝ} (hm : 0 < m)
    (f : SmoothWavepacket) (u : (Fin 4 → ℝ) → ℂ)
    (h_sm : ContDiff ℝ (⊤ : ℕ∞) u) (h_supp : HasCompactSupport u)
    (hu_vel : ∀ q ∈ tsupport u, spatialPart q ∈ tsupport f.amp)
    (r : ℝ) (hr : 0 < r) (l k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (timeModTailTestFn m hm f u h_sm h_supp r hr t) *
        (1 + |t|) ^ N ≤ C := by
  obtain ⟨C1, K1, hC1_nn, hC1_bd⟩ :=
    schwartzSeminorm_timeModTestFn_poly_growth hm u h_sm h_supp l k
  obtain ⟨C2, K2, hC2_nn, hC2_bd⟩ :=
    schwartzSeminorm_timeModCoreTestFn_poly_growth hm f u h_sm h_supp r hr l k
  let C_small : ℝ := (C1 * 2 ^ K1 + C2 * 2 ^ K2) * 2 ^ N
  have hCsmall_nn : 0 ≤ C_small := by positivity
  obtain ⟨R₀, hR₀⟩ := Metric.isBounded_iff_subset_ball (0 : Fin 4 → ℝ) |>.mp
    h_supp.isCompact.isBounded
  let R_u : ℝ := max R₀ 1
  let B_u : Set (Fin 4 → ℝ) := Metric.closedBall 0 (R_u + 1)
  have hBu_comp : IsCompact B_u := isCompact_closedBall 0 (R_u + 1)
  have hBu_ne : B_u.Nonempty := ⟨0, Metric.mem_closedBall_self (by positivity)⟩
  let v_map : (Fin 4 → ℝ) → (Fin 3 → ℝ) := fun q => velocityVec m (spatialPart q)
  have hv_map_cd : ContDiff ℝ (⊤ : ℕ∞) v_map :=
    (contDiff_velocityVec hm).comp contDiff_spatialPart
  have hv_map_fd_cont : Continuous (fderiv ℝ v_map) :=
    (hv_map_cd.fderiv_right top_enat_coe_add_one_le).continuous
  obtain ⟨q_m, _, hq_m⟩ := hBu_comp.exists_isMaxOn hBu_ne
    (continuous_norm.comp hv_map_fd_cont).continuousOn
  let M_lip : ℝ := 1 + ‖fderiv ℝ v_map q_m‖
  have hMlip_pos : 0 < M_lip := by positivity
  have hMlip_bd : ∀ q ∈ B_u, ‖fderiv ℝ v_map q‖ ≤ M_lip := fun q hq =>
    (hq_m hq).trans (by dsimp [M_lip]; linarith)
  let δ_q : ℝ := min (1 / 2) (r / (8 * M_lip))
  have hδ_pos : 0 < δ_q := by positivity
  obtain ⟨b_K, hb_cd, _, hb_bd, hb_one, hb_tsupp⟩ :=
    exists_smoothCutoff_compact_nhd (tsupport u) h_supp.isCompact hδ_pos
  have h_vel_approx : ∀ q ∈ tsupport b_K, ∃ v ∈ velocitySupport m f,
      ‖velocityVec m (spatialPart q) - v‖ ≤ r / 8 := by
    intro q hq
    obtain ⟨q₀, hq₀_u, h_dist⟩ := hb_tsupp q hq
    have hq₀_Bu : q₀ ∈ B_u := by
      have h1 := hR₀ hq₀_u
      rw [Metric.mem_ball, dist_zero_right] at h1
      exact Metric.mem_closedBall.mpr
        (by rw [dist_zero_right]; linarith [le_max_left R₀ 1])
    have hq_Bu : q ∈ B_u := by
      have h1 := hR₀ hq₀_u
      rw [Metric.mem_ball, dist_zero_right] at h1
      rw [dist_eq_norm] at h_dist
      have hd1 : 2 * δ_q / 3 ≤ 1 / 2 := by
        have := min_le_left (1 / 2) (r / (8 * M_lip))
        linarith
      have htri : ‖q‖ ≤ ‖q - q₀‖ + ‖q₀‖ := by simpa using norm_add_le (q - q₀) q₀
      exact Metric.mem_closedBall.mpr
        (by rw [dist_zero_right]; linarith [le_max_left R₀ 1])
    have hv_lip := (convex_closedBall (0 : Fin 4 → ℝ) (R_u + 1)).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hv_map_cd.differentiable (by simp)) y) hMlip_bd hq₀_Bu hq_Bu
    have h_diff_le : M_lip * ‖q - q₀‖ ≤ r / 8 := by
      rw [dist_eq_norm] at h_dist
      have h2 : 2 * δ_q / 3 ≤ r / (8 * M_lip) := by
        have := min_le_right (1 / 2) (r / (8 * M_lip))
        linarith
      have h3 := mul_le_mul_of_nonneg_left (h_dist.trans h2) hMlip_pos.le
      have h4 : M_lip * (r / (8 * M_lip)) = r / 8 := by field_simp [hMlip_pos.ne']
      linarith
    refine ⟨velocityVec m (spatialPart q₀), ⟨spatialPart q₀, hu_vel q₀ hq₀_u, rfl⟩, ?_⟩
    exact hv_lip.trans h_diff_le
  let c₀ : ℝ := (2 * (32 / r + 1))⁻¹
  have hc₀ : 0 < c₀ := by positivity
  have h_full_deriv_bd : ∀ j : Fin (k + 1), ∃ M_j : ℝ, 0 ≤ M_j ∧
      ∀ (x : Fin 1 → Fin 4 → ℝ) (t : ℝ),
        (∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m (x 0) t μ q) ^ 2) →
        ‖iteratedFDeriv ℝ j.val
          (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ *
          (spacetimeScale (x 0) t) ^ (l + N) ≤ M_j := by
    intro j
    have h_alpha : ∀ α : Fin j.val → Fin 4, ∃ C_α : ℝ, 0 ≤ C_α ∧
        ∀ (x : Fin 1 → Fin 4 → ℝ) (t : ℝ),
          (∀ q ∈ tsupport b_K, c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m (x 0) t μ q) ^ 2) →
          ‖(iterMinkCoordDeriv (List.ofFn α) (timeModTestFn m hm u h_sm h_supp t)) x‖ *
            (spacetimeScale (x 0) t) ^ (l + N) ≤ C_α := by
      intro α
      let u_α := momCoordBase (List.ofFn α) u
      have hu_cd := contDiff_momCoordBase (List.ofFn α) h_sm
      have hu_supp := hasCompactSupport_momCoordBase (List.ofFn α) h_supp
      have hb_one_α : ∀ q ∈ tsupport u_α, b_K q = 1 :=
        fun q hq => hb_one q (tsupport_momCoordBase_subset (List.ofFn α) u hq)
      obtain ⟨C_α, hCα_nn, hCα⟩ := norm_timeModTestFn_mul_spacetimeScale_pow_le hm u_α hu_cd hu_supp
        hb_cd hb_bd hb_one_α hc₀ (l + N)
      refine ⟨C_α, hCα_nn, fun x t hns => ?_⟩
      rw [iterMinkCoordDeriv_timeModTestFn hm (List.ofFn α) h_sm h_supp t]
      exact hCα x t hns
    choose C_α hCα_nn hCα_bd using h_alpha
    let M_j : ℝ := ∑ α : Fin j.val → Fin 4, C_α α
    have hMj_nn : 0 ≤ M_j := Finset.sum_nonneg fun α _ => hCα_nn α
    refine ⟨M_j, hMj_nn, fun x t hns => ?_⟩
    have h_norm := norm_iteratedFDeriv_le_sum_iterMinkCoordDeriv
      (timeModTestFn m hm u h_sm h_supp t) j.val x
    calc ‖iteratedFDeriv ℝ j.val
            (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ *
          (spacetimeScale (x 0) t) ^ (l + N)
        ≤ (∑ α : Fin j.val → Fin 4,
            ‖(iterMinkCoordDeriv (List.ofFn α) (timeModTestFn m hm u h_sm h_supp t)) x‖) *
            (spacetimeScale (x 0) t) ^ (l + N) :=
          mul_le_mul_of_nonneg_right h_norm (pow_nonneg (spacetimeScale_pos (x 0) t).le _)
      _ = ∑ α : Fin j.val → Fin 4,
            ‖(iterMinkCoordDeriv (List.ofFn α) (timeModTestFn m hm u h_sm h_supp t)) x‖ *
              (spacetimeScale (x 0) t) ^ (l + N) := Finset.sum_mul _ _ _
      _ ≤ M_j := Finset.sum_le_sum fun α _ => hCα_bd α x t hns
  choose M_j hMj_nn hMj_bd using h_full_deriv_bd
  let C_large : ℝ := ∑ j ∈ Finset.range (k + 1),
    (k.choose j : ℝ) * (1 + coneDerivBoundFn m hm f r hr (k - j)) *
      (if h : j < k + 1 then M_j ⟨j, h⟩ else 0)
  have hClarge_nn : 0 ≤ C_large := Finset.sum_nonneg fun j _ => by
    have h_m : 0 ≤ (if h : j < k + 1 then M_j ⟨j, h⟩ else 0) := by
      split_ifs with h
      · exact hMj_nn ⟨j, h⟩
      · exact le_rfl
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (by linarith [coneDerivBoundFn_nonneg hm f r hr (k - j)])) h_m
  let C : ℝ := max C_small C_large
  refine ⟨C, le_trans hCsmall_nn (le_max_left _ _), fun t => ?_⟩
  by_cases ht1 : |t| < 1
  · have h_sum_sn : SchwartzMap.seminorm ℝ l k
        (timeModTailTestFn m hm f u h_sm h_supp r hr t) ≤
        C1 * 2 ^ K1 + C2 * 2 ^ K2 := by
      unfold timeModTailTestFn
      have htri := map_sub_le_add (SchwartzMap.seminorm ℝ l k)
        (timeModTestFn m hm u h_sm h_supp t)
        (timeModCoreTestFn m hm f u h_sm h_supp r hr t)
      have ht_le : 1 + |t| ≤ 2 := by linarith
      have h1 : SchwartzMap.seminorm ℝ l k (timeModTestFn m hm u h_sm h_supp t) ≤ C1 * 2 ^ K1 :=
        (hC1_bd t).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht_le K1) hC1_nn)
      have h2 : SchwartzMap.seminorm ℝ l k (timeModCoreTestFn m hm f u h_sm h_supp r hr t) ≤
          C2 * 2 ^ K2 :=
        (hC2_bd t).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht_le K2) hC2_nn)
      linarith
    have ht_pow : (1 + |t|) ^ N ≤ 2 ^ N :=
      pow_le_pow_left₀ (by positivity) (by linarith) N
    calc SchwartzMap.seminorm ℝ l k (timeModTailTestFn m hm f u h_sm h_supp r hr t) *
          (1 + |t|) ^ N
        ≤ (C1 * 2 ^ K1 + C2 * 2 ^ K2) * 2 ^ N :=
          mul_le_mul h_sum_sn ht_pow (pow_nonneg (by positivity) _) (by positivity)
      _ = C_small := rfl
      _ ≤ C := le_max_left _ _
  · have ht_ge : 1 ≤ |t| := not_lt.mp ht1
    have ht_pos : 0 < 1 + |t| := by positivity
    have hpow_pos : 0 < (1 + |t|) ^ N := pow_pos ht_pos N
    have h_sem_le : SchwartzMap.seminorm ℝ l k
        (timeModTailTestFn m hm f u h_sm h_supp r hr t) ≤ C_large * ((1 + |t|) ^ N)⁻¹ := by
      refine SchwartzMap.seminorm_le_bound ℝ l k _
        (mul_nonneg hClarge_nn (inv_nonneg.mpr hpow_pos.le)) fun x => ?_
      rw [le_mul_inv_iff₀ hpow_pos]
      by_cases h_int : |x 0 0 - t| < (r / 4) * |t| ∧
          ∃ v ∈ velocitySupport m f, ‖spatialPart (x 0) - t • v‖ < (r / 4) * |t|
      · have h_ev_one :=
          velocityConeCutoff_eventually_one_interior hm f r hr ht_ge h_int.1 h_int.2
        have h_ev0 : (timeModTailTestFn m hm f u h_sm h_supp r hr t :
            (Fin 1 → Fin 4 → ℝ) → ℂ) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
          filter_upwards [h_ev_one] with y hy
          unfold timeModTailTestFn
          rw [_root_.sub_apply]
          dsimp only [timeModCoreTestFn, mulBoundedCutoffSchwartz_apply]
          rw [hy, Complex.ofReal_one, one_mul, sub_self]
        have h_id0 : iteratedFDeriv ℝ k
            (timeModTailTestFn m hm f u h_sm h_supp r hr t : (Fin 1 → Fin 4 → ℝ) → ℂ) x = 0 := by
          rw [(h_ev0.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds]
          simp
        rw [h_id0, norm_zero, mul_zero, zero_mul]
        exact hClarge_nn
      · have h_ext : (r / 4) * |t| ≤ |x 0 0 - t| ∨
            ∀ v ∈ velocitySupport m f, (r / 4) * |t| ≤ ‖spatialPart (x 0) - t • v‖ := by
          by_cases h1 : |x 0 0 - t| < (r / 4) * |t|
          · right
            intro v hv
            by_contra hlt
            exact h_int ⟨h1, v, hv, not_le.mp hlt⟩
          · exact Or.inl (not_lt.mp h1)
        have h_ns : ∀ q ∈ tsupport b_K,
            c₀ ^ 2 ≤ ∑ μ : Fin 4, (normPhaseGrad m (x 0) t μ q) ^ 2 := by
          intro q hq
          obtain ⟨v, hv, h_v_app⟩ := h_vel_approx q hq
          have h_grad_ge : (r / 8) * |t| ≤ ∑ μ : Fin 4, |hrPhaseGrad m (x 0) t μ q| := by
            rcases h_ext with h_t | h_sp
            · have h0 : (r / 8) * |t| ≤ |hrPhaseGrad m (x 0) t 0 q| := by
                change (r / 8) * |t| ≤ |x 0 0 - t|
                have h12 : (r / 8) * |t| ≤ (r / 4) * |t| := by nlinarith [abs_nonneg t]
                linarith
              exact h0.trans (Finset.single_le_sum
                (fun (μ : Fin 4) _ => abs_nonneg (hrPhaseGrad m (x 0) t μ q))
                (Finset.mem_univ (0 : Fin 4)))
            · have h_v := h_sp v hv
              let w : Fin 3 → ℝ := fun j => hrPhaseGrad m (x 0) t j.succ q
              have hw_eq : w = t • velocityVec m (spatialPart q) - spatialPart (x 0) := by
                ext j
                fin_cases j <;> simp [w, hrPhaseGrad, spatialPart, smul_eq_mul, mul_comm]
              have h_tri_sp : ‖spatialPart (x 0) - t • v‖ ≤
                  ‖w‖ + |t| * ‖velocityVec m (spatialPart q) - v‖ := by
                have heq : spatialPart (x 0) - t • v =
                    -w + t • (velocityVec m (spatialPart q) - v) := by
                  rw [hw_eq, smul_sub]
                  abel
                rw [heq]
                calc ‖-w + t • (velocityVec m (spatialPart q) - v)‖
                    ≤ ‖-w‖ + ‖t • (velocityVec m (spatialPart q) - v)‖ := norm_add_le _ _
                  _ = ‖w‖ + |t| * ‖velocityVec m (spatialPart q) - v‖ := by
                      rw [norm_neg, norm_smul, Real.norm_eq_abs]
              have h_w_ge : (r / 8) * |t| ≤ ‖w‖ := by
                have h_err : |t| * ‖velocityVec m (spatialPart q) - v‖ ≤ |t| * (r / 8) :=
                  mul_le_mul_of_nonneg_left h_v_app (abs_nonneg t)
                linarith
              have h_w_sum : ‖w‖ ≤ ∑ j : Fin 3, |w j| := by
                rw [pi_norm_le_iff_of_nonneg
                  (Finset.sum_nonneg fun (j' : Fin 3) _ => abs_nonneg (w j'))]
                intro j
                rw [Real.norm_eq_abs]
                exact Finset.single_le_sum (fun (j' : Fin 3) _ => abs_nonneg (w j'))
                  (Finset.mem_univ j)
              have h_sp_sum : (∑ j : Fin 3, |w j|) ≤ ∑ μ : Fin 4, |hrPhaseGrad m (x 0) t μ q| := by
                rw [Fin.sum_univ_succ (f := fun μ : Fin 4 => |hrPhaseGrad m (x 0) t μ q|)]
                linarith [abs_nonneg (hrPhaseGrad m (x 0) t 0 q)]
              exact h_w_ge.trans (h_w_sum.trans h_sp_sum)
          have h_scale_bd : spacetimeScale (x 0) t ≤
              4 * |t| + ∑ μ : Fin 4, |hrPhaseGrad m (x 0) t μ q| := by
            have hx0_bd : |x 0 0| ≤ |hrPhaseGrad m (x 0) t 0 q| + |t| := by
              have h1 : |x 0 0| ≤ |x 0 0 - t| + |t| := by simpa using abs_add_le (x 0 0 - t) t
              exact h1
            have hxsp_bd : ‖spatialPart (x 0)‖ ≤
                (∑ j : Fin 3, |hrPhaseGrad m (x 0) t j.succ q|) + |t| := by
              let w : Fin 3 → ℝ := fun j => hrPhaseGrad m (x 0) t j.succ q
              have hw_eq : w = t • velocityVec m (spatialPart q) - spatialPart (x 0) := by
                ext j
                fin_cases j <;> simp [w, hrPhaseGrad, spatialPart, smul_eq_mul, mul_comm]
              have h_sp_eq : spatialPart (x 0) = t • velocityVec m (spatialPart q) - w := by
                rw [hw_eq]; abel
              have hv_lt : ‖velocityVec m (spatialPart q)‖ < 1 :=
                norm_velocityVec_lt_one hm (spatialPart q)
              have hw_sum : ‖w‖ ≤ ∑ j : Fin 3, |w j| := by
                rw [pi_norm_le_iff_of_nonneg
                  (Finset.sum_nonneg fun (j' : Fin 3) _ => abs_nonneg (w j'))]
                intro j
                rw [Real.norm_eq_abs]
                exact Finset.single_le_sum (fun (j' : Fin 3) _ => abs_nonneg (w j'))
                  (Finset.mem_univ j)
              calc ‖spatialPart (x 0)‖
                  ≤ ‖t • velocityVec m (spatialPart q)‖ + ‖w‖ := by
                    rw [h_sp_eq]; exact norm_sub_le _ _
                _ = |t| * ‖velocityVec m (spatialPart q)‖ + ‖w‖ := by
                    rw [norm_smul, Real.norm_eq_abs]
                _ ≤ |t| * 1 + ∑ j : Fin 3, |w j| :=
                    add_le_add (mul_le_mul_of_nonneg_left hv_lt.le (abs_nonneg t)) hw_sum
                _ = (∑ j : Fin 3, |hrPhaseGrad m (x 0) t j.succ q|) + |t| := by ring
            have h_all : |hrPhaseGrad m (x 0) t 0 q| +
                  (∑ j : Fin 3, |hrPhaseGrad m (x 0) t j.succ q|) =
                ∑ μ : Fin 4, |hrPhaseGrad m (x 0) t μ q| :=
              (Fin.sum_univ_succ (f := fun μ : Fin 4 => |hrPhaseGrad m (x 0) t μ q|)).symm
            unfold spacetimeScale
            linarith
          let S_g : ℝ := ∑ μ : Fin 4, |hrPhaseGrad m (x 0) t μ q|
          have ht_le_sum : |t| ≤ (8 / r) * S_g := by
            have h1 := mul_le_mul_of_nonneg_left h_grad_ge (by positivity : 0 ≤ 8 / r)
            have h2 : (8 / r) * ((r / 8) * |t|) = |t| := by field_simp [hr.ne']
            linarith
          have h_sc_mult : spacetimeScale (x 0) t ≤ (32 / r + 1) * S_g := by
            have h4 : 4 * |t| ≤ (32 / r) * S_g := by
              calc 4 * |t| ≤ 4 * ((8 / r) * S_g) := by linarith
                _ = (32 / r) * S_g := by ring
            linarith [h_scale_bd, h4]
          have hs_pos : 0 < spacetimeScale (x 0) t := spacetimeScale_pos (x 0) t
          have h_norm_sum : (32 / r + 1)⁻¹ ≤ ∑ μ : Fin 4, |normPhaseGrad m (x 0) t μ q| := by
            have h_inv : 1 ≤ (32 / r + 1) * ∑ μ : Fin 4, |normPhaseGrad m (x 0) t μ q| := by
              have h_each : ∀ μ : Fin 4, |normPhaseGrad m (x 0) t μ q| =
                  (spacetimeScale (x 0) t)⁻¹ * |hrPhaseGrad m (x 0) t μ q| := fun μ => by
                unfold normPhaseGrad
                rw [abs_mul, abs_inv, abs_of_pos hs_pos]
              simp only [h_each, ← Finset.mul_sum]
              have h1 := mul_le_mul_of_nonneg_left h_sc_mult (inv_pos.mpr hs_pos).le
              rw [inv_mul_cancel₀ hs_pos.ne'] at h1
              calc 1 ≤ (spacetimeScale (x 0) t)⁻¹ * ((32 / r + 1) * S_g) := h1
                _ = (32 / r + 1) * ((spacetimeScale (x 0) t)⁻¹ * S_g) := by ring
            have h_pos_f : 0 < (32 / r + 1) := by positivity
            have h2 := mul_le_mul_of_nonneg_left h_inv (inv_pos.mpr h_pos_f).le
            rw [← mul_assoc, inv_mul_cancel₀ h_pos_f.ne', one_mul, mul_one] at h2
            exact h2
          have h_cs : (∑ μ : Fin 4, |normPhaseGrad m (x 0) t μ q|) ^ 2 ≤
              4 * ∑ μ : Fin 4, (normPhaseGrad m (x 0) t μ q) ^ 2 := by
            rw [Fin.sum_univ_four, Fin.sum_univ_four]
            have hs0 := sq_abs (normPhaseGrad m (x 0) t 0 q)
            have hs1 := sq_abs (normPhaseGrad m (x 0) t 1 q)
            have hs2 := sq_abs (normPhaseGrad m (x 0) t 2 q)
            have hs3 := sq_abs (normPhaseGrad m (x 0) t 3 q)
            rw [← hs0, ← hs1, ← hs2, ← hs3]
            nlinarith [sq_nonneg (|normPhaseGrad m (x 0) t 0 q| - |normPhaseGrad m (x 0) t 1 q|),
              sq_nonneg (|normPhaseGrad m (x 0) t 0 q| - |normPhaseGrad m (x 0) t 2 q|),
              sq_nonneg (|normPhaseGrad m (x 0) t 0 q| - |normPhaseGrad m (x 0) t 3 q|),
              sq_nonneg (|normPhaseGrad m (x 0) t 1 q| - |normPhaseGrad m (x 0) t 2 q|),
              sq_nonneg (|normPhaseGrad m (x 0) t 1 q| - |normPhaseGrad m (x 0) t 3 q|),
              sq_nonneg (|normPhaseGrad m (x 0) t 2 q| - |normPhaseGrad m (x 0) t 3 q|)]
          have h_sq_inv : ((32 / r + 1)⁻¹) ^ 2 ≤
              (∑ μ : Fin 4, |normPhaseGrad m (x 0) t μ q|) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h_norm_sum 2
          have hc0_eq : c₀ ^ 2 = ((32 / r + 1)⁻¹) ^ 2 / 4 := by
            have h_pos_r : (32 / r + 1 : ℝ) ≠ 0 := by positivity
            dsimp [c₀]
            field_simp [hr.ne', h_pos_r]
            ring
          linarith
        let χ_tail : (Fin 1 → Fin 4 → ℝ) → ℂ := fun y =>
          1 - (velocityConeCutoff m hm f r hr t y : ℂ)
        have hχ_cd : ContDiff ℝ (⊤ : ℕ∞) χ_tail :=
          contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
            (contDiff_velocityConeCutoff hm f r hr t))
        have hχ_bd : ∀ i : ℕ, ‖iteratedFDeriv ℝ i χ_tail x‖ ≤
            1 + coneDerivBoundFn m hm f r hr i := by
          intro i
          rcases i with _ | i'
          · rw [norm_iteratedFDeriv_zero]
            have h0 := coneDerivBoundFn_spec hm f r hr 0 t x
            rw [norm_iteratedFDeriv_zero] at h0
            calc ‖(1 : ℂ) - (velocityConeCutoff m hm f r hr t x : ℂ)‖
                ≤ ‖(1 : ℂ)‖ + ‖(velocityConeCutoff m hm f r hr t x : ℂ)‖ := norm_sub_le _ _
              _ ≤ 1 + coneDerivBoundFn m hm f r hr 0 := by
                  rw [norm_one]
                  linarith [h0]
          · have h_sub_fn : χ_tail = (fun _ => (1 : ℂ)) -
                (fun y => (velocityConeCutoff m hm f r hr t y : ℂ)) := rfl
            have h_c_cd : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Fin 1 → Fin 4 → ℝ => (1 : ℂ)) :=
              contDiff_const
            have h_v_cd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin 1 → Fin 4 → ℝ =>
                (velocityConeCutoff m hm f r hr t y : ℂ)) :=
              Complex.ofRealCLM.contDiff.comp (contDiff_velocityConeCutoff hm f r hr t)
            rw [h_sub_fn, iteratedFDeriv_sub_apply
              (h_c_cd.of_le (natCast_le_top_enat_coe (i' + 1))).contDiffAt
              (h_v_cd.of_le (natCast_le_top_enat_coe (i' + 1))).contDiffAt,
              iteratedFDeriv_const_succ, zero_sub, norm_neg]
            exact (coneDerivBoundFn_spec hm f r hr (i' + 1) t x).trans (by linarith)
        have h_tail_eq : (timeModTailTestFn m hm f u h_sm h_supp r hr t :
            (Fin 1 → Fin 4 → ℝ) → ℂ) = fun y =>
              χ_tail y * (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) y := by
          ext y
          unfold timeModTailTestFn
          rw [_root_.sub_apply]
          dsimp only [timeModCoreTestFn, mulBoundedCutoffSchwartz_apply, χ_tail]
          ring
        rw [h_tail_eq]
        have hm_le := norm_iteratedFDeriv_mul_le (hχ_cd.of_le (natCast_le_top_enat_coe k))
          (((timeModTestFn m hm u h_sm h_supp t).smooth (⊤ : ℕ∞)).of_le
            (natCast_le_top_enat_coe k)) x le_rfl
        have h_sc_pow : ‖x‖ ^ l * (1 + |t|) ^ N ≤ (spacetimeScale (x 0) t) ^ (l + N) := by
          have h1 := pow_le_pow_left₀ (norm_nonneg x) (norm_le_spacetimeScale x t) l
          have h2 := pow_le_pow_left₀ (by positivity) (one_add_abs_le_spacetimeScale x t) N
          rw [pow_add]
          exact mul_le_mul h1 h2 (pow_nonneg (by positivity) N)
            (pow_nonneg (spacetimeScale_pos (x 0) t).le l)
        calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ k (fun y =>
              χ_tail y * (timeModTestFn m hm u h_sm h_supp t :
                (Fin 1 → Fin 4 → ℝ) → ℂ) y) x‖ * (1 + |t|) ^ N
            = (‖x‖ ^ l * (1 + |t|) ^ N) * ‖iteratedFDeriv ℝ k (fun y =>
                χ_tail y * (timeModTestFn m hm u h_sm h_supp t :
                  (Fin 1 → Fin 4 → ℝ) → ℂ) y) x‖ := by ring
          _ ≤ (spacetimeScale (x 0) t) ^ (l + N) * ∑ j ∈ Finset.range (k + 1),
                (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j χ_tail x‖ *
                  ‖iteratedFDeriv ℝ (k - j)
                    (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ :=
              mul_le_mul h_sc_pow hm_le (norm_nonneg _)
                (pow_nonneg (spacetimeScale_pos (x 0) t).le (l + N))
          _ = ∑ j ∈ Finset.range (k + 1),
                (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j χ_tail x‖ *
                  (‖iteratedFDeriv ℝ (k - j)
                    (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ *
                    (spacetimeScale (x 0) t) ^ (l + N)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j ∈ Finset.range (k + 1),
                (k.choose j : ℝ) * ‖iteratedFDeriv ℝ (k - j) χ_tail x‖ *
                  (‖iteratedFDeriv ℝ j
                    (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ *
                    (spacetimeScale (x 0) t) ^ (l + N)) := by
              have h_ref := Finset.sum_range_reflect
                (fun j => (k.choose j : ℝ) * ‖iteratedFDeriv ℝ (k - j) χ_tail x‖ *
                  (‖iteratedFDeriv ℝ j
                    (timeModTestFn m hm u h_sm h_supp t : (Fin 1 → Fin 4 → ℝ) → ℂ) x‖ *
                    (spacetimeScale (x 0) t) ^ (l + N))) (k + 1)
              rw [← h_ref]
              refine Finset.sum_congr rfl fun j hj => ?_
              have hj_le : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hk_sub : k + 1 - 1 - j = k - j := by omega
              rw [hk_sub, Nat.sub_sub_self hj_le, Nat.choose_symm hj_le]
          _ ≤ C_large := by
              refine Finset.sum_le_sum fun j hj => ?_
              have hj_lt : j < k + 1 := Finset.mem_range.mp hj
              have h_if : (if h : j < k + 1 then M_j ⟨j, h⟩ else 0) = M_j ⟨j, hj_lt⟩ :=
                dif_pos hj_lt
              rw [h_if]
              have h1 := mul_le_mul_of_nonneg_left (hχ_bd (k - j)) (Nat.cast_nonneg (k.choose j))
              have h2 := hMj_bd ⟨j, hj_lt⟩ x t h_ns
              exact mul_le_mul h1 h2
                (mul_nonneg (norm_nonneg _) (pow_nonneg (spacetimeScale_pos (x 0) t).le _))
                (mul_nonneg (Nat.cast_nonneg _)
                  (by linarith [coneDerivBoundFn_nonneg hm f r hr (k - j)]))
    calc SchwartzMap.seminorm ℝ l k (timeModTailTestFn m hm f u h_sm h_supp r hr t) *
          (1 + |t|) ^ N
        ≤ (C_large * ((1 + |t|) ^ N)⁻¹) * (1 + |t|) ^ N :=
          mul_le_mul_of_nonneg_right h_sem_le hpow_pos.le
      _ = C_large := by rw [mul_assoc, inv_mul_cancel₀ hpow_pos.ne', mul_one]
      _ ≤ C := le_max_right _ _

theorem schwartzSeminorm_haagRuelleTailTestFn_rapid_decay (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (l k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (haagRuelleTailTestFn m M hm hM f r hr t) *
        (1 + |t|) ^ N ≤ C :=
  schwartzSeminorm_timeModTailTestFn_rapid_decay hm f (haagRuelleBaseAmp m M hm hM f)
    (contDiff_haagRuelleBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleBaseAmp m M hm hM f)
    (fun q hq => tsupport_haagRuelleBaseAmp_spatialPart_subset m M hm hM f ⟨q, hq, rfl⟩)
    r hr l k N

theorem schwartzSeminorm_haagRuelleDerivTailTestFn_rapid_decay (m M : ℝ) (hm : 0 < m)
    (hM : m < M) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (l k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℝ l k (haagRuelleDerivTailTestFn m M hm hM f r hr t) *
        (1 + |t|) ^ N ≤ C :=
  schwartzSeminorm_timeModTailTestFn_rapid_decay hm f (haagRuelleDerivBaseAmp m M hm hM f)
    (contDiff_haagRuelleDerivBaseAmp m M hm hM f)
    (hasCompactSupport_haagRuelleDerivBaseAmp m M hm hM f)
    (fun q hq => tsupport_haagRuelleBaseAmp_spatialPart_subset m M hm hM f
      ⟨q, tsupport_haagRuelleDerivBaseAmp_subset m M hm hM f hq, rfl⟩)
    r hr l k N

lemma spacelike_velocityConeCutoffs_of_radius {m : ℝ} (hm : 0 < m)
    {f₁ f₂ : SmoothWavepacket} {d_sep r : ℝ} (hr : 0 < r) (hd : 5 * r ≤ d_sep)
    (h_sep : ∀ v₁ ∈ velocitySupport m f₁, ∀ v₂ ∈ velocitySupport m f₂, d_sep ≤ ‖v₁ - v₂‖)
    {t : ℝ} (ht : 1 ≤ |t|) {x y : Fin 1 → Fin 4 → ℝ}
    (hx : x ∈ tsupport (velocityConeCutoff m hm f₁ r hr t))
    (hy : y ∈ tsupport (velocityConeCutoff m hm f₂ r hr t)) :
    minkowskiInner (x 0 - y 0) (x 0 - y 0) < 0 := by
  obtain ⟨hx0, v₁, hv₁, hxsp⟩ := tsupport_velocityConeCutoff_large_time hm f₁ r hr ht hx
  obtain ⟨hy0, v₂, hv₂, hysp⟩ := tsupport_velocityConeCutoff_large_time hm f₂ r hr ht hy
  have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have h_time_le : |x 0 0 - y 0 0| ≤ 2 * r * |t| := by
    have htri : |x 0 0 - y 0 0| ≤ |x 0 0 - t| + |y 0 0 - t| := by
      have heq : x 0 0 - y 0 0 = (x 0 0 - t) - (y 0 0 - t) := by ring
      rw [heq]
      exact abs_sub _ _
    linarith
  have h_sp_ge : (d_sep - 2 * r) * |t| ≤ ‖spatialPart (x 0) - spatialPart (y 0)‖ := by
    have hv := h_sep v₁ hv₁ v₂ hv₂
    have htv : d_sep * |t| ≤ ‖t • v₁ - t • v₂‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      calc d_sep * |t| = |t| * d_sep := mul_comm _ _
        _ ≤ |t| * ‖v₁ - v₂‖ := mul_le_mul_of_nonneg_left hv ht_pos.le
    have htri : ‖t • v₁ - t • v₂‖ ≤
        ‖spatialPart (x 0) - t • v₁‖ + ‖spatialPart (x 0) - spatialPart (y 0)‖ +
          ‖spatialPart (y 0) - t • v₂‖ := by
      have heq : t • v₁ - t • v₂ =
          -(spatialPart (x 0) - t • v₁) + (spatialPart (x 0) - spatialPart (y 0)) +
            (spatialPart (y 0) - t • v₂) := by
        abel
      rw [heq]
      calc ‖-(spatialPart (x 0) - t • v₁) + (spatialPart (x 0) - spatialPart (y 0)) +
              (spatialPart (y 0) - t • v₂)‖
          ≤ ‖-(spatialPart (x 0) - t • v₁) + (spatialPart (x 0) - spatialPart (y 0))‖ +
              ‖spatialPart (y 0) - t • v₂‖ := norm_add_le _ _
        _ ≤ (‖-(spatialPart (x 0) - t • v₁)‖ + ‖spatialPart (x 0) - spatialPart (y 0)‖) +
              ‖spatialPart (y 0) - t • v₂‖ := by
            linarith [norm_add_le (-(spatialPart (x 0) - t • v₁))
              (spatialPart (x 0) - spatialPart (y 0))]
        _ = _ := by rw [norm_neg]
    linarith
  have h_gap : 2 * r * |t| < (d_sep - 2 * r) * |t| := by
    have : 2 * r < d_sep - 2 * r := by linarith
    exact mul_lt_mul_of_pos_right this ht_pos
  have h_time_sq : (x 0 0 - y 0 0) ^ 2 ≤ (2 * r * |t|) ^ 2 := by
    rw [← sq_abs (x 0 0 - y 0 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) h_time_le 2
  have h_strict_sq : (2 * r * |t|) ^ 2 < ((d_sep - 2 * r) * |t|) ^ 2 := by
    have h_l_nn : 0 ≤ 2 * r * |t| := by positivity
    nlinarith
  have h_sp_sq : ((d_sep - 2 * r) * |t|) ^ 2 ≤
      ‖spatialPart (x 0 - y 0)‖ ^ 2 := by
    have h_eq : spatialPart (x 0 - y 0) = spatialPart (x 0) - spatialPart (y 0) := by
      ext j; simp [spatialPart]
    rw [h_eq]
    exact pow_le_pow_left₀ (mul_nonneg (by linarith) ht_pos.le) h_sp_ge 2
  have h_eucl := sum_sq_fin3_ge_pi_norm_sq (spatialPart (x 0 - y 0))
  have hm_eq : minkowskiInner (x 0 - y 0) (x 0 - y 0) =
      (x 0 0 - y 0 0) ^ 2 -
        (spatialPart (x 0 - y 0) 0 ^ 2 + spatialPart (x 0 - y 0) 1 ^ 2 +
          spatialPart (x 0 - y 0) 2 ^ 2) := by
    rw [minkowskiInner_explicit]
    simp [spatialPart]
    ring
  rw [hm_eq]
  linarith

theorem exists_spacelike_cores_of_velocityDisjoint {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {f₁ f₂ : SmoothWavepacket} (hdisj : VelocityDisjoint m f₁ f₂) :
    ∃ (r : ℝ) (hr : 0 < r) (T₀ : ℝ), 0 < T₀ ∧
      ∀ (t : ℝ), T₀ ≤ |t| →
        ∀ x ∈ tsupport (haagRuelleCoreTestFn m M hm hM f₁ r hr t :
                (Fin 1 → Fin 4 → ℝ) → ℂ) ∪
              tsupport (haagRuelleDerivCoreTestFn m M hm hM f₁ r hr t :
                (Fin 1 → Fin 4 → ℝ) → ℂ),
        ∀ y ∈ tsupport (haagRuelleCoreTestFn m M hm hM f₂ r hr t :
                (Fin 1 → Fin 4 → ℝ) → ℂ) ∪
              tsupport (haagRuelleDerivCoreTestFn m M hm hM f₂ r hr t :
                (Fin 1 → Fin 4 → ℝ) → ℂ),
          minkowskiInner (x 0 - y 0) (x 0 - y 0) < 0 := by
  obtain ⟨d_sep, hd_pos, h_sep⟩ := exists_pos_sep_of_velocityDisjoint hm hdisj
  let r : ℝ := d_sep / 6
  have hr : 0 < r := by positivity
  refine ⟨r, hr, 1, zero_lt_one, fun t ht x hx y hy => ?_⟩
  have hx' : x ∈ tsupport (velocityConeCutoff m hm f₁ r hr t) := by
    rcases hx with hx1 | hx2
    · exact tsupport_timeModCoreTestFn_subset hm f₁ _ _ _ r hr t hx1
    · exact tsupport_timeModCoreTestFn_subset hm f₁ _ _ _ r hr t hx2
  have hy' : y ∈ tsupport (velocityConeCutoff m hm f₂ r hr t) := by
    rcases hy with hy1 | hy2
    · exact tsupport_timeModCoreTestFn_subset hm f₂ _ _ _ r hr t hy1
    · exact tsupport_timeModCoreTestFn_subset hm f₂ _ _ _ r hr t hy2
  exact spacelike_velocityConeCutoffs_of_radius hm hr (by dsimp [r]; linarith) h_sep ht hx' hy'

theorem exists_disjoint_nonvanishing_haagRuelle_wavepackets {m M : ℝ} (hm : 0 < m) (hM : m < M) :
    ∃ f₁ f₂ : SmoothWavepacket,
      VelocityDisjoint m f₁ f₂ ∧
        (∀ t : ℝ, haagRuelleTestFn m M hm hM f₁ t ≠ 0 ∧
          haagRuelleTestFn m M hm hM f₂ t ≠ 0) ∧
        (∀ (r : ℝ) (hr : 0 < r), ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ |t| →
          haagRuelleCoreTestFn m M hm hM f₁ r hr t ≠ 0 ∧
          haagRuelleCoreTestFn m M hm hM f₂ r hr t ≠ 0) := by
  let f₁ : SmoothWavepacket := bumpWavepacket 0 (m / 4) (by positivity)
  let c₂ : Fin 3 → ℝ := Pi.single 0 (2 * m)
  let f₂ : SmoothWavepacket := bumpWavepacket c₂ (m / 4) (by positivity)
  have hdisj : VelocityDisjoint m f₁ f₂ := by
    unfold VelocityDisjoint
    rw [Set.disjoint_left]
    intro v hv1 hv2
    rcases hv1 with ⟨p, hp, rfl⟩
    rcases hv2 with ⟨q, hq, h_eq⟩
    have hp_ball := tsupport_bumpWavepacket_subset 0 (m / 4) (by positivity) hp
    rw [Metric.mem_closedBall, dist_zero_right] at hp_ball
    have hq_ball := tsupport_bumpWavepacket_subset c₂ (m / 4) (by positivity) hq
    rw [Metric.mem_closedBall, dist_eq_norm] at hq_ball
    have hp0 : p 0 ≤ m / 2 := by
      have h1 : ‖p 0‖ ≤ m / 2 := (norm_le_pi_norm p 0).trans (by linarith)
      rw [Real.norm_eq_abs] at h1
      exact le_trans (le_abs_self _) h1
    have hv1_le : velocityVec m p 0 ≤ 1 / 2 := by
      dsimp [velocityVec, Pi.smul_apply, smul_eq_mul]
      have he_ge : m ≤ massShellEnergy m p := massShellEnergy_ge_mass hm p
      have he_pos : 0 < massShellEnergy m p := massShellEnergy_pos hm p
      calc (massShellEnergy m p)⁻¹ * p 0
          ≤ (massShellEnergy m p)⁻¹ * (m / 2) :=
            mul_le_mul_of_nonneg_left hp0 (inv_pos.mpr he_pos).le
        _ ≤ m⁻¹ * (m / 2) :=
            mul_le_mul_of_nonneg_right (inv_anti₀ hm he_ge) (by positivity)
        _ = 1 / 2 := by field_simp [hm.ne']
    have hq0_ge : 3 * m / 2 ≤ q 0 := by
      have h1 : ‖(q - c₂) 0‖ ≤ m / 2 := (norm_le_pi_norm (q - c₂) 0).trans (by linarith)
      simp only [Pi.sub_apply, c₂, Pi.single_eq_same, Real.norm_eq_abs] at h1
      linarith [abs_le.mp h1]
    have hq1_le : |q 1| ≤ m / 2 := by
      have h1 : ‖(q - c₂) 1‖ ≤ m / 2 := (norm_le_pi_norm (q - c₂) 1).trans (by linarith)
      simp only [Pi.sub_apply, c₂, Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0), sub_zero,
        Real.norm_eq_abs] at h1
      exact h1
    have hq2_le : |q 2| ≤ m / 2 := by
      have h1 : ‖(q - c₂) 2‖ ≤ m / 2 := (norm_le_pi_norm (q - c₂) 2).trans (by linarith)
      simp only [Pi.sub_apply, c₂, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), sub_zero,
        Real.norm_eq_abs] at h1
      exact h1
    have he_lt : massShellEnergy m q < 2 * q 0 := by
      have he_sq : massShellEnergy m q ^ 2 = m ^ 2 + q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 := by
        rw [massShellEnergy_sq m q, massShellSpatialSq]
        ring
      have h1_sq : q 1 ^ 2 ≤ (m / 2) ^ 2 := by
        rw [← sq_abs (q 1)]
        exact pow_le_pow_left₀ (abs_nonneg _) hq1_le 2
      have h2_sq : q 2 ^ 2 ≤ (m / 2) ^ 2 := by
        rw [← sq_abs (q 2)]
        exact pow_le_pow_left₀ (abs_nonneg _) hq2_le 2
      have h_sq_lt : massShellEnergy m q ^ 2 < (2 * q 0) ^ 2 := by
        nlinarith [sq_nonneg m, sq_nonneg (q 0)]
      have he_pos : 0 < massShellEnergy m q := massShellEnergy_pos hm q
      nlinarith
    have hv2_gt : 1 / 2 < velocityVec m q 0 := by
      dsimp [velocityVec, Pi.smul_apply, smul_eq_mul]
      have he_pos : 0 < massShellEnergy m q := massShellEnergy_pos hm q
      have h1 : 1 / 2 * massShellEnergy m q < q 0 := by linarith
      calc 1 / 2 = (1 / 2 * massShellEnergy m q) * (massShellEnergy m q)⁻¹ := by
            field_simp [he_pos.ne']
        _ < q 0 * (massShellEnergy m q)⁻¹ :=
            mul_lt_mul_of_pos_right h1 (inv_pos.mpr he_pos)
        _ = (massShellEnergy m q)⁻¹ * q 0 := mul_comm _ _
    have h0_eq : velocityVec m p 0 = velocityVec m q 0 := congrFun h_eq.symm 0
    linarith
  have h_eval : ∀ (f : SmoothWavepacket) (k : Fin 3 → ℝ) (hk : f.amp k = 1),
      (∀ t : ℝ, haagRuelleTestFn m M hm hM f t ≠ 0) ∧
      (∀ (r : ℝ) (hr : 0 < r), ∃ T₁ : ℝ, 0 < T₁ ∧ ∀ t : ℝ, T₁ ≤ |t| →
        haagRuelleCoreTestFn m M hm hM f r hr t ≠ 0) := by
    intro f k hk
    refine ⟨fun t h0 => ?_, fun r hr => ?_⟩
    · have h1 : minkowskiFourier (haagRuelleTestFn m M hm hM f t) (fun _ => -massShellVec m k) =
          1 := by
        rw [minkowskiFourier_haagRuelleTestFn_massShell, hk]
      rw [h0] at h1
      have h2 : minkowskiFourier (0 : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
          (fun _ => -massShellVec m k) = 0 := by
        rw [← minkowskiFourierCLM_apply, map_zero]
        rfl
      rw [h2] at h1
      exact zero_ne_one h1
    · have h_with := schwartz_withSeminorms ℝ (Fin 1 → Fin 4 → ℝ) ℂ
      let T_real := (minkowskiFourierCLM 1).toLinearMap.restrictScalars ℝ
      let q_sem : Seminorm ℝ (SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :=
        (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ (0, 0)).comp T_real
      have hq_cont : Continuous q_sem :=
        (h_with.continuous_seminorm (0, 0)).comp (minkowskiFourierCLM 1).continuous
      obtain ⟨s, C₀, _, hq_le⟩ := Seminorm.bound_of_continuous h_with q_sem hq_cont
      have h_dec : ∀ p : ℕ × ℕ, ∃ C_p : ℝ, 0 ≤ C_p ∧ ∀ t : ℝ,
          SchwartzMap.seminorm ℝ p.1 p.2 (haagRuelleTailTestFn m M hm hM f r hr t) *
            (1 + |t|) ≤ C_p := fun p => by
        simpa [pow_one] using schwartzSeminorm_haagRuelleTailTestFn_rapid_decay m M hm hM f r hr
          p.1 p.2 1
      choose C_p hCp_nn hCp_bd using h_dec
      let C_sup : ℝ := ∑ p ∈ s, C_p p
      have hCsup_nn : 0 ≤ C_sup := Finset.sum_nonneg fun p _ => hCp_nn p
      let C_tot : ℝ := (C₀ : ℝ) * C_sup
      have hCtot_nn : 0 ≤ C_tot := mul_nonneg (NNReal.coe_nonneg _) hCsup_nn
      let T₁ : ℝ := max 1 (2 * C_tot)
      have hT1_pos : 0 < T₁ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      refine ⟨T₁, hT1_pos, fun t ht h0 => ?_⟩
      have ht_big : 2 * C_tot < 1 + |t| := by
        have h1 : 2 * C_tot ≤ T₁ := le_max_right _ _
        linarith
      have h_tail_pt : ‖minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
          (fun _ => -massShellVec m k)‖ ≤ C_tot * (1 + |t|)⁻¹ := by
        have h_pt : ‖minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
            (fun _ => -massShellVec m k)‖ ≤
            SchwartzMap.seminorm ℝ 0 0
              (minkowskiFourierCLM 1 (haagRuelleTailTestFn m M hm hM f r hr t)) := by
          rw [← minkowskiFourierCLM_apply]
          have h_s := (minkowskiFourierCLM 1 (haagRuelleTailTestFn m M hm hM f r hr t)).le_seminorm
            ℝ 0 0 (fun _ => -massShellVec m k)
          simpa [norm_iteratedFDeriv_zero, pow_zero, one_mul] using h_s
        have h_q : SchwartzMap.seminorm ℝ 0 0
              (minkowskiFourierCLM 1 (haagRuelleTailTestFn m M hm hM f r hr t)) ≤
            (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ))
              (haagRuelleTailTestFn m M hm hM f r hr t) := by
          have h_le := hq_le (haagRuelleTailTestFn m M hm hM f r hr t)
          exact le_trans h_le (le_of_eq (NNReal.smul_def _ _))
        have h_sup : (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ))
              (haagRuelleTailTestFn m M hm hM f r hr t) ≤ C_sup * (1 + |t|)⁻¹ := by
          have ht_pos : 0 < 1 + |t| := by positivity
          refine Seminorm.finset_sup_apply_le
            (mul_nonneg hCsup_nn (inv_nonneg.mpr ht_pos.le)) fun p hp => ?_
          rw [SchwartzMap.schwartzSeminormFamily_apply, le_mul_inv_iff₀ ht_pos]
          calc SchwartzMap.seminorm ℝ p.1 p.2 (haagRuelleTailTestFn m M hm hM f r hr t) *
                (1 + |t|)
              ≤ C_p p := hCp_bd p t
            _ ≤ C_sup := Finset.single_le_sum (fun p' _ => hCp_nn p') hp
        calc ‖minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
              (fun _ => -massShellVec m k)‖
            ≤ (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ))
                (haagRuelleTailTestFn m M hm hM f r hr t) := h_pt.trans h_q
          _ ≤ (C₀ : ℝ) * (C_sup * (1 + |t|)⁻¹) :=
              mul_le_mul_of_nonneg_left h_sup (NNReal.coe_nonneg _)
          _ = C_tot * (1 + |t|)⁻¹ := by ring
      have h_lt_half : ‖minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
          (fun _ => -massShellVec m k)‖ < 1 / 2 := by
        have ht_pos : 0 < 1 + |t| := by positivity
        have h1 : C_tot * (1 + |t|)⁻¹ < 1 / 2 := by
          rw [mul_comm, inv_mul_lt_iff₀ ht_pos]
          linarith
        exact h_tail_pt.trans_lt h1
      have h_core_eq : minkowskiFourier (haagRuelleCoreTestFn m M hm hM f r hr t)
            (fun _ => -massShellVec m k) =
          1 - minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
            (fun _ => -massShellVec m k) := by
        have h_add := haagRuelleTestFn_eq_core_add_tail m M hm hM f r hr t
        have h_sub : haagRuelleCoreTestFn m M hm hM f r hr t =
            haagRuelleTestFn m M hm hM f t - haagRuelleTailTestFn m M hm hM f r hr t := by
          rw [h_add]
          abel
        rw [h_sub, ← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply,
          minkowskiFourierCLM_apply, minkowskiFourierCLM_apply,
          minkowskiFourier_haagRuelleTestFn_massShell, hk]
      rw [h0, ← minkowskiFourierCLM_apply, map_zero] at h_core_eq
      change (0 : ℂ) = 1 - minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
          (fun _ => -massShellVec m k) at h_core_eq
      have h_eq1 : minkowskiFourier (haagRuelleTailTestFn m M hm hM f r hr t)
          (fun _ => -massShellVec m k) = 1 := by
        exact (sub_eq_zero.mp h_core_eq.symm).symm
      rw [h_eq1, norm_one] at h_lt_half
      norm_num at h_lt_half
  obtain ⟨h1_full, h1_core⟩ := h_eval f₁ 0 (bumpWavepacket_apply_center 0 (m / 4) (by positivity))
  obtain ⟨h2_full, h2_core⟩ := h_eval f₂ c₂ (bumpWavepacket_apply_center c₂ (m / 4) (by positivity))
  refine ⟨f₁, f₂, hdisj, fun t => ⟨h1_full t, h2_full t⟩, fun r hr => ?_⟩
  obtain ⟨T₁, hT1_pos, h1⟩ := h1_core r hr
  obtain ⟨T₂, hT2_pos, h2⟩ := h2_core r hr
  refine ⟨max T₁ T₂, lt_of_lt_of_le hT1_pos (le_max_left _ _), fun t ht =>
    ⟨h1 t ((le_max_left _ _).trans ht), h2 t ((le_max_right _ _).trans ht)⟩⟩

def posMassShell (m : ℝ) : Set (Fin 4 → ℝ) :=
  { P | 0 < P 0 ∧ minkowskiInner P P = m ^ 2 }

def continuumCone (M : ℝ) : Set (Fin 4 → ℝ) :=
  { P | 0 < P 0 ∧ M ^ 2 ≤ minkowskiInner P P }

def excitedMassSpectrum (m M : ℝ) : Set (Fin 4 → ℝ) :=
  posMassShell m ∪ continuumCone M

def massGapSpectrum (m M : ℝ) : Set (Fin 4 → ℝ) :=
  ({0} : Set (Fin 4 → ℝ)) ∪ excitedMassSpectrum m M

def massGapSpectralRegion (m M : ℝ) (n : ℕ) : Set (Fin n → Fin 4 → ℝ) :=
  { p | (∑ i, p i = 0) ∧ ∀ k : Fin n, partial_sum_p n p k ∈ massGapSpectrum m M }

lemma zero_mem_massGapSpectrum (m M : ℝ) :
    (0 : Fin 4 → ℝ) ∈ massGapSpectrum m M :=
  Or.inl rfl

lemma zero_mem_massGapSpectralRegion (m M : ℝ) (n : ℕ) :
    (0 : Fin n → Fin 4 → ℝ) ∈ massGapSpectralRegion m M n := by
  refine ⟨by simp, fun k => ?_⟩
  simp only [partial_sum_p, Pi.zero_apply, Finset.sum_const_zero]
  exact zero_mem_massGapSpectrum m M

lemma massShellVec_mem_posMassShell {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    massShellVec m p ∈ posMassShell m :=
  ⟨massShellEnergy_pos hm p, minkowskiInner_massShellVec_self m p⟩

lemma mem_posMassShell_energy_ge {m : ℝ} (hm : 0 < m) {P : Fin 4 → ℝ}
    (hP : P ∈ posMassShell m) :
    m ≤ P 0 := by
  have h0 : 0 < P 0 := hP.1
  have hm_sq : minkowskiInner P P = m ^ 2 := hP.2
  rw [minkowskiInner_explicit] at hm_sq
  have h_sq : m ^ 2 ≤ (P 0) ^ 2 := by
    nlinarith [sq_nonneg (P 1), sq_nonneg (P 2), sq_nonneg (P 3)]
  nlinarith

lemma mem_continuumCone_energy_ge {M : ℝ} (hM0 : 0 < M) {P : Fin 4 → ℝ}
    (hP : P ∈ continuumCone M) :
    M ≤ P 0 := by
  have h0 : 0 < P 0 := hP.1
  have hM_sq : M ^ 2 ≤ minkowskiInner P P := hP.2
  rw [minkowskiInner_explicit] at hM_sq
  have h_sq : M ^ 2 ≤ (P 0) ^ 2 := by
    nlinarith [sq_nonneg (P 1), sq_nonneg (P 2), sq_nonneg (P 3)]
  nlinarith

lemma mem_excitedMassSpectrum_bounds {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {P : Fin 4 → ℝ} (hP : P ∈ excitedMassSpectrum m M) :
    m ≤ P 0 ∧ m ^ 2 ≤ minkowskiInner P P := by
  rcases hP with h1 | h2
  · exact ⟨mem_posMassShell_energy_ge hm h1, le_of_eq h1.2.symm⟩
  · have hM0 : 0 < M := lt_trans hm hM
    have hm_le_M : m ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm.le hM.le 2
    exact ⟨le_trans hM.le (mem_continuumCone_energy_ge hM0 h2), le_trans hm_le_M h2.2⟩

lemma mem_massGapSpectrum_energy_nonneg {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {P : Fin 4 → ℝ} (hP : P ∈ massGapSpectrum m M) :
    0 ≤ P 0 := by
  rcases hP with h0 | hex
  · rw [Set.mem_singleton_iff.mp h0]
    simp
  · exact le_trans hm.le (mem_excitedMassSpectrum_bounds hm hM hex).1

lemma massGapSpectrum_subset_closure_forward_light_cone {m M : ℝ} (hm : 0 < m) (hM : m < M) :
    massGapSpectrum m M ⊆ closure forward_light_cone := by
  rw [closure_forward_light_cone_eq]
  intro P hP
  rcases hP with h0 | hex
  · rw [Set.mem_singleton_iff.mp h0]
    exact ⟨le_rfl, by simp [minkowskiInner_explicit]⟩
  · have hb := mem_excitedMassSpectrum_bounds hm hM hex
    exact ⟨le_trans hm.le hb.1, le_trans (sq_nonneg m) hb.2⟩

lemma massGapSpectralRegion_subset_spectralRegion {m M : ℝ} (hm : 0 < m) (hM : m < M) (n : ℕ) :
    massGapSpectralRegion m M n ⊆ spectralRegion n := by
  intro p hp
  exact ⟨hp.1, fun k => massGapSpectrum_subset_closure_forward_light_cone hm hM (hp.2 k)⟩

def MassGapSpectrumCondition {ι : Type*} (m M : ℝ) (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ massGapSpectralRegion m M n ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier f p = 0) → W n α f = 0

theorem MassGapSpectrumCondition.toSpectrumCondition {ι : Type*}
    {m M : ℝ} (hm : 0 < m) (hM : m < M) {W : WightmanFamily ι}
    (hgap : MassGapSpectrumCondition m M W) :
    SpectrumCondition W := by
  intro n α f ⟨U, hU_open, hU_sub, hU_zero⟩
  exact hgap n α f ⟨U, hU_open,
    (massGapSpectralRegion_subset_spectralRegion hm hM n).trans hU_sub, hU_zero⟩

lemma left_castAdd_sum_mem_massGapSpectrum {m M : ℝ} {j k : ℕ} (hj : 0 < j)
    {p : Fin (j + k) → Fin 4 → ℝ} (hp : p ∈ massGapSpectralRegion m M (j + k)) :
    (∑ s : Fin j, p (Fin.castAdd k s)) ∈ massGapSpectrum m M := by
  let m₀ : Fin (j + k) := ⟨j - 1, by omega⟩
  have h_eq : (∑ s : Fin j, p (Fin.castAdd k s)) = partial_sum_p (j + k) p m₀ := by
    dsimp [partial_sum_p]
    rw [Finset.sum_filter, Fin.sum_univ_add]
    have h1 : (∑ s : Fin j, if Fin.castAdd k s ≤ m₀ then p (Fin.castAdd k s) else 0) =
        ∑ s : Fin j, p (Fin.castAdd k s) := by
      refine Finset.sum_congr rfl fun s _ => if_pos ?_
      rw [Fin.le_iff_val_le_val]
      dsimp [m₀]
      omega
    have h2 : (∑ u : Fin k, if Fin.natAdd j u ≤ m₀ then p (Fin.natAdd j u) else 0) = 0 := by
      refine Finset.sum_eq_zero fun u _ => if_neg ?_
      rw [Fin.le_iff_val_le_val]
      dsimp [m₀]
      omega
    rw [h1, h2, add_zero]
  rw [h_eq]
  exact hp.2 m₀

theorem wightmanSchwartzVec_eq_zero_of_fourier_zero_near_massGapSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {m M : ℝ}
    (hgap : MassGapSpectrumCondition m M WData.W) (k : ℕ) (α : Fin k → ι)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (hsupp : ∃ V : Set (Fin k → Fin 4 → ℝ), IsOpen V ∧
      { q : Fin k → Fin 4 → ℝ | -(∑ i : Fin k, q i) ∈ massGapSpectrum m M } ⊆ V ∧
      ∀ q ∈ V, minkowskiFourier F q = 0) :
    wightmanSchwartzVec WData k α F = 0 := by
  rcases hsupp with ⟨V, hV_open, hV_sub, hV_zero⟩
  by_cases hk : k = 0
  · subst hk
    have h0_mem : (0 : Fin 0 → Fin 4 → ℝ) ∈
        { q : Fin 0 → Fin 4 → ℝ | -(∑ i : Fin 0, q i) ∈ massGapSpectrum m M } := by
      simp only [Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty, neg_zero]
      exact zero_mem_massGapSpectrum m M
    have h0 : minkowskiFourier F 0 = 0 := hV_zero 0 (hV_sub h0_mem)
    have h_all : ∀ q : Fin 0 → Fin 4 → ℝ, minkowskiFourier F q =
        minkowskiFourier (0 : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) q := by
      intro q
      rw [Subsingleton.elim q 0, h0]
      simp [minkowskiFourier]
    have hF0 : F = 0 := minkowskiFourier_injective h_all
    rw [hF0, map_zero]
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    rw [← inner_self_eq_zero (𝕜 := ℂ), inner_wightmanSchwartzVec]
    refine Finset.sum_eq_zero fun β _ => ?_
    let π_L : (Fin (k + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) := -(concatProjLeftCLM k k)
    let U : Set (Fin (k + k) → Fin 4 → ℝ) := π_L ⁻¹' V
    have hU_open : IsOpen U := hV_open.preimage π_L.continuous
    have hU_sub : massGapSpectralRegion m M (k + k) ⊆ U := by
      intro p hp
      refine hV_sub ?_
      have h_sum_eq : -(∑ i : Fin k, π_L p i) = ∑ s : Fin k, p (Fin.castAdd k s) := by
        change -(∑ i : Fin k, -(p (Fin.castAdd k (Fin.rev i)))) = _
        simp only [Finset.sum_neg_distrib, neg_neg]
        exact Equiv.sum_comp Fin.revPerm (fun s : Fin k => p (Fin.castAdd k s))
      rw [Set.mem_setOf_eq, h_sum_eq]
      exact left_castAdd_sum_mem_massGapSpectrum hk_pos hp
    have hW0 : WData.W (k + k) (Fin.append (β ∘ Fin.rev) α)
        (borchersConcatSchwartz k k F F) = 0 := by
      refine hgap (k + k) (Fin.append (β ∘ Fin.rev) α) _ ⟨U, hU_open, hU_sub, fun p hp => ?_⟩
      rw [minkowskiFourier_borchersProduct_eq k k F F _
        (borchersConcatSchwartz_apply k k F F) p]
      have hL0 : minkowskiFourier F (fun i => -p (Fin.castAdd k (Fin.rev i))) = 0 :=
        hV_zero (π_L p) hp
      rw [hL0, star_zero, zero_mul]
    rw [hW0, mul_zero]

theorem wightmanSchwartzVec_eq_of_fourier_eq_near_massGapSpectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {m M : ℝ}
    (hgap : MassGapSpectrumCondition m M WData.W) (k : ℕ) (α : Fin k → ι)
    (F₁ F₂ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (h_eq : ∃ V : Set (Fin k → Fin 4 → ℝ), IsOpen V ∧
      { q : Fin k → Fin 4 → ℝ | -(∑ i : Fin k, q i) ∈ massGapSpectrum m M } ⊆ V ∧
      ∀ q ∈ V, minkowskiFourier F₁ q = minkowskiFourier F₂ q) :
    wightmanSchwartzVec WData k α F₁ = wightmanSchwartzVec WData k α F₂ := by
  rw [← sub_eq_zero, ← map_sub]
  rcases h_eq with ⟨V, hV_open, hV_sub, hV_eq⟩
  refine wightmanSchwartzVec_eq_zero_of_fourier_zero_near_massGapSpectrum WData hgap k α
    (F₁ - F₂) ⟨V, hV_open, hV_sub, fun q hq => ?_⟩
  rw [← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply, minkowskiFourierCLM_apply,
    minkowskiFourierCLM_apply, hV_eq q hq, sub_self]

structure IsolatedMassShellData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (m M : ℝ) (η : ℂ) where
  hm : 0 < m
  hM : m < M
  wightman : GeneralWightmanAxiomsWithUniqueVacuum R S η
  locality : LocalCommutativity η wightman.WData.W
  massGap : MassGapSpectrumCondition m M wightman.WData.W
  C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ
  hC : MassShellCoeffData m C_shell
  mode : MassShellModeData R S m η C_shell
  dual_w : Fin mode.ν → (Fin 3 → ℝ) → ι → ℂ
  contDiff_dual_w : ∀ (s : Fin mode.ν) (α : ι),
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => dual_w s p α)
  dual_orthonormal : ∀ (s₁ s₂ : Fin mode.ν) (p : Fin 3 → ℝ),
    ∑ α : ι, mode.w s₁ p α * dual_w s₂ p α = if s₁ = s₂ then 1 else 0
  twoPoint_shell : ∀ (β : Fin 2 → ι) (F : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
    (∃ U : Set (Fin 2 → Fin 4 → ℝ), IsOpen U ∧
      { p : Fin 2 → Fin 4 → ℝ |
          p 0 + p 1 = 0 ∧ (p 0 = 0 ∨ p 0 ∈ continuumCone M) } ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier F p = 0) →
    wightman.WData.W 2 β F = massShellTwoPointW m C_shell hC 2 β F

namespace IsolatedMassShellData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {m M : ℝ} {η : ℂ}

abbrev Hilbert (D : IsolatedMassShellData R S m M η) : Type _ :=
  WightmanHilbert D.wightman.WData

def vacuum (D : IsolatedMassShellData R S m M η) : D.Hilbert :=
  wightmanVacuum D.wightman.WData

def translate (D : IsolatedMassShellData R S m M η) (a : Fin 4 → ℝ) :
    D.Hilbert →L[ℂ] D.Hilbert :=
  wightmanTranslate D.wightman.WData D.wightman.translationInvariant a

theorem permLocality (D : IsolatedMassShellData R S m M η) :
    PermSpacelikeLocality η D.wightman.WData.W :=
  PermSpacelikeLocality.of_localCommutativity D.locality

@[simp]
theorem inner_vacuum_self (D : IsolatedMassShellData R S m M η) :
    ⟪D.vacuum, D.vacuum⟫_ℂ = 1 :=
  inner_wightmanVacuum_self_of_normalized D.wightman.WData D.wightman.vacuumNormalized

@[simp]
theorem norm_vacuum (D : IsolatedMassShellData R S m M η) :
    ‖D.vacuum‖ = 1 :=
  norm_wightmanVacuum_of_normalized D.wightman.WData D.wightman.vacuumNormalized

theorem eq_smul_vacuum_of_translate_fixed (D : IsolatedMassShellData R S m M η)
    {Ψ : D.Hilbert} (hfixed : ∀ a : Fin 4 → ℝ, D.translate a Ψ = Ψ) :
    Ψ = ⟪D.vacuum, Ψ⟫_ℂ • D.vacuum :=
  D.wightman.vacuumUnique Ψ hfixed

end IsolatedMassShellData

def prependHeadLM (k : ℕ) :
    (Fin (k + 1) → Fin 4 → ℝ) →ₗ[ℝ] (Fin 1 → Fin 4 → ℝ) where
  toFun x _ := x 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def prependHeadCLM (k : ℕ) :
    (Fin (k + 1) → Fin 4 → ℝ) →L[ℝ] (Fin 1 → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (prependHeadLM k)

@[simp]
lemma prependHeadCLM_apply (k : ℕ) (x : Fin (k + 1) → Fin 4 → ℝ) (i : Fin 1) :
    prependHeadCLM k x i = x 0 := rfl

lemma opNorm_prependHeadCLM_le_one (k : ℕ) : ‖prependHeadCLM k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun _ => ?_
  exact norm_le_pi_norm x 0

def prependTailLM (k : ℕ) :
    (Fin (k + 1) → Fin 4 → ℝ) →ₗ[ℝ] (Fin k → Fin 4 → ℝ) where
  toFun x u := x (Fin.succ u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def prependTailCLM (k : ℕ) :
    (Fin (k + 1) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (prependTailLM k)

@[simp]
lemma prependTailCLM_apply (k : ℕ) (x : Fin (k + 1) → Fin 4 → ℝ) (u : Fin k) :
    prependTailCLM k x u = x (Fin.succ u) := rfl

lemma opNorm_prependTailCLM_le_one (k : ℕ) : ‖prependTailCLM k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun u => ?_
  exact norm_le_pi_norm x (Fin.succ u)

lemma norm_le_max_prependCLM (k : ℕ) (x : Fin (k + 1) → Fin 4 → ℝ) :
    ‖x‖ ≤ max ‖prependHeadCLM k x‖ ‖prependTailCLM k x‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr fun i => ?_
  refine Fin.cases ?_ ?_ i
  · exact (norm_le_pi_norm (prependHeadCLM k x) 0).trans (le_max_left _ _)
  · intro u
    exact (norm_le_pi_norm (prependTailCLM k x) u).trans (le_max_right _ _)

lemma norm_pow_le_add_prependCLM (k l : ℕ) (x : Fin (k + 1) → Fin 4 → ℝ) :
    ‖x‖ ^ l ≤ ‖prependHeadCLM k x‖ ^ l + ‖prependTailCLM k x‖ ^ l := by
  have h1 := pow_le_pow_left₀ (norm_nonneg x) (norm_le_max_prependCLM k x) l
  rcases le_total ‖prependHeadCLM k x‖ ‖prependTailCLM k x‖ with hle | hle
  · rw [max_eq_right hle] at h1
    exact h1.trans (le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) l))
  · rw [max_eq_left hle] at h1
    exact h1.trans (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) l))

lemma norm_iteratedFDeriv_comp_prependHead_le (k : ℕ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (l q : ℕ) (x : Fin (k + 1) → Fin 4 → ℝ) :
    ‖prependHeadCLM k x‖ ^ l *
      ‖iteratedFDeriv ℝ q
        (fun y : Fin (k + 1) → Fin 4 → ℝ => ψ (prependHeadCLM k y)) x‖ ≤
      SchwartzMap.seminorm ℝ l q ψ := by
  let L := prependHeadCLM k
  have hψ_sm : ContDiff ℝ (q : ℕ∞) (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) :=
    (ψ.smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
  have h_fn : (fun y : Fin (k + 1) → Fin 4 → ℝ => ψ (L y)) =
      (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) ∘ L := rfl
  rw [h_fn, L.iteratedFDeriv_comp_right hψ_sm x le_rfl]
  have h_c2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ q (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) (L x)) (fun _ : Fin q => L)
  have h_prod : (∏ _ : Fin q, ‖L‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg L) (fun _ _ => opNorm_prependHeadCLM_le_one k)
  have h_le : ‖(iteratedFDeriv ℝ q (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) (L x)).compContinuousLinearMap
      (fun _ : Fin q => L)‖ ≤
      ‖iteratedFDeriv ℝ q (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) (L x)‖ := by
    have h_pnn : 0 ≤ ∏ _ : Fin q, ‖L‖ := Finset.prod_nonneg fun _ _ => norm_nonneg L
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) (L x))]
  calc ‖L x‖ ^ l * ‖(iteratedFDeriv ℝ q (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) (L x)
          ).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖L x‖ ^ l * ‖iteratedFDeriv ℝ q (ψ : (Fin 1 → Fin 4 → ℝ) → ℂ) (L x)‖ :=
        mul_le_mul_of_nonneg_left h_le (pow_nonneg (norm_nonneg _) l)
    _ ≤ SchwartzMap.seminorm ℝ l q ψ := SchwartzMap.le_seminorm ℝ l q ψ (L x)

lemma norm_iteratedFDeriv_comp_prependTail_le (k : ℕ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (l q : ℕ) (x : Fin (k + 1) → Fin 4 → ℝ) :
    ‖prependTailCLM k x‖ ^ l *
      ‖iteratedFDeriv ℝ q
        (fun y : Fin (k + 1) → Fin 4 → ℝ => F (prependTailCLM k y)) x‖ ≤
      SchwartzMap.seminorm ℝ l q F := by
  let L := prependTailCLM k
  have hF_sm : ContDiff ℝ (q : ℕ∞) (F : (Fin k → Fin 4 → ℝ) → ℂ) :=
    (F.smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
  have h_fn : (fun y : Fin (k + 1) → Fin 4 → ℝ => F (L y)) =
      (F : (Fin k → Fin 4 → ℝ) → ℂ) ∘ L := rfl
  rw [h_fn, L.iteratedFDeriv_comp_right hF_sm x le_rfl]
  have h_c2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ q (F : (Fin k → Fin 4 → ℝ) → ℂ) (L x)) (fun _ : Fin q => L)
  have h_prod : (∏ _ : Fin q, ‖L‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg L) (fun _ _ => opNorm_prependTailCLM_le_one k)
  have h_le : ‖(iteratedFDeriv ℝ q (F : (Fin k → Fin 4 → ℝ) → ℂ) (L x)).compContinuousLinearMap
      (fun _ : Fin q => L)‖ ≤
      ‖iteratedFDeriv ℝ q (F : (Fin k → Fin 4 → ℝ) → ℂ) (L x)‖ := by
    have h_pnn : 0 ≤ ∏ _ : Fin q, ‖L‖ := Finset.prod_nonneg fun _ _ => norm_nonneg L
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (F : (Fin k → Fin 4 → ℝ) → ℂ) (L x))]
  calc ‖L x‖ ^ l * ‖(iteratedFDeriv ℝ q (F : (Fin k → Fin 4 → ℝ) → ℂ) (L x)
          ).compContinuousLinearMap (fun _ => L)‖
      ≤ ‖L x‖ ^ l * ‖iteratedFDeriv ℝ q (F : (Fin k → Fin 4 → ℝ) → ℂ) (L x)‖ :=
        mul_le_mul_of_nonneg_left h_le (pow_nonneg (norm_nonneg _) l)
    _ ≤ SchwartzMap.seminorm ℝ l q F := SchwartzMap.le_seminorm ℝ l q F (L x)

def schwartzPrepend (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ where
  toFun x := ψ (prependHeadCLM k x) * F (prependTailCLM k x)
  smooth' :=
    ((ψ.smooth ⊤).comp (prependHeadCLM k).contDiff).mul
      ((F.smooth ⊤).comp (prependTailCLM k).contDiff)
  decay' l d := by
    let B_val : ℝ := ∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
      (SchwartzMap.seminorm ℝ l q ψ * SchwartzMap.seminorm ℝ 0 (d - q) F +
        SchwartzMap.seminorm ℝ 0 q ψ * SchwartzMap.seminorm ℝ l (d - q) F)
    refine ⟨B_val, fun x => ?_⟩
    let ψL : (Fin (k + 1) → Fin 4 → ℝ) → ℂ := fun y => ψ (prependHeadCLM k y)
    let FR : (Fin (k + 1) → Fin 4 → ℝ) → ℂ := fun y => F (prependTailCLM k y)
    have hψL_sm : ContDiff ℝ (⊤ : ℕ∞) ψL := (ψ.smooth ⊤).comp (prependHeadCLM k).contDiff
    have hFR_sm : ContDiff ℝ (⊤ : ℕ∞) FR := (F.smooth ⊤).comp (prependTailCLM k).contDiff
    have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ψL) (g := FR) (n := d)
      (N := (⊤ : ℕ∞)) hψL_sm hFR_sm x (WithTop.coe_le_coe.mpr le_top)
    have h_pow := norm_pow_le_add_prependCLM k l x
    calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ d (fun y => ψL y * FR y) x‖
        ≤ (‖prependHeadCLM k x‖ ^ l + ‖prependTailCLM k x‖ ^ l) *
            ∑ q ∈ Finset.range (d + 1),
              (d.choose q : ℝ) * ‖iteratedFDeriv ℝ q ψL x‖ * ‖iteratedFDeriv ℝ (d - q) FR x‖ :=
          mul_le_mul h_pow h_leib (norm_nonneg _)
            (add_nonneg (pow_nonneg (norm_nonneg _) l) (pow_nonneg (norm_nonneg _) l))
      _ = ∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
            ((‖prependHeadCLM k x‖ ^ l * ‖iteratedFDeriv ℝ q ψL x‖) *
              (‖prependTailCLM k x‖ ^ 0 * ‖iteratedFDeriv ℝ (d - q) FR x‖) +
            (‖prependHeadCLM k x‖ ^ 0 * ‖iteratedFDeriv ℝ q ψL x‖) *
              (‖prependTailCLM k x‖ ^ l * ‖iteratedFDeriv ℝ (d - q) FR x‖)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [pow_zero, one_mul]
          ring
      _ ≤ B_val := by
          refine Finset.sum_le_sum fun q _ => ?_
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Nat.cast_nonneg _)
          · exact mul_le_mul
              (norm_iteratedFDeriv_comp_prependHead_le k ψ l q x)
              (norm_iteratedFDeriv_comp_prependTail_le k F 0 (d - q) x)
              (by positivity) (apply_nonneg _ _)
          · exact mul_le_mul
              (norm_iteratedFDeriv_comp_prependHead_le k ψ 0 q x)
              (norm_iteratedFDeriv_comp_prependTail_le k F l (d - q) x)
              (by positivity) (apply_nonneg _ _)

@[simp]
lemma schwartzPrepend_apply (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x : Fin (k + 1) → Fin 4 → ℝ) :
    schwartzPrepend k ψ F x = ψ (fun _ => x 0) * F (fun u => x (Fin.succ u)) := rfl

lemma seminorm_schwartzPrepend_le (k l d : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ l d (schwartzPrepend k ψ F) ≤
      ∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
        (SchwartzMap.seminorm ℝ l q ψ * SchwartzMap.seminorm ℝ 0 (d - q) F +
          SchwartzMap.seminorm ℝ 0 q ψ * SchwartzMap.seminorm ℝ l (d - q) F) := by
  let B_val : ℝ := ∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
    (SchwartzMap.seminorm ℝ l q ψ * SchwartzMap.seminorm ℝ 0 (d - q) F +
      SchwartzMap.seminorm ℝ 0 q ψ * SchwartzMap.seminorm ℝ l (d - q) F)
  have hB_nn : 0 ≤ B_val := Finset.sum_nonneg fun q _ =>
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
        (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  refine SchwartzMap.seminorm_le_bound ℝ l d (schwartzPrepend k ψ F) hB_nn fun x => ?_
  let ψL : (Fin (k + 1) → Fin 4 → ℝ) → ℂ := fun y => ψ (prependHeadCLM k y)
  let FR : (Fin (k + 1) → Fin 4 → ℝ) → ℂ := fun y => F (prependTailCLM k y)
  have hψL_sm : ContDiff ℝ (⊤ : ℕ∞) ψL := (ψ.smooth ⊤).comp (prependHeadCLM k).contDiff
  have hFR_sm : ContDiff ℝ (⊤ : ℕ∞) FR := (F.smooth ⊤).comp (prependTailCLM k).contDiff
  have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ψL) (g := FR) (n := d)
    (N := (⊤ : ℕ∞)) hψL_sm hFR_sm x (WithTop.coe_le_coe.mpr le_top)
  have h_pow := norm_pow_le_add_prependCLM k l x
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ d (schwartzPrepend k ψ F :
          (Fin (k + 1) → Fin 4 → ℝ) → ℂ) x‖
      ≤ (‖prependHeadCLM k x‖ ^ l + ‖prependTailCLM k x‖ ^ l) *
          ∑ q ∈ Finset.range (d + 1),
            (d.choose q : ℝ) * ‖iteratedFDeriv ℝ q ψL x‖ * ‖iteratedFDeriv ℝ (d - q) FR x‖ :=
        mul_le_mul h_pow h_leib (norm_nonneg _)
          (add_nonneg (pow_nonneg (norm_nonneg _) l) (pow_nonneg (norm_nonneg _) l))
    _ = ∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
          ((‖prependHeadCLM k x‖ ^ l * ‖iteratedFDeriv ℝ q ψL x‖) *
            (‖prependTailCLM k x‖ ^ 0 * ‖iteratedFDeriv ℝ (d - q) FR x‖) +
          (‖prependHeadCLM k x‖ ^ 0 * ‖iteratedFDeriv ℝ q ψL x‖) *
            (‖prependTailCLM k x‖ ^ l * ‖iteratedFDeriv ℝ (d - q) FR x‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [pow_zero, one_mul]
        ring
    _ ≤ B_val := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Nat.cast_nonneg _)
        · exact mul_le_mul
            (norm_iteratedFDeriv_comp_prependHead_le k ψ l q x)
            (norm_iteratedFDeriv_comp_prependTail_le k F 0 (d - q) x)
            (by positivity) (apply_nonneg _ _)
        · exact mul_le_mul
            (norm_iteratedFDeriv_comp_prependHead_le k ψ 0 q x)
            (norm_iteratedFDeriv_comp_prependTail_le k F l (d - q) x)
            (by positivity) (apply_nonneg _ _)

@[simp]
lemma schwartzPrepend_zero_left (k : ℕ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k 0 F = 0 := by
  ext x
  simp

@[simp]
lemma schwartzPrepend_zero_right (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k ψ 0 = 0 := by
  ext x
  simp

lemma schwartzPrepend_add_left (k : ℕ) (ψ₁ ψ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k (ψ₁ + ψ₂) F = schwartzPrepend k ψ₁ F + schwartzPrepend k ψ₂ F := by
  ext x
  simp [add_mul]

lemma schwartzPrepend_add_right (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F₁ F₂ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k ψ (F₁ + F₂) = schwartzPrepend k ψ F₁ + schwartzPrepend k ψ F₂ := by
  ext x
  simp [mul_add]

lemma schwartzPrepend_sub_left (k : ℕ) (ψ₁ ψ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k (ψ₁ - ψ₂) F = schwartzPrepend k ψ₁ F - schwartzPrepend k ψ₂ F := by
  ext x
  simp [sub_mul]

lemma schwartzPrepend_sub_right (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F₁ F₂ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k ψ (F₁ - F₂) = schwartzPrepend k ψ F₁ - schwartzPrepend k ψ F₂ := by
  ext x
  simp [mul_sub]

lemma schwartzPrepend_smul_left (k : ℕ) (c : ℂ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k (c • ψ) F = c • schwartzPrepend k ψ F := by
  ext x
  simp [mul_assoc]

lemma schwartzPrepend_smul_right (k : ℕ) (c : ℂ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k ψ (c • F) = c • schwartzPrepend k ψ F := by
  ext x
  simp [mul_left_comm]

@[simp]
lemma momentumWavepacketSchwartz_zero_zero_apply (x : Fin 0 → Fin 4 → ℝ) :
    momentumWavepacketSchwartz 0 0 x = 1 := by
  have h1 := integral_momentumWavepacketSchwartz_zero 0
  rw [integral_fin0] at h1
  rwa [Subsingleton.elim x 0]

@[simp]
lemma schwartzPrepend_zero_vac (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzPrepend 0 ψ (momentumWavepacketSchwartz 0 0) = ψ := by
  ext x
  rw [schwartzPrepend_apply, momentumWavepacketSchwartz_zero_zero_apply, mul_one]
  have h_eq : (fun _ : Fin 1 => x 0) = x := by
    ext i
    rw [Subsingleton.elim i 0]
  rw [h_eq]

lemma minkowskiFourier_schwartzPrepend (k : ℕ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (q : Fin (k + 1) → Fin 4 → ℝ) :
    minkowskiFourier (schwartzPrepend k ψ F) q =
      minkowskiFourier ψ (fun _ => q 0) * minkowskiFourier F (fun u => q (Fin.succ u)) := by
  let e_split := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => Fin 4 → ℝ) 0).symm
  let mp_split := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => Fin 4 → ℝ) 0).symm
  let eu := (MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ)).symm
  let mp_u := (volume_preserving_funUnique (Fin 1) (Fin 4 → ℝ)).symm
  let G_full : (Fin (k + 1) → Fin 4 → ℝ) → ℂ := fun x =>
    schwartzPrepend k ψ F x *
      Complex.exp (-(Complex.I * ((∑ i : Fin (k + 1), minkowskiInner (q i) (x i) : ℝ) : ℂ)))
  let A_fn : (Fin 4 → ℝ) → ℂ := fun y =>
    ψ (fun _ => y) * Complex.exp (-(Complex.I * ((minkowskiInner (q 0) y : ℝ) : ℂ)))
  let B_fn : (Fin k → Fin 4 → ℝ) → ℂ := fun z =>
    F z * Complex.exp (-(Complex.I *
      ((∑ u : Fin k, minkowskiInner (q (Fin.succ u)) (z u) : ℝ) : ℂ)))
  have h_comp : (fun p : (Fin 4 → ℝ) × (Fin k → Fin 4 → ℝ) => G_full (e_split p)) =
      fun p => A_fn p.1 * B_fn p.2 := by
    ext ⟨y, z⟩
    have hy : e_split (y, z) 0 = y := by
      simp [e_split, MeasurableEquiv.piFinSuccAbove]
    have hz : (fun u : Fin k => e_split (y, z) (Fin.succ u)) = z := by
      ext u
      simp [e_split, MeasurableEquiv.piFinSuccAbove]
    have hz_pt : ∀ u : Fin k, e_split (y, z) (Fin.succ u) = z u := congr_fun hz
    dsimp [G_full, A_fn, B_fn]
    rw [hy, hz, Fin.sum_univ_succ]
    simp only [hy, hz_pt]
    have h_exp :
        -(Complex.I *
            ((minkowskiInner (q 0) y +
              ∑ u : Fin k, minkowskiInner (q (Fin.succ u)) (z u) : ℝ) : ℂ)) =
          (-(Complex.I * ((minkowskiInner (q 0) y : ℝ) : ℂ))) +
            (-(Complex.I *
              ((∑ u : Fin k, minkowskiInner (q (Fin.succ u)) (z u) : ℝ) : ℂ))) := by
      push_cast
      ring
    rw [h_exp, Complex.exp_add]
    ring
  have h_lhs : minkowskiFourier (schwartzPrepend k ψ F) q =
      (∫ y : Fin 4 → ℝ, A_fn y) * (∫ z : Fin k → Fin 4 → ℝ, B_fn z) := by
    change ∫ x : Fin (k + 1) → Fin 4 → ℝ, G_full x = _
    rw [← mp_split.integral_comp e_split.measurableEmbedding, h_comp,
      MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul]
  have h_A : minkowskiFourier ψ (fun _ => q 0) = ∫ y : Fin 4 → ℝ, A_fn y := by
    refine Eq.trans (mp_u.integral_comp eu.measurableEmbedding
      (fun x : Fin 1 → Fin 4 → ℝ =>
        ψ x * Complex.exp (-(Complex.I *
          ((∑ i : Fin 1, minkowskiInner (q 0) (x i) : ℝ) : ℂ))))).symm ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have h_eu_val : eu y = fun _ : Fin 1 => y := by
      ext i μ
      rw [Subsingleton.elim i 0]
      rfl
    dsimp [A_fn]
    rw [h_eu_val, Fin.sum_univ_one]
  rw [h_lhs, h_A]
  rfl

lemma minkowskiFourier_schwartzConj_one
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (q : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (schwartzConj ψ) q = star (minkowskiFourier ψ (-q)) := by
  symm
  rw [minkowskiFourier, minkowskiFourier, Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [schwartzConj_apply, Complex.star_def, map_mul, ← Complex.exp_conj]
  congr 2
  simp only [Fin.sum_univ_one, Pi.neg_apply, minkowskiInner_explicit, neg_mul,
    map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

abbrev IndexedSchwartz (ι : Type*) (k : ℕ) : Type _ :=
  (Fin k → ι) → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ

def vacuumIndexedSchwartz (ι : Type*) : IndexedSchwartz ι 0 :=
  fun _ => momentumWavepacketSchwartz 0 0

def translateIndexedSchwartz {ι : Type*} (k : ℕ) (a : Fin 4 → ℝ)
    (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι k :=
  fun α => schwartzDiagTranslateN k a (Φ α)

def indexedPrepend {ι : Type*} (k : ℕ) (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι (k + 1) :=
  fun γ => schwartzPrepend k (Ψ (γ 0)) (Φ (Fin.tail γ))

lemma wightman_congr_eq {ι : Type*} {n₁ n₂ : ℕ} (h : n₁ = n₂) (W : WightmanFamily ι)
    (α₁ : Fin n₁ → ι) (f₁ : SchwartzMap (Fin n₁ → Fin 4 → ℝ) ℂ)
    (α₂ : Fin n₂ → ι) (f₂ : SchwartzMap (Fin n₂ → Fin 4 → ℝ) ℂ)
    (hα : ∀ i : Fin n₁, α₁ i = α₂ (Fin.cast h i))
    (hf : ∀ x : Fin n₂ → Fin 4 → ℝ, f₁ (fun i => x (Fin.cast h i)) = f₂ x) :
    W n₁ α₁ f₁ = W n₂ α₂ f₂ := by
  subst h
  have hα' : α₁ = α₂ := funext hα
  have hf' : f₁ = f₂ := by
    ext x
    exact hf x
  subst hα' hf'
  rfl

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wightmanIndexedVec {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (k : ℕ) (Φ : IndexedSchwartz ι k) :
    WightmanHilbert WData :=
  ∑ α : Fin k → ι, wightmanSchwartzVec WData k α (Φ α)

@[simp]
lemma wightmanIndexedVec_vacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanIndexedVec WData 0 (vacuumIndexedSchwartz ι) = wightmanVacuum WData := by
  unfold wightmanIndexedVec vacuumIndexedSchwartz
  rw [Fintype.sum_eq_single Fin.elim0 fun α hne => False.elim (hne (Subsingleton.elim _ _))]
  exact wightmanSchwartzVec_compact WData 0 Fin.elim0 (momentumWavepacketCompactSchwartz 0 0)

theorem wightmanTranslate_wightmanIndexedVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 4 → ℝ) (k : ℕ) (Φ : IndexedSchwartz ι k) :
    wightmanTranslate WData htrans a (wightmanIndexedVec WData k Φ) =
      wightmanIndexedVec WData k (translateIndexedSchwartz k a Φ) := by
  unfold wightmanIndexedVec translateIndexedSchwartz
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact wightmanTranslate_wightmanSchwartzVec WData htrans a k α (Φ α)

def starIndexedTest {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun β₀ => ∑ α₀ : ι, S.C α₀ β₀ • schwartzConj (Ψ α₀)

lemma starIndexedTest_involutive {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    starIndexedTest S (starIndexedTest S Ψ) = Ψ := by
  ext β₀ x
  unfold starIndexedTest
  rw [schwartzMap_sum_apply]
  have h_sum_star :
      (∑ α₀ : ι, (S.C α₀ β₀ • schwartzConj (∑ γ : ι, S.C γ α₀ • schwartzConj (Ψ γ))) x) =
        ∑ α₀ : ι, ∑ γ : ι, S.C α₀ β₀ * (star (S.C γ α₀) * Ψ γ x) := by
    refine Finset.sum_congr rfl fun α₀ _ => ?_
    rw [_root_.smul_apply, smul_eq_mul, schwartzConj_apply, schwartzMap_sum_apply,
      Complex.star_def, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [_root_.smul_apply, smul_eq_mul, schwartzConj_apply, Complex.star_def,
      map_mul, starRingEnd_self_apply, ← Complex.star_def]
  rw [h_sum_star, Finset.sum_comm]
  have h_orth :
      (∑ γ : ι, ∑ α₀ : ι, S.C α₀ β₀ * (star (S.C γ α₀) * Ψ γ x)) =
        ∑ γ : ι, ((S.C.map star * S.C) γ β₀) * Ψ γ x := by
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α₀ _ => ?_
    simp only [Matrix.map_apply]
    ring
  rw [h_orth]
  have h_id : S.C.map star * S.C = 1 := mul_eq_one_comm.mp S.involutive
  rw [h_id]
  simp [Matrix.one_apply]

theorem inner_wightmanIndexedVec_indexedPrepend
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j k : ℕ)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Φ₁ : IndexedSchwartz ι j) (Φ₂ : IndexedSchwartz ι k) :
    ⟪wightmanIndexedVec WData (j + 1) (indexedPrepend j Ψ Φ₁),
      wightmanIndexedVec WData k Φ₂⟫_ℂ =
    ⟪wightmanIndexedVec WData j Φ₁,
      wightmanIndexedVec WData (k + 1)
        (indexedPrepend k (starIndexedTest S Ψ) Φ₂)⟫_ℂ := by
  unfold wightmanIndexedVec
  rw [sum_inner, ← (Fin.consEquiv (fun _ : Fin (j + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  have h_ce : ∀ (a : ι) (b : Fin j → ι),
      Fin.consEquiv (fun _ : Fin (j + 1) => ι) (a, b) = Fin.cons a b := fun _ _ => rfl
  simp_rw [h_ce]
  have h_lhs :
      (∑ γ₀ : ι, ∑ γ' : Fin j → ι,
        ⟪wightmanSchwartzVec WData (j + 1) (Fin.cons γ₀ γ')
            (indexedPrepend j Ψ Φ₁ (Fin.cons γ₀ γ')),
          ∑ α' : Fin k → ι, wightmanSchwartzVec WData k α' (Φ₂ α')⟫_ℂ) =
      ∑ γ₀ : ι, ∑ γ' : Fin j → ι, ∑ α' : Fin k → ι, ∑ β₀ : ι, ∑ β' : Fin j → ι,
        (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
          WData.W ((j + 1) + k) (Fin.append ((Fin.cons β₀ β') ∘ Fin.rev) α')
            (borchersConcatSchwartz (j + 1) k (schwartzPrepend j (Ψ γ₀) (Φ₁ γ')) (Φ₂ α')) := by
    refine Finset.sum_congr rfl fun γ₀ _ => Finset.sum_congr rfl fun γ' _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun α' _ => ?_
    rw [inner_wightmanSchwartzVec,
      ← (Fin.consEquiv (fun _ : Fin (j + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    simp_rw [h_ce]
    refine Finset.sum_congr rfl fun β₀ _ => Finset.sum_congr rfl fun β' _ => ?_
    have h_prod : (∏ i : Fin (j + 1),
        S.C ((Fin.cons γ₀ γ' : Fin (j + 1) → ι) i) ((Fin.cons β₀ β' : Fin (j + 1) → ι) i)) =
        S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s) := by
      rw [Fin.prod_univ_succ]
      simp
    have h_ind : indexedPrepend j Ψ Φ₁ (Fin.cons γ₀ γ') = schwartzPrepend j (Ψ γ₀) (Φ₁ γ') := by
      dsimp [indexedPrepend]
      rfl
    rw [h_prod, h_ind]
  rw [h_lhs]
  symm
  rw [sum_inner]
  have h_rhs :
      (∑ γ' : Fin j → ι,
        ⟪wightmanSchwartzVec WData j γ' (Φ₁ γ'),
          ∑ δ : Fin (k + 1) → ι, wightmanSchwartzVec WData (k + 1) δ
            (indexedPrepend k (starIndexedTest S Ψ) Φ₂ δ)⟫_ℂ) =
      ∑ γ₀ : ι, ∑ γ' : Fin j → ι, ∑ α' : Fin k → ι, ∑ β₀ : ι, ∑ β' : Fin j → ι,
        (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
          WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
            (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
              (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α'))) := by
    have h_step1 :
        (∑ γ' : Fin j → ι,
          ⟪wightmanSchwartzVec WData j γ' (Φ₁ γ'),
            ∑ δ : Fin (k + 1) → ι, wightmanSchwartzVec WData (k + 1) δ
              (indexedPrepend k (starIndexedTest S Ψ) Φ₂ δ)⟫_ℂ) =
        ∑ γ' : Fin j → ι, ∑ β₀ : ι, ∑ α' : Fin k → ι, ∑ β' : Fin j → ι, ∑ γ₀ : ι,
          (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
            WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
              (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α'))) := by
      refine Finset.sum_congr rfl fun γ' _ => ?_
      rw [inner_sum, ← (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).sum_comp, Fintype.sum_prod_type]
      have h_cek : ∀ (a : ι) (b : Fin k → ι),
          Fin.consEquiv (fun _ : Fin (k + 1) => ι) (a, b) = Fin.cons a b := fun _ _ => rfl
      simp_rw [h_cek]
      refine Finset.sum_congr rfl fun β₀ _ => Finset.sum_congr rfl fun α' _ => ?_
      rw [inner_wightmanSchwartzVec]
      refine Finset.sum_congr rfl fun β' _ => ?_
      have h_prep : indexedPrepend k (starIndexedTest S Ψ) Φ₂ (Fin.cons β₀ α') =
          ∑ γ₀ : ι, S.C γ₀ β₀ • schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α') := by
        unfold indexedPrepend starIndexedTest
        ext y
        simp [Finset.sum_mul, mul_assoc]
      rw [h_prep, borchersConcatSchwartz_sum_right, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ₀ _ => ?_
      rw [borchersConcatSchwartz_smul_right, map_smul, smul_eq_mul]
      ring
    rw [h_step1]
    have h_s1 :
        (∑ γ' : Fin j → ι, ∑ β₀ : ι, ∑ α' : Fin k → ι, ∑ β' : Fin j → ι, ∑ γ₀ : ι,
          (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
            WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
              (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α')))) =
        ∑ γ' : Fin j → ι, ∑ γ₀ : ι, ∑ α' : Fin k → ι, ∑ β₀ : ι, ∑ β' : Fin j → ι,
          (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
            WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
              (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α'))) := by
      refine Finset.sum_congr rfl fun γ' _ => ?_
      rw [Finset.sum_comm]
      have h_inner : ∀ α' : Fin k → ι,
          (∑ β₀ : ι, ∑ β' : Fin j → ι, ∑ γ₀ : ι,
            (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
              WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
                (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                  (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α')))) =
          ∑ γ₀ : ι, ∑ β₀ : ι, ∑ β' : Fin j → ι,
            (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
              WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
                (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                  (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α'))) := by
        intro α'
        have h_b : ∀ β₀ : ι,
            (∑ β' : Fin j → ι, ∑ γ₀ : ι,
              (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
                WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
                  (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                    (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α')))) =
            ∑ γ₀ : ι, ∑ β' : Fin j → ι,
              (S.C γ₀ β₀ * ∏ s : Fin j, S.C (γ' s) (β' s)) *
                WData.W (j + (k + 1)) (Fin.append (β' ∘ Fin.rev) (Fin.cons β₀ α'))
                  (borchersConcatSchwartz j (k + 1) (Φ₁ γ')
                    (schwartzPrepend k (schwartzConj (Ψ γ₀)) (Φ₂ α'))) :=
          fun _ => Finset.sum_comm
        simp_rw [h_b]
        exact Finset.sum_comm
      simp_rw [h_inner]
      exact Finset.sum_comm
    rw [h_s1, Finset.sum_comm]
  rw [h_rhs]
  refine Finset.sum_congr rfl fun γ₀ _ => Finset.sum_congr rfl fun γ' _ =>
    Finset.sum_congr rfl fun α' _ => Finset.sum_congr rfl fun β₀ _ =>
      Finset.sum_congr rfl fun β' _ => ?_
  congr 1
  have h_len : j + (k + 1) = (j + 1) + k := by omega
  refine wightman_congr_eq h_len WData.W _ _ _ _ (fun i => ?_) (fun x => ?_)
  · refine Fin.addCases (fun s => ?_) (fun u => ?_) i
    · have h_cast : Fin.cast h_len (Fin.castAdd (k + 1) s) =
          Fin.castAdd k (Fin.castAdd 1 s) := by
        ext; rfl
      rw [h_cast, Fin.append_left, Fin.append_left]
      have h_rev : Fin.rev (Fin.castAdd 1 s) = Fin.succ (Fin.rev s) := by
        ext
        simp only [Fin.val_rev, Fin.val_castAdd, Fin.val_succ]
        omega
      change β' (Fin.rev s) =
        (Fin.cons β₀ β' : Fin (j + 1) → ι) (Fin.rev (Fin.castAdd 1 s))
      rw [h_rev]
      rfl
    · refine Fin.cases ?_ ?_ u
      · have h_cast : Fin.cast h_len (Fin.natAdd j 0) = Fin.castAdd k (Fin.last j) := by
          ext; simp
        rw [h_cast, Fin.append_right, Fin.append_left]
        have h_rev : Fin.rev (Fin.last j) = 0 := by
          ext; simp
        change (Fin.cons β₀ α' : Fin (k + 1) → ι) 0 =
          (Fin.cons β₀ β' : Fin (j + 1) → ι) (Fin.rev (Fin.last j))
        rw [h_rev]
        rfl
      · intro v
        have h_cast : Fin.cast h_len (Fin.natAdd j (Fin.succ v)) = Fin.natAdd (j + 1) v := by
          ext; simp; omega
        rw [h_cast, Fin.append_right, Fin.append_right]
        rfl
  · rw [borchersConcatSchwartz_apply, borchersConcatSchwartz_apply,
      schwartzPrepend_apply, schwartzPrepend_apply, schwartzConj_apply]
    have h_L : (fun s : Fin j => x (Fin.cast h_len (Fin.castAdd (k + 1) (Fin.rev s)))) =
        fun s : Fin j => x (Fin.castAdd k (Fin.rev (Fin.succ s))) := by
      ext s μ
      have h_eq_idx : Fin.cast h_len (Fin.castAdd (k + 1) (Fin.rev s)) =
          Fin.castAdd k (Fin.rev (Fin.succ s)) := by
        ext
        simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_rev, Fin.val_succ]
        omega
      rw [h_eq_idx]
    have h_M : (fun _ : Fin 1 => x (Fin.cast h_len (Fin.natAdd j 0))) =
        fun _ : Fin 1 => x (Fin.castAdd k (Fin.rev 0)) := by
      ext i μ
      have h_eq_idx : Fin.cast h_len (Fin.natAdd j 0) = Fin.castAdd k (Fin.rev 0) := by
        ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_zero, add_zero, Fin.val_castAdd,
          Fin.val_rev]
        omega
      rw [h_eq_idx]
    have h_R : (fun u : Fin k => x (Fin.cast h_len (Fin.natAdd j (Fin.succ u)))) =
        fun u : Fin k => x (Fin.natAdd (j + 1) u) := by
      ext u μ
      have h_eq_idx : Fin.cast h_len (Fin.natAdd j (Fin.succ u)) = Fin.natAdd (j + 1) u := by
        ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
        omega
      rw [h_eq_idx]
    rw [h_L, h_M, h_R]
    change star (Φ₁ γ' _) * (star (Ψ γ₀ _) * Φ₂ α' _) =
      star (Ψ γ₀ _ * Φ₁ γ' _) * Φ₂ α' _
    rw [star_mul']
    ring

theorem wightmanIndexedVec_indexedPrepend_swap_of_spacelike
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {η : ℂ} (hloc : LocalCommutativity η WData.W)
    (Ψ₁ Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hsp : ∀ (α₁ α₂ : ι) (x₁ : Fin 1 → Fin 4 → ℝ) (x₂ : Fin 1 → Fin 4 → ℝ),
      x₁ ∈ tsupport (Ψ₁ α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      x₂ ∈ tsupport (Ψ₂ α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      is_spacelike (x₁ 0 - x₂ 0))
    (k : ℕ) (Φ : IndexedSchwartz ι k) :
    wightmanIndexedVec WData (k + 2) (indexedPrepend (k + 1) Ψ₁ (indexedPrepend k Ψ₂ Φ)) =
      η • wightmanIndexedVec WData (k + 2)
        (indexedPrepend (k + 1) Ψ₂ (indexedPrepend k Ψ₁ Φ)) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_wightmanBasis_eq_zero WData fun cfg => ?_
  rcases cfg with ⟨j, α, f_c⟩
  rw [inner_sub_right, sub_eq_zero, ← wightmanSchwartzVec_compact]
  let g := f_c.val
  have h_one : ∀ (Ψ_a Ψ_b : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (γ₀ γ₁ : ι)
      (γ_tail : Fin k → ι),
      indexedPrepend (k + 1) Ψ_a (indexedPrepend k Ψ_b Φ)
          (Fin.cons γ₀ (Fin.cons γ₁ γ_tail)) =
        schwartzPrepend (k + 1) (Ψ_a γ₀) (schwartzPrepend k (Ψ_b γ₁) (Φ γ_tail)) := by
    intro _ _ _ _ _
    rfl
  unfold wightmanIndexedVec
  rw [inner_sum, inner_smul_right, inner_sum, Finset.mul_sum,
    ← (Fin.consEquiv (fun _ : Fin (k + 2) => ι)).sum_comp, Fintype.sum_prod_type]
  rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => ι)).sum_comp, Fintype.sum_prod_type]
  simp_rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).sum_comp, Fintype.sum_prod_type]
  have h_ce2 : ∀ (a : ι) (b : Fin (k + 1) → ι),
      Fin.consEquiv (fun _ : Fin (k + 2) => ι) (a, b) = Fin.cons a b := fun _ _ => rfl
  have h_ce1 : ∀ (a : ι) (b : Fin k → ι),
      Fin.consEquiv (fun _ : Fin (k + 1) => ι) (a, b) = Fin.cons a b := fun _ _ => rfl
  simp_rw [h_ce2, h_ce1]
  have h_swap_sum :
      (∑ γ₀ : ι, ∑ γ₁ : ι, ∑ γ_tail : Fin k → ι,
        ⟪wightmanSchwartzVec WData j α g,
          wightmanSchwartzVec WData (k + 2) (Fin.cons γ₀ (Fin.cons γ₁ γ_tail))
            (indexedPrepend (k + 1) Ψ₁ (indexedPrepend k Ψ₂ Φ)
              (Fin.cons γ₀ (Fin.cons γ₁ γ_tail)))⟫_ℂ) =
      ∑ γ₀ : ι, ∑ γ₁ : ι, ∑ γ_tail : Fin k → ι,
        η * ⟪wightmanSchwartzVec WData j α g,
          wightmanSchwartzVec WData (k + 2) (Fin.cons γ₁ (Fin.cons γ₀ γ_tail))
            (indexedPrepend (k + 1) Ψ₂ (indexedPrepend k Ψ₁ Φ)
              (Fin.cons γ₁ (Fin.cons γ₀ γ_tail)))⟫_ℂ := by
    refine Finset.sum_congr rfl fun γ₀ _ => Finset.sum_congr rfl fun γ₁ _ =>
      Finset.sum_congr rfl fun γ_tail _ => ?_
    rw [inner_wightmanSchwartzVec, inner_wightmanSchwartzVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    have h_mul_swap : η * ((∏ i : Fin j, S.C (α i) (β i)) *
        WData.W (j + (k + 2)) (Fin.append (β ∘ Fin.rev) (Fin.cons γ₁ (Fin.cons γ₀ γ_tail)))
          (borchersConcatSchwartz j (k + 2) g
            (indexedPrepend (k + 1) Ψ₂ (indexedPrepend k Ψ₁ Φ)
              (Fin.cons γ₁ (Fin.cons γ₀ γ_tail))))) =
        (∏ i : Fin j, S.C (α i) (β i)) *
          (η * WData.W (j + (k + 2))
            (Fin.append (β ∘ Fin.rev) (Fin.cons γ₁ (Fin.cons γ₀ γ_tail)))
            (borchersConcatSchwartz j (k + 2) g
              (indexedPrepend (k + 1) Ψ₂ (indexedPrepend k Ψ₁ Φ)
                (Fin.cons γ₁ (Fin.cons γ₀ γ_tail))))) := by ring
    rw [h_mul_swap]
    congr 1
    let i₀ : Fin (j + (k + 2)) := ⟨j, by omega⟩
    have hi₀ : i₀.val + 1 < j + (k + 2) := by dsimp [i₀]; omega
    let i₁ : Fin (j + (k + 2)) := ⟨i₀.val + 1, hi₀⟩
    let σ := Equiv.swap i₀ i₁
    have h_i0_eq : i₀ = Fin.natAdd j 0 := Fin.ext (by simp [i₀])
    have h_i1_eq : i₁ = Fin.natAdd j 1 := Fin.ext (by simp [i₀, i₁])
    have h_supp : tsupport (borchersConcatSchwartz j (k + 2) g
          (indexedPrepend (k + 1) Ψ₁ (indexedPrepend k Ψ₂ Φ)
            (Fin.cons γ₀ (Fin.cons γ₁ γ_tail))) : (Fin (j + (k + 2)) → Fin 4 → ℝ) → ℂ) ⊆
        { x | is_spacelike (x i₀ - x i₁) } := by
      intro x hx
      let p₀ : (Fin (j + (k + 2)) → Fin 4 → ℝ) → (Fin 1 → Fin 4 → ℝ) :=
        fun y _ => y i₀
      let p₁ : (Fin (j + (k + 2)) → Fin 4 → ℝ) → (Fin 1 → Fin 4 → ℝ) :=
        fun y _ => y i₁
      have hp₀_cont : Continuous p₀ :=
        continuous_pi fun _ => continuous_apply i₀
      have hp₁_cont : Continuous p₁ :=
        continuous_pi fun _ => continuous_apply i₁
      have h_fn_eq : (borchersConcatSchwartz j (k + 2) g
          (indexedPrepend (k + 1) Ψ₁ (indexedPrepend k Ψ₂ Φ)
            (Fin.cons γ₀ (Fin.cons γ₁ γ_tail))) :
          (Fin (j + (k + 2)) → Fin 4 → ℝ) → ℂ) =
          fun y => (Ψ₁ γ₀ (p₀ y)) * ((Ψ₂ γ₁ (p₁ y)) *
            (star (g (fun s => y (Fin.castAdd (k + 2) (Fin.rev s)))) *
              Φ γ_tail (fun u => y (Fin.natAdd j (Fin.succ (Fin.succ u)))))) := by
        ext y
        rw [borchersConcatSchwartz_apply, h_one Ψ₁ Ψ₂ γ₀ γ₁ γ_tail,
          schwartzPrepend_apply, schwartzPrepend_apply]
        have hy0 : (fun _ : Fin 1 => y (Fin.natAdd j 0)) = p₀ y := by
          ext a μ; rw [← h_i0_eq]
        have hy1 : (fun _ : Fin 1 => y (Fin.natAdd j (Fin.succ 0))) = p₁ y := by
          ext a μ
          change y (Fin.natAdd j 1) μ = y i₁ μ
          rw [h_i1_eq]
        rw [hy0, hy1]
        simp only [Complex.star_def]
        ring
      have h_ts0 : p₀ x ∈ tsupport (Ψ₁ γ₀ : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
        rw [h_fn_eq] at hx
        exact tsupport_comp_subset_preimage (Ψ₁ γ₀ : (Fin 1 → Fin 4 → ℝ) → ℂ)
          hp₀_cont (tsupport_mul_subset_left hx)
      have h_ts1 : p₁ x ∈ tsupport (Ψ₂ γ₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
        rw [h_fn_eq] at hx
        exact tsupport_comp_subset_preimage (Ψ₂ γ₁ : (Fin 1 → Fin 4 → ℝ) → ℂ)
          hp₁_cont (tsupport_mul_subset_left (tsupport_mul_subset_right hx))
      exact hsp γ₀ γ₁ (p₀ x) (p₁ x) h_ts0 h_ts1
    have h_α_eq : (Fin.append (β ∘ Fin.rev) (Fin.cons γ₀ (Fin.cons γ₁ γ_tail))) ∘ σ =
        Fin.append (β ∘ Fin.rev) (Fin.cons γ₁ (Fin.cons γ₀ γ_tail)) := by
      ext r
      refine Fin.addCases (fun s => ?_) (fun u => ?_) r
      · have h_ne0 : Fin.castAdd (k + 2) s ≠ i₀ := fun h => by
          have := congrArg Fin.val h; simp [i₀] at this; omega
        have h_ne1 : Fin.castAdd (k + 2) s ≠ i₁ := fun h => by
          have := congrArg Fin.val h; simp [i₀, i₁] at this; omega
        simp only [Function.comp_apply, σ, Equiv.swap_apply_of_ne_of_ne h_ne0 h_ne1,
          Fin.append_left]
      · refine Fin.cases ?_ (fun u' => Fin.cases ?_ (fun v => ?_) u') u
        · have h_eq0 : Fin.natAdd j 0 = i₀ := h_i0_eq.symm
          rw [Function.comp_apply, h_eq0, Equiv.swap_apply_left, h_i1_eq, h_i0_eq,
            Fin.append_right, Fin.append_right]
          rfl
        · have h_eq1 : Fin.natAdd j (Fin.succ 0) = i₁ := by rw [h_i1_eq]; rfl
          rw [Function.comp_apply, h_eq1, Equiv.swap_apply_right, h_i0_eq, h_i1_eq,
            Fin.append_right, Fin.append_right]
          rfl
        · have h_ne0 : Fin.natAdd j (Fin.succ (Fin.succ v)) ≠ i₀ := fun h => by
            have := congrArg Fin.val h; simp [i₀] at this
          have h_ne1 : Fin.natAdd j (Fin.succ (Fin.succ v)) ≠ i₁ := fun h => by
            have := congrArg Fin.val h; simp [i₀, i₁] at this
          simp only [Function.comp_apply, σ, Equiv.swap_apply_of_ne_of_ne h_ne0 h_ne1,
            Fin.append_right]
          rfl
    have h_f_eq : ∀ x : Fin (j + (k + 2)) → Fin 4 → ℝ,
        (borchersConcatSchwartz j (k + 2) g
          (indexedPrepend (k + 1) Ψ₂ (indexedPrepend k Ψ₁ Φ)
            (Fin.cons γ₁ (Fin.cons γ₀ γ_tail)))) (x ∘ σ) =
        (borchersConcatSchwartz j (k + 2) g
          (indexedPrepend (k + 1) Ψ₁ (indexedPrepend k Ψ₂ Φ)
            (Fin.cons γ₀ (Fin.cons γ₁ γ_tail)))) x := by
      intro x
      rw [borchersConcatSchwartz_apply, borchersConcatSchwartz_apply,
        h_one Ψ₂ Ψ₁ γ₁ γ₀ γ_tail, h_one Ψ₁ Ψ₂ γ₀ γ₁ γ_tail,
        schwartzPrepend_apply, schwartzPrepend_apply,
        schwartzPrepend_apply, schwartzPrepend_apply]
      have hL : (fun s : Fin j => (x ∘ σ) (Fin.castAdd (k + 2) (Fin.rev s))) =
          fun s : Fin j => x (Fin.castAdd (k + 2) (Fin.rev s)) := by
        ext s μ
        have h_ne0 : Fin.castAdd (k + 2) (Fin.rev s) ≠ i₀ := fun h => by
          have := congrArg Fin.val h; simp [i₀] at this; omega
        have h_ne1 : Fin.castAdd (k + 2) (Fin.rev s) ≠ i₁ := fun h => by
          have := congrArg Fin.val h; simp [i₀, i₁] at this; omega
        simp [σ, Equiv.swap_apply_of_ne_of_ne h_ne0 h_ne1]
      have h0 : (fun _ : Fin 1 => (x ∘ σ) (Fin.natAdd j 0)) =
          fun _ : Fin 1 => x (Fin.natAdd j (Fin.succ 0)) := by
        ext a μ
        change x (σ (Fin.natAdd j 0)) μ = x (Fin.natAdd j 1) μ
        rw [← h_i0_eq, Equiv.swap_apply_left, h_i1_eq]
      have h1 : (fun _ : Fin 1 => (x ∘ σ) (Fin.natAdd j (Fin.succ 0))) =
          fun _ : Fin 1 => x (Fin.natAdd j 0) := by
        ext a μ
        have h_arg : Fin.natAdd j (Fin.succ (0 : Fin (k + 1))) = i₁ := by rw [h_i1_eq]; rfl
        rw [Function.comp_apply, h_arg, Equiv.swap_apply_right, h_i0_eq]
      have hT : (fun u : Fin k => (x ∘ σ) (Fin.natAdd j (Fin.succ (Fin.succ u)))) =
          fun u : Fin k => x (Fin.natAdd j (Fin.succ (Fin.succ u))) := by
        ext u μ
        have h_ne0 : Fin.natAdd j (Fin.succ (Fin.succ u)) ≠ i₀ := fun h => by
          have := congrArg Fin.val h; simp [i₀] at this
        have h_ne1 : Fin.natAdd j (Fin.succ (Fin.succ u)) ≠ i₁ := fun h => by
          have := congrArg Fin.val h; simp [i₀, i₁] at this
        simp [σ, Equiv.swap_apply_of_ne_of_ne h_ne0 h_ne1]
      rw [hL, h0, h1]
      change star (g _) * (Ψ₂ γ₁ _ * (Ψ₁ γ₀ _ * Φ γ_tail (fun u => (x ∘ σ) _))) =
        star (g _) * (Ψ₁ γ₀ _ * (Ψ₂ γ₁ _ * Φ γ_tail _))
      rw [hT]
      ring
    have h_loc_eq := hloc (j + (k + 2)) i₀ hi₀
      (Fin.append (β ∘ Fin.rev) (Fin.cons γ₀ (Fin.cons γ₁ γ_tail)))
      (borchersConcatSchwartz j (k + 2) g
        (indexedPrepend (k + 1) Ψ₁ (indexedPrepend k Ψ₂ Φ) (Fin.cons γ₀ (Fin.cons γ₁ γ_tail))))
      (borchersConcatSchwartz j (k + 2) g
        (indexedPrepend (k + 1) Ψ₂ (indexedPrepend k Ψ₁ Φ) (Fin.cons γ₁ (Fin.cons γ₀ γ_tail))))
      h_supp h_f_eq
    rw [h_α_eq] at h_loc_eq
    exact h_loc_eq
  rw [h_swap_sum]
  rw [Finset.sum_comm]

def dualModeWavepacket {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) (f : SmoothWavepacket) : SmoothWavepacket where
  amp p := D.dual_w s p α * f.amp p
  smooth := (D.contDiff_dual_w s α).mul f.smooth
  compactSupport := f.compactSupport.mul_left

lemma dualModeWavepacket_apply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) (f : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (dualModeWavepacket D s α f).amp p = D.dual_w s p α * f.amp p := rfl

lemma tsupport_dualModeWavepacket_subset {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) (f : SmoothWavepacket) :
    tsupport (dualModeWavepacket D s α f).amp ⊆ tsupport f.amp :=
  tsupport_mul_subset_right

lemma velocitySupport_dualModeWavepacket_subset {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) (f : SmoothWavepacket) :
    velocitySupport m (dualModeWavepacket D s α f) ⊆ velocitySupport m f := by
  rintro v ⟨p, hp, rfl⟩
  exact ⟨p, tsupport_dualModeWavepacket_subset D s α f hp, rfl⟩

def haagRuelleIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun α => haagRuelleTestFn m M D.hm D.hM (dualModeWavepacket D s α f) t

def haagRuelleDerivIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun α => haagRuelleDerivTestFn m M D.hm D.hM (dualModeWavepacket D s α f) t

def haagRuelleCoreIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun α => haagRuelleCoreTestFn m M D.hm D.hM (dualModeWavepacket D s α f) r hr t

def haagRuelleTailIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun α => haagRuelleTailTestFn m M D.hm D.hM (dualModeWavepacket D s α f) r hr t

def haagRuelleAdjIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  starIndexedTest S (haagRuelleIndexedTest D s f t)

def haagRuelleApply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) (k : ℕ)
    (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι (k + 1) :=
  indexedPrepend k (haagRuelleIndexedTest D s f t) Φ

def haagRuelleDerivApply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) (k : ℕ)
    (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι (k + 1) :=
  indexedPrepend k (haagRuelleDerivIndexedTest D s f t) Φ

def haagRuelleCoreApply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (k : ℕ) (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι (k + 1) :=
  indexedPrepend k (haagRuelleCoreIndexedTest D s f r hr t) Φ

def haagRuelleTailApply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (k : ℕ) (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι (k + 1) :=
  indexedPrepend k (haagRuelleTailIndexedTest D s f r hr t) Φ

def haagRuelleAdjApply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) (k : ℕ)
    (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι (k + 1) :=
  indexedPrepend k (haagRuelleAdjIndexedTest D s f t) Φ

lemma haagRuelleApply_eq_core_add_tail {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (k : ℕ) (Φ : IndexedSchwartz ι k) (γ : Fin (k + 1) → ι) :
    haagRuelleApply D s f t k Φ γ =
      haagRuelleCoreApply D s f r hr t k Φ γ + haagRuelleTailApply D s f r hr t k Φ γ := by
  dsimp [haagRuelleApply, haagRuelleCoreApply, haagRuelleTailApply, indexedPrepend,
    haagRuelleIndexedTest, haagRuelleCoreIndexedTest, haagRuelleTailIndexedTest]
  rw [haagRuelleTestFn_eq_core_add_tail m M D.hm D.hM (dualModeWavepacket D s (γ 0) f) r hr t,
    schwartzPrepend_add_left]

lemma wightmanIndexedVec_haagRuelleApply_eq_core_add_tail
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (k : ℕ) (Φ : IndexedSchwartz ι k) :
    wightmanIndexedVec D.wightman.WData (k + 1) (haagRuelleApply D s f t k Φ) =
      wightmanIndexedVec D.wightman.WData (k + 1) (haagRuelleCoreApply D s f r hr t k Φ) +
        wightmanIndexedVec D.wightman.WData (k + 1) (haagRuelleTailApply D s f r hr t k Φ) := by
  unfold wightmanIndexedVec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [haagRuelleApply_eq_core_add_tail, map_add]

theorem inner_haagRuelleApply_eq_adj {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) (j k : ℕ)
    (Φ₁ : IndexedSchwartz ι j) (Φ₂ : IndexedSchwartz ι k) :
    ⟪wightmanIndexedVec D.wightman.WData (j + 1) (haagRuelleApply D s f t j Φ₁),
      wightmanIndexedVec D.wightman.WData k Φ₂⟫_ℂ =
    ⟪wightmanIndexedVec D.wightman.WData j Φ₁,
      wightmanIndexedVec D.wightman.WData (k + 1) (haagRuelleAdjApply D s f t k Φ₂)⟫_ℂ :=
  inner_wightmanIndexedVec_indexedPrepend D.wightman.WData j k
    (haagRuelleIndexedTest D s f t) Φ₁ Φ₂

theorem tendsto_schwartzPrepend_haagRuelle_deriv {m M : ℝ} (hm : 0 < m) (hM : m < M)
    (f : SmoothWavepacket) (k : ℕ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (t : ℝ) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ • (schwartzPrepend k (haagRuelleTestFn m M hm hM f (t + h)) F -
          schwartzPrepend k (haagRuelleTestFn m M hm hM f t) F))
      (𝓝[≠] 0) (𝓝 (schwartzPrepend k (haagRuelleDerivTestFn m M hm hM f t) F)) := by
  have h_eq :
      (fun h : ℝ =>
        h⁻¹ • (schwartzPrepend k (haagRuelleTestFn m M hm hM f (t + h)) F -
          schwartzPrepend k (haagRuelleTestFn m M hm hM f t) F)) =
      fun h : ℝ => schwartzPrepend k
        (h⁻¹ • (haagRuelleTestFn m M hm hM f (t + h) - haagRuelleTestFn m M hm hM f t)) F := by
    funext h
    ext x
    simp only [_root_.smul_apply, _root_.sub_apply, schwartzPrepend_apply, Complex.real_smul]
    ring
  rw [h_eq]
  let L_lin : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →ₗ[ℂ]
      SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ :=
    { toFun := fun ψ => schwartzPrepend k ψ F
      map_add' := fun ψ₁ ψ₂ => schwartzPrepend_add_left k ψ₁ ψ₂ F
      map_smul' := fun c ψ => schwartzPrepend_smul_left k c ψ F }
  have h_cont : Continuous L_lin := by
    have h_with1 := schwartz_withSeminorms ℝ (Fin 1 → Fin 4 → ℝ) ℂ
    have h_with2 := schwartz_withSeminorms ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ
    refine WithSeminorms.continuous_of_isBounded h_with1 h_with2
      (L_lin.restrictScalars ℝ) fun ⟨l, d⟩ => ?_
    let C_F : ℝ :=
      (∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
        (SchwartzMap.seminorm ℝ 0 (d - q) F + SchwartzMap.seminorm ℝ l (d - q) F)) + 1
    have hCF_pos : 0 < C_F := by
      dsimp [C_F]
      have h_nn : 0 ≤ ∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
          (SchwartzMap.seminorm ℝ 0 (d - q) F + SchwartzMap.seminorm ℝ l (d - q) F) :=
        Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _)
          (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      linarith
    let s : Finset (ℕ × ℕ) := Finset.Iic (l, d)
    let fam := schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ
    refine ⟨s, ⟨C_F, hCF_pos.le⟩, fun ψ => ?_⟩
    simp only [SchwartzMap.schwartzSeminormFamily_apply, Seminorm.comp_apply,
      LinearMap.coe_restrictScalars, _root_.smul_apply, NNReal.smul_def, smul_eq_mul]
    change SchwartzMap.seminorm ℝ l d (schwartzPrepend k ψ F) ≤ C_F * (s.sup fam) ψ
    refine (seminorm_schwartzPrepend_le k l d ψ F).trans ?_
    have hs_nn : 0 ≤ (s.sup fam) ψ := apply_nonneg _ _
    have h_sum_le :
        (∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
          (SchwartzMap.seminorm ℝ l q ψ * SchwartzMap.seminorm ℝ 0 (d - q) F +
            SchwartzMap.seminorm ℝ 0 q ψ * SchwartzMap.seminorm ℝ l (d - q) F)) ≤
        (∑ q ∈ Finset.range (d + 1), (d.choose q : ℝ) *
          (SchwartzMap.seminorm ℝ 0 (d - q) F + SchwartzMap.seminorm ℝ l (d - q) F)) *
          (s.sup fam) ψ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun q hq => ?_
      have hqd : q ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
      have h_in1 : (l, q) ∈ s := Finset.mem_Iic.mpr ⟨le_rfl, hqd⟩
      have h_in2 : (0, q) ∈ s := Finset.mem_Iic.mpr ⟨Nat.zero_le l, hqd⟩
      have hle1 : fam (l, q) ψ ≤ (s.sup fam) ψ :=
        Seminorm.le_def.mp (Finset.le_sup (f := fam) h_in1) ψ
      have hle2 : fam (0, q) ψ ≤ (s.sup fam) ψ :=
        Seminorm.le_def.mp (Finset.le_sup (f := fam) h_in2) ψ
      change SchwartzMap.seminorm ℝ l q ψ ≤ (s.sup fam) ψ at hle1
      change SchwartzMap.seminorm ℝ 0 q ψ ≤ (s.sup fam) ψ at hle2
      have h_term :
          SchwartzMap.seminorm ℝ l q ψ * SchwartzMap.seminorm ℝ 0 (d - q) F +
            SchwartzMap.seminorm ℝ 0 q ψ * SchwartzMap.seminorm ℝ l (d - q) F ≤
          (SchwartzMap.seminorm ℝ 0 (d - q) F + SchwartzMap.seminorm ℝ l (d - q) F) *
            (s.sup fam) ψ := by
        have hF0 := apply_nonneg (SchwartzMap.seminorm ℝ 0 (d - q)) F
        have hFl := apply_nonneg (SchwartzMap.seminorm ℝ l (d - q)) F
        nlinarith
      calc (d.choose q : ℝ) *
            (SchwartzMap.seminorm ℝ l q ψ * SchwartzMap.seminorm ℝ 0 (d - q) F +
              SchwartzMap.seminorm ℝ 0 q ψ * SchwartzMap.seminorm ℝ l (d - q) F)
          ≤ (d.choose q : ℝ) *
              ((SchwartzMap.seminorm ℝ 0 (d - q) F + SchwartzMap.seminorm ℝ l (d - q) F) *
                (s.sup fam) ψ) :=
            mul_le_mul_of_nonneg_left h_term (Nat.cast_nonneg _)
        _ = _ := by ring
    refine h_sum_le.trans (mul_le_mul_of_nonneg_right ?_ hs_nn)
    dsimp [C_F]
    linarith
  let L : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ :=
    { L_lin with cont := h_cont }
  exact (L.continuous.tendsto _).comp (tendsto_haagRuelleTestFn_timeDeriv m M hm hM f t)

theorem hasDerivAt_wightmanIndexedVec_haagRuelleApply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (k : ℕ)
    (Φ : IndexedSchwartz ι k) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => wightmanIndexedVec D.wightman.WData (k + 1)
        (haagRuelleApply D s f τ k Φ))
      (wightmanIndexedVec D.wightman.WData (k + 1) (haagRuelleDerivApply D s f t k Φ)) t := by
  unfold wightmanIndexedVec haagRuelleApply haagRuelleDerivApply
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h_each : ∀ γ : Fin (k + 1) → ι,
      Tendsto
        (fun h : ℝ =>
          h⁻¹ • (wightmanSchwartzVec D.wightman.WData (k + 1) γ
              (schwartzPrepend k (haagRuelleIndexedTest D s f (t + h) (γ 0)) (Φ (Fin.tail γ))) -
            wightmanSchwartzVec D.wightman.WData (k + 1) γ
              (schwartzPrepend k (haagRuelleIndexedTest D s f t (γ 0)) (Φ (Fin.tail γ)))))
        (𝓝[≠] 0)
        (𝓝 (wightmanSchwartzVec D.wightman.WData (k + 1) γ
          (schwartzPrepend k (haagRuelleDerivIndexedTest D s f t (γ 0)) (Φ (Fin.tail γ))))) := by
    intro γ
    let Wvec := wightmanSchwartzVec D.wightman.WData (k + 1) γ
    have h_sm : (fun h : ℝ =>
        h⁻¹ • (Wvec (schwartzPrepend k (haagRuelleIndexedTest D s f (t + h) (γ 0))
            (Φ (Fin.tail γ))) -
          Wvec (schwartzPrepend k (haagRuelleIndexedTest D s f t (γ 0)) (Φ (Fin.tail γ))))) =
        fun h : ℝ => Wvec (h⁻¹ • (schwartzPrepend k (haagRuelleIndexedTest D s f (t + h) (γ 0))
            (Φ (Fin.tail γ)) -
          schwartzPrepend k (haagRuelleIndexedTest D s f t (γ 0)) (Φ (Fin.tail γ)))) := by
      ext h
      rw [← map_sub, ← ContinuousLinearMap.map_smul_of_tower]
    rw [h_sm]
    exact (Wvec.continuous.tendsto _).comp
      (tendsto_schwartzPrepend_haagRuelle_deriv D.hm D.hM
        (dualModeWavepacket D s (γ 0) f) k (Φ (Fin.tail γ)) t)
  have h_sum := tendsto_finsetSum (Finset.univ : Finset (Fin (k + 1) → ι)) fun γ _ => h_each γ
  refine h_sum.congr fun h => ?_
  dsimp [indexedPrepend]
  rw [← Finset.sum_sub_distrib, ← Finset.smul_sum]

theorem exists_haagRuelleCoreApply_comm_of_velocityDisjoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {f₁ f₂ : SmoothWavepacket} (hdisj : VelocityDisjoint m f₁ f₂) :
    ∃ (r : ℝ) (hr : 0 < r) (T₀ : ℝ), 0 < T₀ ∧
      ∀ (s₁ s₂ : Fin D.mode.ν) (t : ℝ), T₀ ≤ |t| →
        ∀ (k : ℕ) (Φ : IndexedSchwartz ι k),
          wightmanIndexedVec D.wightman.WData (k + 2)
            (haagRuelleCoreApply D s₁ f₁ r hr t (k + 1)
              (haagRuelleCoreApply D s₂ f₂ r hr t k Φ)) =
          η • wightmanIndexedVec D.wightman.WData (k + 2)
            (haagRuelleCoreApply D s₂ f₂ r hr t (k + 1)
              (haagRuelleCoreApply D s₁ f₁ r hr t k Φ)) := by
  obtain ⟨d_sep, hd_pos, h_sep⟩ := exists_pos_sep_of_velocityDisjoint D.hm hdisj
  let r : ℝ := d_sep / 6
  have hr : 0 < r := by positivity
  refine ⟨r, hr, 1, zero_lt_one, fun s₁ s₂ t ht k Φ => ?_⟩
  refine wightmanIndexedVec_indexedPrepend_swap_of_spacelike D.wightman.WData D.locality
    (haagRuelleCoreIndexedTest D s₁ f₁ r hr t)
    (haagRuelleCoreIndexedTest D s₂ f₂ r hr t) ?_ k Φ
  intro α₁ α₂ x₁ x₂ hx₁ hx₂
  have hx₁' : x₁ ∈ tsupport (velocityConeCutoff m D.hm
      (dualModeWavepacket D s₁ α₁ f₁) r hr t) :=
    tsupport_timeModCoreTestFn_subset D.hm (dualModeWavepacket D s₁ α₁ f₁) _ _ _ r hr t hx₁
  have hx₂' : x₂ ∈ tsupport (velocityConeCutoff m D.hm
      (dualModeWavepacket D s₂ α₂ f₂) r hr t) :=
    tsupport_timeModCoreTestFn_subset D.hm (dualModeWavepacket D s₂ α₂ f₂) _ _ _ r hr t hx₂
  have h_sep_modes : ∀ v₁ ∈ velocitySupport m (dualModeWavepacket D s₁ α₁ f₁),
      ∀ v₂ ∈ velocitySupport m (dualModeWavepacket D s₂ α₂ f₂), d_sep ≤ ‖v₁ - v₂‖ :=
    fun v₁ hv₁ v₂ hv₂ => h_sep v₁
      (velocitySupport_dualModeWavepacket_subset D s₁ α₁ f₁ hv₁) v₂
      (velocitySupport_dualModeWavepacket_subset D s₂ α₂ f₂ hv₂)
  exact spacelike_velocityConeCutoffs_of_radius D.hm hr (by dsimp [r]; linarith)
    h_sep_modes ht hx₁' hx₂'

def haagRuelleVacCreate {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) : D.Hilbert :=
  wightmanIndexedVec D.wightman.WData 1 (haagRuelleApply D s f t 0 (vacuumIndexedSchwartz ι))

def haagRuelleDerivVacCreate {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) : D.Hilbert :=
  wightmanIndexedVec D.wightman.WData 1
    (haagRuelleDerivApply D s f t 0 (vacuumIndexedSchwartz ι))

def haagRuelleAdjVacCreate {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) : D.Hilbert :=
  wightmanIndexedVec D.wightman.WData 1
    (haagRuelleAdjApply D s f t 0 (vacuumIndexedSchwartz ι))

lemma haagRuelleVacCreate_eq_sum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleVacCreate D s f t =
      ∑ α : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α)
        (haagRuelleIndexedTest D s f t α) := by
  unfold haagRuelleVacCreate wightmanIndexedVec haagRuelleApply indexedPrepend
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h_eq : (fun _ : Fin 1 => α) = (Equiv.funUnique (Fin 1) ι).symm α := by
    ext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h_eq]
  have h_vac : (vacuumIndexedSchwartz ι (Fin.tail ((Equiv.funUnique (Fin 1) ι).symm α))) =
      momentumWavepacketSchwartz 0 0 := rfl
  rw [h_vac, schwartzPrepend_zero_vac]
  rfl

lemma haagRuelleDerivVacCreate_eq_sum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleDerivVacCreate D s f t =
      ∑ α : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α)
        (haagRuelleDerivIndexedTest D s f t α) := by
  unfold haagRuelleDerivVacCreate wightmanIndexedVec haagRuelleDerivApply indexedPrepend
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h_eq : (fun _ : Fin 1 => α) = (Equiv.funUnique (Fin 1) ι).symm α := by
    ext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h_eq]
  have h_vac : (vacuumIndexedSchwartz ι (Fin.tail ((Equiv.funUnique (Fin 1) ι).symm α))) =
      momentumWavepacketSchwartz 0 0 := rfl
  rw [h_vac, schwartzPrepend_zero_vac]
  rfl

lemma haagRuelleAdjVacCreate_eq_sum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleAdjVacCreate D s f t =
      ∑ α : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α)
        (haagRuelleAdjIndexedTest D s f t α) := by
  unfold haagRuelleAdjVacCreate wightmanIndexedVec haagRuelleAdjApply indexedPrepend
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h_eq : (fun _ : Fin 1 => α) = (Equiv.funUnique (Fin 1) ι).symm α := by
    ext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h_eq]
  have h_vac : (vacuumIndexedSchwartz ι (Fin.tail ((Equiv.funUnique (Fin 1) ι).symm α))) =
      momentumWavepacketSchwartz 0 0 := rfl
  rw [h_vac, schwartzPrepend_zero_vac]
  rfl

lemma tsupport_massShellCutoff_bounds {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {q : Fin 4 → ℝ} (hq : q ∈ tsupport (massShellCutoff m M hm hM)) :
    m / 4 ≤ q 0 ∧
      |minkowskiInner q q - m ^ 2| ≤ 2 * massShellGapDelta m M ∧
      minkowskiInner q q < M ^ 2 := by
  let S_closed : Set (Fin 4 → ℝ) :=
    { x | m / 4 ≤ x 0 ∧ |minkowskiInner x x - m ^ 2| ≤ 2 * massShellGapDelta m M }
  have h_closed : IsClosed S_closed := by
    have hc1 : IsClosed { x : Fin 4 → ℝ | m / 4 ≤ x 0 } :=
      isClosed_le continuous_const (continuous_apply 0)
    have hc2 : IsClosed
        { x : Fin 4 → ℝ | |minkowskiInner x x - m ^ 2| ≤ 2 * massShellGapDelta m M } :=
      isClosed_le
        (((contDiff_minkowskiInner_self.continuous).sub continuous_const).abs)
        continuous_const
    exact hc1.inter hc2
  have h_sub : Function.support (massShellCutoff m M hm hM) ⊆ S_closed := by
    intro x hx
    rw [Function.mem_support] at hx
    have hb := massShellCutoff_support_bounds hm hM hx
    exact ⟨hb.1.le, hb.2.1⟩
  have hqS : q ∈ S_closed := closure_minimal h_sub h_closed hq
  have h_sub_delta := massShellGapDelta_four_le_sub (m := m) (M := M)
  have h_pos_delta := massShellGapDelta_pos hm hM
  have h_lt_M : minkowskiInner q q < M ^ 2 := by
    have := abs_le.mp hqS.2
    linarith
  exact ⟨hqS.1, hqS.2, h_lt_M⟩

lemma minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem
    {m M : ℝ} (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket) (t : ℝ)
    {q : Fin 4 → ℝ} (hq : q ∉ tsupport (massShellCutoff m M hm hM)) :
    minkowskiFourier (haagRuelleTestFn m M hm hM f t) (fun _ => -q) = 0 := by
  rw [minkowskiFourier_haagRuelleTestFn]
  have hc0 : massShellCutoff m M hm hM q = 0 := image_eq_zero_of_notMem_tsupport hq
  unfold timeModMomAmp haagRuelleBaseAmp
  rw [hc0]
  simp

lemma minkowskiFourier_haagRuelleDerivTestFn_eq_zero_of_notMem
    {m M : ℝ} (hm : 0 < m) (hM : m < M) (f : SmoothWavepacket) (t : ℝ)
    {q : Fin 4 → ℝ} (hq : q ∉ tsupport (massShellCutoff m M hm hM)) :
    minkowskiFourier (haagRuelleDerivTestFn m M hm hM f t) (fun _ => -q) = 0 := by
  unfold haagRuelleDerivTestFn
  rw [minkowskiFourier_timeModTestFn]
  have hc0 : massShellCutoff m M hm hM q = 0 := image_eq_zero_of_notMem_tsupport hq
  unfold timeModMomAmp haagRuelleDerivBaseAmp haagRuelleBaseAmp
  rw [hc0]
  simp

lemma twoPoint_borchersConcat_eq_massShell_of_right_cutoff
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (β : Fin 2 → ι) (ψ₁ ψ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hψ₂ : ∀ q : Fin 4 → ℝ, q ∉ tsupport (massShellCutoff m M D.hm D.hM) →
      minkowskiFourier ψ₂ (fun _ => -q) = 0) :
    D.wightman.WData.W 2 β (borchersConcatSchwartz 1 1 ψ₁ ψ₂) =
      massShellTwoPointW m D.C_shell D.hC 2 β (borchersConcatSchwartz 1 1 ψ₁ ψ₂) := by
  refine D.twoPoint_shell β (borchersConcatSchwartz 1 1 ψ₁ ψ₂) ?_
  let U : Set (Fin 2 → Fin 4 → ℝ) :=
    { p | -p 1 ∉ tsupport (massShellCutoff m M D.hm D.hM) }
  have hU_open : IsOpen U :=
    (isClosed_tsupport (massShellCutoff m M D.hm D.hM)).isOpen_compl.preimage
      (by fun_prop : Continuous fun p : Fin 2 → Fin 4 → ℝ => -p 1)
  have hU_sub : { p : Fin 2 → Fin 4 → ℝ |
      p 0 + p 1 = 0 ∧ (p 0 = 0 ∨ p 0 ∈ continuumCone M) } ⊆ U := by
    intro p ⟨h_sum, h_cases⟩
    have hp0_eq : -p 1 = p 0 := by
      ext μ
      have hμ := congr_fun h_sum μ
      simp only [Pi.add_apply, Pi.zero_apply] at hμ
      simp only [Pi.neg_apply]
      linarith
    dsimp [U]
    rw [hp0_eq]
    intro hp_ts
    have hb := tsupport_massShellCutoff_bounds D.hm D.hM hp_ts
    rcases h_cases with hp0 | hpM
    · rw [hp0] at hb
      simp at hb
      linarith [D.hm]
    · linarith [hpM.2, hb.2.2]
  refine ⟨U, hU_open, hU_sub, fun p hp => ?_⟩
  rw [minkowskiFourier_borchersProduct_eq 1 1 ψ₁ ψ₂ _
    (borchersConcatSchwartz_apply 1 1 ψ₁ ψ₂) p]
  have h_right : minkowskiFourier ψ₂ (fun i => p (Fin.natAdd 1 i)) = 0 := by
    have h_arg : (fun i : Fin 1 => p (Fin.natAdd 1 i)) = fun _ => -(-p 1) := by
      ext i μ
      rw [Subsingleton.elim i 0]
      simp [Fin.natAdd]
    rw [h_arg]
    exact hψ₂ (-p 1) hp
  rw [h_right, mul_zero]

lemma continuous_smoothWavepacket_normSq (f : SmoothWavepacket) :
    Continuous (fun p : Fin 3 → ℝ => ‖f.amp p‖ ^ 2) :=
  (continuous_pow 2).comp f.smooth.continuous.norm

lemma smoothWavepacket_normSq_integrable (f : SmoothWavepacket) :
    Integrable (fun p : Fin 3 → ℝ => ‖f.amp p‖ ^ 2) volume :=
  (continuous_smoothWavepacket_normSq f).integrable_of_hasCompactSupport
    (HasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) f.compactSupport (by simp))

def fockOneParticleFun (ν : ℕ) (s : Fin ν) (f : SmoothWavepacket) :
    FockSectorDom ν 1 → ℂ :=
  fun x => if x.2 0 = s then f.amp (x.1 0) else 0

lemma measurable_fockOneParticleFun (ν : ℕ) (s : Fin ν) (f : SmoothWavepacket) :
    Measurable (fockOneParticleFun ν s f) := by
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_singleton s).preimage ((measurable_pi_apply 0).comp measurable_snd)
  · exact f.smooth.continuous.measurable.comp ((measurable_pi_apply 0).comp measurable_fst)

lemma memLp_fockOneParticleFun (ν : ℕ) (s : Fin ν) (f : SmoothWavepacket) :
    MemLp (fockOneParticleFun ν s f) 2 (fockSectorMeasure ν 1) := by
  have hm := measurable_fockOneParticleFun ν s f
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  let eu := (MeasurableEquiv.funUnique (Fin 1) (Fin 3 → ℝ)).symm
  let mp_u := (volume_preserving_funUnique (Fin 1) (Fin 3 → ℝ)).symm
  have h_amp_int : Integrable (fun p : Fin 3 → ℝ => ‖f.amp p‖ ^ 2) volume :=
    smoothWavepacket_normSq_integrable f
  have h_k_int : Integrable (fun k : Fin 1 → Fin 3 → ℝ => ‖f.amp (k 0)‖ ^ 2) volume :=
    (mp_u.integrable_comp_emb eu.measurableEmbedding).mp h_amp_int
  let h_dom : FockSectorDom ν 1 → ℝ := fun x => ‖f.amp (x.1 0)‖ ^ 2 * (1 : ℝ)
  have h_dom_int : Integrable h_dom (fockSectorMeasure ν 1) :=
    h_k_int.mul_prod (integrable_const (1 : ℝ))
  refine h_dom_int.mono' ((hm.norm).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  dsimp [h_dom, fockOneParticleFun]
  rw [abs_of_nonneg (sq_nonneg _), mul_one]
  split_ifs
  · exact le_rfl
  · simp

def fockOneParticleVec (ν : ℕ) (s : Fin ν) (f : SmoothWavepacket) : FockHilbert ν :=
  liftSectorToFock ν 1 (fockOneParticleFun ν s f)
    (measurable_fockOneParticleFun ν s f) (memLp_fockOneParticleFun ν s f)

lemma integral_fockSectorMeasure_complex {ν r : ℕ}
    {h : FockSectorDom ν r → ℂ} (hh : Integrable h (fockSectorMeasure ν r)) :
    (∫ x : FockSectorDom ν r, h x ∂(fockSectorMeasure ν r)) =
      ∑ s : Fin r → Fin ν, ∫ k : Fin r → Fin 3 → ℝ, h (k, s) ∂volume := by
  unfold fockSectorMeasure at hh ⊢
  rw [integral_prod_symm _ hh, integral_fintype_count]

theorem inner_fockOneParticleVec_eq (ν : ℕ) (s₁ s₂ : Fin ν)
    (f₁ f₂ : SmoothWavepacket) :
    ⟪fockOneParticleVec ν s₁ f₁, fockOneParticleVec ν s₂ f₂⟫_ℂ =
      if s₁ = s₂ then ∫ p : Fin 3 → ℝ, star (f₁.amp p) * f₂.amp p else 0 := by
  unfold fockOneParticleVec
  rw [inner_liftSectorToFock_eq]
  have h1 := memLp_fockOneParticleFun ν s₁ f₁
  have h2 := memLp_fockOneParticleFun ν s₂ f₂
  have h_prod_int : Integrable
      (fun x : FockSectorDom ν 1 =>
        star (fockOneParticleFun ν s₁ f₁ x) * fockOneParticleFun ν s₂ f₂ x)
      (fockSectorMeasure ν 1) := by
    have hi := L2.integrable_inner (𝕜 := ℂ) (h1.toLp _) (h2.toLp _)
    refine hi.congr ?_
    filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [mul_comm]
  rw [integral_fockSectorMeasure_complex h_prod_int,
    ← (Equiv.funUnique (Fin 1) (Fin ν)).symm.sum_comp]
  let eu := (MeasurableEquiv.funUnique (Fin 1) (Fin 3 → ℝ)).symm
  let mp_u := (volume_preserving_funUnique (Fin 1) (Fin 3 → ℝ)).symm
  by_cases h12 : s₁ = s₂
  · subst h12
    rw [if_pos rfl, Finset.sum_eq_single s₁]
    · refine Eq.trans (mp_u.integral_comp eu.measurableEmbedding
        (fun k : Fin 1 → Fin 3 → ℝ =>
          star (fockOneParticleFun ν s₁ f₁ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm s₁)) *
            fockOneParticleFun ν s₁ f₂
              (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm s₁))).symm ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      have h_u : (Equiv.funUnique (Fin 1) (Fin ν)).symm s₁ 0 = s₁ := rfl
      simp [fockOneParticleFun, h_u]
    · intro σ _ hne
      have h_zero : (fun k : Fin 1 → Fin 3 → ℝ =>
          star (fockOneParticleFun ν s₁ f₁ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) *
            fockOneParticleFun ν s₁ f₂ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) =
          fun _ => 0 := by
        ext k
        simp [fockOneParticleFun, hne]
      rw [h_zero, integral_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s₁))
  · rw [if_neg h12]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have h_zero : (fun k : Fin 1 → Fin 3 → ℝ =>
        star (fockOneParticleFun ν s₁ f₁ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) *
          fockOneParticleFun ν s₂ f₂ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) =
        fun _ => 0 := by
      ext k
      dsimp [fockOneParticleFun]
      by_cases hσ1 : σ = s₁
      · subst hσ1
        have hσ2 : σ ≠ s₂ := h12
        simp [hσ2]
      · simp [hσ1]
    rw [h_zero, integral_zero]

lemma fockMinkowskiTranslate_fockOneParticleVec_inner (m : ℝ)
    (ν : ℕ) (s₁ s₂ : Fin ν) (a : Fin 4 → ℝ) (f₁ f₂ : SmoothWavepacket) :
    ⟪fockMinkowskiTranslate m a (fockOneParticleVec ν s₁ f₁),
      fockOneParticleVec ν s₂ f₂⟫_ℂ =
      if s₁ = s₂ then
        ∫ p : Fin 3 → ℝ,
          star (fockMinkowskiPhase a (massShellVec m p) * f₁.amp p) * f₂.amp p
      else 0 := by
  let v₁ := fockOneParticleVec ν s₁ f₁
  let v₂ := fockOneParticleVec ν s₂ f₂
  let Uv₁ := fockMinkowskiTranslate m a v₁
  have h_ae1 : (Uv₁ : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      fun z => fockMinkowskiPhase a (fockTotalMomentum m z) *
        sectorToOmega ν 1 (fockOneParticleFun ν s₁ f₁) z := by
    have h_m := fockMultCLM_coeFn (fun z : FockOmega ν =>
        fockMinkowskiPhase a (fockTotalMomentum m z))
      ((continuous_fockMinkowskiPhase a).measurable.comp (measurable_fockTotalMomentum ν m))
      zero_le_one (fun z => (norm_fockMinkowskiPhase a (fockTotalMomentum m z)).le) v₁
    have h_v1 : (v₁ : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
        sectorToOmega ν 1 (fockOneParticleFun ν s₁ f₁) :=
      (memLp_sectorToOmega (measurable_fockOneParticleFun ν s₁ f₁)
        (memLp_fockOneParticleFun ν s₁ f₁)).coeFn_toLp
    filter_upwards [h_m, h_v1] with z hmz hv1z
    dsimp [Uv₁, fockMinkowskiTranslate]
    rw [hmz, hv1z]
  have h_ae2 : (v₂ : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      sectorToOmega ν 1 (fockOneParticleFun ν s₂ f₂) :=
    (memLp_sectorToOmega (measurable_fockOneParticleFun ν s₂ f₂)
      (memLp_fockOneParticleFun ν s₂ f₂)).coeFn_toLp
  rw [L2.inner_def]
  have h_congr :
      (∫ z : FockOmega ν, ⟪(Uv₁ : FockOmega ν → ℂ) z, (v₂ : FockOmega ν → ℂ) z⟫_ℂ
        ∂(fockMeasure ν)) =
      ∫ z : FockOmega ν,
        star (fockMinkowskiPhase a (fockTotalMomentum m z) *
            sectorToOmega ν 1 (fockOneParticleFun ν s₁ f₁) z) *
          sectorToOmega ν 1 (fockOneParticleFun ν s₂ f₂) z ∂(fockMeasure ν) := by
    refine integral_congr_ae ?_
    filter_upwards [h_ae1, h_ae2] with z hz1 hz2
    rw [hz1, hz2]
    simp [RCLike.inner_apply, mul_comm]
  rw [h_congr]
  let g₁ : FockSectorDom ν 1 → ℂ := fun x =>
    fockMinkowskiPhase a (massShellVec m (x.1 0)) * fockOneParticleFun ν s₁ f₁ x
  have hg₁_meas : Measurable g₁ :=
    ((continuous_fockMinkowskiPhase a).measurable.comp
      ((continuous_massShellVec m).measurable.comp
        ((measurable_pi_apply 0).comp measurable_fst))).mul
      (measurable_fockOneParticleFun ν s₁ f₁)
  have hg₁_lp : MemLp g₁ 2 (fockSectorMeasure ν 1) := by
    refine (memLp_fockOneParticleFun ν s₁ f₁).norm.mono' hg₁_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    dsimp [g₁]
    rw [norm_mul, norm_fockMinkowskiPhase, one_mul]
  have h_sec_eq :
      (fun z : FockOmega ν =>
        star (fockMinkowskiPhase a (fockTotalMomentum m z) *
            sectorToOmega ν 1 (fockOneParticleFun ν s₁ f₁) z) *
          sectorToOmega ν 1 (fockOneParticleFun ν s₂ f₂) z) =
      fun z : FockOmega ν =>
        star (sectorToOmega ν 1 g₁ z) * sectorToOmega ν 1 (fockOneParticleFun ν s₂ f₂) z := by
    ext ⟨r, x⟩
    by_cases hr : r = 1
    · subst hr
      have h_tot : fockTotalMomentum m ⟨1, x⟩ = massShellVec m (x.1 0) := by
        unfold fockTotalMomentum
        simp
      simp [sectorToOmega, g₁, h_tot]
    · simp [sectorToOmega, hr]
  rw [h_sec_eq, integral_fockMeasure_mul_sectorToOmega_eq hg₁_meas hg₁_lp
    (measurable_fockOneParticleFun ν s₂ f₂) (memLp_fockOneParticleFun ν s₂ f₂)]
  have h_prod_int : Integrable
      (fun x : FockSectorDom ν 1 => star (g₁ x) * fockOneParticleFun ν s₂ f₂ x)
      (fockSectorMeasure ν 1) := by
    have h1 := memLp_sectorToOmega hg₁_meas hg₁_lp
    have h2 := memLp_sectorToOmega (measurable_fockOneParticleFun ν s₂ f₂)
      (memLp_fockOneParticleFun ν s₂ f₂)
    have hi := L2.integrable_inner (𝕜 := ℂ) (h1.toLp _) (h2.toLp _)
    have h_fint : Integrable (fun z : FockOmega ν =>
        star (sectorToOmega ν 1 g₁ z) * sectorToOmega ν 1 (fockOneParticleFun ν s₂ f₂) z)
        (fockMeasure ν) := by
      refine hi.congr ?_
      filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with z hz1 hz2
      rw [RCLike.inner_apply, hz1, hz2]
      simp [mul_comm]
    unfold fockMeasure at h_fint
    have hm_map : Integrable (fun z : FockOmega ν =>
        star (sectorToOmega ν 1 g₁ z) * sectorToOmega ν 1 (fockOneParticleFun ν s₂ f₂) z)
        ((fockSectorMeasure ν 1).map (Sigma.mk 1)) :=
      h_fint.mono_measure (Measure.le_sum _ 1)
    have h_comp := (integrable_map_measure hm_map.1
      (measurable_fockSigmaMk ν 1).aemeasurable).mp hm_map
    exact h_comp.congr (Filter.Eventually.of_forall fun x => by simp [sectorToOmega])
  rw [integral_fockSectorMeasure_complex h_prod_int,
    ← (Equiv.funUnique (Fin 1) (Fin ν)).symm.sum_comp]
  let eu := (MeasurableEquiv.funUnique (Fin 1) (Fin 3 → ℝ)).symm
  let mp_u := (volume_preserving_funUnique (Fin 1) (Fin 3 → ℝ)).symm
  by_cases h12 : s₁ = s₂
  · subst h12
    rw [if_pos rfl, Finset.sum_eq_single s₁]
    · refine Eq.trans (mp_u.integral_comp eu.measurableEmbedding
        (fun k : Fin 1 → Fin 3 → ℝ =>
          star (g₁ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm s₁)) *
            fockOneParticleFun ν s₁ f₂
              (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm s₁))).symm ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      have h_u : (Equiv.funUnique (Fin 1) (Fin ν)).symm s₁ 0 = s₁ := rfl
      simp [g₁, fockOneParticleFun, h_u]
    · intro σ _ hne
      have h_zero : (fun k : Fin 1 → Fin 3 → ℝ =>
          star (g₁ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) *
            fockOneParticleFun ν s₁ f₂ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) =
          fun _ => 0 := by
        ext k
        simp [g₁, fockOneParticleFun, hne]
      rw [h_zero, integral_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s₁))
  · rw [if_neg h12]
    refine Finset.sum_eq_zero fun σ _ => ?_
    have h_zero : (fun k : Fin 1 → Fin 3 → ℝ =>
        star (g₁ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) *
          fockOneParticleFun ν s₂ f₂ (k, (Equiv.funUnique (Fin 1) (Fin ν)).symm σ)) =
        fun _ => 0 := by
      ext k
      dsimp [g₁, fockOneParticleFun]
      by_cases hσ1 : σ = s₁
      · subst hσ1
        have hσ2 : σ ≠ s₂ := h12
        simp [hσ2]
      · simp [hσ1]
    rw [h_zero, integral_zero]

theorem inner_vacuum_haagRuelleVacCreate_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    ⟪D.vacuum, haagRuelleVacCreate D s f t⟫_ℂ = 0 := by
  have h_vac_eq : D.vacuum = wightmanSchwartzVec D.wightman.WData 0 Fin.elim0
      (momentumWavepacketCompactSchwartz 0 0).val :=
    (wightmanSchwartzVec_compact D.wightman.WData 0 Fin.elim0
      (momentumWavepacketCompactSchwartz 0 0)).symm
  rw [h_vac_eq, haagRuelleVacCreate_eq_sum, inner_sum]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [inner_wightmanSchwartzVec, Finset.univ_unique, Finset.sum_singleton]
  have h_id : (Fin.append ((default : Fin 0 → ι) ∘ Fin.rev) (fun _ : Fin 1 => α)) =
      fun _ : Fin 1 => α := by
    ext i
    fin_cases i
    rfl
  rw [Fin.prod_univ_zero, one_mul, h_id]
  have h_cat_test : borchersConcatSchwartz 0 1 (momentumWavepacketCompactSchwartz 0 0).val
      (haagRuelleIndexedTest D s f t α) = haagRuelleIndexedTest D s f t α := by
    ext x
    rw [borchersConcatSchwartz_apply, momentumWavepacketCompactSchwartz_val,
      momentumWavepacketSchwartz_zero_zero_apply, map_one, one_mul]
    have hx : (fun i : Fin 1 => x (Fin.natAdd 0 i)) = x := by
      ext i μ; rw [Subsingleton.elim i 0]; rfl
    rw [hx]
  rw [h_cat_test]
  refine D.massGap 1 (fun _ => α) (haagRuelleIndexedTest D s f t α) ?_
  let U : Set (Fin 1 → Fin 4 → ℝ) :=
    { p | -p 0 ∉ tsupport (massShellCutoff m M D.hm D.hM) }
  have hU_open : IsOpen U :=
    (isClosed_tsupport (massShellCutoff m M D.hm D.hM)).isOpen_compl.preimage
      (by fun_prop : Continuous fun p : Fin 1 → Fin 4 → ℝ => -p 0)
  have hU_sub : massGapSpectralRegion m M 1 ⊆ U := by
    intro p hp
    have hp0 : p 0 = 0 := by simpa [Fin.sum_univ_one] using hp.1
    dsimp [U]
    rw [hp0, neg_zero]
    intro h_ts
    have hb := tsupport_massShellCutoff_bounds D.hm D.hM h_ts
    have hb1 : m / 4 ≤ 0 := by simpa using hb.1
    linarith [D.hm, hb1]
  refine ⟨U, hU_open, hU_sub, fun p hp => ?_⟩
  have h_eq : p = fun _ => -(-p 0) := by
    ext i μ
    rw [Subsingleton.elim i 0]
    simp
  rw [h_eq]
  exact minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
    (dualModeWavepacket D s α f) t hp

lemma inner_oneParticle_pair_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s₁ s₂ : Fin D.mode.ν) (f₁ f₂ : SmoothWavepacket)
    (ψ₁ ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (φ₁ φ₂ : (Fin 3 → ℝ) → ℂ)
    (hφ₁_cont : Continuous φ₁) (hφ₂_cont : Continuous φ₂)
    (hψ₂_supp : ∀ α₂ : ι, ∀ q : Fin 4 → ℝ,
      q ∉ tsupport (massShellCutoff m M D.hm D.hM) →
      minkowskiFourier (ψ₂ α₂) (fun _ => -q) = 0)
    (hψ₁_shell : ∀ α₁ : ι, ∀ p : Fin 3 → ℝ,
      minkowskiFourier (ψ₁ α₁) (fun _ => -massShellVec m p) =
        φ₁ p * (D.dual_w s₁ p α₁ * f₁.amp p))
    (hψ₂_shell : ∀ α₂ : ι, ∀ p : Fin 3 → ℝ,
      minkowskiFourier (ψ₂ α₂) (fun _ => -massShellVec m p) =
        φ₂ p * (D.dual_w s₂ p α₂ * f₂.amp p)) :
    ⟪∑ α₁ : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₁) (ψ₁ α₁),
      ∑ α₂ : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₂) (ψ₂ α₂)⟫_ℂ =
      if s₁ = s₂ then ∫ p : Fin 3 → ℝ, star (φ₁ p * f₁.amp p) * (φ₂ p * f₂.amp p) else 0 := by
  rw [sum_inner]
  simp_rw [inner_sum]
  let g₁ : ι → (Fin 3 → ℝ) → ℂ := fun α₁ p => φ₁ p * (D.dual_w s₁ p α₁ * f₁.amp p)
  let g₂ : ι → (Fin 3 → ℝ) → ℂ := fun α₂ p => φ₂ p * (D.dual_w s₂ p α₂ * f₂.amp p)
  have hg₁_cont : ∀ α₁ : ι, Continuous (g₁ α₁) := fun α₁ =>
    hφ₁_cont.mul ((D.contDiff_dual_w s₁ α₁).continuous.mul f₁.smooth.continuous)
  have hg₂_cont : ∀ α₂ : ι, Continuous (g₂ α₂) := fun α₂ =>
    hφ₂_cont.mul ((D.contDiff_dual_w s₂ α₂).continuous.mul f₂.smooth.continuous)
  have hg₁_supp : ∀ α₁ : ι, HasCompactSupport (g₁ α₁) := fun α₁ =>
    (f₁.compactSupport.mul_left).mul_left
  have hg₂_supp : ∀ α₂ : ι, HasCompactSupport (g₂ α₂) := fun α₂ =>
    (f₂.compactSupport.mul_left).mul_left
  have h_term : ∀ α₁ α₂ : ι,
      ⟪wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₁) (ψ₁ α₁),
        wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₂) (ψ₂ α₂)⟫_ℂ =
      ∫ p : Fin 3 → ℝ, (star (g₁ α₁ p) * g₂ α₂ p) *
        (∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) := by
    intro α₁ α₂
    rw [inner_wightmanSchwartzVec, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    have h_shell : ∀ γ : ι,
        D.wightman.WData.W (1 + 1)
          (Fin.append ((fun _ : Fin 1 => γ) ∘ Fin.rev) (fun _ : Fin 1 => α₂))
          (borchersConcatSchwartz 1 1 (ψ₁ α₁) (ψ₂ α₂)) =
        ∫ p : Fin 3 → ℝ,
          massShellWeight m D.C_shell ![γ, α₂] p * (star (g₁ α₁ p) * g₂ α₂ p) := by
      intro γ
      have h_app : (Fin.append ((fun _ : Fin 1 => γ) ∘ Fin.rev) (fun _ : Fin 1 => α₂)) =
          ![γ, α₂] := by
        ext i; fin_cases i <;> rfl
      rw [h_app]
      have h_two := twoPoint_borchersConcat_eq_massShell_of_right_cutoff D ![γ, α₂]
        (ψ₁ α₁) (ψ₂ α₂) (hψ₂_supp α₂)
      rw [h_two, massShellTwoPointW_two_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      dsimp only
      rw [minkowskiFourier_split_one_one_twoPointMomentum (massShellVec m p)
        (ψ₁ α₁) (ψ₂ α₂) _ (borchersConcatSchwartz_apply 1 1 _ _),
        hψ₁_shell α₁ p, hψ₂_shell α₂ p]
      rfl
    have h_sum_step :
        (∑ γ : ι,
          (∏ i : Fin 1, S.C α₁ ((Equiv.funUnique (Fin 1) ι).symm γ i)) *
            D.wightman.WData.W (1 + 1)
              (Fin.append ((Equiv.funUnique (Fin 1) ι).symm γ ∘ Fin.rev) (fun _ => α₂))
              (borchersConcatSchwartz 1 1 (ψ₁ α₁) (ψ₂ α₂))) =
        ∑ γ : ι, ∫ p : Fin 3 → ℝ, S.C α₁ γ *
          (massShellWeight m D.C_shell ![γ, α₂] p * (star (g₁ α₁ p) * g₂ α₂ p)) := by
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [Fin.prod_univ_one]
      have h_sym : (Equiv.funUnique (Fin 1) ι).symm γ 0 = γ := rfl
      have h_fun_sym : (Equiv.funUnique (Fin 1) ι).symm γ = fun _ : Fin 1 => γ := by
        ext i; rw [Subsingleton.elim i 0]; rfl
      rw [h_sym, h_fun_sym, h_shell γ, integral_const_mul]
    rw [h_sum_step]
    have h_int_each : ∀ γ : ι, Integrable
        (fun p : Fin 3 → ℝ =>
          S.C α₁ γ * (massShellWeight m D.C_shell ![γ, α₂] p * (star (g₁ α₁ p) * g₂ α₂ p)))
        volume := by
      intro γ
      rcases D.hC.2 ![γ, α₂] with ⟨B_w, hBw_nn, hBw⟩
      let K_int : (Fin 3 → ℝ) → ℝ := fun p =>
        ‖S.C α₁ γ‖ * B_w * ‖star (g₁ α₁ p) * g₂ α₂ p‖
      have h_prod_cont : Continuous (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
        (hg₁_cont α₁).star.mul (hg₂_cont α₂)
      have h_prod_supp : HasCompactSupport (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
        (hg₂_supp α₂).mul_left
      have hK_int : Integrable K_int volume :=
        ((h_prod_cont.norm).integrable_of_hasCompactSupport h_prod_supp.norm).const_mul
          (‖S.C α₁ γ‖ * B_w)
      have h_meas : Measurable (fun p : Fin 3 → ℝ =>
          S.C α₁ γ * (massShellWeight m D.C_shell ![γ, α₂] p * (star (g₁ α₁ p) * g₂ α₂ p))) :=
        measurable_const.mul ((measurable_massShellWeight D.hC ![γ, α₂]).mul h_prod_cont.measurable)
      refine hK_int.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
      rw [norm_mul, norm_mul]
      have h1 : ‖massShellWeight m D.C_shell ![γ, α₂] p‖ ≤ B_w := hBw p
      calc ‖S.C α₁ γ‖ * (‖massShellWeight m D.C_shell ![γ, α₂] p‖ *
            ‖star (g₁ α₁ p) * g₂ α₂ p‖)
          ≤ ‖S.C α₁ γ‖ * (B_w * ‖star (g₁ α₁ p) * g₂ α₂ p‖) := by gcongr
        _ = K_int p := by dsimp [K_int]; ring
    rw [← integral_finsetSum Finset.univ fun γ _ => h_int_each γ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    have h_swap_w :
        (∑ γ : ι, S.C α₁ γ * (massShellWeight m D.C_shell ![γ, α₂] p *
          (star (g₁ α₁ p) * g₂ α₂ p))) =
        (star (g₁ α₁ p) * g₂ α₂ p) *
          (∑ γ : ι, S.C α₁ γ * massShellWeight m D.C_shell ![γ, α₂] p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      ring
    rw [h_swap_w, D.mode.factor_weight]
  simp_rw [h_term]
  have h_prod_int : ∀ α₁ α₂ : ι, Integrable
      (fun p : Fin 3 → ℝ => (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) volume := by
    intro α₁ α₂
    have h_prod_cont : Continuous (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
      (hg₁_cont α₁).star.mul (hg₂_cont α₂)
    have h_prod_supp : HasCompactSupport (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
      (hg₂_supp α₂).mul_left
    have h_meas_w : Measurable (fun p : Fin 3 → ℝ =>
        ∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) :=
      Finset.measurable_sum Finset.univ fun r_s _ =>
        (continuous_star.measurable.comp (D.mode.measurable_w r_s α₁)).mul
          (D.mode.measurable_w r_s α₂)
    let C_bd : ℝ := (D.mode.ν : ℝ) * D.mode.M ^ 2
    have h_dom_int : Integrable (fun p : Fin 3 → ℝ =>
        C_bd * ‖star (g₁ α₁ p) * g₂ α₂ p‖) volume :=
      ((h_prod_cont.norm).integrable_of_hasCompactSupport h_prod_supp.norm).const_mul C_bd
    refine h_dom_int.mono' (h_prod_cont.measurable.mul h_meas_w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    have h_sum_le : ‖∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂‖ ≤
        C_bd := by
      calc ‖∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂‖
          ≤ ∑ r_s : Fin D.mode.ν, ‖star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _r_s : Fin D.mode.ν, D.mode.M ^ 2 := by
            refine Finset.sum_le_sum fun r_s _ => ?_
            rw [norm_mul, norm_star, sq]
            exact mul_le_mul (D.mode.norm_w_le r_s p α₁) (D.mode.norm_w_le r_s p α₂)
              (norm_nonneg _) D.mode.hM
        _ = C_bd := by simp [C_bd]
    exact (mul_le_mul_of_nonneg_left h_sum_le (norm_nonneg _)).trans (le_of_eq (mul_comm _ _))
  have h_sum_int :
      (∑ α₁ : ι, ∑ α₂ : ι, ∫ p : Fin 3 → ℝ, (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) =
      ∫ p : Fin 3 → ℝ, ∑ α₁ : ι, ∑ α₂ : ι, (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂ := by
    symm
    rw [integral_finsetSum Finset.univ fun α₁ _ =>
      integrable_finsetSum Finset.univ fun α₂ _ => h_prod_int α₁ α₂]
    refine Finset.sum_congr rfl fun α₁ _ => ?_
    exact integral_finsetSum Finset.univ fun α₂ _ => h_prod_int α₁ α₂
  rw [h_sum_int]
  have h_pt : ∀ p : Fin 3 → ℝ,
      (∑ α₁ : ι, ∑ α₂ : ι, (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) =
      if s₁ = s₂ then star (φ₁ p * f₁.amp p) * (φ₂ p * f₂.amp p) else 0 := by
    intro p
    have h_alg :
        (∑ α₁ : ι, ∑ α₂ : ι, (star (g₁ α₁ p) * g₂ α₂ p) *
          ∑ r_s : Fin D.mode.ν, star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) =
        ∑ r_s : Fin D.mode.ν,
          star ((∑ α₁ : ι, D.mode.w r_s p α₁ * D.dual_w s₁ p α₁) * (φ₁ p * f₁.amp p)) *
            ((∑ α₂ : ι, D.mode.w r_s p α₂ * D.dual_w s₂ p α₂) * (φ₂ p * f₂.amp p)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, star_sum, star_mul']
      have h_pull : ∀ α₁ : ι,
          (∑ α₂ : ι, ∑ r_s : Fin D.mode.ν,
            (star (g₁ α₁ p) * g₂ α₂ p) * (star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂)) =
          ∑ r_s : Fin D.mode.ν, ∑ α₂ : ι,
            (star (g₁ α₁ p) * g₂ α₂ p) * (star (D.mode.w r_s p α₁) * D.mode.w r_s p α₂) :=
        fun _ => Finset.sum_comm
      simp_rw [h_pull]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r_s _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun α₁ _ => ?_
      dsimp [g₁, g₂]
      simp only [map_mul]
      ring
    rw [h_alg]
    simp_rw [D.dual_orthonormal]
    by_cases h12 : s₁ = s₂
    · subst h12
      rw [if_pos rfl, Finset.sum_eq_single s₁]
      · simp
      · intro r_s _ hne
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ s₁))
    · rw [if_neg h12]
      refine Finset.sum_eq_zero fun r_s _ => ?_
      by_cases hr1 : r_s = s₁
      · subst hr1
        have hr2 : r_s ≠ s₂ := h12
        simp [hr2]
      · simp [hr1]
  simp_rw [h_pt]
  split_ifs with h12
  · rfl
  · simp

theorem inner_haagRuelleVacCreate_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s₁ s₂ : Fin D.mode.ν) (f₁ f₂ : SmoothWavepacket) (t₁ t₂ : ℝ) :
    ⟪haagRuelleVacCreate D s₁ f₁ t₁, haagRuelleVacCreate D s₂ f₂ t₂⟫_ℂ =
      ⟪fockOneParticleVec D.mode.ν s₁ f₁, fockOneParticleVec D.mode.ν s₂ f₂⟫_ℂ := by
  rw [haagRuelleVacCreate_eq_sum, haagRuelleVacCreate_eq_sum, inner_fockOneParticleVec_eq]
  refine (inner_oneParticle_pair_eq D s₁ s₂ f₁ f₂
    (haagRuelleIndexedTest D s₁ f₁ t₁) (haagRuelleIndexedTest D s₂ f₂ t₂)
    (fun _ => 1) (fun _ => 1) continuous_const continuous_const
    (fun α₂ q hq => minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
      (dualModeWavepacket D s₂ α₂ f₂) t₂ hq)
    (fun α₁ p => by
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply, one_mul])
    (fun α₂ p => by
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply, one_mul])).trans
      ?_
  simp

theorem haagRuelleVacCreate_time_indep
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleVacCreate D s f t = haagRuelleVacCreate D s f 0 := by
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ),
    inner_sub_left, inner_sub_right, inner_sub_right,
    inner_haagRuelleVacCreate_eq, inner_haagRuelleVacCreate_eq,
    inner_haagRuelleVacCreate_eq, inner_haagRuelleVacCreate_eq]
  ring

theorem haagRuelleDerivVacCreate_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleDerivVacCreate D s f t = 0 := by
  rw [← inner_self_eq_zero (𝕜 := ℂ), haagRuelleDerivVacCreate_eq_sum]
  refine (inner_oneParticle_pair_eq D s s f f
    (haagRuelleDerivIndexedTest D s f t) (haagRuelleDerivIndexedTest D s f t)
    (fun _ => 0) (fun _ => 0) continuous_const continuous_const
    (fun α₂ q hq => minkowskiFourier_haagRuelleDerivTestFn_eq_zero_of_notMem D.hm D.hM
      (dualModeWavepacket D s α₂ f) t hq)
    (fun α₁ p => by
      dsimp [haagRuelleDerivIndexedTest]
      rw [minkowskiFourier_haagRuelleDerivTestFn_massShell, zero_mul])
    (fun α₂ p => by
      dsimp [haagRuelleDerivIndexedTest]
      rw [minkowskiFourier_haagRuelleDerivTestFn_massShell, zero_mul])).trans ?_
  simp

theorem inner_translate_haagRuelleVacCreate_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (s₁ s₂ : Fin D.mode.ν) (f₁ f₂ : SmoothWavepacket) (t₁ t₂ : ℝ) :
    ⟪D.translate a (haagRuelleVacCreate D s₁ f₁ t₁), haagRuelleVacCreate D s₂ f₂ t₂⟫_ℂ =
      ⟪fockMinkowskiTranslate m a (fockOneParticleVec D.mode.ν s₁ f₁),
        fockOneParticleVec D.mode.ν s₂ f₂⟫_ℂ := by
  rw [haagRuelleVacCreate_eq_sum, haagRuelleVacCreate_eq_sum]
  change ⟪D.translate a (∑ α₁ : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₁)
      (haagRuelleIndexedTest D s₁ f₁ t₁ α₁)),
    ∑ α₂ : ι, wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₂)
      (haagRuelleIndexedTest D s₂ f₂ t₂ α₂)⟫_ℂ = _
  rw [IsolatedMassShellData.translate, map_sum]
  simp_rw [wightmanTranslate_wightmanSchwartzVec]
  rw [inner_oneParticle_pair_eq D s₁ s₂ f₁ f₂
    (fun α₁ => schwartzDiagTranslateN 1 a (haagRuelleIndexedTest D s₁ f₁ t₁ α₁))
    (haagRuelleIndexedTest D s₂ f₂ t₂)
    (fun p => fockMinkowskiPhase a (massShellVec m p)) (fun _ => 1)
    ((continuous_fockMinkowskiPhase a).comp (continuous_massShellVec m)) continuous_const
    (fun α₂ q hq => minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
      (dualModeWavepacket D s₂ α₂ f₂) t₂ hq)
    (fun α₁ p => by
      rw [minkowskiFourier_schwartzDiagTranslateN]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply]
      congr 1
      rw [Fin.sum_univ_one]
      unfold fockMinkowskiPhase
      congr 1
      have h_neg : minkowskiInner (-massShellVec m p) a =
          -minkowskiInner (massShellVec m p) a := by
        simp [minkowskiInner_explicit]
        ring
      rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg])
    (fun α₂ p => by
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply, one_mul])]
  rw [fockMinkowskiTranslate_fockOneParticleVec_inner]
  split_ifs with h12
  · simp_rw [one_mul]
  · rfl

theorem haagRuelleVacCreate_bump_ne_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (t : ℝ) :
    haagRuelleVacCreate D s (bumpWavepacket 0 (m / 4) (by positivity [D.hm])) t ≠ 0 := by
  let f := bumpWavepacket 0 (m / 4) (by positivity [D.hm])
  intro h0
  have h_inner0 : ⟪haagRuelleVacCreate D s f t, haagRuelleVacCreate D s f t⟫_ℂ = 0 := by
    rw [h0, inner_zero_left]
  rw [inner_haagRuelleVacCreate_eq, inner_fockOneParticleVec_eq, if_pos rfl] at h_inner0
  have h_re : (∫ p : Fin 3 → ℝ, (star (f.amp p) * f.amp p)) =
      ((∫ p : Fin 3 → ℝ, ‖f.amp p‖ ^ 2 : ℝ) : ℂ) := by
    have h_fn : (fun p : Fin 3 → ℝ => star (f.amp p) * f.amp p) =
        fun p => ((‖f.amp p‖ ^ 2 : ℝ) : ℂ) := by
      ext p
      rw [Complex.star_def, mul_comm, Complex.mul_conj', Complex.ofReal_pow]
    rw [h_fn, integral_complex_ofReal]
  rw [h_re, Complex.ofReal_eq_zero] at h_inner0
  have h_int : Integrable (fun p : Fin 3 → ℝ => ‖f.amp p‖ ^ 2) volume :=
    smoothWavepacket_normSq_integrable f
  have h_ae : (fun p : Fin 3 → ℝ => ‖f.amp p‖ ^ 2) =ᶠ[ae volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg _) h_int).mp h_inner0
  have h_ev : ∀ p : Fin 3 → ℝ, ‖f.amp p‖ ^ 2 = 0 :=
    fun p => congr_fun
      ((Continuous.ae_eq_iff_eq volume
        (continuous_smoothWavepacket_normSq f) continuous_const).mp
        h_ae) p
  have h_at0 := h_ev 0
  have h_val0 : f.amp 0 = 1 := bumpWavepacket_apply_center 0 (m / 4) (by positivity [D.hm])
  rw [h_val0, norm_one, one_pow] at h_at0
  exact one_ne_zero h_at0

theorem haagRuelleAdjVacCreate_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleAdjVacCreate D s f t = 0 := by
  rw [haagRuelleAdjVacCreate_eq_sum]
  refine Finset.sum_eq_zero fun β₀ _ => ?_
  refine wightmanSchwartzVec_eq_zero_of_fourier_zero_near_massGapSpectrum D.wightman.WData
    D.massGap 1 (fun _ => β₀) (haagRuelleAdjIndexedTest D s f t β₀) ?_
  let V : Set (Fin 1 → Fin 4 → ℝ) := { q | -(q 0) 0 > -m / 8 }
  have hV_open : IsOpen V :=
    isOpen_lt continuous_const (by fun_prop : Continuous fun q : Fin 1 → Fin 4 → ℝ => -(q 0) 0)
  have hV_sub : { q : Fin 1 → Fin 4 → ℝ | -(∑ i : Fin 1, q i) ∈ massGapSpectrum m M } ⊆ V := by
    intro q hq
    rw [Set.mem_setOf_eq, Fin.sum_univ_one] at hq
    have h0_nn : 0 ≤ (-q 0) 0 := mem_massGapSpectrum_energy_nonneg D.hm D.hM hq
    simp only [Pi.neg_apply] at h0_nn
    dsimp [V]
    linarith [D.hm, h0_nn]
  refine ⟨V, hV_open, hV_sub, fun q hq => ?_⟩
  unfold haagRuelleAdjIndexedTest starIndexedTest
  rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply]
  refine Finset.sum_eq_zero fun α₀ _ => ?_
  rw [map_smul, _root_.smul_apply, minkowskiFourierCLM_apply,
    minkowskiFourier_schwartzConj_one, smul_eq_mul]
  have h_not : -( -q) 0 ∉ tsupport (massShellCutoff m M D.hm D.hM) := by
    have h_eq : -(-q) 0 = q 0 := by simp
    rw [h_eq]
    intro hts
    have hb := tsupport_massShellCutoff_bounds D.hm D.hM hts
    dsimp [V] at hq
    have hneg : -(q 0) 0 ≤ -m / 4 := by linarith [hb.1]
    linarith [D.hm]
  have h_eq_arg : -q = fun _ => -(q 0) := by
    ext i μ
    rw [Subsingleton.elim i 0]
    rfl
  rw [h_eq_arg]
  have h_not' : q 0 ∉ tsupport (massShellCutoff m M D.hm D.hM) := by
    simpa using h_not
  dsimp [haagRuelleIndexedTest]
  rw [minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
    (dualModeWavepacket D s α₀ f) t h_not', map_zero, mul_zero]

end

lemma fderiv_schwartzDiagTranslateN_apply (k : ℕ) (a : Fin 4 → ℝ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x d : Fin k → Fin 4 → ℝ) :
    fderiv ℝ (⇑(schwartzDiagTranslateN k a F)) x d =
      schwartzDiagTranslateN k a (schwartzDirDerivCLM k d F) x := by
  let v : Fin k → Fin 4 → ℝ := fun _ => a
  have h_sub_fn : (⇑(schwartzDiagTranslateN k a F)) = fun y => F (y - v) := rfl
  have h_diff_F : DifferentiableAt ℝ (⇑F) (x - v) :=
    (F.smooth 1).differentiable one_ne_zero (x - v)
  have h_fderiv : HasFDerivAt (fun y : Fin k → Fin 4 → ℝ => F (y - v))
      ((fderiv ℝ (⇑F) (x - v)).comp (ContinuousLinearMap.id ℝ (Fin k → Fin 4 → ℝ))) x :=
    h_diff_F.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const v)
  rw [h_sub_fn, h_fderiv.fderiv]
  rfl

lemma iteratedFDeriv_schwartzDiagTranslateN (k m : ℕ) (a : Fin 4 → ℝ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x : Fin k → Fin 4 → ℝ)
    (w : Fin m → (Fin k → Fin 4 → ℝ)) :
    iteratedFDeriv ℝ m (⇑(schwartzDiagTranslateN k a F)) x w =
      iteratedFDeriv ℝ m (⇑F) (x - fun _ => a) w := by
  induction m generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply]
    rfl
  | succ m ih =>
    rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]
    let v : Fin k → Fin 4 → ℝ := w (Fin.last m)
    let L_v : ((Fin k → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.apply ℝ ℂ v
    have h_comm1 : (iteratedFDeriv ℝ m (fderiv ℝ (⇑(schwartzDiagTranslateN k a F))) x
          (Fin.init w)) v =
        iteratedFDeriv ℝ m (L_v ∘ fderiv ℝ (⇑(schwartzDiagTranslateN k a F))) x
          (Fin.init w) := by
      have h_fcd : ContDiff ℝ (m : ℕ) (fderiv ℝ (⇑(schwartzDiagTranslateN k a F))) :=
        ((schwartzDiagTranslateN k a F).smooth (m + 1)).fderiv_right (by simp)
      change L_v _ = _
      rw [L_v.iteratedFDeriv_comp_left h_fcd.contDiffAt le_rfl]
      rfl
    have h_comm2 : (iteratedFDeriv ℝ m (fderiv ℝ (⇑F)) (x - fun _ => a) (Fin.init w)) v =
        iteratedFDeriv ℝ m (L_v ∘ fderiv ℝ (⇑F)) (x - fun _ => a) (Fin.init w) := by
      have h_fcd : ContDiff ℝ (m : ℕ) (fderiv ℝ (⇑F)) :=
        (F.smooth (m + 1)).fderiv_right (by simp)
      change L_v _ = _
      rw [L_v.iteratedFDeriv_comp_left h_fcd.contDiffAt le_rfl]
      rfl
    have h_fn1 : (L_v ∘ fderiv ℝ (⇑(schwartzDiagTranslateN k a F))) =
        ⇑(schwartzDiagTranslateN k a (schwartzDirDerivCLM k v F)) := by
      ext y
      exact fderiv_schwartzDiagTranslateN_apply k a F y v
    have h_fn2 : (L_v ∘ fderiv ℝ (⇑F)) = ⇑(schwartzDirDerivCLM k v F) := rfl
    rw [h_comm1, h_comm2, h_fn1, h_fn2]
    exact ih (schwartzDirDerivCLM k v F) (Fin.init w)

lemma norm_iteratedFDeriv_schwartzDiagTranslateN_eq (k m : ℕ) (a : Fin 4 → ℝ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x : Fin k → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ m (⇑(schwartzDiagTranslateN k a F)) x‖ =
      ‖iteratedFDeriv ℝ m (⇑F) (x - fun _ => a)‖ := by
  congr 1
  ext w
  exact iteratedFDeriv_schwartzDiagTranslateN k m a F x w

def diagConvRaw (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x : Fin k → Fin 4 → ℝ) : ℂ :=
  ∫ z : Fin 1 → Fin 4 → ℝ, ψ z * F (x - fun _ => z 0)

lemma hasFDerivAt_diagConvRaw (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x : Fin k → Fin 4 → ℝ) :
    HasFDerivAt (diagConvRaw k ψ F)
      (∫ z : Fin 1 → Fin 4 → ℝ, ψ z • fderiv ℝ (⇑F) (x - fun _ => z 0)) x := by
  let G : (Fin k → Fin 4 → ℝ) → (Fin 1 → Fin 4 → ℝ) → ℂ :=
    fun y z => ψ z * F (y - fun _ => z 0)
  let G' : (Fin k → Fin 4 → ℝ) → (Fin 1 → Fin 4 → ℝ) → (Fin k → Fin 4 → ℝ) →L[ℝ] ℂ :=
    fun y z => ψ z • fderiv ℝ (⇑F) (y - fun _ => z 0)
  let bound : (Fin 1 → Fin 4 → ℝ) → ℝ :=
    fun z => ‖ψ z‖ * SchwartzMap.seminorm ℝ 0 1 F
  have hG_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (G y) volume := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h_cont : Continuous (G y) :=
      ψ.continuous.mul (F.continuous.comp
        (continuous_const.sub (continuous_pi fun _ => continuous_apply 0)))
    exact h_cont.aestronglyMeasurable
  have hG_int : Integrable (G x) volume := by
    refine (ψ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 F)).mono' ?_ ?_
    · have h_cont : Continuous (G x) :=
        ψ.continuous.mul (F.continuous.comp
          (continuous_const.sub (continuous_pi fun _ => continuous_apply 0)))
      exact h_cont.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      dsimp [G]
      rw [norm_mul]
      have hF_bd : ‖F (x - fun _ => z 0)‖ ≤ SchwartzMap.seminorm ℝ 0 0 F := by
        simpa [norm_iteratedFDeriv_zero, pow_zero, one_mul] using
          SchwartzMap.le_seminorm ℝ 0 0 F (x - fun _ => z 0)
      exact mul_le_mul_of_nonneg_left hF_bd (norm_nonneg _)
  have hG'_meas : AEStronglyMeasurable (G' x) volume := by
    have h_fd : Continuous (fderiv ℝ (⇑F)) := (F.smooth 1).continuous_fderiv one_ne_zero
    have h_cont : Continuous (G' x) :=
      ψ.continuous.smul (h_fd.comp
        (continuous_const.sub (continuous_pi fun _ => continuous_apply 0)))
    exact h_cont.aestronglyMeasurable
  have h_bound : ∀ᵐ z ∂volume, ∀ y ∈ Metric.ball x 1, ‖G' y z‖ ≤ bound z := by
    refine Filter.Eventually.of_forall fun z y _ => ?_
    dsimp [G', bound]
    rw [norm_smul]
    have hF_bd : ‖fderiv ℝ (⇑F) (y - fun _ => z 0)‖ ≤ SchwartzMap.seminorm ℝ 0 1 F := by
      have h_s := SchwartzMap.le_seminorm ℝ 0 1 F (y - fun _ => z 0)
      simpa [norm_iteratedFDeriv_one, pow_zero, one_mul] using h_s
    exact mul_le_mul_of_nonneg_left hF_bd (norm_nonneg _)
  have h_bound_int : Integrable bound volume :=
    ψ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 1 F)
  have h_diff : ∀ᵐ z ∂volume, ∀ y ∈ Metric.ball x 1,
      HasFDerivAt (fun w => G w z) (G' y z) y := by
    refine Filter.Eventually.of_forall fun z y _ => ?_
    have h_diff_F : DifferentiableAt ℝ (⇑F) (y - fun _ => z 0) :=
      (F.smooth 1).differentiable one_ne_zero (y - fun _ => z 0)
    have h_comp : HasFDerivAt (fun w : Fin k → Fin 4 → ℝ => F (w - fun _ => z 0))
        ((fderiv ℝ (⇑F) (y - fun _ => z 0)).comp (ContinuousLinearMap.id ℝ (Fin k → Fin 4 → ℝ)))
        y :=
      h_diff_F.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (fun _ => z 0))
    rw [ContinuousLinearMap.comp_id] at h_comp
    exact h_comp.const_mul (ψ z)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.ball_mem_nhds x one_pos) hG_meas hG_int hG'_meas h_bound h_bound_int h_diff

lemma fderiv_diagConvRaw_apply (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x d : Fin k → Fin 4 → ℝ) :
    fderiv ℝ (diagConvRaw k ψ F) x d =
      diagConvRaw k ψ (schwartzDirDerivCLM k d F) x := by
  have h_fd := hasFDerivAt_diagConvRaw k ψ F x
  rw [h_fd.fderiv]
  let G' : (Fin 1 → Fin 4 → ℝ) → (Fin k → Fin 4 → ℝ) →L[ℝ] ℂ :=
    fun z => ψ z • fderiv ℝ (⇑F) (x - fun _ => z 0)
  have hG'_int : Integrable G' volume := by
    have h_cont : Continuous G' :=
      ψ.continuous.smul (((F.smooth 1).continuous_fderiv one_ne_zero).comp
        (continuous_const.sub (continuous_pi fun _ => continuous_apply 0)))
    refine (ψ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 1 F)).mono'
      h_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    dsimp [G']
    rw [norm_smul]
    have hF_bd : ‖fderiv ℝ (⇑F) (x - fun _ => z 0)‖ ≤ SchwartzMap.seminorm ℝ 0 1 F := by
      simpa [norm_iteratedFDeriv_one, pow_zero, one_mul] using
        SchwartzMap.le_seminorm ℝ 0 1 F (x - fun _ => z 0)
    exact mul_le_mul_of_nonneg_left hF_bd (norm_nonneg _)
  let ev : ((Fin k → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ d
  change ev (∫ z, G' z) = _
  rw [← ev.integral_comp_comm hG'_int]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp [ev, G']
  rw [_root_.smul_apply, smul_eq_mul]

lemma contDiff_nat_diagConvRaw (k n : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    ∀ F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ, ContDiff ℝ (n : ℕ) (diagConvRaw k ψ F) := by
  induction n with
  | zero =>
    intro F
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun x =>
      (hasFDerivAt_diagConvRaw k ψ F x).differentiableAt.continuousAt
  | succ n ih =>
    intro F
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_diagConvRaw k ψ F x).differentiableAt, fun h => by simp at h,
      fun d => ?_⟩
    have h_eq : (fun x => fderiv ℝ (diagConvRaw k ψ F) x d) =
        diagConvRaw k ψ (schwartzDirDerivCLM k d F) := by
      ext x
      exact fderiv_diagConvRaw_apply k ψ F x d
    rw [h_eq]
    exact ih (schwartzDirDerivCLM k d F)

lemma contDiff_diagConvRaw (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (diagConvRaw k ψ F) :=
  contDiff_infty.mpr fun n => contDiff_nat_diagConvRaw k n ψ F

lemma iteratedFDeriv_diagConvRaw_eq_integral (k m : ℕ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    ∀ (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (p : Fin k → Fin 4 → ℝ)
      (w : Fin m → (Fin k → Fin 4 → ℝ)),
      Integrable (fun z : Fin 1 → Fin 4 → ℝ =>
        ψ z * iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0) w) volume ∧
      iteratedFDeriv ℝ m (diagConvRaw k ψ F) p w =
        ∫ z : Fin 1 → Fin 4 → ℝ, ψ z * iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0) w := by
  induction m with
  | zero =>
    intro F p w
    have h_int : Integrable (fun z : Fin 1 → Fin 4 → ℝ =>
        ψ z * iteratedFDeriv ℝ 0 (⇑F) (p - fun _ => z 0) w) volume := by
      have h_eq : (fun z : Fin 1 → Fin 4 → ℝ =>
          ψ z * iteratedFDeriv ℝ 0 (⇑F) (p - fun _ => z 0) w) =
          fun z => ψ z * F (p - fun _ => z 0) := by
        ext z
        rw [iteratedFDeriv_zero_apply]
      rw [h_eq]
      refine (ψ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 F)).mono' ?_ ?_
      · exact (ψ.continuous.mul (F.continuous.comp
          (continuous_const.sub (continuous_pi fun _ => continuous_apply 0)))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun z => ?_
        rw [norm_mul]
        have hF_bd : ‖F (p - fun _ => z 0)‖ ≤ SchwartzMap.seminorm ℝ 0 0 F := by
          simpa [norm_iteratedFDeriv_zero, pow_zero, one_mul] using
            SchwartzMap.le_seminorm ℝ 0 0 F (p - fun _ => z 0)
        exact mul_le_mul_of_nonneg_left hF_bd (norm_nonneg _)
    refine ⟨h_int, ?_⟩
    rw [iteratedFDeriv_zero_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [iteratedFDeriv_zero_apply]
  | succ m ih =>
    intro F p w
    let v : Fin k → Fin 4 → ℝ := w (Fin.last m)
    let L_v : ((Fin k → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.apply ℝ ℂ v
    have h_comm1 :
        (iteratedFDeriv ℝ m (fderiv ℝ (diagConvRaw k ψ F)) p (Fin.init w)) v =
          iteratedFDeriv ℝ m (L_v ∘ fderiv ℝ (diagConvRaw k ψ F)) p (Fin.init w) := by
      have h_fcd : ContDiff ℝ (m : ℕ) (fderiv ℝ (diagConvRaw k ψ F)) :=
        (contDiff_nat_diagConvRaw k (m + 1) ψ F).fderiv_right (by simp)
      change L_v _ = _
      rw [L_v.iteratedFDeriv_comp_left h_fcd.contDiffAt le_rfl]
      rfl
    have h_fn1 : (L_v ∘ fderiv ℝ (diagConvRaw k ψ F)) =
        diagConvRaw k ψ (schwartzDirDerivCLM k v F) := by
      ext y
      exact fderiv_diagConvRaw_apply k ψ F y v
    have h_comm2 : ∀ q : Fin k → Fin 4 → ℝ,
        iteratedFDeriv ℝ (m + 1) (⇑F) q w =
          iteratedFDeriv ℝ m (⇑(schwartzDirDerivCLM k v F)) q (Fin.init w) := by
      intro q
      rw [iteratedFDeriv_succ_apply_right]
      have h_fcd : ContDiff ℝ (m : ℕ) (fderiv ℝ (⇑F)) :=
        (F.smooth (m + 1)).fderiv_right (by simp)
      have h_eqL : (iteratedFDeriv ℝ m (fderiv ℝ (⇑F)) q (Fin.init w)) v =
          iteratedFDeriv ℝ m (L_v ∘ fderiv ℝ (⇑F)) q (Fin.init w) := by
        change L_v _ = _
        rw [L_v.iteratedFDeriv_comp_left h_fcd.contDiffAt le_rfl]
        rfl
      exact h_eqL
    have h_ih := ih (schwartzDirDerivCLM k v F) p (Fin.init w)
    refine ⟨?_, ?_⟩
    · simp_rw [h_comm2]
      exact h_ih.1
    · rw [iteratedFDeriv_succ_apply_right, h_comm1, h_fn1, h_ih.2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [h_comm2]

lemma add_pow_le_two_pow_mul_add_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (l : ℕ) :
    (a + b) ^ l ≤ 2 ^ l * (a ^ l + b ^ l) := by
  have h1 : a + b ≤ 2 * max a b := by
    linarith [le_max_left a b, le_max_right a b]
  have h2 : (a + b) ^ l ≤ 2 ^ l * (max a b) ^ l := by
    calc (a + b) ^ l ≤ (2 * max a b) ^ l := pow_le_pow_left₀ (add_nonneg ha hb) h1 l
      _ = 2 ^ l * (max a b) ^ l := mul_pow 2 (max a b) l
  have h3 : (max a b) ^ l ≤ a ^ l + b ^ l := by
    rcases le_total a b with hab | hba
    · rw [max_eq_right hab]
      exact le_add_of_nonneg_left (pow_nonneg ha l)
    · rw [max_eq_left hba]
      exact le_add_of_nonneg_right (pow_nonneg hb l)
  exact h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))

lemma schwartzDiagTranslateN_poly_bound (k l m : ℕ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Fin 1 → Fin 4 → ℝ) (p : Fin k → Fin 4 → ℝ),
      ‖p‖ ^ l * ‖iteratedFDeriv ℝ m (⇑(schwartzDiagTranslateN k (z 0) F)) p‖ ≤
        C * (1 + ‖z‖ ^ l) := by
  let C : ℝ := 2 ^ l * (SchwartzMap.seminorm ℝ l m F + SchwartzMap.seminorm ℝ 0 m F)
  have hC_nn : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  refine ⟨C, hC_nn, fun z p => ?_⟩
  let v : Fin k → Fin 4 → ℝ := fun _ => z 0
  have hv_norm : ‖v‖ ≤ ‖z‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun _ => ?_
    exact norm_le_pi_norm z 0
  have hp_tri : ‖p‖ ≤ ‖p - v‖ + ‖z‖ :=
    (norm_le_norm_sub_add p v).trans (add_le_add le_rfl hv_norm)
  have hp_pow : ‖p‖ ^ l ≤ 2 ^ l * (‖p - v‖ ^ l + ‖z‖ ^ l) :=
    (pow_le_pow_left₀ (norm_nonneg p) hp_tri l).trans
      (add_pow_le_two_pow_mul_add_pow (norm_nonneg (p - v)) (norm_nonneg z) l)
  rw [norm_iteratedFDeriv_schwartzDiagTranslateN_eq]
  have h_sl := SchwartzMap.le_seminorm ℝ l m F (p - v)
  have h_s0 : ‖iteratedFDeriv ℝ m (⇑F) (p - v)‖ ≤ SchwartzMap.seminorm ℝ 0 m F := by
    simpa [pow_zero, one_mul] using SchwartzMap.le_seminorm ℝ 0 m F (p - v)
  calc ‖p‖ ^ l * ‖iteratedFDeriv ℝ m (⇑F) (p - v)‖
      ≤ 2 ^ l * (‖p - v‖ ^ l + ‖z‖ ^ l) * ‖iteratedFDeriv ℝ m (⇑F) (p - v)‖ :=
        mul_le_mul_of_nonneg_right hp_pow (norm_nonneg _)
    _ = 2 ^ l * ((‖p - v‖ ^ l * ‖iteratedFDeriv ℝ m (⇑F) (p - v)‖) +
          ‖z‖ ^ l * ‖iteratedFDeriv ℝ m (⇑F) (p - v)‖) := by ring
    _ ≤ 2 ^ l * (SchwartzMap.seminorm ℝ l m F + ‖z‖ ^ l * SchwartzMap.seminorm ℝ 0 m F) := by
        gcongr
    _ ≤ 2 ^ l * ((SchwartzMap.seminorm ℝ l m F + SchwartzMap.seminorm ℝ 0 m F) *
          (1 + ‖z‖ ^ l)) := by
        have hsl_nn := apply_nonneg (SchwartzMap.seminorm ℝ l m) F
        have hs0_nn := apply_nonneg (SchwartzMap.seminorm ℝ 0 m) F
        have hz_nn : 0 ≤ ‖z‖ ^ l := pow_nonneg (norm_nonneg z) l
        have h_prod_nn : 0 ≤ SchwartzMap.seminorm ℝ l m F * ‖z‖ ^ l := mul_nonneg hsl_nn hz_nn
        have h_inner_le : SchwartzMap.seminorm ℝ l m F +
              ‖z‖ ^ l * SchwartzMap.seminorm ℝ 0 m F ≤
            (SchwartzMap.seminorm ℝ l m F + SchwartzMap.seminorm ℝ 0 m F) * (1 + ‖z‖ ^ l) := by
          linarith only [hs0_nn, h_prod_nn]
        exact mul_le_mul_of_nonneg_left h_inner_le (by positivity)
    _ = C * (1 + ‖z‖ ^ l) := by dsimp [C]; ring

def diagConvSchwartz (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    SchwartzMap (Fin k → Fin 4 → ℝ) ℂ where
  toFun := diagConvRaw k ψ F
  smooth' := contDiff_diagConvRaw k ψ F
  decay' l m := by
    obtain ⟨C_F, hCF_nn, h_bd⟩ := schwartzDiagTranslateN_poly_bound k l m F
    refine ⟨∫ z : Fin 1 → Fin 4 → ℝ, C_F * (1 + ‖z‖ ^ l) * ‖ψ z‖, fun p => ?_⟩
    have h_op : ‖iteratedFDeriv ℝ m (diagConvRaw k ψ F) p‖ ≤
        ∫ z : Fin 1 → Fin 4 → ℝ, ‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ := by
      refine ContinuousMultilinearMap.opNorm_le_bound
        (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun w => ?_
      rw [(iteratedFDeriv_diagConvRaw_eq_integral k m ψ F p w).2]
      refine (norm_integral_le_integral_norm _).trans ?_
      have h_int_w : Integrable (fun z : Fin 1 → Fin 4 → ℝ =>
          ‖ψ z * iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0) w‖) volume :=
        (iteratedFDeriv_diagConvRaw_eq_integral k m ψ F p w).1.norm
      have h_int_dom : Integrable (fun z : Fin 1 → Fin 4 → ℝ =>
          ‖ψ z‖ * (‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ * ∏ i : Fin m, ‖w i‖))
          volume := by
        have h_cont : Continuous (fun z : Fin 1 → Fin 4 → ℝ =>
            ‖ψ z‖ * (‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ * ∏ i : Fin m, ‖w i‖)) :=
          ψ.continuous.norm.mul
            ((((F.smooth (m : ℕ∞)).continuous_iteratedFDeriv le_rfl).comp
              (continuous_const.sub (continuous_pi fun _ => continuous_apply 0))).norm.mul
              continuous_const)
        refine (ψ.integrable.norm.mul_const
          (SchwartzMap.seminorm ℝ 0 m F * ∏ i : Fin m, ‖w i‖)).mono'
          h_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have h_s0 : ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ ≤
            SchwartzMap.seminorm ℝ 0 m F := by
          simpa [pow_zero, one_mul] using
            SchwartzMap.le_seminorm ℝ 0 m F (p - fun _ => z 0)
        calc ‖ψ z‖ * (‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ * ∏ i : Fin m, ‖w i‖)
            ≤ ‖ψ z‖ * (SchwartzMap.seminorm ℝ 0 m F * ∏ i : Fin m, ‖w i‖) := by gcongr
          _ = ‖ψ z‖ * (SchwartzMap.seminorm ℝ 0 m F * ∏ i : Fin m, ‖w i‖) := rfl
      calc (∫ z : Fin 1 → Fin 4 → ℝ, ‖ψ z * iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0) w‖)
          ≤ ∫ z : Fin 1 → Fin 4 → ℝ,
              ‖ψ z‖ * (‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ * ∏ i : Fin m, ‖w i‖) := by
            refine integral_mono h_int_w h_int_dom fun z => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.le_opNorm _ _)
              (norm_nonneg _)
        _ = (∫ z : Fin 1 → Fin 4 → ℝ, ‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖) *
              ∏ i : Fin m, ‖w i‖ := by
            simp_rw [← mul_assoc]
            rw [integral_mul_const]
    have h_int_mid : Integrable (fun z : Fin 1 → Fin 4 → ℝ =>
        ‖p‖ ^ l * (‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖)) volume := by
      have h_cont : Continuous (fun z : Fin 1 → Fin 4 → ℝ =>
          ‖p‖ ^ l * (‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖)) :=
        continuous_const.mul (ψ.continuous.norm.mul
          (((F.smooth (m : ℕ∞)).continuous_iteratedFDeriv le_rfl).comp
            (continuous_const.sub (continuous_pi fun _ => continuous_apply 0))).norm)
      refine ((ψ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 m F)).const_mul
        (‖p‖ ^ l)).mono' h_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      have h_s0 : ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ ≤ SchwartzMap.seminorm ℝ 0 m F := by
        simpa [pow_zero, one_mul] using
          SchwartzMap.le_seminorm ℝ 0 m F (p - fun _ => z 0)
      gcongr
    have h_int_dom := integrable_polynomial_mul_schwartz 1 ψ C_F l
    calc ‖p‖ ^ l * ‖iteratedFDeriv ℝ m (diagConvRaw k ψ F) p‖
        ≤ ‖p‖ ^ l * ∫ z : Fin 1 → Fin 4 → ℝ,
            ‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖ :=
          mul_le_mul_of_nonneg_left h_op (pow_nonneg (norm_nonneg p) l)
      _ = ∫ z : Fin 1 → Fin 4 → ℝ,
            ‖p‖ ^ l * (‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖) :=
          (integral_const_mul _ _).symm
      _ ≤ ∫ z : Fin 1 → Fin 4 → ℝ, C_F * (1 + ‖z‖ ^ l) * ‖ψ z‖ := by
          refine integral_mono h_int_mid h_int_dom fun z => ?_
          have h_bd_z := h_bd z p
          rw [norm_iteratedFDeriv_schwartzDiagTranslateN_eq] at h_bd_z
          calc ‖p‖ ^ l * (‖ψ z‖ * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖)
              = (‖p‖ ^ l * ‖iteratedFDeriv ℝ m (⇑F) (p - fun _ => z 0)‖) * ‖ψ z‖ := by ring
            _ ≤ C_F * (1 + ‖z‖ ^ l) * ‖ψ z‖ :=
                mul_le_mul_of_nonneg_right h_bd_z (norm_nonneg _)

@[simp]
lemma diagConvSchwartz_apply (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (x : Fin k → Fin 4 → ℝ) :
    diagConvSchwartz k ψ F x = ∫ z : Fin 1 → Fin 4 → ℝ, ψ z * F (x - fun _ => z 0) := rfl

lemma diagConvSchwartz_sub_left (k : ℕ) (ψ₁ ψ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    diagConvSchwartz k (ψ₁ - ψ₂) F = diagConvSchwartz k ψ₁ F - diagConvSchwartz k ψ₂ F := by
  ext x
  rw [diagConvSchwartz_apply, _root_.sub_apply, diagConvSchwartz_apply, diagConvSchwartz_apply]
  have h_sub : (fun z : Fin 1 → Fin 4 → ℝ => (ψ₁ - ψ₂) z * F (x - fun _ => z 0)) =
      fun z => ψ₁ z * F (x - fun _ => z 0) - ψ₂ z * F (x - fun _ => z 0) := by
    ext z
    simp [_root_.sub_apply, sub_mul]
  rw [h_sub]
  have h_int : ∀ χ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ,
      Integrable (fun z : Fin 1 → Fin 4 → ℝ => χ z * F (x - fun _ => z 0)) volume := fun χ => by
    have h_cont : Continuous (fun z : Fin 1 → Fin 4 → ℝ => χ z * F (x - fun _ => z 0)) :=
      χ.continuous.mul (F.continuous.comp
        (continuous_const.sub (continuous_pi fun _ => continuous_apply 0)))
    refine (χ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 F)).mono'
      h_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    have hF_bd : ‖F (x - fun _ => z 0)‖ ≤ SchwartzMap.seminorm ℝ 0 0 F := by
      simpa [norm_iteratedFDeriv_zero, pow_zero, one_mul] using
        SchwartzMap.le_seminorm ℝ 0 0 F (x - fun _ => z 0)
    exact mul_le_mul_of_nonneg_left hF_bd (norm_nonneg _)
  exact integral_sub (h_int ψ₁) (h_int ψ₂)

lemma schwartzDiagTranslateN_diagConvSchwartz (k : ℕ) (a : Fin 4 → ℝ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN k a (diagConvSchwartz k ψ F) =
      diagConvSchwartz k (schwartzDiagTranslateN 1 a ψ) F := by
  ext x
  rw [schwartzDiagTranslateN_apply, diagConvSchwartz_apply, diagConvSchwartz_apply]
  let va : Fin 1 → Fin 4 → ℝ := fun _ => a
  symm
  refine Eq.trans (MeasureTheory.integral_add_right_eq_self
    (fun z : Fin 1 → Fin 4 → ℝ =>
      schwartzDiagTranslateN 1 a ψ z * F (x - fun _ => z 0)) va).symm ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have h1 : schwartzDiagTranslateN 1 a ψ (z + va) = ψ z := by
    rw [schwartzDiagTranslateN_apply]
    congr 1
    ext i μ
    simp [va]
  have h2 : (x - fun _ => (z + va) 0) = (fun i => x i - a) - fun _ => z 0 := by
    ext i μ
    simp only [Pi.sub_apply, Pi.add_apply, va]
    ring
  dsimp only
  rw [h1, h2]

lemma minkowskiFourier_diagConvSchwartz (k : ℕ) (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (q : Fin k → Fin 4 → ℝ) :
    minkowskiFourier (diagConvSchwartz k ψ F) q =
      minkowskiFourier ψ (fun _ => ∑ i : Fin k, q i) * minkowskiFourier F q := by
  let H : (Fin k → Fin 4 → ℝ) × (Fin 1 → Fin 4 → ℝ) → ℂ := fun p =>
    (ψ p.2 * F (p.1 - fun _ => p.2 0)) *
      Complex.exp (-(Complex.I * ((∑ i : Fin k, minkowskiInner (q i) (p.1 i) : ℝ) : ℂ)))
  have hH_cont : Continuous H :=
    (ψ.continuous.comp continuous_snd |>.mul
      (F.continuous.comp (continuous_fst.sub
        (continuous_pi fun _ => (continuous_apply 0).comp continuous_snd)))).mul
      (Complex.continuous_exp.comp (continuous_neg.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp ((continuous_minkowskiPhase k q).comp continuous_fst)))))
  have h_prod_int : Integrable H (volume.prod volume) := by
    rw [MeasureTheory.integrable_prod_iff' hH_cont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
    · refine ((F.integrable.norm).comp_sub_right (fun _ : Fin k => z 0)
        |>.const_mul ‖ψ z‖).mono' (hH_cont.comp (continuous_id.prodMk continuous_const)
          |>.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      dsimp [H]
      rw [norm_mul, norm_mul]
      have h_im : -(Complex.I * ((∑ i : Fin k, minkowskiInner (q i) (x i) : ℝ) : ℂ)) =
          ((-(∑ i : Fin k, minkowskiInner (q i) (x i)) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [h_im, Complex.norm_exp_ofReal_mul_I, mul_one]
    · have h_int_eq : (fun z : Fin 1 → Fin 4 → ℝ => ∫ x : Fin k → Fin 4 → ℝ, ‖H (x, z)‖) =
          fun z => ‖ψ z‖ * ∫ x : Fin k → Fin 4 → ℝ, ‖F x‖ := by
        ext z
        have h_fn : (fun x : Fin k → Fin 4 → ℝ => ‖H (x, z)‖) =
            fun x => ‖ψ z‖ * ‖F (x - fun _ => z 0)‖ := by
          ext x
          dsimp [H]
          rw [norm_mul, norm_mul]
          have h_im : -(Complex.I * ((∑ i : Fin k, minkowskiInner (q i) (x i) : ℝ) : ℂ)) =
              ((-(∑ i : Fin k, minkowskiInner (q i) (x i)) : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [h_im, Complex.norm_exp_ofReal_mul_I, mul_one]
        rw [h_fn, integral_const_mul,
          MeasureTheory.integral_sub_right_eq_self (fun x : Fin k → Fin 4 → ℝ => ‖F x‖)
            (fun _ => z 0)]
      rw [h_int_eq]
      exact ψ.integrable.norm.mul_const _
  calc minkowskiFourier (diagConvSchwartz k ψ F) q
      = ∫ x : Fin k → Fin 4 → ℝ, ∫ z : Fin 1 → Fin 4 → ℝ, H (x, z) := by
        dsimp [minkowskiFourier]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only [H]
        rw [← integral_mul_const]
    _ = ∫ z : Fin 1 → Fin 4 → ℝ, ∫ x : Fin k → Fin 4 → ℝ, H (x, z) :=
        MeasureTheory.integral_integral_swap h_prod_int
    _ = ∫ z : Fin 1 → Fin 4 → ℝ, ψ z * minkowskiFourier (schwartzDiagTranslateN k (z 0) F) q := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [minkowskiFourier, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp [H]
        have h_sub_x : (x - fun _ => z 0) = fun i : Fin k => x i - z 0 := rfl
        rw [h_sub_x]
        ring
    _ = ∫ z : Fin 1 → Fin 4 → ℝ,
          ψ z * (Complex.exp (-(Complex.I * ((minkowskiInner (∑ i : Fin k, q i) (z 0) : ℝ) :
            ℂ))) * minkowskiFourier F q) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [minkowskiFourier_schwartzDiagTranslateN]
    _ = (∫ z : Fin 1 → Fin 4 → ℝ, ψ z * Complex.exp (-(Complex.I *
          ((∑ j : Fin 1, minkowskiInner (∑ i : Fin k, q i) (z j) : ℝ) : ℂ)))) *
          minkowskiFourier F q := by
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        dsimp only
        rw [Fin.sum_univ_one]
        ring
    _ = minkowskiFourier ψ (fun _ => ∑ i : Fin k, q i) * minkowskiFourier F q := rfl

def iterDirDerivSchwartz (k : ℕ) :
    ∀ m : ℕ, (Fin m → (Fin k → Fin 4 → ℝ)) →
      SchwartzMap (Fin k → Fin 4 → ℝ) ℂ → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ
  | 0, _, F => F
  | m + 1, w, F =>
      iterDirDerivSchwartz k m (Fin.init w) (schwartzDirDerivCLM k (w (Fin.last m)) F)

lemma iteratedFDeriv_eq_iterDirDerivSchwartz (k m : ℕ) :
    ∀ (w : Fin m → (Fin k → Fin 4 → ℝ)) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
      (p : Fin k → Fin 4 → ℝ),
      iteratedFDeriv ℝ m (⇑F) p w = iterDirDerivSchwartz k m w F p := by
  induction m with
  | zero =>
    intro w F p
    rw [iteratedFDeriv_zero_apply]
    rfl
  | succ m ih =>
    intro w F p
    rw [iteratedFDeriv_succ_apply_right]
    let v : Fin k → Fin 4 → ℝ := w (Fin.last m)
    let L_v : ((Fin k → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
      ContinuousLinearMap.apply ℝ ℂ v
    have h_comm : (iteratedFDeriv ℝ m (fderiv ℝ (⇑F)) p (Fin.init w)) v =
        iteratedFDeriv ℝ m (L_v ∘ fderiv ℝ (⇑F)) p (Fin.init w) := by
      have h_fcd : ContDiff ℝ (m : ℕ) (fderiv ℝ (⇑F)) :=
        (F.smooth (m + 1)).fderiv_right (by simp)
      change L_v _ = _
      rw [L_v.iteratedFDeriv_comp_left h_fcd.contDiffAt le_rfl]
      rfl
    have h_fn : (L_v ∘ fderiv ℝ (⇑F)) = ⇑(schwartzDirDerivCLM k v F) := rfl
    rw [h_comm, h_fn]
    exact ih (Fin.init w) (schwartzDirDerivCLM k v F) p

lemma continuous_jetCoord_schwartzDiagTranslateN (k l m : ℕ)
    (α : Fin m → Fin k × Fin 4) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    Continuous (fun z : Fin 1 → Fin 4 → ℝ =>
      jetCoordLM k l m α (schwartzDiagTranslateN k (z 0) F)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let G := iterDirDerivSchwartz k m (fun r => stdBasisVec k (α r)) F
  let A : ℝ := 2 ^ l *
    (SchwartzMap.seminorm ℝ l 1 G + (‖z₀‖ + 1) ^ l * SchwartzMap.seminorm ℝ 0 1 G)
  have hA_nn : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by positivity) (add_nonneg (apply_nonneg _ _)
      (mul_nonneg (by positivity) (apply_nonneg _ _)))
  refine ⟨min 1 (ε / (A + 1)), lt_min one_pos (div_pos hε (by linarith)), fun z hz => ?_⟩
  rw [lt_min_iff] at hz
  have hz1 : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz.1
  have hzA : ‖z - z₀‖ < ε / (A + 1) := by simpa [dist_eq_norm] using hz.2
  rw [dist_eq_norm, ← map_sub]
  have h_le_A : ‖jetCoordLM k l m α (schwartzDiagTranslateN k (z 0) F -
      schwartzDiagTranslateN k (z₀ 0) F)‖ ≤ A * ‖z - z₀‖ := by
    refine (BoundedContinuousFunction.norm_le (mul_nonneg hA_nn (norm_nonneg _))).mpr fun p => ?_
    dsimp [jetCoordLM, jetCoordBCF]
    change ‖((‖p‖ ^ l : ℝ) : ℂ) *
        (iteratedFDeriv ℝ m
          (⇑(schwartzDiagTranslateN k (z 0) F) - ⇑(schwartzDiagTranslateN k (z₀ 0) F)) p
          (fun r => stdBasisVec k (α r)))‖ ≤
      A * ‖z - z₀‖
    rw [iteratedFDeriv_sub_apply ((schwartzDiagTranslateN k (z 0) F).smooth m).contDiffAt
      ((schwartzDiagTranslateN k (z₀ 0) F).smooth m).contDiffAt,
      _root_.sub_apply,
      iteratedFDeriv_schwartzDiagTranslateN, iteratedFDeriv_schwartzDiagTranslateN,
      iteratedFDeriv_eq_iterDirDerivSchwartz, iteratedFDeriv_eq_iterDirDerivSchwartz]
    let q₀ : Fin k → Fin 4 → ℝ := p - fun _ => z₀ 0
    let q₁ : Fin k → Fin 4 → ℝ := p - fun _ => z 0
    have hq_sub : q₁ - q₀ = fun _ => z₀ 0 - z 0 := by
      ext i μ
      simp only [q₁, q₀, Pi.sub_apply]
      ring
    have hq_norm : ‖q₁ - q₀‖ ≤ ‖z - z₀‖ := by
      rw [hq_sub]
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun _ => ?_
      have h0 : ‖z₀ 0 - z 0‖ = ‖z 0 - z₀ 0‖ := norm_sub_rev _ _
      rw [h0]
      exact norm_le_pi_norm (z - z₀) 0
    have hq0_mem : q₀ ∈ Metric.closedBall q₀ 1 := Metric.mem_closedBall_self zero_le_one
    have hq1_mem : q₁ ∈ Metric.closedBall q₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hq_norm.trans hz1.le
    let φ : (Fin k → Fin 4 → ℝ) → ℂ := fun y => ((‖p‖ ^ l : ℝ) : ℂ) * G y
    have hφ_diff : ∀ y ∈ Metric.closedBall q₀ 1, DifferentiableAt ℝ φ y := fun y _ =>
      ((G.smooth 1).differentiable one_ne_zero y).const_mul ((‖p‖ ^ l : ℝ) : ℂ)
    have hφ_bd : ∀ y ∈ Metric.closedBall q₀ 1, ‖fderiv ℝ φ y‖ ≤ A := by
      intro y hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      have hp_y : ‖p - y‖ ≤ ‖z₀‖ + 1 := by
        have h_pz₀ : ‖p - q₀‖ ≤ ‖z₀‖ := by
          have hpq : p - q₀ = fun _ => z₀ 0 := by
            ext i μ
            simp [q₀]
          rw [hpq]
          refine (pi_norm_le_iff_of_nonneg (norm_nonneg z₀)).mpr fun _ => ?_
          exact norm_le_pi_norm z₀ 0
        calc ‖p - y‖ = ‖(p - q₀) + (q₀ - y)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖p - q₀‖ + ‖q₀ - y‖ := norm_add_le _ _
          _ = ‖p - q₀‖ + ‖y - q₀‖ := by rw [norm_sub_rev q₀ y]
          _ ≤ ‖z₀‖ + 1 := add_le_add h_pz₀ hy
      have hp_le : ‖p‖ ≤ ‖y‖ + (‖z₀‖ + 1) := by
        calc ‖p‖ = ‖y + (p - y)‖ := by rw [add_sub_cancel]
          _ ≤ ‖y‖ + ‖p - y‖ := norm_add_le _ _
          _ ≤ ‖y‖ + (‖z₀‖ + 1) := add_le_add le_rfl hp_y
      have hp_pow : ‖p‖ ^ l ≤ 2 ^ l * (‖y‖ ^ l + (‖z₀‖ + 1) ^ l) :=
        (pow_le_pow_left₀ (norm_nonneg p) hp_le l).trans
          (add_pow_le_two_pow_mul_add_pow (norm_nonneg y) (by positivity) l)
      have h_fd_φ : fderiv ℝ φ y = ((‖p‖ ^ l : ℝ) : ℂ) • fderiv ℝ (⇑G) y :=
        fderiv_const_mul ((G.smooth 1).differentiable one_ne_zero y) ((‖p‖ ^ l : ℝ) : ℂ)
      rw [h_fd_φ, norm_smul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (norm_nonneg p) l)]
      have hG1 := SchwartzMap.le_seminorm ℝ l 1 G y
      have hG0 : ‖fderiv ℝ (⇑G) y‖ ≤ SchwartzMap.seminorm ℝ 0 1 G := by
        simpa [norm_iteratedFDeriv_one, pow_zero, one_mul] using SchwartzMap.le_seminorm ℝ 0 1 G y
      rw [norm_iteratedFDeriv_one] at hG1
      calc ‖p‖ ^ l * ‖fderiv ℝ (⇑G) y‖
          ≤ 2 ^ l * (‖y‖ ^ l + (‖z₀‖ + 1) ^ l) * ‖fderiv ℝ (⇑G) y‖ :=
            mul_le_mul_of_nonneg_right hp_pow (norm_nonneg _)
        _ = 2 ^ l * (‖y‖ ^ l * ‖fderiv ℝ (⇑G) y‖ + (‖z₀‖ + 1) ^ l * ‖fderiv ℝ (⇑G) y‖) := by
            ring
        _ ≤ A := by
            dsimp [A]
            gcongr
    have h_mvt := (convex_closedBall q₀ 1).norm_image_sub_le_of_norm_fderiv_le
      hφ_diff hφ_bd hq0_mem hq1_mem
    have h_lhs_eq : ((‖p‖ ^ l : ℝ) : ℂ) * (G q₁ - G q₀) = φ q₁ - φ q₀ := by
      dsimp [φ]
      ring
    rw [h_lhs_eq]
    exact h_mvt.trans (mul_le_mul_of_nonneg_left hq_norm hA_nn)
  calc ‖jetCoordLM k l m α (schwartzDiagTranslateN k (z 0) F -
          schwartzDiagTranslateN k (z₀ 0) F)‖
      ≤ A * ‖z - z₀‖ := h_le_A
    _ ≤ (A + 1) * ‖z - z₀‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (A + 1) * (ε / (A + 1)) := mul_lt_mul_of_pos_left hzA (by linarith)
    _ = ε := mul_div_cancel₀ ε (by linarith)

theorem clm_diagConvSchwartz_eq_integral (k : ℕ)
    (T : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    T (diagConvSchwartz k ψ F) =
      ∫ z : Fin 1 → Fin 4 → ℝ, ψ z * T (schwartzDiagTranslateN k (z 0) F) := by
  obtain ⟨s, T_tilde, h_factor⟩ := clm_factors_through_jetSpace k T
  let F_z : (Fin 1 → Fin 4 → ℝ) → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ :=
    fun z => schwartzDiagTranslateN k (z 0) F
  let G : (Fin 1 → Fin 4 → ℝ) → JetSpace k s := fun z => ψ z • jetMap k s (F_z z)
  have hG_int : Integrable G volume := by
    let M_l : ℕ := s.sup Prod.fst
    let h_ex := fun km : { km : ℕ × ℕ // km ∈ s } =>
      schwartzDiagTranslateN_poly_bound k km.1.1 km.1.2 F
    let C_tot : ℝ := ∑ km : { km : ℕ × ℕ // km ∈ s }, (h_ex km).choose
    let E_lp := (PiLp.continuousLinearEquiv ⊤ ℂ (fun _ : JetIdx k s => JetBCF k)).symm
    have hG_eq : G = fun z => E_lp fun j =>
        ψ z • jetCoordLM k j.1.1.1 j.1.1.2 j.2 (F_z z) := by
      funext z
      change ψ z • E_lp (jetMapRaw k s (F_z z)) = _
      rw [← map_smul]
      rfl
    have h_cont : Continuous G := by
      rw [hG_eq]
      exact E_lp.continuous.comp (continuous_pi fun j =>
        ψ.continuous.smul (continuous_jetCoord_schwartzDiagTranslateN k j.1.1.1 j.1.1.2 j.2 F))
    haveI : SecondCountableTopologyEither (Fin 1 → Fin 4 → ℝ) (JetSpace k s) :=
      ⟨Or.inl inferInstance⟩
    have hC_nn : 0 ≤ C_tot :=
      Finset.sum_nonneg fun km _ => (h_ex km).choose_spec.1
    refine (integrable_polynomial_mul_schwartz 1 ψ (2 * C_tot) M_l).mono
      h_cont.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    dsimp [G]
    rw [norm_smul]
    have h_lp_bnd : ‖jetMap k s (F_z z)‖ ≤ 2 * C_tot * (1 + ‖z‖ ^ M_l) := by
      by_cases h_ne : Nonempty (JetIdx k s)
      · rw [PiLp.norm_eq_ciSup]
        refine ciSup_le fun j => ?_
        have hCkm_nn : 0 ≤ (h_ex j.1).choose := (h_ex j.1).choose_spec.1
        have h_bcf : ‖(jetMap k s (F_z z)).ofLp j‖ ≤
            (h_ex j.1).choose * (1 + ‖z‖ ^ j.1.1.1) := by
          refine BoundedContinuousFunction.norm_le (by positivity) |>.mpr fun p => ?_
          change ‖((‖p‖ ^ j.1.1.1 : ℝ) : ℂ) *
              iteratedFDeriv ℝ j.1.1.2 (⇑(F_z z)) p (fun r => stdBasisVec k (j.2 r))‖ ≤ _
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (pow_nonneg (norm_nonneg p) j.1.1.1)]
          have h_eval : ‖iteratedFDeriv ℝ j.1.1.2 (⇑(F_z z)) p
              (fun r => stdBasisVec k (j.2 r))‖ ≤
              ‖iteratedFDeriv ℝ j.1.1.2 (⇑(F_z z)) p‖ := by
            calc _ ≤ _ * ∏ r : Fin j.1.1.2, ‖stdBasisVec k (j.2 r)‖ :=
                  ContinuousMultilinearMap.le_opNorm _ _
              _ ≤ _ * ∏ _r : Fin j.1.1.2, (1 : ℝ) :=
                  mul_le_mul_of_nonneg_left
                    (Finset.prod_le_prod (fun r _ => norm_nonneg _)
                      (fun r _ => norm_stdBasisVec_le_one k (j.2 r)))
                    (norm_nonneg _)
              _ = _ := by simp
          calc ‖p‖ ^ j.1.1.1 * ‖iteratedFDeriv ℝ j.1.1.2 (⇑(F_z z)) p
                  (fun r => stdBasisVec k (j.2 r))‖
              ≤ ‖p‖ ^ j.1.1.1 * ‖iteratedFDeriv ℝ j.1.1.2 (⇑(F_z z)) p‖ :=
                mul_le_mul_of_nonneg_left h_eval (pow_nonneg (norm_nonneg p) j.1.1.1)
            _ ≤ (h_ex j.1).choose * (1 + ‖z‖ ^ j.1.1.1) := (h_ex j.1).choose_spec.2 z p
        have hC_km_le : (h_ex j.1).choose ≤ C_tot :=
          Finset.single_le_sum (fun km _ => (h_ex km).choose_spec.1) (Finset.mem_univ j.1)
        have h_pow_le : 1 + ‖z‖ ^ j.1.1.1 ≤ 2 * (1 + ‖z‖ ^ M_l) :=
          one_add_pow_le_two_mul_one_add_pow ‖z‖ (norm_nonneg z) j.1.1.1 M_l
            (Finset.le_sup (f := Prod.fst) j.1.2)
        calc ‖(jetMap k s (F_z z)).ofLp j‖
            ≤ (h_ex j.1).choose * (1 + ‖z‖ ^ j.1.1.1) := h_bcf
          _ ≤ C_tot * (2 * (1 + ‖z‖ ^ M_l)) := by gcongr
          _ = 2 * C_tot * (1 + ‖z‖ ^ M_l) := by ring
      · rw [not_nonempty_iff] at h_ne
        have h0 : jetMap k s (F_z z) = 0 :=
          (WithLp.equiv ⊤ (JetIdx k s → JetBCF k)).injective (Subsingleton.elim _ _)
        rw [h0, norm_zero]
        positivity
    calc ‖ψ z‖ * ‖jetMap k s (F_z z)‖
        ≤ ‖ψ z‖ * (2 * C_tot * (1 + ‖z‖ ^ M_l)) :=
          mul_le_mul_of_nonneg_left h_lp_bnd (norm_nonneg _)
      _ = 2 * C_tot * (1 + ‖z‖ ^ M_l) * ‖ψ z‖ := by ring
  have h_jet_eq : jetMap k s (diagConvSchwartz k ψ F) = ∫ z, G z := by
    apply (WithLp.equiv ⊤ (JetIdx k s → JetBCF k)).injective
    funext j
    ext p
    let E_jpC : JetSpace k s →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ p).comp
        (PiLp.proj ⊤ (𝕜 := ℂ) (fun _ : JetIdx k s => JetBCF k) j)
    let E_jp : JetSpace k s →L[ℝ] ℂ := E_jpC.restrictScalars ℝ
    have h_comm := ContinuousLinearMap.integral_comp_comm E_jp hG_int
    have h_rhs : ((∫ z, G z).ofLp j) p =
        ∫ z : Fin 1 → Fin 4 → ℝ, ψ z * (((‖p‖ ^ j.1.1.1 : ℝ) : ℂ) *
          iteratedFDeriv ℝ j.1.1.2 (⇑F) (p - fun _ => z 0) (fun r => stdBasisVec k (j.2 r))) := by
      change E_jp (∫ z, G z) = _
      rw [← h_comm]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      change E_jpC (ψ z • jetMap k s (F_z z)) = _
      rw [map_smul, smul_eq_mul]
      dsimp [E_jpC, jetMap, jetMapRaw, jetCoordLM, jetCoordBCF]
      rw [PiLp.continuousLinearEquiv_symm_apply]
      simp only [BoundedContinuousFunction.evalCLM_apply, PiLp.proj_apply]
      change ψ z * (((‖p‖ ^ j.1.1.1 : ℝ) : ℂ) *
          iteratedFDeriv ℝ j.1.1.2 (⇑(schwartzDiagTranslateN k (z 0) F)) p
            (fun r => stdBasisVec k (j.2 r))) = _
      rw [iteratedFDeriv_schwartzDiagTranslateN]
    change ((‖p‖ ^ j.1.1.1 : ℝ) : ℂ) *
        iteratedFDeriv ℝ j.1.1.2 (diagConvRaw k ψ F) p
          (fun r => stdBasisVec k (j.2 r)) = ((∫ z, G z).ofLp j) p
    rw [h_rhs, (iteratedFDeriv_diagConvRaw_eq_integral k j.1.1.2 ψ F p
      (fun r => stdBasisVec k (j.2 r))).2, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  rw [h_factor, h_jet_eq]
  have h_tilde_comm := ContinuousLinearMap.integral_comp_comm (T_tilde.restrictScalars ℝ) hG_int
  change (T_tilde.restrictScalars ℝ) (∫ z, G z) = _
  rw [← h_tilde_comm]
  congr 1
  ext z
  change T_tilde (ψ z • jetMap k s (F_z z)) = ψ z * T (F_z z)
  rw [map_smul, smul_eq_mul, ← h_factor]

def subGapBumpRaw (m : ℝ) (hm : 0 < m) : ContDiffBump (0 : Fin 1 → Fin 4 → ℝ) where
  rIn := m / 4
  rOut := m / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

def subGapMomBump (m : ℝ) (hm : 0 < m) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  ((subGapBumpRaw m hm).hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (subGapBumpRaw m hm).contDiff)

lemma subGapMomBump_eq_one_of_norm_le {m : ℝ} (hm : 0 < m)
    {q : Fin 1 → Fin 4 → ℝ} (hq : ‖q‖ ≤ m / 4) :
    subGapMomBump m hm q = 1 := by
  dsimp [subGapMomBump]
  have hb : subGapBumpRaw m hm q = 1 :=
    (subGapBumpRaw m hm).one_of_mem_closedBall
      (by rw [Metric.mem_closedBall, dist_zero_right]; exact hq)
  change ((subGapBumpRaw m hm q : ℝ) : ℂ) = 1
  rw [hb, Complex.ofReal_one]

def subGapPosKernel (m : ℝ) (hm : 0 < m) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  invMinkowskiFourierCLM 1 (subGapMomBump m hm)

def smulFin1CLE {c : ℝ} (hc : c ≠ 0) :
    (Fin 1 → Fin 4 → ℝ) ≃L[ℝ] (Fin 1 → Fin 4 → ℝ) where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := by
    ext i μ
    simp [hc]
  right_inv x := by
    ext i μ
    simp [hc]
  map_add' x y := smul_add c x y
  map_smul' r x := smul_comm c r x
  continuous_toFun := continuous_id.const_smul c
  continuous_invFun := continuous_id.const_smul c⁻¹

def subGapPosKernelScale (m : ℝ) (hm : 0 < m) (R : ℝ) (hR : 0 < R) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  (R⁻¹ ^ 4 : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (smulFin1CLE (inv_ne_zero hR.ne')) (subGapPosKernel m hm)

@[simp]
lemma subGapPosKernelScale_apply (m : ℝ) (hm : 0 < m) (R : ℝ) (hR : 0 < R)
    (z : Fin 1 → Fin 4 → ℝ) :
    subGapPosKernelScale m hm R hR z = ((R⁻¹ ^ 4 : ℝ) : ℂ) * subGapPosKernel m hm (R⁻¹ • z) := by
  dsimp [subGapPosKernelScale]
  rw [_root_.smul_apply, Complex.real_smul, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rfl

lemma finrank_fin1_fin4 : Module.finrank ℝ (Fin 1 → Fin 4 → ℝ) = 4 := by
  rw [(piSpaceEquiv 1).toLinearEquiv.finrank_eq]
  simp

lemma minkowskiFourier_subGapPosKernelScale (m : ℝ) (hm : 0 < m) (R : ℝ) (hR : 0 < R)
    (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (subGapPosKernelScale m hm R hR) p = subGapMomBump m hm (R • p) := by
  let H : (Fin 1 → Fin 4 → ℝ) → ℂ := fun y =>
    subGapPosKernel m hm y *
      Complex.exp (-(Complex.I * ((∑ i : Fin 1, minkowskiInner ((R • p) i) (y i) : ℝ) : ℂ)))
  have h_comp : (fun z : Fin 1 → Fin 4 → ℝ =>
      subGapPosKernel m hm (R⁻¹ • z) *
        Complex.exp (-(Complex.I * ((∑ i : Fin 1, minkowskiInner (p i) (z i) : ℝ) : ℂ)))) =
      fun z => H (R⁻¹ • z) := by
    ext z
    dsimp [H]
    congr 2
    rw [Fin.sum_univ_one, Fin.sum_univ_one]
    congr 2
    simp only [Pi.smul_apply, smul_eq_mul, minkowskiInner_explicit]
    have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
    have h_m : p 0 0 * z 0 0 - p 0 1 * z 0 1 - p 0 2 * z 0 2 - p 0 3 * z 0 3 =
        R * p 0 0 * (R⁻¹ * z 0 0) - R * p 0 1 * (R⁻¹ * z 0 1) -
          R * p 0 2 * (R⁻¹ * z 0 2) - R * p 0 3 * (R⁻¹ * z 0 3) := by
      calc p 0 0 * z 0 0 - p 0 1 * z 0 1 - p 0 2 * z 0 2 - p 0 3 * z 0 3
          = (R * R⁻¹) * (p 0 0 * z 0 0 - p 0 1 * z 0 1 - p 0 2 * z 0 2 - p 0 3 * z 0 3) := by
              rw [hRR, one_mul]
        _ = R * p 0 0 * (R⁻¹ * z 0 0) - R * p 0 1 * (R⁻¹ * z 0 1) -
              R * p 0 2 * (R⁻¹ * z 0 2) - R * p 0 3 * (R⁻¹ * z 0 3) := by ring
    rw [h_m]
  have h_sc := Measure.integral_comp_smul_of_nonneg (μ := volume) H R⁻¹
    (hR := (by positivity : 0 ≤ R⁻¹))
  rw [finrank_fin1_fin4, inv_pow, inv_inv] at h_sc
  dsimp [minkowskiFourier]
  simp_rw [subGapPosKernelScale_apply, mul_assoc, integral_const_mul]
  rw [h_comp, h_sc, Complex.real_smul, ← mul_assoc]
  have h_inv_pow : ((R⁻¹ ^ 4 : ℝ) : ℂ) * ((R ^ 4 : ℝ) : ℂ) = 1 := by
    push_cast
    have hR4 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    field_simp [hR4]
  rw [h_inv_pow, one_mul]
  change minkowskiFourier (subGapPosKernel m hm) (R • p) = subGapMomBump m hm (R • p)
  exact minkowskiFourier_invMinkowskiFourierCLM_one (subGapMomBump m hm) (R • p)

lemma integral_norm_shift_subGapPosKernelScale (m : ℝ) (hm : 0 < m) (R : ℝ) (hR : 0 < R)
    (a : Fin 4 → ℝ) :
    (∫ z : Fin 1 → Fin 4 → ℝ,
        ‖(schwartzDiagTranslateN 1 a (subGapPosKernelScale m hm R hR) -
          subGapPosKernelScale m hm R hR) z‖) =
      ∫ y : Fin 1 → Fin 4 → ℝ,
        ‖subGapPosKernel m hm (fun _ => y 0 - R⁻¹ • a) - subGapPosKernel m hm y‖ := by
  let G : (Fin 1 → Fin 4 → ℝ) → ℝ := fun y =>
    ‖subGapPosKernel m hm (fun _ => y 0 - R⁻¹ • a) - subGapPosKernel m hm y‖
  have h_norm_eq : (fun z : Fin 1 → Fin 4 → ℝ =>
      ‖(schwartzDiagTranslateN 1 a (subGapPosKernelScale m hm R hR) -
        subGapPosKernelScale m hm R hR) z‖) =
      fun z => (R⁻¹ ^ 4) * G (R⁻¹ • z) := by
    ext z
    rw [_root_.sub_apply, schwartzDiagTranslateN_apply, subGapPosKernelScale_apply,
      subGapPosKernelScale_apply, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    congr 2
    dsimp [G]
    congr 2
    ext i μ
    rw [Subsingleton.elim i 0]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [h_norm_eq, integral_const_mul]
  have h_sc := Measure.integral_comp_smul_of_nonneg (μ := volume) G R⁻¹
    (hR := (by positivity : 0 ≤ R⁻¹))
  rw [finrank_fin1_fin4, inv_pow, inv_inv, smul_eq_mul] at h_sc
  rw [h_sc, ← mul_assoc]
  have h_cancel : R⁻¹ ^ 4 * R ^ 4 = 1 := by field_simp [hR.ne']
  rw [h_cancel, one_mul]

lemma tendsto_l1_schwartz_shift_inv_scale (χ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (a : Fin 4 → ℝ) :
    Tendsto (fun R : ℝ =>
        ∫ y : Fin 1 → Fin 4 → ℝ, ‖χ (fun _ => y 0 - R⁻¹ • a) - χ y‖)
      atTop (𝓝 0) := by
  let va : Fin 1 → Fin 4 → ℝ := fun _ => a
  let S_χ : ℝ := (Finset.Iic (5, 0)).sup
    (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ) χ
  have hS_nn : 0 ≤ S_χ := apply_nonneg _ _
  let C_bd : ℝ := 2 ^ 5 * S_χ * ((1 + ‖va‖) ^ 5 + 1)
  let bound : (Fin 1 → Fin 4 → ℝ) → ℝ := fun y => C_bd * ((1 + ‖y‖) ^ 5)⁻¹
  have h_int_inv : Integrable (fun y : Fin 1 → Fin 4 → ℝ => ((1 + ‖y‖) ^ 5)⁻¹) volume := by
    have hlt : (Module.finrank ℝ (Fin 1 → Fin 4 → ℝ) : ℝ) < (5 : ℝ) := by
      rw [finrank_fin1_fin4]
      norm_num
    have h := integrable_one_add_norm
      (E := Fin 1 → Fin 4 → ℝ) (μ := volume) (r := (5 : ℝ)) hlt
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    have hy : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hy.le]
    norm_cast
  have h_bound_int : Integrable bound volume := h_int_inv.const_mul C_bd
  have h_meas : ∀ᶠ R : ℝ in atTop, AEStronglyMeasurable
      (fun y : Fin 1 → Fin 4 → ℝ => ‖χ (fun _ => y 0 - R⁻¹ • a) - χ y‖) volume := by
    refine Filter.Eventually.of_forall fun R => ?_
    have h_shift : Continuous (fun y : Fin 1 → Fin 4 → ℝ => fun _ : Fin 1 => y 0 - R⁻¹ • a) :=
      continuous_pi fun _ => (continuous_apply 0).sub continuous_const
    exact ((χ.continuous.comp h_shift).sub χ.continuous).norm.aestronglyMeasurable
  have h_bound : ∀ᶠ R : ℝ in atTop, ∀ᵐ y : Fin 1 → Fin 4 → ℝ ∂volume,
      ‖‖χ (fun _ => y 0 - R⁻¹ • a) - χ y‖‖ ≤ bound y := by
    refine Filter.eventually_ge_atTop (1 : ℝ) |>.mono fun R hR => ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    have h_pt_eq : (fun _ : Fin 1 => y 0 - R⁻¹ • a) = y - R⁻¹ • va := by
      ext i μ
      rw [Subsingleton.elim i 0]
      rfl
    have h_inv_le : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    have h_inv_nn : 0 ≤ R⁻¹ := by positivity
    have h_sv_le : ‖R⁻¹ • va‖ ≤ ‖va‖ := by
      rw [norm_smul, Real.norm_of_nonneg h_inv_nn]
      exact mul_le_of_le_one_left (norm_nonneg va) h_inv_le
    have h_one_add : 1 + ‖y‖ ≤ (1 + ‖va‖) * (1 + ‖y - R⁻¹ • va‖) := by
      have h_tri : ‖y‖ ≤ ‖y - R⁻¹ • va‖ + ‖R⁻¹ • va‖ := norm_le_norm_sub_add y (R⁻¹ • va)
      nlinarith [norm_nonneg va, norm_nonneg (y - R⁻¹ • va)]
    have h_pow5 : (1 + ‖y‖) ^ 5 ≤ (1 + ‖va‖) ^ 5 * (1 + ‖y - R⁻¹ • va‖) ^ 5 := by
      calc (1 + ‖y‖) ^ 5 ≤ ((1 + ‖va‖) * (1 + ‖y - R⁻¹ • va‖)) ^ 5 :=
            pow_le_pow_left₀ (by positivity) h_one_add 5
        _ = (1 + ‖va‖) ^ 5 * (1 + ‖y - R⁻¹ • va‖) ^ 5 := mul_pow _ _ 5
    have h_sch : ∀ u : Fin 1 → Fin 4 → ℝ, ‖χ u‖ ≤ 2 ^ 5 * S_χ * ((1 + ‖u‖) ^ 5)⁻¹ := by
      intro u
      have h0 := SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℝ) (m := (5, 0)) (k := 5) (n := 0) le_rfl le_rfl χ u
      have h_fam :
          (fun m : ℕ × ℕ =>
            SchwartzMap.seminorm (E := Fin 1 → Fin 4 → ℝ) (F := ℂ) ℝ m.1 m.2) =
          schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ := rfl
      have h_prod : (1 + ‖u‖) ^ 5 * ‖χ u‖ ≤ 2 ^ 5 * S_χ := by
        simpa [norm_iteratedFDeriv_zero, h_fam, S_χ] using h0
      have h_pos5 : 0 < (1 + ‖u‖) ^ 5 := by positivity
      exact (le_mul_inv_iff₀' h_pos5).mpr h_prod
    have h_u1 : ‖χ (y - R⁻¹ • va)‖ ≤
        (2 ^ 5 * S_χ * (1 + ‖va‖) ^ 5) * ((1 + ‖y‖) ^ 5)⁻¹ := by
      have h1 := h_sch (y - R⁻¹ • va)
      have h_inv_pow : ((1 + ‖y - R⁻¹ • va‖) ^ 5)⁻¹ ≤ (1 + ‖va‖) ^ 5 * ((1 + ‖y‖) ^ 5)⁻¹ := by
        calc ((1 + ‖y - R⁻¹ • va‖) ^ 5)⁻¹
            = (1 + ‖va‖) ^ 5 * ((1 + ‖va‖) ^ 5 * (1 + ‖y - R⁻¹ • va‖) ^ 5)⁻¹ := by
                have h_va : 0 < (1 + ‖va‖) ^ 5 := by positivity
                field_simp [h_va.ne']
          _ ≤ (1 + ‖va‖) ^ 5 * ((1 + ‖y‖) ^ 5)⁻¹ := by gcongr
      calc ‖χ (y - R⁻¹ • va)‖ ≤ 2 ^ 5 * S_χ * ((1 + ‖y - R⁻¹ • va‖) ^ 5)⁻¹ := h1
        _ ≤ 2 ^ 5 * S_χ * ((1 + ‖va‖) ^ 5 * ((1 + ‖y‖) ^ 5)⁻¹) := by gcongr
        _ = (2 ^ 5 * S_χ * (1 + ‖va‖) ^ 5) * ((1 + ‖y‖) ^ 5)⁻¹ := by ring
    have h_u2 := h_sch y
    rw [h_pt_eq]
    calc ‖χ (y - R⁻¹ • va) - χ y‖ ≤ ‖χ (y - R⁻¹ • va)‖ + ‖χ y‖ := norm_sub_le _ _
      _ ≤ (2 ^ 5 * S_χ * (1 + ‖va‖) ^ 5) * ((1 + ‖y‖) ^ 5)⁻¹ +
            2 ^ 5 * S_χ * ((1 + ‖y‖) ^ 5)⁻¹ := add_le_add h_u1 h_u2
      _ = bound y := by dsimp [bound, C_bd]; ring
  have h_lim : ∀ᵐ y : Fin 1 → Fin 4 → ℝ ∂volume,
      Tendsto (fun R : ℝ => ‖χ (fun _ => y 0 - R⁻¹ • a) - χ y‖) atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h_arg : Tendsto (fun R : ℝ => (fun _ : Fin 1 => y 0 - R⁻¹ • a)) atTop (𝓝 y) := by
      have h_sub : Tendsto (fun R : ℝ => y - R⁻¹ • va) atTop (𝓝 (y - (0 : ℝ) • va)) :=
        tendsto_const_nhds.sub (tendsto_inv_atTop_zero.smul_const va)
      rw [zero_smul, sub_zero] at h_sub
      refine h_sub.congr fun R => ?_
      ext i μ
      rw [Subsingleton.elim i 0]
      rfl
    have h_val := (χ.continuous.tendsto y).comp h_arg
    have h_norm := (h_val.sub (tendsto_const_nhds (x := χ y))).norm
    simpa using h_norm
  have h_tend := tendsto_integral_filter_of_dominated_convergence
    bound h_meas h_bound h_bound_int h_lim
  simpa using h_tend

lemma minkowskiInner_sub_le_half_sq_of_massShellStrip {m M : ℝ} (hm : 0 < m) (hM : m < M)
    {p_g p_f : Fin 4 → ℝ}
    (hg : p_g ∈ tsupport (massShellCutoff m M hm hM))
    (hf : p_f ∈ tsupport (massShellCutoff m M hm hM)) :
    minkowskiInner (p_g - p_f) (p_g - p_f) ≤ m ^ 2 / 2 := by
  have hbg := tsupport_massShellCutoff_bounds hm hM hg
  have hbf := tsupport_massShellCutoff_bounds hm hM hf
  have h_del := massShellGapDelta_four_le_sq (m := m) (M := M)
  let s_g : ℝ := minkowskiInner p_g p_g
  let s_f : ℝ := minkowskiInner p_f p_f
  have hsg_abs := abs_le.mp hbg.2.1
  have hsf_abs := abs_le.mp hbf.2.1
  have hsg_lo : m ^ 2 / 2 ≤ s_g := by dsimp [s_g]; linarith only [hsg_abs.1, h_del]
  have hsg_hi : s_g ≤ 3 * m ^ 2 / 2 := by dsimp [s_g]; linarith only [hsg_abs.2, h_del]
  have hsf_lo : m ^ 2 / 2 ≤ s_f := by dsimp [s_f]; linarith only [hsf_abs.1, h_del]
  have hsf_hi : s_f ≤ 3 * m ^ 2 / 2 := by dsimp [s_f]; linarith only [hsf_abs.2, h_del]
  have hm2_pos : 0 < m ^ 2 := sq_pos_of_pos hm
  have hsg_pos : 0 < s_g := by linarith only [hm2_pos, hsg_lo]
  have hpg0_pos : 0 < p_g 0 := by linarith only [hm, hbg.1]
  have hpf0_pos : 0 < p_f 0 := by linarith only [hm, hbf.1]
  let Kg : ℝ := Real.sqrt (p_g 1 ^ 2 + p_g 2 ^ 2 + p_g 3 ^ 2)
  let Kf : ℝ := Real.sqrt (p_f 1 ^ 2 + p_f 2 ^ 2 + p_f 3 ^ 2)
  have hKg_nn : 0 ≤ Kg := Real.sqrt_nonneg _
  have hKf_nn : 0 ≤ Kf := Real.sqrt_nonneg _
  have hKg_sq : Kg ^ 2 = p_g 1 ^ 2 + p_g 2 ^ 2 + p_g 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hKf_sq : Kf ^ 2 = p_f 1 ^ 2 + p_f 2 ^ 2 + p_f 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hpg0_sq : p_g 0 ^ 2 = s_g + Kg ^ 2 := by
    dsimp [s_g]
    rw [minkowskiInner_explicit, hKg_sq]
    ring
  have hpf0_sq : p_f 0 ^ 2 = s_f + Kf ^ 2 := by
    dsimp [s_f]
    rw [minkowskiInner_explicit, hKf_sq]
    ring
  let S_gf : ℝ := p_g 1 * p_f 1 + p_g 2 * p_f 2 + p_g 3 * p_f 3
  have h_cs : S_gf ^ 2 ≤ (Kg * Kf) ^ 2 := by
    have h1 := cauchy_schwarz_3 (p_g 1) (p_g 2) (p_g 3) (p_f 1) (p_f 2) (p_f 3)
    dsimp [S_gf]
    rw [← hKg_sq, ← hKf_sq] at h1
    exact h1.trans_eq (mul_pow Kg Kf 2).symm
  have hS_gf_le : S_gf ≤ Kg * Kf :=
    (abs_le_of_sq_le_sq' h_cs (mul_nonneg hKg_nn hKf_nn)).2
  let B : ℝ := s_g + s_f - m ^ 2 / 2
  have hu_nn : 0 ≤ s_g - m ^ 2 / 2 := sub_nonneg.mpr hsg_lo
  have hu_le : s_g - m ^ 2 / 2 ≤ m ^ 2 := by linarith only [hsg_hi]
  have hv_nn : 0 ≤ s_f - m ^ 2 / 2 := sub_nonneg.mpr hsf_lo
  have hv_le : s_f - m ^ 2 / 2 ≤ m ^ 2 := by linarith only [hsf_hi]
  let u : ℝ := s_g - m ^ 2 / 2
  let v : ℝ := s_f - m ^ 2 / 2
  let D_disc : ℝ := 4 * s_g * s_f - B ^ 2
  have hD_id : D_disc = 3 / 4 * m ^ 4 + u * (m ^ 2 - u) + v * (m ^ 2 - v) + 2 * u * v := by
    dsimp [D_disc, B, u, v]
    ring
  have hD_nn : 0 ≤ D_disc := by
    rw [hD_id]
    have h1 : 0 ≤ u * (m ^ 2 - u) := mul_nonneg hu_nn (sub_nonneg.mpr hu_le)
    have h2 : 0 ≤ v * (m ^ 2 - v) := mul_nonneg hv_nn (sub_nonneg.mpr hv_le)
    have h3 : 0 ≤ 3 / 4 * m ^ 4 := by positivity
    have h4 : 0 ≤ 2 * u * v := mul_nonneg (mul_nonneg zero_le_two hu_nn) hv_nn
    exact add_nonneg (add_nonneg (add_nonneg h3 h1) h2) h4
  have h_sos : s_g * (4 * (s_g + Kg ^ 2) * (s_f + Kf ^ 2) - (2 * Kg * Kf + B) ^ 2) =
      (2 * s_g * Kf - B * Kg) ^ 2 + D_disc * Kg ^ 2 + s_g * D_disc := by
    dsimp [D_disc]
    ring
  have h_diff_nn : 0 ≤ 4 * (s_g + Kg ^ 2) * (s_f + Kf ^ 2) - (2 * Kg * Kf + B) ^ 2 := by
    have h_rhs_nn : 0 ≤ s_g * (4 * (s_g + Kg ^ 2) * (s_f + Kf ^ 2) - (2 * Kg * Kf + B) ^ 2) := by
      rw [h_sos]
      exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hD_nn (sq_nonneg _)))
        (mul_nonneg hsg_pos.le hD_nn)
    exact (mul_nonneg_iff_of_pos_left hsg_pos).mp h_rhs_nn
  have h_sq_le : (2 * Kg * Kf + B) ^ 2 ≤ (2 * p_g 0 * p_f 0) ^ 2 := by
    have h_eq : (2 * p_g 0 * p_f 0) ^ 2 = 4 * (s_g + Kg ^ 2) * (s_f + Kf ^ 2) := by
      calc (2 * p_g 0 * p_f 0) ^ 2 = 4 * p_g 0 ^ 2 * p_f 0 ^ 2 := by ring
        _ = 4 * (s_g + Kg ^ 2) * (s_f + Kf ^ 2) := by rw [hpg0_sq, hpf0_sq]
    linarith only [h_eq, h_diff_nn]
  have h_lin_le : 2 * Kg * Kf + B ≤ 2 * p_g 0 * p_f 0 :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h_sq_le
  have h_mink_sub : minkowskiInner (p_g - p_f) (p_g - p_f) =
      s_g + s_f - 2 * (p_g 0 * p_f 0 - S_gf) := by
    dsimp [s_g, s_f, S_gf]
    simp only [minkowskiInner_explicit, Pi.sub_apply]
    ring
  rw [h_mink_sub]
  dsimp [B] at h_lin_le
  linarith only [h_lin_le, hS_gf_le]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem wightmanTranslate_eq_self_of_fourier_zero_near_excited
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (htrans : WightmanTranslationInvariant WData.W)
    {m M : ℝ} (hm : 0 < m) (hgap : MassGapSpectrumCondition m M WData.W)
    (k : ℕ) (α : Fin k → ι) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (hsupp : ∃ V_exc : Set (Fin k → Fin 4 → ℝ), IsOpen V_exc ∧
      { q : Fin k → Fin 4 → ℝ | -(∑ i : Fin k, q i) ∈ excitedMassSpectrum m M } ⊆ V_exc ∧
      ∀ q ∈ V_exc, minkowskiFourier F q = 0)
    (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a (wightmanSchwartzVec WData k α F) =
      wightmanSchwartzVec WData k α F := by
  rcases hsupp with ⟨V_exc, hVexc_open, hVexc_sub, hVexc_zero⟩
  let v : WightmanHilbert WData := wightmanSchwartzVec WData k α F
  let Ψ₀ : WightmanHilbert WData := wightmanTranslate WData htrans a v - v
  suffices h0 : ‖Ψ₀‖ ^ 2 ≤ 0 by
    have h_norm0 : ‖Ψ₀‖ = 0 := by nlinarith [norm_nonneg Ψ₀]
    exact sub_eq_zero.mp (norm_eq_zero.mp h_norm0)
  have h_conv_eq : ∀ (R : ℝ) (hR : 0 < R),
      wightmanSchwartzVec WData k α (diagConvSchwartz k (subGapPosKernelScale m hm R hR) F) =
        v := by
    intro R hR
    refine wightmanSchwartzVec_eq_of_fourier_eq_near_massGapSpectrum WData hgap k α _ F ?_
    let V_zero : Set (Fin k → Fin 4 → ℝ) :=
      { q | ‖(fun _ : Fin 1 => ∑ i : Fin k, q i)‖ < m / (4 * R) }
    have hVzero_open : IsOpen V_zero := by
      refine isOpen_lt ?_ continuous_const
      exact continuous_norm.comp
        (continuous_pi fun _ => continuous_finsetSum Finset.univ fun i _ => continuous_apply i)
    refine ⟨V_zero ∪ V_exc, hVzero_open.union hVexc_open, fun q hq => ?_, fun q hq => ?_⟩
    · rcases hq with h_z | h_ex
      · refine Or.inl ?_
        have h_sum0 : ∑ i : Fin k, q i = 0 := by
          have := Set.mem_singleton_iff.mp h_z
          exact neg_eq_zero.mp this
        dsimp [V_zero]
        have h_z_fn : (fun _ : Fin 1 => ∑ i : Fin k, q i) = 0 := by
          ext i μ
          rw [h_sum0]
          rfl
        rw [h_z_fn, norm_zero]
        positivity
      · exact Or.inr (hVexc_sub h_ex)
    · rw [minkowskiFourier_diagConvSchwartz, minkowskiFourier_subGapPosKernelScale]
      rcases hq with h_z | h_ex
      · dsimp [V_zero] at h_z
        have h_ball : ‖R • (fun _ : Fin 1 => ∑ i : Fin k, q i)‖ ≤ m / 4 := by
          rw [norm_smul, Real.norm_of_nonneg hR.le]
          calc R * ‖(fun _ : Fin 1 => ∑ i : Fin k, q i)‖ ≤ R * (m / (4 * R)) :=
                mul_le_mul_of_nonneg_left h_z.le hR.le
            _ = m / 4 := by field_simp [hR.ne']
        rw [subGapMomBump_eq_one_of_norm_le hm h_ball, one_mul]
      · rw [hVexc_zero q h_ex, mul_zero]
  have h_le_R : ∀ R : ℝ, 0 < R →
      ‖Ψ₀‖ ^ 2 ≤ (‖Ψ₀‖ * ‖v‖) *
        ∫ y : Fin 1 → Fin 4 → ℝ,
          ‖subGapPosKernel m hm (fun _ => y 0 - R⁻¹ • a) - subGapPosKernel m hm y‖ := by
    intro R hR
    let χ_R := subGapPosKernelScale m hm R hR
    have hΨ₀_eq : Ψ₀ = wightmanSchwartzVec WData k α
        (diagConvSchwartz k (schwartzDiagTranslateN 1 a χ_R - χ_R) F) := by
      rw [diagConvSchwartz_sub_left, map_sub, ← schwartzDiagTranslateN_diagConvSchwartz,
        ← wightmanTranslate_wightmanSchwartzVec WData htrans a k α (diagConvSchwartz k χ_R F),
        h_conv_eq R hR]
    let T : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
      (innerSL ℂ Ψ₀).comp (wightmanSchwartzVec WData k α)
    have h_inner_eq : ⟪Ψ₀, Ψ₀⟫_ℂ =
        ∫ z : Fin 1 → Fin 4 → ℝ,
          (schwartzDiagTranslateN 1 a χ_R - χ_R) z *
            ⟪Ψ₀, wightmanTranslate WData htrans (z 0) v⟫_ℂ := by
      have hT := clm_diagConvSchwartz_eq_integral k T (schwartzDiagTranslateN 1 a χ_R - χ_R) F
      have hL : T (diagConvSchwartz k (schwartzDiagTranslateN 1 a χ_R - χ_R) F) = ⟪Ψ₀, Ψ₀⟫_ℂ := by
        dsimp [T]
        rw [← hΨ₀_eq]
      rw [← hL, hT]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      dsimp [T]
      rw [← wightmanTranslate_wightmanSchwartzVec WData htrans (z 0) k α F]
    have h_sq_eq : ‖⟪Ψ₀, Ψ₀⟫_ℂ‖ = ‖Ψ₀‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) Ψ₀]
      norm_cast
      rw [abs_of_nonneg (sq_nonneg _)]
    have h_int_dom : Integrable (fun z : Fin 1 → Fin 4 → ℝ =>
        ‖(schwartzDiagTranslateN 1 a χ_R - χ_R) z‖ * (‖Ψ₀‖ * ‖v‖)) volume :=
      (schwartzDiagTranslateN 1 a χ_R - χ_R).integrable.norm.mul_const (‖Ψ₀‖ * ‖v‖)
    have h_norm_int := norm_integral_le_integral_norm
      (μ := volume)
      (fun z : Fin 1 → Fin 4 → ℝ =>
        (schwartzDiagTranslateN 1 a χ_R - χ_R) z * ⟪Ψ₀, wightmanTranslate WData htrans (z 0) v⟫_ℂ)
    have h_mono : (∫ z : Fin 1 → Fin 4 → ℝ,
        ‖(schwartzDiagTranslateN 1 a χ_R - χ_R) z *
          ⟪Ψ₀, wightmanTranslate WData htrans (z 0) v⟫_ℂ‖) ≤
        ∫ z : Fin 1 → Fin 4 → ℝ,
          ‖(schwartzDiagTranslateN 1 a χ_R - χ_R) z‖ * (‖Ψ₀‖ * ‖v‖) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        h_int_dom (Filter.Eventually.of_forall fun z => ?_)
      dsimp only
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact (norm_inner_le_norm _ _).trans_eq (by rw [norm_wightmanTranslate])
    rw [integral_mul_const] at h_mono
    rw [← h_sq_eq, h_inner_eq]
    refine h_norm_int.trans (h_mono.trans ?_)
    rw [mul_comm _ (‖Ψ₀‖ * ‖v‖), integral_norm_shift_subGapPosKernelScale]
  have h_tend_rhs : Tendsto (fun R : ℝ => (‖Ψ₀‖ * ‖v‖) *
      ∫ y : Fin 1 → Fin 4 → ℝ,
        ‖subGapPosKernel m hm (fun _ => y 0 - R⁻¹ • a) - subGapPosKernel m hm y‖)
      atTop (𝓝 ((‖Ψ₀‖ * ‖v‖) * 0)) :=
    tendsto_const_nhds.mul (tendsto_l1_schwartz_shift_inv_scale (subGapPosKernel m hm) a)
  rw [mul_zero] at h_tend_rhs
  have h_ev_le : ∀ᶠ R : ℝ in atTop,
      ‖Ψ₀‖ ^ 2 ≤ (‖Ψ₀‖ * ‖v‖) *
        ∫ y : Fin 1 → Fin 4 → ℝ,
          ‖subGapPosKernel m hm (fun _ => y 0 - R⁻¹ • a) - subGapPosKernel m hm y‖ :=
    (Filter.eventually_gt_atTop (0 : ℝ)).mono fun R hR => h_le_R R hR
  exact ge_of_tendsto h_tend_rhs h_ev_le

theorem hepp_subgap_vacuum_projection
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (α : Fin k → ι) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (hsupp : ∃ V_exc : Set (Fin k → Fin 4 → ℝ), IsOpen V_exc ∧
      { q : Fin k → Fin 4 → ℝ | -(∑ i : Fin k, q i) ∈ excitedMassSpectrum m M } ⊆ V_exc ∧
      ∀ q ∈ V_exc, minkowskiFourier F q = 0) :
    wightmanSchwartzVec D.wightman.WData k α F =
      ⟪D.vacuum, wightmanSchwartzVec D.wightman.WData k α F⟫_ℂ • D.vacuum :=
  D.eq_smul_vacuum_of_translate_fixed fun a =>
    wightmanTranslate_eq_self_of_fourier_zero_near_excited D.wightman.WData
      D.wightman.translationInvariant D.hm D.massGap k α F hsupp a

theorem hepp_subgap_vacuum_projection_indexed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (Φ : IndexedSchwartz ι k)
    (hsupp : ∀ α : Fin k → ι, ∃ V_exc : Set (Fin k → Fin 4 → ℝ), IsOpen V_exc ∧
      { q : Fin k → Fin 4 → ℝ | -(∑ i : Fin k, q i) ∈ excitedMassSpectrum m M } ⊆ V_exc ∧
      ∀ q ∈ V_exc, minkowskiFourier (Φ α) q = 0) :
    wightmanIndexedVec D.wightman.WData k Φ =
      ⟪D.vacuum, wightmanIndexedVec D.wightman.WData k Φ⟫_ℂ • D.vacuum := by
  unfold wightmanIndexedVec
  calc (∑ α : Fin k → ι, wightmanSchwartzVec D.wightman.WData k α (Φ α))
      = ∑ α : Fin k → ι,
          ⟪D.vacuum, wightmanSchwartzVec D.wightman.WData k α (Φ α)⟫_ℂ • D.vacuum := by
        refine Finset.sum_congr rfl fun α _ => ?_
        exact hepp_subgap_vacuum_projection D k α (Φ α) (hsupp α)
    _ = (∑ α : Fin k → ι, ⟪D.vacuum, wightmanSchwartzVec D.wightman.WData k α (Φ α)⟫_ℂ) •
          D.vacuum := by rw [← Finset.sum_smul]
    _ = ⟪D.vacuum, ∑ α : Fin k → ι, wightmanSchwartzVec D.wightman.WData k α (Φ α)⟫_ℂ •
          D.vacuum := by rw [inner_sum]

theorem haagRuelleAdjApply_haagRuelleApply_vacuum_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s₁ s₂ : Fin D.mode.ν) (f g : SmoothWavepacket) (t₁ t₂ : ℝ) :
    wightmanIndexedVec D.wightman.WData 2
        (haagRuelleAdjApply D s₁ f t₁ 1
          (haagRuelleApply D s₂ g t₂ 0 (vacuumIndexedSchwartz ι))) =
      ⟪haagRuelleVacCreate D s₁ f 0, haagRuelleVacCreate D s₂ g 0⟫_ℂ • D.vacuum := by
  let Φ_one : IndexedSchwartz ι 1 := haagRuelleApply D s₂ g t₂ 0 (vacuumIndexedSchwartz ι)
  let Φ_two : IndexedSchwartz ι 2 := haagRuelleAdjApply D s₁ f t₁ 1 Φ_one
  have h_proj : wightmanIndexedVec D.wightman.WData 2 Φ_two =
      ⟪D.vacuum, wightmanIndexedVec D.wightman.WData 2 Φ_two⟫_ℂ • D.vacuum := by
    refine hepp_subgap_vacuum_projection_indexed D 2 Φ_two fun γ => ?_
    let V_exc : Set (Fin 2 → Fin 4 → ℝ) :=
      { q | m ^ 2 * (3 / 4) < minkowskiInner (-(q 0 + q 1)) (-(q 0 + q 1)) }
    have hV_open : IsOpen V_exc := by
      refine isOpen_lt continuous_const ?_
      exact contDiff_minkowskiInner_self.continuous.comp
        ((continuous_apply 0).add (continuous_apply 1)).neg
    have hV_sub : { q : Fin 2 → Fin 4 → ℝ |
        -(∑ i : Fin 2, q i) ∈ excitedMassSpectrum m M } ⊆ V_exc := by
      intro q hq
      rw [Set.mem_setOf_eq, Fin.sum_univ_two] at hq
      have hb := (mem_excitedMassSpectrum_bounds D.hm D.hM hq).2
      have hm2 : 0 < m ^ 2 := sq_pos_of_pos D.hm
      dsimp [V_exc]
      linarith
    refine ⟨V_exc, hV_open, hV_sub, fun q hq => ?_⟩
    have h_one_eq : Φ_one (Fin.tail γ) = haagRuelleIndexedTest D s₂ g t₂ (γ 1) := by
      dsimp [Φ_one, haagRuelleApply, indexedPrepend]
      have h_vac : vacuumIndexedSchwartz ι (Fin.tail (Fin.tail γ)) =
          momentumWavepacketSchwartz 0 0 := rfl
      rw [h_vac, schwartzPrepend_zero_vac]
      rfl
    have h_two_eq : Φ_two γ =
        schwartzPrepend 1 (haagRuelleAdjIndexedTest D s₁ f t₁ (γ 0))
          (haagRuelleIndexedTest D s₂ g t₂ (γ 1)) := by
      dsimp [Φ_two, haagRuelleAdjApply, indexedPrepend]
      rw [h_one_eq]
    rw [h_two_eq, minkowskiFourier_schwartzPrepend]
    by_cases hq0 : q 0 ∈ tsupport (massShellCutoff m M D.hm D.hM)
    · by_cases hq1 : -q 1 ∈ tsupport (massShellCutoff m M D.hm D.hM)
      · have h_strip := minkowskiInner_sub_le_half_sq_of_massShellStrip D.hm D.hM hq1 hq0
        have h_vec : -q 1 - q 0 = -(q 0 + q 1) := by
          ext μ
          simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply]
          ring
        rw [h_vec] at h_strip
        dsimp [V_exc] at hq
        have hm2 : 0 < m ^ 2 := sq_pos_of_pos D.hm
        linarith
      · have h_right0 :
            minkowskiFourier (haagRuelleIndexedTest D s₂ g t₂ (γ 1))
              (fun u : Fin 1 => q (Fin.succ u)) = 0 := by
          have h_arg : (fun u : Fin 1 => q (Fin.succ u)) = fun _ => -(-q 1) := by
            ext u μ
            rw [Subsingleton.elim u 0]
            simp
          rw [h_arg]
          exact minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
            (dualModeWavepacket D s₂ (γ 1) g) t₂ hq1
        rw [h_right0, mul_zero]
    · have h_left0 :
          minkowskiFourier (haagRuelleAdjIndexedTest D s₁ f t₁ (γ 0)) (fun _ => q 0) = 0 := by
        unfold haagRuelleAdjIndexedTest starIndexedTest
        rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply]
        refine Finset.sum_eq_zero fun α₀ _ => ?_
        rw [map_smul, _root_.smul_apply, minkowskiFourierCLM_apply,
          minkowskiFourier_schwartzConj_one, smul_eq_mul]
        have h_arg : -(fun _ : Fin 1 => q 0) = fun _ => -q 0 := rfl
        rw [h_arg]
        dsimp [haagRuelleIndexedTest]
        rw [minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
          (dualModeWavepacket D s₁ α₀ f) t₁ hq0, map_zero, mul_zero]
      rw [h_left0, zero_mul]
  change wightmanIndexedVec D.wightman.WData 2 Φ_two = _
  rw [h_proj]
  congr 1
  have h_vac0 : D.vacuum = wightmanIndexedVec D.wightman.WData 0 (vacuumIndexedSchwartz ι) :=
    (wightmanIndexedVec_vacuum D.wightman.WData).symm
  dsimp [Φ_two, Φ_one]
  rw [h_vac0, ← inner_haagRuelleApply_eq_adj]
  change ⟪haagRuelleVacCreate D s₁ f t₁, haagRuelleVacCreate D s₂ g t₂⟫_ℂ =
    ⟪haagRuelleVacCreate D s₁ f 0, haagRuelleVacCreate D s₂ g 0⟫_ℂ
  rw [haagRuelleVacCreate_time_indep D s₁ f t₁, haagRuelleVacCreate_time_indep D s₂ g t₂]

theorem haagRuelleAdjApply_haagRuelleApply_vacuum_eq_fock
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s₁ s₂ : Fin D.mode.ν) (f g : SmoothWavepacket) (t₁ t₂ : ℝ) :
    wightmanIndexedVec D.wightman.WData 2
        (haagRuelleAdjApply D s₁ f t₁ 1
          (haagRuelleApply D s₂ g t₂ 0 (vacuumIndexedSchwartz ι))) =
      ⟪fockOneParticleVec D.mode.ν s₁ f, fockOneParticleVec D.mode.ν s₂ g⟫_ℂ • D.vacuum := by
  rw [haagRuelleAdjApply_haagRuelleApply_vacuum_eq, inner_haagRuelleVacCreate_eq]

lemma wightmanIndexedVec_indexedPrepend_congr
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {m₁ m₂ : ℕ} {c : ℂ}
    (Ψ₀ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Φ₁ : IndexedSchwartz ι m₁) (Φ₂ : IndexedSchwartz ι m₂)
    (h_eq : wightmanIndexedVec WData m₁ Φ₁ = c • wightmanIndexedVec WData m₂ Φ₂) :
    wightmanIndexedVec WData (m₁ + 1) (indexedPrepend m₁ Ψ₀ Φ₁) =
      c • wightmanIndexedVec WData (m₂ + 1) (indexedPrepend m₂ Ψ₀ Φ₂) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_wightmanBasis_eq_zero WData fun cfg => ?_
  rcases cfg with ⟨j, α, f_c⟩
  let Χ : IndexedSchwartz ι j := fun γ => if γ = α then f_c.val else 0
  have h_basis : wightmanBasis WData ⟨j, (α, f_c)⟩ = wightmanIndexedVec WData j Χ := by
    rw [← wightmanSchwartzVec_compact WData j α f_c]
    unfold wightmanIndexedVec
    rw [Fintype.sum_eq_single α]
    · simp [Χ]
    · intro γ hne
      simp [Χ, hne]
  have h_adj : ∀ (m : ℕ) (Φ : IndexedSchwartz ι m),
      ⟪wightmanIndexedVec WData j Χ,
        wightmanIndexedVec WData (m + 1) (indexedPrepend m Ψ₀ Φ)⟫_ℂ =
      ⟪wightmanIndexedVec WData (j + 1) (indexedPrepend j (starIndexedTest S Ψ₀) Χ),
        wightmanIndexedVec WData m Φ⟫_ℂ := fun m Φ => by
    rw [← inner_conj_symm, inner_wightmanIndexedVec_indexedPrepend, inner_conj_symm]
  rw [h_basis, inner_sub_right, inner_smul_right, h_adj m₁ Φ₁, h_adj m₂ Φ₂,
    ← inner_smul_right, ← inner_sub_right, h_eq, sub_self, inner_zero_right]

lemma wightmanIndexedVec_indexedPrepend_congr_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {m₁ m₂ : ℕ}
    (Ψ₀ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Φ₁ : IndexedSchwartz ι m₁) (Φ₂ : IndexedSchwartz ι m₂)
    (h_eq : wightmanIndexedVec WData m₁ Φ₁ = wightmanIndexedVec WData m₂ Φ₂) :
    wightmanIndexedVec WData (m₁ + 1) (indexedPrepend m₁ Ψ₀ Φ₁) =
      wightmanIndexedVec WData (m₂ + 1) (indexedPrepend m₂ Ψ₀ Φ₂) := by
  simpa using wightmanIndexedVec_indexedPrepend_congr WData Ψ₀ Φ₁ Φ₂ (c := 1)
    (by simpa using h_eq)

def schwartzChain : (r : ℕ) →
    (Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) → SchwartzMap (Fin r → Fin 4 → ℝ) ℂ
  | 0, _ => momentumWavepacketSchwartz 0 0
  | k + 1, ψ => schwartzPrepend k (ψ 0) (schwartzChain k (ψ ∘ Fin.succ))

def indexedChain (κ : Type*) : (r : ℕ) →
    (Fin r → κ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) → IndexedSchwartz κ r
  | 0, _ => vacuumIndexedSchwartz κ
  | k + 1, Ψ => indexedPrepend k (Ψ 0) (indexedChain κ k (Ψ ∘ Fin.succ))

lemma indexedChain_apply (κ : Type*) (r : ℕ)
    (Ψ : Fin r → κ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (γ : Fin r → κ) :
    indexedChain κ r Ψ γ = schwartzChain r (fun i => Ψ i (γ i)) := by
  induction r with
  | zero => rfl
  | succ k ih =>
    dsimp [indexedChain, schwartzChain, indexedPrepend]
    rw [ih]
    rfl

lemma schwartzChain_update_zero (r : ℕ) (j : Fin r)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (Function.update ψ j 0) = 0 := by
  induction r with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ ?_ j
    · dsimp [schwartzChain]
      rw [Function.update_self, schwartzPrepend_zero_left]
    · intro j'
      dsimp [schwartzChain]
      have h_upd : Function.update ψ j'.succ 0 ∘ Fin.succ =
          Function.update (ψ ∘ Fin.succ) j' 0 := by
        ext i x
        by_cases hi : i = j'
        · subst hi; simp
        · simp [Function.update_of_ne hi, Fin.succ_inj.ne.mpr hi]
      rw [h_upd, ih j' (ψ ∘ Fin.succ), schwartzPrepend_zero_right]

lemma schwartzChain_update_add (r : ℕ) (j : Fin r)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (φ₁ φ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (Function.update ψ j (φ₁ + φ₂)) =
      schwartzChain r (Function.update ψ j φ₁) + schwartzChain r (Function.update ψ j φ₂) := by
  induction r with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ ?_ j
    · dsimp [schwartzChain]
      have h_tl : ∀ φ, Function.update ψ 0 φ ∘ Fin.succ = ψ ∘ Fin.succ := fun φ => by
        ext i x
        simp
      rw [Function.update_self, Function.update_self, Function.update_self,
        h_tl, h_tl, h_tl, schwartzPrepend_add_left]
    · intro j'
      dsimp [schwartzChain]
      have h0 : ∀ φ, Function.update ψ j'.succ φ 0 = ψ 0 := fun φ =>
        Function.update_of_ne (Fin.succ_ne_zero j').symm _ ψ
      have h_tl : ∀ φ, Function.update ψ j'.succ φ ∘ Fin.succ =
          Function.update (ψ ∘ Fin.succ) j' φ := fun φ => by
        ext i x
        by_cases hi : i = j'
        · subst hi; simp
        · simp [Function.update_of_ne hi, Fin.succ_inj.ne.mpr hi]
      rw [h0, h0, h0, h_tl, h_tl, h_tl, ih j' (ψ ∘ Fin.succ), schwartzPrepend_add_right]

lemma schwartzChain_update_sub (r : ℕ) (j : Fin r)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (φ₁ φ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (Function.update ψ j (φ₁ - φ₂)) =
      schwartzChain r (Function.update ψ j φ₁) - schwartzChain r (Function.update ψ j φ₂) := by
  induction r with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ ?_ j
    · dsimp [schwartzChain]
      have h_tl : ∀ φ, Function.update ψ 0 φ ∘ Fin.succ = ψ ∘ Fin.succ := fun φ => by
        ext i x
        simp
      rw [Function.update_self, Function.update_self, Function.update_self,
        h_tl, h_tl, h_tl, schwartzPrepend_sub_left]
    · intro j'
      dsimp [schwartzChain]
      have h0 : ∀ φ, Function.update ψ j'.succ φ 0 = ψ 0 := fun φ =>
        Function.update_of_ne (Fin.succ_ne_zero j').symm _ ψ
      have h_tl : ∀ φ, Function.update ψ j'.succ φ ∘ Fin.succ =
          Function.update (ψ ∘ Fin.succ) j' φ := fun φ => by
        ext i x
        by_cases hi : i = j'
        · subst hi; simp
        · simp [Function.update_of_ne hi, Fin.succ_inj.ne.mpr hi]
      rw [h0, h0, h0, h_tl, h_tl, h_tl, ih j' (ψ ∘ Fin.succ), schwartzPrepend_sub_right]

lemma schwartzChain_update_smul (r : ℕ) (j : Fin r)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (c : ℂ) (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (Function.update ψ j (c • φ)) =
      c • schwartzChain r (Function.update ψ j φ) := by
  induction r with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ ?_ j
    · dsimp [schwartzChain]
      have h_tl : ∀ φ', Function.update ψ 0 φ' ∘ Fin.succ = ψ ∘ Fin.succ := fun φ' => by
        ext i x
        simp
      rw [Function.update_self, Function.update_self, h_tl, h_tl, schwartzPrepend_smul_left]
    · intro j'
      dsimp [schwartzChain]
      have h0 : ∀ φ', Function.update ψ j'.succ φ' 0 = ψ 0 := fun φ' =>
        Function.update_of_ne (Fin.succ_ne_zero j').symm _ ψ
      have h_tl : ∀ φ', Function.update ψ j'.succ φ' ∘ Fin.succ =
          Function.update (ψ ∘ Fin.succ) j' φ' := fun φ' => by
        ext i x
        by_cases hi : i = j'
        · subst hi; simp
        · simp [Function.update_of_ne hi, Fin.succ_inj.ne.mpr hi]
      rw [h0, h0, h_tl, h_tl, ih j' (ψ ∘ Fin.succ), schwartzPrepend_smul_right]

lemma schwartzChain_update_sum {κ : Type*} (r : ℕ) (j : Fin r)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (s : Finset κ)
    (φ : κ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (Function.update ψ j (∑ a ∈ s, φ a)) =
      ∑ a ∈ s, schwartzChain r (Function.update ψ j (φ a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact schwartzChain_update_zero r j ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, schwartzChain_update_add, ih]

omit [Fintype ι] [DecidableEq ι] in
lemma indexedChain_update_eq (r : ℕ) (j : Fin r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Θ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (γ : Fin r → ι) :
    indexedChain ι r (Function.update Ψ j Θ) γ =
      schwartzChain r (Function.update (fun i => Ψ i (γ i)) j (Θ (γ j))) := by
  rw [indexedChain_apply]
  congr 1
  ext i x
  by_cases hi : i = j
  · subst hi; simp
  · simp [Function.update_of_ne hi]

lemma wightmanIndexedVec_indexedChain_update_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (j : Fin r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j 0)) = 0 := by
  unfold wightmanIndexedVec
  refine Finset.sum_eq_zero fun γ _ => ?_
  rw [indexedChain_update_eq r j Ψ 0 γ]
  change wightmanSchwartzVec WData r γ (schwartzChain r (Function.update _ j 0)) = 0
  rw [schwartzChain_update_zero, map_zero]

lemma wightmanIndexedVec_indexedChain_update_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (j : Fin r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Θ₁ Θ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j (Θ₁ + Θ₂))) =
      wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j Θ₁)) +
        wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j Θ₂)) := by
  unfold wightmanIndexedVec
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [indexedChain_update_eq r j Ψ (Θ₁ + Θ₂) γ, indexedChain_update_eq r j Ψ Θ₁ γ,
    indexedChain_update_eq r j Ψ Θ₂ γ]
  change wightmanSchwartzVec WData r γ
      (schwartzChain r (Function.update (fun i => Ψ i (γ i)) j (Θ₁ (γ j) + Θ₂ (γ j)))) = _
  rw [schwartzChain_update_add, map_add]

lemma wightmanIndexedVec_indexedChain_update_sub
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (j : Fin r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Θ₁ Θ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j (Θ₁ - Θ₂))) =
      wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j Θ₁)) -
        wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j Θ₂)) := by
  unfold wightmanIndexedVec
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [indexedChain_update_eq r j Ψ (Θ₁ - Θ₂) γ, indexedChain_update_eq r j Ψ Θ₁ γ,
    indexedChain_update_eq r j Ψ Θ₂ γ]
  change wightmanSchwartzVec WData r γ
      (schwartzChain r (Function.update (fun i => Ψ i (γ i)) j (Θ₁ (γ j) - Θ₂ (γ j)))) = _
  rw [schwartzChain_update_sub, map_sub]

lemma wightmanIndexedVec_indexedChain_update_smul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (j : Fin r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (c : ℂ) (Θ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j (c • Θ))) =
      c • wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j Θ)) := by
  unfold wightmanIndexedVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [indexedChain_update_eq r j Ψ (c • Θ) γ, indexedChain_update_eq r j Ψ Θ γ]
  change wightmanSchwartzVec WData r γ
      (schwartzChain r (Function.update (fun i => Ψ i (γ i)) j (c • Θ (γ j)))) = _
  rw [schwartzChain_update_smul, map_smul]

lemma wightmanIndexedVec_indexedChain_update_sum
    {κ : Type*} {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (j : Fin r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (s : Finset κ)
    (Θ : κ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j (∑ a ∈ s, Θ a))) =
      ∑ a ∈ s, wightmanIndexedVec WData r (indexedChain ι r (Function.update Ψ j (Θ a))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact wightmanIndexedVec_indexedChain_update_zero WData r j Ψ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      wightmanIndexedVec_indexedChain_update_add, ih]

lemma wightmanIndexedVec_indexedChain_congr_cast
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {n₁ n₂ : ℕ} (h : n₁ = n₂)
    (Ψ₁ : Fin n₁ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (Ψ₂ : Fin n₂ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hΨ : ∀ i : Fin n₁, Ψ₁ i = Ψ₂ (Fin.cast h i)) :
    wightmanIndexedVec WData n₁ (indexedChain ι n₁ Ψ₁) =
      wightmanIndexedVec WData n₂ (indexedChain ι n₂ Ψ₂) := by
  subst h
  have heq : Ψ₁ = Ψ₂ := funext hΨ
  subst heq
  rfl

lemma wightmanIndexedVec_indexedChain_contract_right
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (p m₁ : ℕ) {c : ℂ}
    (Ψ : Fin (p + m₁) → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h_tail : wightmanIndexedVec WData m₁
        (indexedChain ι m₁ (fun u => Ψ (Fin.natAdd p u))) =
      c • wightmanVacuum WData) :
    wightmanIndexedVec WData (p + m₁) (indexedChain ι (p + m₁) Ψ) =
      c • wightmanIndexedVec WData p (indexedChain ι p (fun i => Ψ (Fin.castAdd m₁ i))) := by
  induction p with
  | zero =>
    have h0 : wightmanIndexedVec WData (0 + m₁) (indexedChain ι (0 + m₁) Ψ) =
        wightmanIndexedVec WData m₁ (indexedChain ι m₁ (fun u => Ψ (Fin.natAdd 0 u))) :=
      wightmanIndexedVec_indexedChain_congr_cast WData (Nat.zero_add m₁) Ψ
        (fun u => Ψ (Fin.natAdd 0 u)) fun i => by
          congr 1
          ext
          simp
    rw [h0, h_tail]
    change c • wightmanVacuum WData =
      c • wightmanIndexedVec WData 0 (vacuumIndexedSchwartz ι)
    rw [wightmanIndexedVec_vacuum]
  | succ k ih =>
    have h_len : (k + 1) + m₁ = (k + m₁) + 1 := by omega
    let Ψ_cast : Fin ((k + m₁) + 1) → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
      fun j => Ψ (Fin.cast h_len.symm j)
    have h_lhs_eq :
        wightmanIndexedVec WData ((k + 1) + m₁) (indexedChain ι ((k + 1) + m₁) Ψ) =
          wightmanIndexedVec WData ((k + m₁) + 1) (indexedChain ι ((k + m₁) + 1) Ψ_cast) :=
      wightmanIndexedVec_indexedChain_congr_cast WData h_len Ψ Ψ_cast fun i =>
        congrArg Ψ (by ext; rfl)
    have h_0 : Ψ_cast 0 = Ψ 0 := congrArg Ψ (by ext; rfl)
    have h_tail_fn : (fun u => (Ψ_cast ∘ Fin.succ) (Fin.natAdd k u)) =
        fun u => Ψ (Fin.natAdd (k + 1) u) := funext fun u => by
      dsimp [Ψ_cast]
      exact congrArg Ψ (by ext; dsimp; omega)
    have h_tail' : wightmanIndexedVec WData m₁
        (indexedChain ι m₁ (fun u => (Ψ_cast ∘ Fin.succ) (Fin.natAdd k u))) =
        c • wightmanVacuum WData := by
      rw [h_tail_fn]
      exact h_tail
    have h_ih := ih (Ψ_cast ∘ Fin.succ) h_tail'
    have h_step := wightmanIndexedVec_indexedPrepend_congr WData (Ψ_cast 0)
      (indexedChain ι (k + m₁) (Ψ_cast ∘ Fin.succ))
      (indexedChain ι k (fun i => (Ψ_cast ∘ Fin.succ) (Fin.castAdd m₁ i))) h_ih
    have h_rhs_fn :
        indexedPrepend k (Ψ_cast 0)
          (indexedChain ι k (fun i => (Ψ_cast ∘ Fin.succ) (Fin.castAdd m₁ i))) =
        indexedChain ι (k + 1) (fun i => Ψ (Fin.castAdd m₁ i)) := by
      dsimp [indexedChain]
      rw [h_0]
      congr 2
    rw [h_lhs_eq]
    change wightmanIndexedVec WData (k + m₁ + 1)
        (indexedPrepend (k + m₁) (Ψ_cast 0) (indexedChain ι (k + m₁) (Ψ_cast ∘ Fin.succ))) =
      c • wightmanIndexedVec WData (k + 1) (indexedChain ι (k + 1) fun i => Ψ (Fin.castAdd m₁ i))
    rw [h_step, h_rhs_fn]

lemma wightmanIndexedVec_indexedChain_swap_adj
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {η : ℂ} (hloc : LocalCommutativity η WData.W)
    (r : ℕ) (i : Fin r) (hi : i.val + 1 < r)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hsp : ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
      x₁ ∈ tsupport (Ψ i α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      x₂ ∈ tsupport (Ψ ⟨i.val + 1, hi⟩ α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      is_spacelike (x₁ 0 - x₂ 0)) :
    wightmanIndexedVec WData r (indexedChain ι r Ψ) =
      η • wightmanIndexedVec WData r
        (indexedChain ι r (Ψ ∘ Equiv.swap i ⟨i.val + 1, hi⟩)) := by
  induction r with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases (motive := fun j : Fin (k + 1) =>
      ∀ (hj : j.val + 1 < k + 1)
        (Φ : Fin (k + 1) → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ),
      (∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        x₁ ∈ tsupport (Φ j α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        x₂ ∈ tsupport (Φ ⟨j.val + 1, hj⟩ α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0)) →
      wightmanIndexedVec WData (k + 1) (indexedChain ι (k + 1) Φ) =
        η • wightmanIndexedVec WData (k + 1)
          (indexedChain ι (k + 1) (Φ ∘ Equiv.swap j ⟨j.val + 1, hj⟩))) ?_ ?_ i hi Ψ hsp
    · intro hj Φ hsp0
      rcases k with _ | k'
      · simp at hj
      · have h_sw := wightmanIndexedVec_indexedPrepend_swap_of_spacelike WData hloc
          (Φ 0) (Φ ⟨0 + 1, hj⟩) hsp0 k' (indexedChain ι k' ((Φ ∘ Fin.succ) ∘ Fin.succ))
        have h_rhs_eq :
            indexedPrepend (k' + 1) (Φ ⟨0 + 1, hj⟩)
              (indexedPrepend k' (Φ 0) (indexedChain ι k' ((Φ ∘ Fin.succ) ∘ Fin.succ))) =
            indexedChain ι (k' + 2) (Φ ∘ Equiv.swap 0 ⟨0 + 1, hj⟩) := by
          have h_p0 : Φ ⟨0 + 1, hj⟩ = (Φ ∘ Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩) 0 := by
            simp [Equiv.swap_apply_left]
          have h_p1 : Φ 0 = (Φ ∘ Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩) (Fin.succ 0) := by
            have h1 : (Fin.succ 0 : Fin (k' + 2)) = ⟨0 + 1, hj⟩ := rfl
            rw [Function.comp_apply, h1, Equiv.swap_apply_right]
          have h_tl : (Φ ∘ Fin.succ) ∘ Fin.succ =
              ((Φ ∘ Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩) ∘ Fin.succ) ∘ Fin.succ := by
            funext u α
            ext x
            have hne0 : u.succ.succ ≠ (0 : Fin (k' + 2)) := Fin.succ_ne_zero _
            have hne1 : u.succ.succ ≠ ⟨0 + 1, hj⟩ := fun h => by
              have hv := congrArg Fin.val h
              simp at hv
            change Φ u.succ.succ α x =
              Φ (Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩ u.succ.succ) α x
            rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
          change indexedPrepend (k' + 1) (Φ ⟨0 + 1, hj⟩)
              (indexedPrepend k' (Φ 0) (indexedChain ι k' ((Φ ∘ Fin.succ) ∘ Fin.succ))) =
            indexedPrepend (k' + 1) ((Φ ∘ Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩) 0)
              (indexedPrepend k'
                ((Φ ∘ Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩) (Fin.succ 0))
                (indexedChain ι k'
                  (((Φ ∘ Equiv.swap (0 : Fin (k' + 2)) ⟨0 + 1, hj⟩) ∘ Fin.succ) ∘ Fin.succ)))
          rw [← h_p0, ← h_p1, ← h_tl]
        exact h_sw.trans (congrArg (fun X => η • wightmanIndexedVec WData (k' + 2) X) h_rhs_eq)
    · intro j' hj' Φ hsp_s
      have hj_k : j'.val + 1 < k := Nat.succ_lt_succ_iff.mp hj'
      have hsp' : ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
          x₁ ∈ tsupport ((Φ ∘ Fin.succ) j' α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          x₂ ∈ tsupport ((Φ ∘ Fin.succ) ⟨j'.val + 1, hj_k⟩ α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          is_spacelike (x₁ 0 - x₂ 0) := fun α₁ α₂ x₁ x₂ hx₁ hx₂ =>
        hsp_s α₁ α₂ x₁ x₂ hx₁ hx₂
      have h_ih := ih j' hj_k (Φ ∘ Fin.succ) hsp'
      have h_p := wightmanIndexedVec_indexedPrepend_congr WData (Φ 0)
        (indexedChain ι k (Φ ∘ Fin.succ))
        (indexedChain ι k ((Φ ∘ Fin.succ) ∘ Equiv.swap j' ⟨j'.val + 1, hj_k⟩)) h_ih
      have h_rhs_eq :
          indexedPrepend k (Φ 0)
            (indexedChain ι k ((Φ ∘ Fin.succ) ∘ Equiv.swap j' ⟨j'.val + 1, hj_k⟩)) =
          indexedChain ι (k + 1) (Φ ∘ Equiv.swap j'.succ ⟨j'.succ.val + 1, hj'⟩) := by
        have hne0 : (0 : Fin (k + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
        have hne1 : (0 : Fin (k + 1)) ≠ ⟨j'.succ.val + 1, hj'⟩ := fun h => by
          have hv := congrArg Fin.val h
          simp at hv
        have h0 : Φ 0 = (Φ ∘ Equiv.swap j'.succ ⟨j'.succ.val + 1, hj'⟩) 0 := by
          rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne0 hne1]
        have h_tl : (Φ ∘ Fin.succ) ∘ Equiv.swap j' ⟨j'.val + 1, hj_k⟩ =
            (Φ ∘ Equiv.swap j'.succ ⟨j'.succ.val + 1, hj'⟩) ∘ Fin.succ := by
          ext u α x
          change Φ (Fin.succ (Equiv.swap j' ⟨j'.val + 1, hj_k⟩ u)) α x =
            Φ (Equiv.swap j'.succ ⟨j'.succ.val + 1, hj'⟩ (Fin.succ u)) α x
          congr 2
          by_cases hu0 : u = j'
          · subst hu0
            rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
            rfl
          · by_cases hu1 : u = ⟨j'.val + 1, hj_k⟩
            · subst hu1
              rw [Equiv.swap_apply_right]
              have hu_eq : (Fin.succ ⟨j'.val + 1, hj_k⟩ : Fin (k + 1)) =
                  ⟨j'.succ.val + 1, hj'⟩ := by
                ext; simp
              rw [hu_eq, Equiv.swap_apply_right]
            · have hsu0 : Fin.succ u ≠ j'.succ := Fin.succ_inj.ne.mpr hu0
              have hsu1 : Fin.succ u ≠ ⟨j'.succ.val + 1, hj'⟩ := fun h => by
                apply hu1
                ext
                have hv := congrArg Fin.val h
                simpa using hv
              rw [Equiv.swap_apply_of_ne_of_ne hu0 hu1, Equiv.swap_apply_of_ne_of_ne hsu0 hsu1]
        change indexedPrepend k (Φ 0)
            (indexedChain ι k ((Φ ∘ Fin.succ) ∘ Equiv.swap j' ⟨j'.val + 1, hj_k⟩)) =
          indexedPrepend k ((Φ ∘ Equiv.swap j'.succ ⟨j'.succ.val + 1, hj'⟩) 0)
            (indexedChain ι k ((Φ ∘ Equiv.swap j'.succ ⟨j'.succ.val + 1, hj'⟩) ∘ Fin.succ))
        rw [h0, h_tl]
      exact h_p.trans (congrArg (fun X => η • wightmanIndexedVec WData (k + 1) X) h_rhs_eq)

lemma wightmanIndexedVec_indexedChain_perm_of_pairwise_spacelike
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {η : ℂ} (hloc : LocalCommutativity η WData.W)
    (r : ℕ) (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hsp : Pairwise fun i j : Fin r => ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
      x₁ ∈ tsupport (Ψ i α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      x₂ ∈ tsupport (Ψ j α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      is_spacelike (x₁ 0 - x₂ 0))
    (σ : Equiv.Perm (Fin r)) :
    wightmanIndexedVec WData r (indexedChain ι r Ψ) =
      η ^ permInversions σ • wightmanIndexedVec WData r (indexedChain ι r (Ψ ∘ σ)) := by
  suffices h_ind : ∀ (k : ℕ) (σ : Equiv.Perm (Fin r)), permInversions σ = k →
      ∀ (Φ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ),
        (Pairwise fun i j : Fin r => ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
          x₁ ∈ tsupport (Φ i α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          x₂ ∈ tsupport (Φ j α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          is_spacelike (x₁ 0 - x₂ 0)) →
        wightmanIndexedVec WData r (indexedChain ι r Φ) =
          η ^ k • wightmanIndexedVec WData r (indexedChain ι r (Φ ∘ σ)) from
    h_ind (permInversions σ) σ rfl Ψ hsp
  intro k
  induction k with
  | zero =>
    intro σ hk Φ _
    have hσ1 : σ = 1 := perm_eq_one_of_permInversions_zero hk
    subst hσ1
    simp
  | succ m ih =>
    intro σ hk Φ hΦ
    have hpos : 0 < permInversions σ := by omega
    obtain ⟨i, hi, hinv⟩ := exists_adjacent_inversion_of_pos hpos
    let s : Equiv.Perm (Fin r) := Equiv.swap i ⟨i.val + 1, hi⟩
    let τ : Equiv.Perm (Fin r) := σ * s
    have hτ_inv : permInversions τ = m := by
      have h_step := permInversions_mul_adjacent_swap σ i hi hinv
      change permInversions σ = permInversions τ + 1 at h_step
      omega
    have h1 := ih τ hτ_inv Φ hΦ
    have h_ne : τ i ≠ τ ⟨i.val + 1, hi⟩ :=
      τ.injective.ne (fun h => by have hv := congrArg Fin.val h; simp at hv)
    have h_sw := wightmanIndexedVec_indexedChain_swap_adj WData hloc r i hi (Φ ∘ τ)
      (hΦ h_ne)
    rw [h1, h_sw, smul_smul, pow_succ]
    have hτs : (Φ ∘ τ) ∘ Equiv.swap i ⟨i.val + 1, hi⟩ = Φ ∘ σ := by
      ext u α x
      change Φ (τ (s u)) α x = Φ (σ u) α x
      congr 2
      change (σ * (s * s)) u = σ u
      simp [s, Equiv.swap_mul_self]
    rw [hτs]

lemma wightmanIndexedVec_indexedChain_move_right
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {η : ℂ} (hloc : LocalCommutativity η WData.W)
    (r : ℕ) (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (j : Fin r) (m : ℕ) (hm : j.val + m < r)
    (hsp : ∀ u : Fin m, ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
      x₁ ∈ tsupport (Ψ j α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      x₂ ∈ tsupport (Ψ ⟨j.val + 1 + u.val, by omega⟩ α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
      is_spacelike (x₁ 0 - x₂ 0)) :
    ∃ σ : Equiv.Perm (Fin r),
      (σ ⟨j.val + m, hm⟩ = j ∧
        (∀ a : Fin r, a.val < j.val → σ a = a) ∧
        (∀ u : Fin m, σ ⟨j.val + u.val, by omega⟩ = ⟨j.val + 1 + u.val, by omega⟩) ∧
        (∀ a : Fin r, j.val + m < a.val → σ a = a)) ∧
      wightmanIndexedVec WData r (indexedChain ι r Ψ) =
        η ^ m • wightmanIndexedVec WData r (indexedChain ι r (Ψ ∘ σ)) := by
  induction m with
  | zero =>
    refine ⟨1, ⟨rfl, fun _ _ => rfl, fun u => u.elim0, fun _ _ => rfl⟩, by simp⟩
  | succ k ih =>
    have hk : j.val + k < r := by omega
    obtain ⟨σ_k, ⟨hσ_j, hσ_lt, hσ_mid, hσ_gt⟩, hvec_k⟩ :=
      ih hk fun u => hsp ⟨u.val, by omega⟩
    let pos_k : Fin r := ⟨j.val + k, hk⟩
    let pos_next : Fin r := ⟨pos_k.val + 1, by dsimp [pos_k]; omega⟩
    let sw : Equiv.Perm (Fin r) := Equiv.swap pos_k pos_next
    have hsp_adj : ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        x₁ ∈ tsupport ((Ψ ∘ σ_k) pos_k α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        x₂ ∈ tsupport ((Ψ ∘ σ_k) pos_next α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0) := by
      have h_lhs : σ_k pos_k = j := hσ_j
      have h_rhs : σ_k pos_next = ⟨j.val + 1 + k, by omega⟩ := by
        rw [hσ_gt pos_next (by dsimp [pos_next, pos_k]; omega)]
        ext
        dsimp [pos_next, pos_k]
        omega
      intro α₁ α₂ x₁ x₂ hx₁ hx₂
      rw [Function.comp_apply, h_lhs] at hx₁
      rw [Function.comp_apply, h_rhs] at hx₂
      exact hsp ⟨k, Nat.lt_succ_self k⟩ α₁ α₂ x₁ x₂ hx₁ hx₂
    have h_step := wightmanIndexedVec_indexedChain_swap_adj WData hloc r pos_k
      (by dsimp [pos_k]; exact hm) (Ψ ∘ σ_k) hsp_adj
    refine ⟨σ_k * sw, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · change σ_k (sw ⟨j.val + (k + 1), hm⟩) = j
      have h_eq : (⟨j.val + (k + 1), hm⟩ : Fin r) = pos_next := by
        ext; simp [pos_next, pos_k]; omega
      rw [h_eq, Equiv.swap_apply_right]
      exact hσ_j
    · intro a ha
      have hne1 : a ≠ pos_k := fun h => by have hv := congrArg Fin.val h; simp [pos_k] at hv; omega
      have hne2 : a ≠ pos_next := fun h => by
        have hv := congrArg Fin.val h; simp [pos_next, pos_k] at hv; omega
      change σ_k (sw a) = a
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact hσ_lt a ha
    · intro u
      by_cases hu : u.val < k
      · have hne1 : (⟨j.val + u.val, by omega⟩ : Fin r) ≠ pos_k := fun h => by
          have hv := congrArg Fin.val h; simp [pos_k] at hv; omega
        have hne2 : (⟨j.val + u.val, by omega⟩ : Fin r) ≠ pos_next := fun h => by
          have hv := congrArg Fin.val h; simp [pos_next, pos_k] at hv; omega
        change σ_k (sw ⟨j.val + u.val, by omega⟩) = ⟨j.val + 1 + u.val, by omega⟩
        rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
        exact hσ_mid ⟨u.val, hu⟩
      · have huk : u.val = k := by omega
        have h_eq : (⟨j.val + u.val, by omega⟩ : Fin r) = pos_k := by ext; simp [pos_k, huk]
        change σ_k (sw ⟨j.val + u.val, by omega⟩) = ⟨j.val + 1 + u.val, by omega⟩
        rw [h_eq, Equiv.swap_apply_left]
        refine Eq.trans (hσ_gt pos_next (by dsimp [pos_next, pos_k]; omega)) ?_
        ext; simp [pos_next, pos_k, huk]; omega
    · intro a ha
      have hne1 : a ≠ pos_k := fun h => by have hv := congrArg Fin.val h; simp [pos_k] at hv; omega
      have hne2 : a ≠ pos_next := fun h => by
        have hv := congrArg Fin.val h; simp [pos_next, pos_k] at hv; omega
      change σ_k (sw a) = a
      rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      exact hσ_gt a (by omega)
    · rw [hvec_k, h_step, smul_smul, pow_succ]
      rfl

def schwartzSeminormBoxSum (l d : ℕ) (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) : ℝ :=
  ∑ l' ∈ Finset.range (l + 1), ∑ d' ∈ Finset.range (d + 1), SchwartzMap.seminorm ℝ l' d' φ

lemma schwartzSeminormBoxSum_nonneg (l d : ℕ) (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    0 ≤ schwartzSeminormBoxSum l d φ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _

lemma seminorm_le_schwartzSeminormBoxSum {l d l' d' : ℕ} (hl : l' ≤ l) (hd : d' ≤ d)
    (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ l' d' φ ≤ schwartzSeminormBoxSum l d φ := by
  unfold schwartzSeminormBoxSum
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ =>
      Finset.sum_nonneg fun _ _ => apply_nonneg _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hl)))
  exact Finset.single_le_sum (fun _ _ => apply_nonneg _ _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))

lemma schwartzSeminormBoxSum_mono {l₁ l₂ d₁ d₂ : ℕ} (hl : l₁ ≤ l₂) (hd : d₁ ≤ d₂)
    (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzSeminormBoxSum l₁ d₁ φ ≤ schwartzSeminormBoxSum l₂ d₂ φ := by
  unfold schwartzSeminormBoxSum
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hl))
    (fun _ _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) |>.trans ?_
  refine Finset.sum_le_sum fun _ _ => ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hd))
    fun _ _ _ => apply_nonneg _ _

lemma seminorm_schwartzChain_le (r l d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ),
      SchwartzMap.seminorm ℝ l d (schwartzChain r ψ) ≤
        C * ∏ i : Fin r, schwartzSeminormBoxSum l d (ψ i) := by
  induction r generalizing l d with
  | zero =>
    refine ⟨SchwartzMap.seminorm ℝ l d (momentumWavepacketSchwartz 0 0),
      apply_nonneg _ _, fun ψ => ?_⟩
    rw [Fin.prod_univ_zero, mul_one]
    rfl
  | succ k ih =>
    have h_ih0 : ∀ q : Fin (d + 1), ∃ C₀ : ℝ, 0 ≤ C₀ ∧
        ∀ ψ : Fin k → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ,
          SchwartzMap.seminorm ℝ 0 (d - q.val) (schwartzChain k ψ) ≤
            C₀ * ∏ i : Fin k, schwartzSeminormBoxSum 0 (d - q.val) (ψ i) :=
      fun q => ih 0 (d - q.val)
    have h_ihl : ∀ q : Fin (d + 1), ∃ Cl : ℝ, 0 ≤ Cl ∧
        ∀ ψ : Fin k → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ,
          SchwartzMap.seminorm ℝ l (d - q.val) (schwartzChain k ψ) ≤
            Cl * ∏ i : Fin k, schwartzSeminormBoxSum l (d - q.val) (ψ i) :=
      fun q => ih l (d - q.val)
    choose C₀ hC₀_nn hC₀_bd using h_ih0
    choose Cl hCl_nn hCl_bd using h_ihl
    let C : ℝ := ∑ q : Fin (d + 1), (d.choose q.val : ℝ) * (C₀ q + Cl q)
    have hC_nn : 0 ≤ C := Finset.sum_nonneg fun q _ =>
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hC₀_nn q) (hCl_nn q))
    refine ⟨C, hC_nn, fun ψ => ?_⟩
    dsimp [schwartzChain]
    refine (seminorm_schwartzPrepend_le k l d (ψ 0) (schwartzChain k (ψ ∘ Fin.succ))).trans ?_
    rw [← Fin.sum_univ_eq_sum_range, Fin.prod_univ_succ]
    let P : ℝ := ∏ i : Fin k, schwartzSeminormBoxSum l d (ψ i.succ)
    have hP_nn : 0 ≤ P := Finset.prod_nonneg fun _ _ => schwartzSeminormBoxSum_nonneg _ _ _
    have hB0_nn : 0 ≤ schwartzSeminormBoxSum l d (ψ 0) := schwartzSeminormBoxSum_nonneg _ _ _
    have h_sum_le :
        (∑ q : Fin (d + 1), (d.choose q.val : ℝ) *
          (SchwartzMap.seminorm ℝ l q.val (ψ 0) *
              SchwartzMap.seminorm ℝ 0 (d - q.val) (schwartzChain k (ψ ∘ Fin.succ)) +
            SchwartzMap.seminorm ℝ 0 q.val (ψ 0) *
              SchwartzMap.seminorm ℝ l (d - q.val) (schwartzChain k (ψ ∘ Fin.succ)))) ≤
        ∑ q : Fin (d + 1), ((d.choose q.val : ℝ) * (C₀ q + Cl q)) *
          (schwartzSeminormBoxSum l d (ψ 0) * P) := by
      refine Finset.sum_le_sum fun q _ => ?_
      have hq_le : q.val ≤ d := Nat.lt_succ_iff.mp q.isLt
      have h_psi_l := seminorm_le_schwartzSeminormBoxSum (l := l) (d := d) le_rfl hq_le (ψ 0)
      have h_psi_0 :=
        seminorm_le_schwartzSeminormBoxSum (l := l) (d := d) (Nat.zero_le l) hq_le (ψ 0)
      have h_p0 : (∏ i : Fin k, schwartzSeminormBoxSum 0 (d - q.val) (ψ i.succ)) ≤ P :=
        Finset.prod_le_prod (fun _ _ => schwartzSeminormBoxSum_nonneg _ _ _)
          fun i _ => schwartzSeminormBoxSum_mono (Nat.zero_le l) (Nat.sub_le d q.val) (ψ i.succ)
      have h_pl : (∏ i : Fin k, schwartzSeminormBoxSum l (d - q.val) (ψ i.succ)) ≤ P :=
        Finset.prod_le_prod (fun _ _ => schwartzSeminormBoxSum_nonneg _ _ _)
          fun i _ => schwartzSeminormBoxSum_mono le_rfl (Nat.sub_le d q.val) (ψ i.succ)
      have h_sc0 := (hC₀_bd q (ψ ∘ Fin.succ)).trans
        (mul_le_mul_of_nonneg_left h_p0 (hC₀_nn q))
      have h_scl := (hCl_bd q (ψ ∘ Fin.succ)).trans
        (mul_le_mul_of_nonneg_left h_pl (hCl_nn q))
      have ht1 := mul_le_mul h_psi_l h_sc0 (apply_nonneg _ _) hB0_nn
      have ht2 := mul_le_mul h_psi_0 h_scl (apply_nonneg _ _) hB0_nn
      have h_add : SchwartzMap.seminorm ℝ l q.val (ψ 0) *
            SchwartzMap.seminorm ℝ 0 (d - q.val) (schwartzChain k (ψ ∘ Fin.succ)) +
          SchwartzMap.seminorm ℝ 0 q.val (ψ 0) *
            SchwartzMap.seminorm ℝ l (d - q.val) (schwartzChain k (ψ ∘ Fin.succ)) ≤
          (C₀ q + Cl q) * (schwartzSeminormBoxSum l d (ψ 0) * P) := by
        linarith
      calc (d.choose q.val : ℝ) *
            (SchwartzMap.seminorm ℝ l q.val (ψ 0) *
                SchwartzMap.seminorm ℝ 0 (d - q.val) (schwartzChain k (ψ ∘ Fin.succ)) +
              SchwartzMap.seminorm ℝ 0 q.val (ψ 0) *
                SchwartzMap.seminorm ℝ l (d - q.val) (schwartzChain k (ψ ∘ Fin.succ)))
          ≤ (d.choose q.val : ℝ) * ((C₀ q + Cl q) * (schwartzSeminormBoxSum l d (ψ 0) * P)) :=
            mul_le_mul_of_nonneg_left h_add (Nat.cast_nonneg _)
        _ = _ := by ring
    exact h_sum_le.trans (le_of_eq (Finset.sum_mul _ _ _).symm)

lemma seminorm_schwartzConj_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l d : ℕ) (φ : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℝ l d (schwartzConj φ) ≤
      ‖Complex.conjCLE.toContinuousLinearMap‖ * SchwartzMap.seminorm ℝ l d φ := by
  let L : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  refine SchwartzMap.seminorm_le_bound ℝ l d (schwartzConj φ)
    (mul_nonneg (norm_nonneg L) (apply_nonneg _ _)) fun x => ?_
  have h_cd : ContDiffAt ℝ (⊤ : ℕ∞) (φ : E → ℂ) x := φ.smooth'.contDiffAt
  have h_fn : (schwartzConj φ : E → ℂ) = L ∘ (φ : E → ℂ) := rfl
  rw [h_fn, L.iteratedFDeriv_comp_left h_cd (WithTop.coe_le_coe.mpr le_top)]
  have h_op := L.norm_compContinuousMultilinearMap_le (iteratedFDeriv ℝ d (φ : E → ℂ) x)
  calc ‖x‖ ^ l * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ d (φ : E → ℂ) x)‖
      ≤ ‖x‖ ^ l * (‖L‖ * ‖iteratedFDeriv ℝ d (φ : E → ℂ) x‖) :=
        mul_le_mul_of_nonneg_left h_op (by positivity)
    _ = ‖L‖ * (‖x‖ ^ l * ‖iteratedFDeriv ℝ d (φ : E → ℂ) x‖) := by ring
    _ ≤ ‖L‖ * SchwartzMap.seminorm ℝ l d φ :=
        mul_le_mul_of_nonneg_left (φ.le_seminorm ℝ l d x) (norm_nonneg L)

lemma norm_wightmanSchwartzVec_le_seminorms
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (α : Fin r → ι) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ F : SchwartzMap (Fin r → Fin 4 → ℝ) ℂ,
        ‖wightmanSchwartzVec WData r α F‖ ≤ C * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 F := by
  have h_with := schwartz_withSeminorms ℝ (Fin r → Fin 4 → ℝ) ℂ
  let T := (wightmanSchwartzVec WData r α).toLinearMap.restrictScalars ℝ
  let q_sem : Seminorm ℝ (SchwartzMap (Fin r → Fin 4 → ℝ) ℂ) :=
    (normSeminorm ℝ (WightmanHilbert WData)).comp T
  have hq_cont : Continuous q_sem :=
    continuous_norm.comp (wightmanSchwartzVec WData r α).continuous
  obtain ⟨s, C₀, _, h_bd⟩ := Seminorm.bound_of_continuous h_with q_sem hq_cont
  refine ⟨s, (C₀ : ℝ), NNReal.coe_nonneg C₀, fun F => ?_⟩
  have h1 : ‖wightmanSchwartzVec WData r α F‖ ≤
      (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin r → Fin 4 → ℝ) ℂ)) F := by
    have h_le := h_bd F
    exact le_trans h_le (le_of_eq (NNReal.smul_def _ _))
  have h2 : (s.sup (schwartzSeminormFamily ℝ (Fin r → Fin 4 → ℝ) ℂ)) F ≤
      ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 F := by
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun p _ => apply_nonneg _ _)
      fun p hp => ?_
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact Finset.single_le_sum (fun p' _ => apply_nonneg (SchwartzMap.seminorm ℝ p'.1 p'.2) F) hp
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg C₀))

lemma seminorm_finset_sum_le {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l d : ℕ) (s : Finset κ) (φ : κ → SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℝ l d (∑ a ∈ s, φ a) ≤ ∑ a ∈ s, SchwartzMap.seminorm ℝ l d (φ a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (map_add_le_add (SchwartzMap.seminorm ℝ l d) _ _).trans (add_le_add le_rfl ih)

lemma seminorm_complex_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l d : ℕ) (c : ℂ) (φ : SchwartzMap E ℂ) :
    SchwartzMap.seminorm ℝ l d (c • φ) = ‖c‖ * SchwartzMap.seminorm ℝ l d φ :=
  map_smul_eq_mul (SchwartzMap.seminorm ℂ l d) c φ

def IndexedTestPolyGrowth (Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) : Prop :=
  ∀ (α : ι) (l d : ℕ), ∃ (deg : ℕ) (C : ℝ), 0 ≤ C ∧
    ∀ t : ℝ, SchwartzMap.seminorm ℝ l d (Ψ t α) ≤ C * (1 + |t|) ^ deg

def IndexedTestRapidDecay (Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) : Prop :=
  ∀ (α : ι) (l d N : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ t : ℝ, SchwartzMap.seminorm ℝ l d (Ψ t α) * (1 + |t|) ^ N ≤ C

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_of_rapidDecay
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) : IndexedTestPolyGrowth Ψ := by
  intro α l d
  obtain ⟨C, hC_nn, hC⟩ := h α l d 0
  refine ⟨0, C, hC_nn, fun t => ?_⟩
  simpa [pow_zero] using hC t

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_sub
    {Ψ₁ Ψ₂ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h₁ : IndexedTestPolyGrowth Ψ₁) (h₂ : IndexedTestPolyGrowth Ψ₂) :
    IndexedTestPolyGrowth (fun t α => Ψ₁ t α - Ψ₂ t α) := by
  intro α l d
  obtain ⟨K₁, C₁, hC₁_nn, hC₁⟩ := h₁ α l d
  obtain ⟨K₂, C₂, hC₂_nn, hC₂⟩ := h₂ α l d
  refine ⟨max K₁ K₂, C₁ + C₂, add_nonneg hC₁_nn hC₂_nn, fun t => ?_⟩
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have h_tri := map_sub_le_add (SchwartzMap.seminorm ℝ l d) (Ψ₁ t α) (Ψ₂ t α)
  have h_1 : SchwartzMap.seminorm ℝ l d (Ψ₁ t α) ≤ C₁ * (1 + |t|) ^ max K₁ K₂ :=
    (hC₁ t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (le_max_left K₁ K₂)) hC₁_nn)
  have h_2 : SchwartzMap.seminorm ℝ l d (Ψ₂ t α) ≤ C₂ * (1 + |t|) ^ max K₁ K₂ :=
    (hC₂ t).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (le_max_right K₁ K₂)) hC₂_nn)
  change SchwartzMap.seminorm ℝ l d (Ψ₁ t α - Ψ₂ t α) ≤ (C₁ + C₂) * (1 + |t|) ^ max K₁ K₂
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_neg
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t α => -Ψ t α) := by
  intro α l d
  obtain ⟨deg, C, hC_nn, hC⟩ := h α l d
  refine ⟨deg, C, hC_nn, fun t => ?_⟩
  rw [map_neg_eq_map]
  exact hC t

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestRapidDecay_neg
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t α => -Ψ t α) := by
  intro α l d N
  obtain ⟨C, hC_nn, hC⟩ := h α l d N
  refine ⟨C, hC_nn, fun t => ?_⟩
  rw [map_neg_eq_map]
  exact hC t

lemma indexedTestPolyGrowth_starIndexedTest
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t => starIndexedTest S (Ψ t)) := by
  intro β l d
  have h_each : ∀ α₀ : ι, ∃ (K_a : ℕ) (C_a : ℝ), 0 ≤ C_a ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ l d (Ψ t α₀) ≤ C_a * (1 + |t|) ^ K_a :=
    fun α₀ => h α₀ l d
  choose K_a C_a hCa_nn hCa_bd using h_each
  let K : ℕ := Finset.univ.sup K_a
  let C_L : ℝ := ‖Complex.conjCLE.toContinuousLinearMap‖
  let C : ℝ := ∑ α₀ : ι, ‖S.C α₀ β‖ * C_L * C_a α₀
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun α₀ _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hCa_nn α₀)
  refine ⟨K, C, hC_nn, fun t => ?_⟩
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  unfold starIndexedTest
  calc SchwartzMap.seminorm ℝ l d (∑ α₀ : ι, S.C α₀ β • schwartzConj (Ψ t α₀))
      ≤ ∑ α₀ : ι, SchwartzMap.seminorm ℝ l d (S.C α₀ β • schwartzConj (Ψ t α₀)) :=
        seminorm_finset_sum_le l d Finset.univ _
    _ = ∑ α₀ : ι, ‖S.C α₀ β‖ * SchwartzMap.seminorm ℝ l d (schwartzConj (Ψ t α₀)) := by
        refine Finset.sum_congr rfl fun α₀ _ => ?_
        exact seminorm_complex_smul_eq l d (S.C α₀ β) (schwartzConj (Ψ t α₀))
    _ ≤ ∑ α₀ : ι, ‖S.C α₀ β‖ * (C_L * SchwartzMap.seminorm ℝ l d (Ψ t α₀)) := by
        refine Finset.sum_le_sum fun α₀ _ => mul_le_mul_of_nonneg_left
          (seminorm_schwartzConj_le l d (Ψ t α₀)) (norm_nonneg _)
    _ ≤ ∑ α₀ : ι, (‖S.C α₀ β‖ * C_L * C_a α₀) * (1 + |t|) ^ K := by
        refine Finset.sum_le_sum fun α₀ _ => ?_
        have h1 : SchwartzMap.seminorm ℝ l d (Ψ t α₀) ≤ C_a α₀ * (1 + |t|) ^ K :=
          (hCa_bd α₀ t).trans
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ ht1 (Finset.le_sup (Finset.mem_univ α₀))) (hCa_nn α₀))
        have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (S.C α₀ β))
        calc ‖S.C α₀ β‖ * (C_L * SchwartzMap.seminorm ℝ l d (Ψ t α₀))
            = C_L * (‖S.C α₀ β‖ * SchwartzMap.seminorm ℝ l d (Ψ t α₀)) := by ring
          _ ≤ C_L * (‖S.C α₀ β‖ * (C_a α₀ * (1 + |t|) ^ K)) :=
              mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
          _ = (‖S.C α₀ β‖ * C_L * C_a α₀) * (1 + |t|) ^ K := by ring
    _ = C * (1 + |t|) ^ K := (Finset.sum_mul _ _ _).symm

lemma indexedTestRapidDecay_starIndexedTest
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t => starIndexedTest S (Ψ t)) := by
  intro β l d N
  have h_each : ∀ α₀ : ι, ∃ C_a : ℝ, 0 ≤ C_a ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ l d (Ψ t α₀) * (1 + |t|) ^ N ≤ C_a :=
    fun α₀ => h α₀ l d N
  choose C_a hCa_nn hCa_bd using h_each
  let C_L : ℝ := ‖Complex.conjCLE.toContinuousLinearMap‖
  let C : ℝ := ∑ α₀ : ι, ‖S.C α₀ β‖ * C_L * C_a α₀
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun α₀ _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hCa_nn α₀)
  refine ⟨C, hC_nn, fun t => ?_⟩
  unfold starIndexedTest
  have h_sm_le : SchwartzMap.seminorm ℝ l d (∑ α₀ : ι, S.C α₀ β • schwartzConj (Ψ t α₀)) ≤
      ∑ α₀ : ι, ‖S.C α₀ β‖ * (C_L * SchwartzMap.seminorm ℝ l d (Ψ t α₀)) := by
    calc SchwartzMap.seminorm ℝ l d (∑ α₀ : ι, S.C α₀ β • schwartzConj (Ψ t α₀))
        ≤ ∑ α₀ : ι, SchwartzMap.seminorm ℝ l d (S.C α₀ β • schwartzConj (Ψ t α₀)) :=
          seminorm_finset_sum_le l d Finset.univ _
      _ = ∑ α₀ : ι, ‖S.C α₀ β‖ * SchwartzMap.seminorm ℝ l d (schwartzConj (Ψ t α₀)) := by
          refine Finset.sum_congr rfl fun α₀ _ => ?_
          exact seminorm_complex_smul_eq l d (S.C α₀ β) (schwartzConj (Ψ t α₀))
      _ ≤ ∑ α₀ : ι, ‖S.C α₀ β‖ * (C_L * SchwartzMap.seminorm ℝ l d (Ψ t α₀)) :=
          Finset.sum_le_sum fun α₀ _ => mul_le_mul_of_nonneg_left
            (seminorm_schwartzConj_le l d (Ψ t α₀)) (norm_nonneg _)
  calc SchwartzMap.seminorm ℝ l d (∑ α₀ : ι, S.C α₀ β • schwartzConj (Ψ t α₀)) * (1 + |t|) ^ N
      ≤ (∑ α₀ : ι, ‖S.C α₀ β‖ * (C_L * SchwartzMap.seminorm ℝ l d (Ψ t α₀))) * (1 + |t|) ^ N :=
        mul_le_mul_of_nonneg_right h_sm_le (pow_nonneg (by positivity) N)
    _ = ∑ α₀ : ι, ‖S.C α₀ β‖ * C_L * (SchwartzMap.seminorm ℝ l d (Ψ t α₀) * (1 + |t|) ^ N) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun α₀ _ => by ring
    _ ≤ C := by
        refine Finset.sum_le_sum fun α₀ _ => mul_le_mul_of_nonneg_left (hCa_bd α₀ t)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))

def haagRuelleDerivCoreIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun α => haagRuelleDerivCoreTestFn m M D.hm D.hM (dualModeWavepacket D s α f) r hr t

def haagRuelleDerivTailIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun α => haagRuelleDerivTailTestFn m M D.hm D.hM (dualModeWavepacket D s α f) r hr t

def haagRuelleAdjCoreIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  starIndexedTest S (haagRuelleCoreIndexedTest D s f r hr t)

def haagRuelleAdjTailIndexedTest {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  starIndexedTest S (haagRuelleTailIndexedTest D s f r hr t)

lemma haagRuelleIndexedTest_sub_core
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) (α : ι) :
    haagRuelleIndexedTest D s f t α - haagRuelleCoreIndexedTest D s f r hr t α =
      haagRuelleTailIndexedTest D s f r hr t α := by
  dsimp [haagRuelleIndexedTest, haagRuelleCoreIndexedTest, haagRuelleTailIndexedTest]
  rw [haagRuelleTestFn_eq_core_add_tail m M D.hm D.hM (dualModeWavepacket D s α f) r hr t]
  abel

lemma haagRuelleDerivIndexedTest_sub_core
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) (α : ι) :
    haagRuelleDerivIndexedTest D s f t α - haagRuelleDerivCoreIndexedTest D s f r hr t α =
      haagRuelleDerivTailIndexedTest D s f r hr t α := by
  dsimp [haagRuelleDerivIndexedTest, haagRuelleDerivCoreIndexedTest,
    haagRuelleDerivTailIndexedTest]
  rw [haagRuelleDerivTestFn_eq_core_add_tail m M D.hm D.hM (dualModeWavepacket D s α f) r hr t]
  abel

lemma haagRuelleAdjIndexedTest_sub_core
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ) (α : ι) :
    haagRuelleAdjIndexedTest D s f t α - haagRuelleAdjCoreIndexedTest D s f r hr t α =
      haagRuelleAdjTailIndexedTest D s f r hr t α := by
  dsimp [haagRuelleAdjIndexedTest, haagRuelleAdjCoreIndexedTest,
    haagRuelleAdjTailIndexedTest, starIndexedTest]
  ext x
  rw [_root_.sub_apply, schwartzMap_sum_apply, schwartzMap_sum_apply, schwartzMap_sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α₀ _ => ?_
  rw [_root_.smul_apply, _root_.smul_apply, _root_.smul_apply, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, schwartzConj_apply, schwartzConj_apply, schwartzConj_apply,
    ← haagRuelleIndexedTest_sub_core D s f r hr t α₀, _root_.sub_apply, star_sub, mul_sub]

lemma indexedTestPolyGrowth_haagRuelle
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    IndexedTestPolyGrowth (fun t => haagRuelleIndexedTest D s f t) := fun α l d => by
  obtain ⟨C, K, hC_nn, hC⟩ :=
    schwartzSeminorm_haagRuelleTestFn_poly_growth m M D.hm D.hM (dualModeWavepacket D s α f) l d
  exact ⟨K, C, hC_nn, hC⟩

lemma indexedTestPolyGrowth_haagRuelleDeriv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    IndexedTestPolyGrowth (fun t => haagRuelleDerivIndexedTest D s f t) := fun α l d => by
  obtain ⟨C, K, hC_nn, hC⟩ :=
    schwartzSeminorm_haagRuelleDerivTestFn_poly_growth m M D.hm D.hM
      (dualModeWavepacket D s α f) l d
  exact ⟨K, C, hC_nn, hC⟩

lemma indexedTestPolyGrowth_haagRuelleCore
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    IndexedTestPolyGrowth (fun t => haagRuelleCoreIndexedTest D s f r hr t) := fun α l d => by
  obtain ⟨C, K, hC_nn, hC⟩ :=
    schwartzSeminorm_haagRuelleCoreTestFn_poly_growth m M D.hm D.hM
      (dualModeWavepacket D s α f) r hr l d
  exact ⟨K, C, hC_nn, hC⟩

lemma indexedTestPolyGrowth_haagRuelleDerivCore
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    IndexedTestPolyGrowth (fun t => haagRuelleDerivCoreIndexedTest D s f r hr t) :=
  fun α l d => by
    obtain ⟨C, K, hC_nn, hC⟩ :=
      schwartzSeminorm_haagRuelleDerivCoreTestFn_poly_growth m M D.hm D.hM
        (dualModeWavepacket D s α f) r hr l d
    exact ⟨K, C, hC_nn, hC⟩

lemma indexedTestPolyGrowth_haagRuelleAdj
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    IndexedTestPolyGrowth (fun t => haagRuelleAdjIndexedTest D s f t) :=
  indexedTestPolyGrowth_starIndexedTest S (indexedTestPolyGrowth_haagRuelle D s f)

lemma indexedTestPolyGrowth_haagRuelleAdjCore
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    IndexedTestPolyGrowth (fun t => haagRuelleAdjCoreIndexedTest D s f r hr t) :=
  indexedTestPolyGrowth_starIndexedTest S (indexedTestPolyGrowth_haagRuelleCore D s f r hr)

lemma indexedTestRapidDecay_haagRuelleTail
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    IndexedTestRapidDecay (fun t => haagRuelleTailIndexedTest D s f r hr t) := fun α l d N =>
  schwartzSeminorm_haagRuelleTailTestFn_rapid_decay m M D.hm D.hM
    (dualModeWavepacket D s α f) r hr l d N

lemma indexedTestRapidDecay_haagRuelleDerivTail
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    IndexedTestRapidDecay (fun t => haagRuelleDerivTailIndexedTest D s f r hr t) :=
  fun α l d N =>
    schwartzSeminorm_haagRuelleDerivTailTestFn_rapid_decay m M D.hm D.hM
      (dualModeWavepacket D s α f) r hr l d N

lemma indexedTestRapidDecay_haagRuelleAdjTail
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) :
    IndexedTestRapidDecay (fun t => haagRuelleAdjTailIndexedTest D s f r hr t) :=
  indexedTestRapidDecay_starIndexedTest S (indexedTestRapidDecay_haagRuelleTail D s f r hr)

omit [Fintype ι] [DecidableEq ι] in
lemma boxSum_poly_growth {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) (α : ι) (l d : ℕ) :
    ∃ (deg : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ t : ℝ, schwartzSeminormBoxSum l d (Ψ t α) ≤ C * (1 + |t|) ^ deg := by
  have h_pt : ∀ p : Fin (l + 1) × Fin (d + 1), ∃ (K_p : ℕ) (C_p : ℝ), 0 ≤ C_p ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ p.1.val p.2.val (Ψ t α) ≤ C_p * (1 + |t|) ^ K_p :=
    fun p => h α p.1.val p.2.val
  choose K_p C_p hCp_nn hCp_bd using h_pt
  let deg : ℕ := Finset.univ.sup K_p
  let C : ℝ := ∑ p : Fin (l + 1) × Fin (d + 1), C_p p
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun p _ => hCp_nn p
  refine ⟨deg, C, hC_nn, fun t => ?_⟩
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  unfold schwartzSeminormBoxSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [← Fintype.sum_prod_type']
  calc (∑ p : Fin (l + 1) × Fin (d + 1), SchwartzMap.seminorm ℝ p.1.val p.2.val (Ψ t α))
      ≤ ∑ p : Fin (l + 1) × Fin (d + 1), C_p p * (1 + |t|) ^ deg := by
        refine Finset.sum_le_sum fun p _ => (hCp_bd p t).trans ?_
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ ht1 (Finset.le_sup (Finset.mem_univ p))) (hCp_nn p)
    _ = C * (1 + |t|) ^ deg := (Finset.sum_mul _ _ _).symm

omit [Fintype ι] [DecidableEq ι] in
lemma boxSum_rapid_decay {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) (α : ι) (l d N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, schwartzSeminormBoxSum l d (Ψ t α) * (1 + |t|) ^ N ≤ C := by
  have h_pt : ∀ p : Fin (l + 1) × Fin (d + 1), ∃ C_p : ℝ, 0 ≤ C_p ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ p.1.val p.2.val (Ψ t α) * (1 + |t|) ^ N ≤ C_p :=
    fun p => h α p.1.val p.2.val N
  choose C_p hCp_nn hCp_bd using h_pt
  let C : ℝ := ∑ p : Fin (l + 1) × Fin (d + 1), C_p p
  refine ⟨C, Finset.sum_nonneg fun p _ => hCp_nn p, fun t => ?_⟩
  unfold schwartzSeminormBoxSum
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [← Fintype.sum_prod_type', Finset.sum_mul]
  exact Finset.sum_le_sum fun p _ => hCp_bd p t

lemma norm_indexedChain_poly_growth
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ)
    (Ψ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hpoly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i)) :
    ∃ (deg : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ t : ℝ, ‖wightmanIndexedVec WData r (indexedChain ι r (fun i => Ψ i t))‖ ≤
        C * (1 + |t|) ^ deg := by
  have h_each : ∀ (γ : Fin r → ι), ∃ (deg_g : ℕ) (C_g : ℝ), 0 ≤ C_g ∧
      ∀ t : ℝ, ‖wightmanSchwartzVec WData r γ
          (indexedChain ι r (fun i => Ψ i t) γ)‖ ≤ C_g * (1 + |t|) ^ deg_g := by
    intro γ
    obtain ⟨s, C₀, hC0_nn, h_bd⟩ := norm_wightmanSchwartzVec_le_seminorms WData r γ
    have h_p : ∀ p : s, ∃ (deg_p : ℕ) (C_p : ℝ), 0 ≤ C_p ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ p.1.1 p.1.2 (schwartzChain r (fun i => Ψ i t (γ i))) ≤
          C_p * (1 + |t|) ^ deg_p := by
      rintro ⟨⟨l, d⟩, _⟩
      obtain ⟨C_sc, hCsc_nn, hCsc⟩ := seminorm_schwartzChain_le r l d
      have h_fac : ∀ i : Fin r, ∃ (deg_i : ℕ) (C_i : ℝ), 0 ≤ C_i ∧ ∀ t : ℝ,
          schwartzSeminormBoxSum l d (Ψ i t (γ i)) ≤ C_i * (1 + |t|) ^ deg_i :=
        fun i => boxSum_poly_growth (hpoly i) (γ i) l d
      choose deg_i C_i hCi_nn hCi_bd using h_fac
      refine ⟨∑ i : Fin r, deg_i i, C_sc * ∏ i : Fin r, C_i i,
        mul_nonneg hCsc_nn (Finset.prod_nonneg fun i _ => hCi_nn i), fun t => ?_⟩
      refine (hCsc (fun i => Ψ i t (γ i))).trans ?_
      have h_prod : (∏ i : Fin r, schwartzSeminormBoxSum l d (Ψ i t (γ i))) ≤
          (∏ i : Fin r, C_i i) * (1 + |t|) ^ (∑ i : Fin r, deg_i i) := by
        calc (∏ i : Fin r, schwartzSeminormBoxSum l d (Ψ i t (γ i)))
            ≤ ∏ i : Fin r, (C_i i * (1 + |t|) ^ deg_i i) :=
              Finset.prod_le_prod (fun i _ => schwartzSeminormBoxSum_nonneg _ _ _)
                fun i _ => hCi_bd i t
          _ = (∏ i : Fin r, C_i i) * ∏ i : Fin r, (1 + |t|) ^ deg_i i := Finset.prod_mul_distrib
          _ = (∏ i : Fin r, C_i i) * (1 + |t|) ^ (∑ i : Fin r, deg_i i) := by
              rw [Finset.prod_pow_eq_pow_sum]
      calc C_sc * ∏ i : Fin r, schwartzSeminormBoxSum l d (Ψ i t (γ i))
          ≤ C_sc * ((∏ i : Fin r, C_i i) * (1 + |t|) ^ (∑ i : Fin r, deg_i i)) :=
            mul_le_mul_of_nonneg_left h_prod hCsc_nn
        _ = (C_sc * ∏ i : Fin r, C_i i) * (1 + |t|) ^ (∑ i : Fin r, deg_i i) := by ring
    choose deg_p C_p hCp_nn hCp_bd using h_p
    let deg_g : ℕ := Finset.univ.sup deg_p
    let C_g : ℝ := C₀ * ∑ p : s, C_p p
    refine ⟨deg_g, C_g, mul_nonneg hC0_nn (Finset.sum_nonneg fun p _ => hCp_nn p), fun t => ?_⟩
    have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    rw [indexedChain_apply]
    refine (h_bd _).trans ?_
    have h_s : (∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2
          (schwartzChain r (fun i => Ψ i t (γ i)))) ≤
        (∑ p : s, C_p p) * (1 + |t|) ^ deg_g := by
      rw [← Finset.sum_attach s fun p => SchwartzMap.seminorm ℝ p.1 p.2
        (schwartzChain r (fun i => Ψ i t (γ i))), Finset.sum_mul]
      refine Finset.sum_le_sum fun p _ => (hCp_bd p t).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ ht1 (Finset.le_sup (Finset.mem_univ p))) (hCp_nn p)
    calc C₀ * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2
          (schwartzChain r (fun i => Ψ i t (γ i)))
        ≤ C₀ * ((∑ p : s, C_p p) * (1 + |t|) ^ deg_g) := mul_le_mul_of_nonneg_left h_s hC0_nn
      _ = C_g * (1 + |t|) ^ deg_g := by ring
  choose deg_g C_g hCg_nn hCg_bd using h_each
  let deg : ℕ := Finset.univ.sup deg_g
  let C : ℝ := ∑ γ : Fin r → ι, C_g γ
  refine ⟨deg, C, Finset.sum_nonneg fun γ _ => hCg_nn γ, fun t => ?_⟩
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  unfold wightmanIndexedVec
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun γ _ => (hCg_bd γ t).trans ?_
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht1 (Finset.le_sup (Finset.mem_univ γ))) (hCg_nn γ)

lemma norm_indexedChain_rapid_decay_of_slot
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ) (j₀ : Fin r)
    (Ψ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hpoly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i))
    (hdec : IndexedTestRapidDecay (Ψ j₀)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖wightmanIndexedVec WData r (indexedChain ι r (fun i => Ψ i t))‖ *
        (1 + |t|) ^ N ≤ C := by
  have h_each : ∀ (γ : Fin r → ι), ∃ C_g : ℝ, 0 ≤ C_g ∧
      ∀ t : ℝ, ‖wightmanSchwartzVec WData r γ
          (indexedChain ι r (fun i => Ψ i t) γ)‖ * (1 + |t|) ^ N ≤ C_g := by
    intro γ
    obtain ⟨s, C₀, hC0_nn, h_bd⟩ := norm_wightmanSchwartzVec_le_seminorms WData r γ
    have h_p : ∀ p : s, ∃ C_p : ℝ, 0 ≤ C_p ∧ ∀ t : ℝ,
        SchwartzMap.seminorm ℝ p.1.1 p.1.2 (schwartzChain r (fun i => Ψ i t (γ i))) *
          (1 + |t|) ^ N ≤ C_p := by
      rintro ⟨⟨l, d⟩, _⟩
      obtain ⟨C_sc, hCsc_nn, hCsc⟩ := seminorm_schwartzChain_le r l d
      have h_fac : ∀ i : Fin r, ∃ (deg_i : ℕ) (C_i : ℝ), 0 ≤ C_i ∧ ∀ t : ℝ,
          schwartzSeminormBoxSum l d (Ψ i t (γ i)) ≤ C_i * (1 + |t|) ^ deg_i :=
        fun i => boxSum_poly_growth (hpoly i) (γ i) l d
      choose deg_i C_i hCi_nn hCi_bd using h_fac
      let K_rest : ℕ := ∑ i ∈ Finset.univ.erase j₀, deg_i i
      let M_rest : ℝ := ∏ i ∈ Finset.univ.erase j₀, C_i i
      have hM_nn : 0 ≤ M_rest := Finset.prod_nonneg fun i _ => hCi_nn i
      obtain ⟨B_j0, hBj0_nn, hBj0⟩ := boxSum_rapid_decay hdec (γ j₀) l d (N + K_rest)
      refine ⟨C_sc * M_rest * B_j0, mul_nonneg (mul_nonneg hCsc_nn hM_nn) hBj0_nn, fun t => ?_⟩
      have h_split_prod :
          (∏ i : Fin r, schwartzSeminormBoxSum l d (Ψ i t (γ i))) =
            schwartzSeminormBoxSum l d (Ψ j₀ t (γ j₀)) *
              ∏ i ∈ Finset.univ.erase j₀, schwartzSeminormBoxSum l d (Ψ i t (γ i)) :=
        (Finset.mul_prod_erase Finset.univ
          (fun i => schwartzSeminormBoxSum l d (Ψ i t (γ i))) (Finset.mem_univ j₀)).symm
      have h_rest_le :
          (∏ i ∈ Finset.univ.erase j₀, schwartzSeminormBoxSum l d (Ψ i t (γ i))) ≤
            M_rest * (1 + |t|) ^ K_rest := by
        calc (∏ i ∈ Finset.univ.erase j₀, schwartzSeminormBoxSum l d (Ψ i t (γ i)))
            ≤ ∏ i ∈ Finset.univ.erase j₀, (C_i i * (1 + |t|) ^ deg_i i) :=
              Finset.prod_le_prod (fun i _ => schwartzSeminormBoxSum_nonneg _ _ _)
                fun i _ => hCi_bd i t
          _ = M_rest * ∏ i ∈ Finset.univ.erase j₀, (1 + |t|) ^ deg_i i := Finset.prod_mul_distrib
          _ = M_rest * (1 + |t|) ^ K_rest := by rw [Finset.prod_pow_eq_pow_sum]
      have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
      have h_sc := hCsc (fun i => Ψ i t (γ i))
      have h_box := schwartzSeminormBoxSum_nonneg l d (Ψ j₀ t (γ j₀))
      calc SchwartzMap.seminorm ℝ l d (schwartzChain r (fun i => Ψ i t (γ i))) * (1 + |t|) ^ N
          ≤ (C_sc * ∏ i : Fin r, schwartzSeminormBoxSum l d (Ψ i t (γ i))) * (1 + |t|) ^ N :=
            mul_le_mul_of_nonneg_right h_sc ht_nn
        _ = C_sc * ((schwartzSeminormBoxSum l d (Ψ j₀ t (γ j₀)) *
              ∏ i ∈ Finset.univ.erase j₀, schwartzSeminormBoxSum l d (Ψ i t (γ i))) *
              (1 + |t|) ^ N) := by rw [h_split_prod]; ring
        _ ≤ C_sc * ((schwartzSeminormBoxSum l d (Ψ j₀ t (γ j₀)) *
              (M_rest * (1 + |t|) ^ K_rest)) * (1 + |t|) ^ N) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_rest_le h_box) ht_nn) hCsc_nn
        _ = C_sc * M_rest * (schwartzSeminormBoxSum l d (Ψ j₀ t (γ j₀)) *
              (1 + |t|) ^ (N + K_rest)) := by rw [pow_add]; ring
        _ ≤ C_sc * M_rest * B_j0 :=
            mul_le_mul_of_nonneg_left (hBj0 t) (mul_nonneg hCsc_nn hM_nn)
    choose C_p hCp_nn hCp_bd using h_p
    refine ⟨C₀ * ∑ p : s, C_p p, mul_nonneg hC0_nn (Finset.sum_nonneg fun p _ => hCp_nn p),
      fun t => ?_⟩
    have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
    rw [indexedChain_apply]
    calc ‖wightmanSchwartzVec WData r γ (schwartzChain r (fun i => Ψ i t (γ i)))‖ * (1 + |t|) ^ N
        ≤ (C₀ * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2
            (schwartzChain r (fun i => Ψ i t (γ i)))) * (1 + |t|) ^ N :=
          mul_le_mul_of_nonneg_right (h_bd _) ht_nn
      _ = C₀ * ((∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2
            (schwartzChain r (fun i => Ψ i t (γ i)))) * (1 + |t|) ^ N) := by
          rw [mul_assoc]
      _ = C₀ * ∑ p : s, SchwartzMap.seminorm ℝ p.1.1 p.1.2
            (schwartzChain r (fun i => Ψ i t (γ i))) * (1 + |t|) ^ N := by
          congr 1
          rw [Finset.sum_mul, Finset.univ_eq_attach]
          exact (Finset.sum_attach s fun p => SchwartzMap.seminorm ℝ p.1 p.2
            (schwartzChain r (fun i => Ψ i t (γ i))) * (1 + |t|) ^ N).symm
      _ ≤ C₀ * ∑ p : s, C_p p :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hCp_bd p t) hC0_nn
  choose C_g hCg_nn hCg_bd using h_each
  refine ⟨∑ γ : Fin r → ι, C_g γ, Finset.sum_nonneg fun γ _ => hCg_nn γ, fun t => ?_⟩
  have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
  unfold wightmanIndexedVec
  calc ‖∑ γ : Fin r → ι, wightmanSchwartzVec WData r γ
          (indexedChain ι r (fun i => Ψ i t) γ)‖ * (1 + |t|) ^ N
      ≤ (∑ γ : Fin r → ι, ‖wightmanSchwartzVec WData r γ
          (indexedChain ι r (fun i => Ψ i t) γ)‖) * (1 + |t|) ^ N :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht_nn
    _ = ∑ γ : Fin r → ι, ‖wightmanSchwartzVec WData r γ
          (indexedChain ι r (fun i => Ψ i t) γ)‖ * (1 + |t|) ^ N := Finset.sum_mul _ _ _
    _ ≤ ∑ γ : Fin r → ι, C_g γ := Finset.sum_le_sum fun γ _ => hCg_bd γ t

lemma norm_indexedChain_sub_rapid_decay
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ)
    (Ψ Φ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i))
    (hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ i))
    (hdiff_dec : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Ψ i t α - Φ i t α)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ,
        ‖wightmanIndexedVec WData r (indexedChain ι r (fun i => Ψ i t)) -
          wightmanIndexedVec WData r (indexedChain ι r (fun i => Φ i t))‖ *
          (1 + |t|) ^ N ≤ C := by
  let hyb : ℕ → Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun m i => if i.val < m then Φ i else Ψ i
  have h_hyb_poly : ∀ (m : ℕ) (i : Fin r), IndexedTestPolyGrowth (hyb m i) := fun m i => by
    dsimp [hyb]
    split_ifs
    · exact hΦ_poly i
    · exact hΨ_poly i
  have h_step : ∀ m : Fin r, ∃ C_m : ℝ, 0 ≤ C_m ∧ ∀ t : ℝ,
      ‖wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb m.val i t)) -
        wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb (m.val + 1) i t))‖ *
        (1 + |t|) ^ N ≤ C_m := by
    intro m
    let Θ_t : ℝ → Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun _ => hyb m.val
    let Θ_arg : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
      Function.update (hyb m.val) m (fun t α => Ψ m t α - Φ m t α)
    have h_eq : ∀ t : ℝ,
        wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb m.val i t)) -
          wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb (m.val + 1) i t)) =
        wightmanIndexedVec WData r (indexedChain ι r (fun i => Θ_arg i t)) := by
      intro t
      have h_lhs_upd : (fun i => hyb m.val i t) =
          Function.update (fun i => hyb m.val i t) m (Ψ m t) := by
        ext i α x
        by_cases hi : i = m
        · subst hi
          simp [hyb]
        · simp [Function.update_of_ne hi]
      have h_rhs_upd : (fun i => hyb (m.val + 1) i t) =
          Function.update (fun i => hyb m.val i t) m (Φ m t) := by
        ext i α x
        by_cases hi : i = m
        · subst hi
          simp [hyb]
        · have hne : i.val ≠ m.val := fun h => hi (Fin.ext h)
          have hiff : i.val < m.val + 1 ↔ i.val < m.val := by omega
          simp [hyb, hiff, Function.update_of_ne hi]
      let base_m : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i => hyb m.val i t
      have h_arg_upd : (fun i => Θ_arg i t) =
          Function.update base_m m (Ψ m t - Φ m t) := by
        ext i α x
        by_cases hi : i = m
        · subst hi
          simp [Θ_arg, Function.update_self]
        · simp [Θ_arg, base_m, Function.update_of_ne hi]
      have h_lhs_m : (fun i => hyb m.val i t) = Function.update base_m m (Ψ m t) := h_lhs_upd
      have h_rhs_m : (fun i => hyb (m.val + 1) i t) = Function.update base_m m (Φ m t) := h_rhs_upd
      rw [h_arg_upd, wightmanIndexedVec_indexedChain_update_sub WData r m base_m (Ψ m t) (Φ m t),
        ← h_lhs_m, ← h_rhs_m]
    have h_arg_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Θ_arg i) := fun i => by
      by_cases hi : i = m
      · subst hi
        simpa [Θ_arg] using indexedTestPolyGrowth_sub (hΨ_poly i) (hΦ_poly i)
      · simpa [Θ_arg, Function.update_of_ne hi] using h_hyb_poly m.val i
    have h_arg_dec : IndexedTestRapidDecay (Θ_arg m) := by
      simpa [Θ_arg] using hdiff_dec m
    obtain ⟨C_m, hCm_nn, hCm⟩ := norm_indexedChain_rapid_decay_of_slot WData r m Θ_arg
      h_arg_poly h_arg_dec N
    exact ⟨C_m, hCm_nn, fun t => by rw [h_eq t]; exact hCm t⟩
  choose C_m hCm_nn hCm_bd using h_step
  refine ⟨∑ m : Fin r, C_m m, Finset.sum_nonneg fun m _ => hCm_nn m, fun t => ?_⟩
  have h0 : (fun i => hyb 0 i t) = fun i => Ψ i t := by
    ext i α x
    simp [hyb]
  have hr : (fun i => hyb r i t) = fun i => Φ i t := by
    ext i α x
    simp [hyb, i.isLt]
  have h_tel :
      wightmanIndexedVec WData r (indexedChain ι r (fun i => Ψ i t)) -
        wightmanIndexedVec WData r (indexedChain ι r (fun i => Φ i t)) =
      ∑ m ∈ Finset.range r,
        (wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb m i t)) -
          wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb (m + 1) i t))) := by
    rw [Finset.sum_range_sub']
    rw [h0, hr]
  have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
  rw [h_tel]
  calc ‖∑ m ∈ Finset.range r,
          (wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb m i t)) -
            wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb (m + 1) i t)))‖ *
        (1 + |t|) ^ N
      ≤ (∑ m ∈ Finset.range r,
          ‖wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb m i t)) -
            wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb (m + 1) i t))‖) *
          (1 + |t|) ^ N := mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht_nn
    _ = ∑ m : Fin r,
          ‖wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb m.val i t)) -
            wightmanIndexedVec WData r (indexedChain ι r (fun i => hyb (m.val + 1) i t))‖ *
          (1 + |t|) ^ N := by rw [← Fin.sum_univ_eq_sum_range, Finset.sum_mul]
    _ ≤ ∑ m : Fin r, C_m m := Finset.sum_le_sum fun m _ => hCm_bd m t

lemma tendsto_schwartzPrepend {k : ℕ} {l : Filter ℝ}
    {A : ℝ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ} {A₀ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    {B : ℝ → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ} {B₀ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ}
    (hA : Tendsto A l (𝓝 A₀)) (hB : Tendsto B l (𝓝 B₀)) :
    Tendsto (fun h : ℝ => schwartzPrepend k (A h) (B h)) l (𝓝 (schwartzPrepend k A₀ B₀)) := by
  have h_sub : Tendsto (fun h : ℝ => schwartzPrepend k (A h) (B h) - schwartzPrepend k A₀ B₀)
      l (𝓝 0) := by
    rw [(schwartz_withSeminorms ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0]
    rintro ⟨l₀, d₀⟩ ε hε
    have h_split : ∀ h : ℝ,
        schwartzPrepend k (A h) (B h) - schwartzPrepend k A₀ B₀ =
          schwartzPrepend k (A h - A₀) (B h) + schwartzPrepend k A₀ (B h - B₀) := fun h => by
      rw [schwartzPrepend_sub_left, schwartzPrepend_sub_right]
      abel
    have h_with1 := schwartz_withSeminorms ℝ (Fin 1 → Fin 4 → ℝ) ℂ
    have h_withk := schwartz_withSeminorms ℝ (Fin k → Fin 4 → ℝ) ℂ
    have hB_ev : ∀ᶠ h in l, ∀ q ∈ Finset.range (d₀ + 1),
        SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h) ≤
          SchwartzMap.seminorm ℝ 0 (d₀ - q) B₀ + 1 ∧
        SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h) ≤
          SchwartzMap.seminorm ℝ l₀ (d₀ - q) B₀ + 1 := by
      have h_each : ∀ q : Fin (d₀ + 1), ∀ᶠ h in l,
          SchwartzMap.seminorm ℝ 0 (d₀ - q.val) (B h) ≤
            SchwartzMap.seminorm ℝ 0 (d₀ - q.val) B₀ + 1 ∧
          SchwartzMap.seminorm ℝ l₀ (d₀ - q.val) (B h) ≤
            SchwartzMap.seminorm ℝ l₀ (d₀ - q.val) B₀ + 1 := fun q => by
        have ht1 := ((h_withk.continuous_seminorm (0, d₀ - q.val)).tendsto B₀).comp hB
        have ht2 := ((h_withk.continuous_seminorm (l₀, d₀ - q.val)).tendsto B₀).comp hB
        rw [SchwartzMap.schwartzSeminormFamily_apply] at ht1 ht2
        exact (ht1.eventually_le_const (lt_add_one _)).and
          (ht2.eventually_le_const (lt_add_one _))
      rw [← Filter.eventually_all] at h_each
      refine h_each.mono fun h hh q hq => hh ⟨q, Finset.mem_range.mp hq⟩
    let M_B : ℝ := (∑ q ∈ Finset.range (d₀ + 1), (d₀.choose q : ℝ) *
      (SchwartzMap.seminorm ℝ 0 (d₀ - q) B₀ + SchwartzMap.seminorm ℝ l₀ (d₀ - q) B₀ + 2)) + 1
    have hMB_pos : 0 < M_B := by
      have h_nn : 0 ≤ ∑ q ∈ Finset.range (d₀ + 1), (d₀.choose q : ℝ) *
          (SchwartzMap.seminorm ℝ 0 (d₀ - q) B₀ + SchwartzMap.seminorm ℝ l₀ (d₀ - q) B₀ + 2) :=
        Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _)
          (by linarith [apply_nonneg (SchwartzMap.seminorm ℝ 0 (d₀ - q)) B₀,
            apply_nonneg (SchwartzMap.seminorm ℝ l₀ (d₀ - q)) B₀])
      dsimp [M_B]
      linarith
    let M_A : ℝ := (∑ q ∈ Finset.range (d₀ + 1), (d₀.choose q : ℝ) *
      (SchwartzMap.seminorm ℝ l₀ q A₀ + SchwartzMap.seminorm ℝ 0 q A₀)) + 1
    have hMA_pos : 0 < M_A := by
      have h_nn : 0 ≤ ∑ q ∈ Finset.range (d₀ + 1), (d₀.choose q : ℝ) *
          (SchwartzMap.seminorm ℝ l₀ q A₀ + SchwartzMap.seminorm ℝ 0 q A₀) :=
        Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _)
          (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      dsimp [M_A]
      linarith
    let δA : ℝ := ε / (4 * M_B)
    let δB : ℝ := ε / (4 * M_A)
    have hδA : 0 < δA := by positivity
    have hδB : 0 < δB := by positivity
    have hA_ev : ∀ᶠ h in l, ∀ q ∈ Finset.range (d₀ + 1),
        SchwartzMap.seminorm ℝ l₀ q (A h - A₀) < δA ∧
        SchwartzMap.seminorm ℝ 0 q (A h - A₀) < δA := by
      have h_each : ∀ q : Fin (d₀ + 1), ∀ᶠ h in l,
          SchwartzMap.seminorm ℝ l₀ q.val (A h - A₀) < δA ∧
          SchwartzMap.seminorm ℝ 0 q.val (A h - A₀) < δA := fun q => by
        have hA0 : Tendsto (fun h => A h - A₀) l (𝓝 0) := by simpa using hA.sub_const A₀
        have ht1 := ((h_with1.continuous_seminorm (l₀, q.val)).tendsto 0).comp hA0
        have ht2 := ((h_with1.continuous_seminorm (0, q.val)).tendsto 0).comp hA0
        rw [map_zero] at ht1 ht2
        exact (ht1.eventually_lt_const hδA).and (ht2.eventually_lt_const hδA)
      rw [← Filter.eventually_all] at h_each
      refine h_each.mono fun h hh q hq => hh ⟨q, Finset.mem_range.mp hq⟩
    have hB_sub_ev : ∀ᶠ h in l, ∀ q ∈ Finset.range (d₀ + 1),
        SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h - B₀) < δB ∧
        SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h - B₀) < δB := by
      have h_each : ∀ q : Fin (d₀ + 1), ∀ᶠ h in l,
          SchwartzMap.seminorm ℝ 0 (d₀ - q.val) (B h - B₀) < δB ∧
          SchwartzMap.seminorm ℝ l₀ (d₀ - q.val) (B h - B₀) < δB := fun q => by
        have hB0 : Tendsto (fun h => B h - B₀) l (𝓝 0) := by simpa using hB.sub_const B₀
        have ht1 := ((h_withk.continuous_seminorm (0, d₀ - q.val)).tendsto 0).comp hB0
        have ht2 := ((h_withk.continuous_seminorm (l₀, d₀ - q.val)).tendsto 0).comp hB0
        rw [map_zero] at ht1 ht2
        exact (ht1.eventually_lt_const hδB).and (ht2.eventually_lt_const hδB)
      rw [← Filter.eventually_all] at h_each
      refine h_each.mono fun h hh q hq => hh ⟨q, Finset.mem_range.mp hq⟩
    filter_upwards [hB_ev, hA_ev, hB_sub_ev] with h hBh hAh hBsh
    rw [SchwartzMap.schwartzSeminormFamily_apply, h_split h]
    have h_tri := map_add_le_add (SchwartzMap.seminorm ℝ l₀ d₀)
      (schwartzPrepend k (A h - A₀) (B h)) (schwartzPrepend k A₀ (B h - B₀))
    have h_t1 : SchwartzMap.seminorm ℝ l₀ d₀ (schwartzPrepend k (A h - A₀) (B h)) ≤
        δA * M_B := by
      refine (seminorm_schwartzPrepend_le k l₀ d₀ (A h - A₀) (B h)).trans ?_
      have h_sum_le :
          (∑ q ∈ Finset.range (d₀ + 1), (d₀.choose q : ℝ) *
            (SchwartzMap.seminorm ℝ l₀ q (A h - A₀) * SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h) +
              SchwartzMap.seminorm ℝ 0 q (A h - A₀) *
                SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h))) ≤
          ∑ q ∈ Finset.range (d₀ + 1), δA * ((d₀.choose q : ℝ) *
            (SchwartzMap.seminorm ℝ 0 (d₀ - q) B₀ +
              SchwartzMap.seminorm ℝ l₀ (d₀ - q) B₀ + 2)) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hA1 := (hAh q hq).1.le
        have hA2 := (hAh q hq).2.le
        have hB1 := (hBh q hq).1
        have hB2 := (hBh q hq).2
        have hb0_nn := apply_nonneg (SchwartzMap.seminorm ℝ 0 (d₀ - q)) (B h)
        have hbl_nn := apply_nonneg (SchwartzMap.seminorm ℝ l₀ (d₀ - q)) (B h)
        have h1 := mul_le_mul hA1 hB1 hb0_nn hδA.le
        have h2 := mul_le_mul hA2 hB2 hbl_nn hδA.le
        have h_add : SchwartzMap.seminorm ℝ l₀ q (A h - A₀) *
              SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h) +
            SchwartzMap.seminorm ℝ 0 q (A h - A₀) *
              SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h) ≤
            δA * (SchwartzMap.seminorm ℝ 0 (d₀ - q) B₀ +
              SchwartzMap.seminorm ℝ l₀ (d₀ - q) B₀ + 2) := by
          linarith
        calc (d₀.choose q : ℝ) *
              (SchwartzMap.seminorm ℝ l₀ q (A h - A₀) *
                  SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h) +
                SchwartzMap.seminorm ℝ 0 q (A h - A₀) *
                  SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h))
            ≤ (d₀.choose q : ℝ) * (δA * (SchwartzMap.seminorm ℝ 0 (d₀ - q) B₀ +
                SchwartzMap.seminorm ℝ l₀ (d₀ - q) B₀ + 2)) :=
              mul_le_mul_of_nonneg_left h_add (Nat.cast_nonneg _)
          _ = _ := by ring
      refine h_sum_le.trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (by dsimp [M_B]; linarith) hδA.le
    have h_t2 : SchwartzMap.seminorm ℝ l₀ d₀ (schwartzPrepend k A₀ (B h - B₀)) ≤ δB * M_A := by
      refine (seminorm_schwartzPrepend_le k l₀ d₀ A₀ (B h - B₀)).trans ?_
      have h_sum_le :
          (∑ q ∈ Finset.range (d₀ + 1), (d₀.choose q : ℝ) *
            (SchwartzMap.seminorm ℝ l₀ q A₀ * SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h - B₀) +
              SchwartzMap.seminorm ℝ 0 q A₀ *
                SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h - B₀))) ≤
          ∑ q ∈ Finset.range (d₀ + 1), δB * ((d₀.choose q : ℝ) *
            (SchwartzMap.seminorm ℝ l₀ q A₀ + SchwartzMap.seminorm ℝ 0 q A₀)) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hB1 := (hBsh q hq).1.le
        have hB2 := (hBsh q hq).2.le
        have ha0_nn := apply_nonneg (SchwartzMap.seminorm ℝ l₀ q) A₀
        have hal_nn := apply_nonneg (SchwartzMap.seminorm ℝ 0 q) A₀
        have h1 := mul_le_mul_of_nonneg_left hB1 ha0_nn
        have h2 := mul_le_mul_of_nonneg_left hB2 hal_nn
        have h_add : SchwartzMap.seminorm ℝ l₀ q A₀ *
              SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h - B₀) +
            SchwartzMap.seminorm ℝ 0 q A₀ *
              SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h - B₀) ≤
            δB * (SchwartzMap.seminorm ℝ l₀ q A₀ + SchwartzMap.seminorm ℝ 0 q A₀) := by
          linarith
        calc (d₀.choose q : ℝ) *
              (SchwartzMap.seminorm ℝ l₀ q A₀ *
                  SchwartzMap.seminorm ℝ 0 (d₀ - q) (B h - B₀) +
                SchwartzMap.seminorm ℝ 0 q A₀ *
                  SchwartzMap.seminorm ℝ l₀ (d₀ - q) (B h - B₀))
            ≤ (d₀.choose q : ℝ) * (δB * (SchwartzMap.seminorm ℝ l₀ q A₀ +
                SchwartzMap.seminorm ℝ 0 q A₀)) :=
              mul_le_mul_of_nonneg_left h_add (Nat.cast_nonneg _)
          _ = _ := by ring
      refine h_sum_le.trans ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (by dsimp [M_A]; linarith) hδB.le
    have h_bd1 : δA * M_B = ε / 4 := by
      dsimp [δA]
      field_simp [hMB_pos.ne']
    have h_bd2 : δB * M_A = ε / 4 := by
      dsimp [δB]
      field_simp [hMA_pos.ne']
    rw [sub_zero]
    linarith
  simpa using h_sub.add_const (schwartzPrepend k A₀ B₀)

lemma tendsto_schwartzPrepend_slope {k : ℕ} (t : ℝ)
    {ψ : ℝ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ} {ψ' : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    {F : ℝ → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ} {F' : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ}
    (hψ : Tendsto (fun h : ℝ => h⁻¹ • (ψ (t + h) - ψ t)) (𝓝[≠] 0) (𝓝 ψ'))
    (hF : Tendsto (fun h : ℝ => h⁻¹ • (F (t + h) - F t)) (𝓝[≠] 0) (𝓝 F')) :
    Tendsto
      (fun h : ℝ => h⁻¹ • (schwartzPrepend k (ψ (t + h)) (F (t + h)) -
        schwartzPrepend k (ψ t) (F t)))
      (𝓝[≠] 0)
      (𝓝 (schwartzPrepend k ψ' (F t) + schwartzPrepend k (ψ t) F')) := by
  have hF_shift : Tendsto (fun h : ℝ => F (t + h)) (𝓝[≠] 0) (𝓝 (F t)) := by
    have h_sm : Tendsto (fun h : ℝ => h • (h⁻¹ • (F (t + h) - F t))) (𝓝[≠] 0) (𝓝 0) := by
      have h0 : (0 : ℝ) • F' = 0 := zero_smul ℝ F'
      rw [← h0]
      exact (continuousWithinAt_id.tendsto).smul hF
    have h_ev : (fun h : ℝ => F (t + h) - F t) =ᶠ[𝓝[≠] 0]
        (fun h : ℝ => h • (h⁻¹ • (F (t + h) - F t))) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh0 : h ≠ 0 := hh
      rw [smul_smul, mul_inv_cancel₀ hh0, one_smul]
    have h_sub : Tendsto (fun h : ℝ => F (t + h) - F t) (𝓝[≠] 0) (𝓝 0) := h_sm.congr' h_ev.symm
    simpa using h_sub.add_const (F t)
  have h_sum_ev :
      (fun h : ℝ =>
        schwartzPrepend k (h⁻¹ • (ψ (t + h) - ψ t)) (F (t + h)) +
          schwartzPrepend k (ψ t) (h⁻¹ • (F (t + h) - F t))) =ᶠ[𝓝[≠] 0]
      (fun h : ℝ => h⁻¹ • (schwartzPrepend k (ψ (t + h)) (F (t + h)) -
        schwartzPrepend k (ψ t) (F t))) := by
    filter_upwards [self_mem_nhdsWithin] with h _
    ext x
    simp only [_root_.add_apply, _root_.smul_apply, _root_.sub_apply,
      schwartzPrepend_apply, Complex.real_smul]
    ring
  exact ((tendsto_schwartzPrepend hψ hF_shift).add
    (tendsto_schwartzPrepend tendsto_const_nhds hF)).congr' h_sum_ev

lemma tendsto_schwartzChain_slope (r : ℕ) (t : ℝ)
    (ψ ψ' : Fin r → ℝ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hψ : ∀ i : Fin r,
      Tendsto (fun h : ℝ => h⁻¹ • (ψ i (t + h) - ψ i t)) (𝓝[≠] 0) (𝓝 (ψ' i t))) :
    Tendsto
      (fun h : ℝ =>
        h⁻¹ • (schwartzChain r (fun i => ψ i (t + h)) - schwartzChain r (fun i => ψ i t)))
      (𝓝[≠] 0)
      (𝓝 (∑ j : Fin r, schwartzChain r (Function.update (fun i => ψ i t) j (ψ' j t)))) := by
  induction r with
  | zero =>
    simp [schwartzChain]
  | succ k ih =>
    have h_ih := ih (fun i => ψ i.succ) (fun i => ψ' i.succ) (fun i => hψ i.succ)
    have h_prep := tendsto_schwartzPrepend_slope t
      (ψ := ψ 0) (ψ' := ψ' 0 t) (F := fun τ => schwartzChain k fun i => ψ i.succ τ)
      (F' := ∑ j : Fin k, schwartzChain k (Function.update (fun i => ψ i.succ t) j (ψ' j.succ t)))
      (hψ 0) h_ih
    have h_upd0 : schwartzPrepend k (ψ' 0 t) (schwartzChain k fun i => ψ i.succ t) =
        schwartzPrepend k (Function.update (fun i => ψ i t) 0 (ψ' 0 t) 0)
          (schwartzChain k (Function.update (fun i => ψ i t) 0 (ψ' 0 t) ∘ Fin.succ)) := by
      congr 1
    have h_upd_succ :
        (schwartzPrepend k (ψ 0 t)
          (∑ j : Fin k, schwartzChain k (Function.update (fun i => ψ i.succ t) j (ψ' j.succ t)))) =
        ∑ j : Fin k, schwartzPrepend k (Function.update (fun i => ψ i t) j.succ (ψ' j.succ t) 0)
          (schwartzChain k (Function.update (fun i => ψ i t) j.succ (ψ' j.succ t) ∘ Fin.succ)) := by
      ext x
      simp only [schwartzPrepend_apply, schwartzMap_sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h_head : ψ 0 t = Function.update (fun i => ψ i t) j.succ (ψ' j.succ t) 0 := by
        rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
      have h_fn : Function.update (fun i => ψ i.succ t) j (ψ' j.succ t) =
          Function.update (fun i => ψ i t) j.succ (ψ' j.succ t) ∘ Fin.succ := by
        ext i y
        by_cases hi : i = j
        · subst hi; simp
        · change Function.update (fun i => ψ i.succ t) j (ψ' j.succ t) i y =
            Function.update (fun i => ψ i t) j.succ (ψ' j.succ t) i.succ y
          rw [Function.update_of_ne hi, Function.update_of_ne (Fin.succ_inj.ne.mpr hi)]
      rw [h_head, h_fn]
    have h_lim_eq :
        schwartzPrepend k (ψ' 0 t) (schwartzChain k fun i => ψ i.succ t) +
          schwartzPrepend k (ψ 0 t)
            (∑ j : Fin k, schwartzChain k (Function.update (fun i => ψ i.succ t) j (ψ' j.succ t))) =
        ∑ j : Fin (k + 1), schwartzChain (k + 1) (Function.update (fun i => ψ i t) j (ψ' j t)) := by
      rw [h_upd0, h_upd_succ, Fin.sum_univ_succ]
      rfl
    rw [h_lim_eq] at h_prep
    exact h_prep

def haagRuelleChain {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket) (t : ℝ) :
    IndexedSchwartz ι r :=
  indexedChain ι r (fun i => haagRuelleIndexedTest D (s i) (f i) t)

def haagRuelleChainVec {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket) (t : ℝ) :
    D.Hilbert :=
  wightmanIndexedVec D.wightman.WData r (haagRuelleChain D r s f t)

def haagRuelleDerivSlotChain {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket) (j : Fin r) (t : ℝ) :
    IndexedSchwartz ι r :=
  indexedChain ι r (fun i => if i = j then haagRuelleDerivIndexedTest D (s i) (f i) t
    else haagRuelleIndexedTest D (s i) (f i) t)

theorem hasDerivAt_haagRuelleChainVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket) (t : ℝ) :
    HasDerivAt (haagRuelleChainVec D r s f)
      (∑ j : Fin r, wightmanIndexedVec D.wightman.WData r
        (haagRuelleDerivSlotChain D r s f j t)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h_each : ∀ γ : Fin r → ι, Tendsto
      (fun h : ℝ => h⁻¹ •
        (wightmanSchwartzVec D.wightman.WData r γ (haagRuelleChain D r s f (t + h) γ) -
          wightmanSchwartzVec D.wightman.WData r γ (haagRuelleChain D r s f t γ)))
      (𝓝[≠] 0)
      (𝓝 (∑ j : Fin r, wightmanSchwartzVec D.wightman.WData r γ
        (haagRuelleDerivSlotChain D r s f j t γ))) := by
    intro γ
    let Wv := wightmanSchwartzVec D.wightman.WData r γ
    have h_sc := tendsto_schwartzChain_slope r t
      (fun i τ => haagRuelleIndexedTest D (s i) (f i) τ (γ i))
      (fun i τ => haagRuelleDerivIndexedTest D (s i) (f i) τ (γ i))
      fun i => tendsto_haagRuelleTestFn_timeDeriv m M D.hm D.hM
        (dualModeWavepacket D (s i) (γ i) (f i)) t
    have h_comp := (Wv.continuous.tendsto _).comp h_sc
    rw [map_sum] at h_comp
    have h_lim :
        (∑ j : Fin r, Wv (schwartzChain r (Function.update
          (fun i => haagRuelleIndexedTest D (s i) (f i) t (γ i)) j
          (haagRuelleDerivIndexedTest D (s j) (f j) t (γ j))))) =
        ∑ j : Fin r, Wv (haagRuelleDerivSlotChain D r s f j t γ) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp [haagRuelleDerivSlotChain]
      rw [indexedChain_apply]
      congr 2
      ext i x
      by_cases hi : i = j
      · subst hi; simp [Function.update_self]
      · simp [hi]
    rw [h_lim] at h_comp
    refine h_comp.congr' (Eventually.of_forall fun h => ?_)
    dsimp only [Function.comp_def, haagRuelleChain]
    rw [← indexedChain_apply, ← indexedChain_apply]
    change Wv (h⁻¹ • (indexedChain ι r (fun i => haagRuelleIndexedTest D (s i) (f i) (t + h)) γ -
        indexedChain ι r (fun i => haagRuelleIndexedTest D (s i) (f i) t) γ)) =
      h⁻¹ • (Wv (indexedChain ι r (fun i => haagRuelleIndexedTest D (s i) (f i) (t + h)) γ) -
        Wv (indexedChain ι r (fun i => haagRuelleIndexedTest D (s i) (f i) t) γ))
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub]
  have h_sum := tendsto_finsetSum (Finset.univ : Finset (Fin r → ι)) fun γ _ => h_each γ
  have h_comm :
      (∑ γ : Fin r → ι, ∑ j : Fin r,
        wightmanSchwartzVec D.wightman.WData r γ (haagRuelleDerivSlotChain D r s f j t γ)) =
      ∑ j : Fin r, wightmanIndexedVec D.wightman.WData r (haagRuelleDerivSlotChain D r s f j t) :=
    Finset.sum_comm
  rw [h_comm] at h_sum
  refine h_sum.congr' (Eventually.of_forall fun h => ?_)
  dsimp [haagRuelleChainVec, wightmanIndexedVec]
  rw [← Finset.sum_sub_distrib, ← Finset.smul_sum]

theorem norm_deriv_haagRuelleChainVec_rapid_decay
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖deriv (haagRuelleChainVec D r s f) t‖ * (1 + |t|) ^ (N + 2) ≤ C := by
  have h_slot : ∀ j : Fin r, ∃ C_j : ℝ, 0 ≤ C_j ∧ ∀ t : ℝ,
      ‖wightmanIndexedVec D.wightman.WData r (haagRuelleDerivSlotChain D r s f j t)‖ *
        (1 + |t|) ^ (N + 2) ≤ C_j := by
    intro j
    let d_of : Fin r → ℝ := fun u =>
      if hju : j < u then (exists_pos_sep_of_velocityDisjoint D.hm (hf (ne_of_lt hju))).choose
      else 1
    have hd_pos : ∀ u : Fin r, 0 < d_of u := fun u => by
      dsimp [d_of]
      split_ifs with hju
      · exact (exists_pos_sep_of_velocityDisjoint D.hm (hf (ne_of_lt hju))).choose_spec.1
      · exact zero_lt_one
    haveI : Nonempty (Fin r) := ⟨j⟩
    let d_min : ℝ := Finset.univ.inf' ⟨j, Finset.mem_univ j⟩ d_of
    have hdmin_pos : 0 < d_min := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun u _ => hd_pos u
    let r_cone : ℝ := d_min / 6
    have hr_cone : 0 < r_cone := by positivity
    let Ψ_j : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t =>
      if i = j then haagRuelleDerivIndexedTest D (s i) (f i) t
      else haagRuelleIndexedTest D (s i) (f i) t
    let Φ_j : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t =>
      if i = j then haagRuelleDerivCoreIndexedTest D (s i) (f i) r_cone hr_cone t
      else if j < i then haagRuelleCoreIndexedTest D (s i) (f i) r_cone hr_cone t
      else haagRuelleIndexedTest D (s i) (f i) t
    have hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ_j i) := fun i => by
      dsimp [Ψ_j]
      split_ifs
      · exact indexedTestPolyGrowth_haagRuelleDeriv D (s i) (f i)
      · exact indexedTestPolyGrowth_haagRuelle D (s i) (f i)
    have hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ_j i) := fun i => by
      dsimp [Φ_j]
      split_ifs
      · exact indexedTestPolyGrowth_haagRuelleDerivCore D (s i) (f i) r_cone hr_cone
      · exact indexedTestPolyGrowth_haagRuelleCore D (s i) (f i) r_cone hr_cone
      · exact indexedTestPolyGrowth_haagRuelle D (s i) (f i)
    have h_diff_dec : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Ψ_j i t α - Φ_j i t α) :=
      fun i => by
        by_cases hij : i = j
        · subst hij
          have h_sub : (fun t α => Ψ_j i t α - Φ_j i t α) =
              fun t => haagRuelleDerivTailIndexedTest D (s i) (f i) r_cone hr_cone t := by
            ext t α x
            simp only [Ψ_j, Φ_j, ↓reduceIte]
            rw [← haagRuelleDerivIndexedTest_sub_core D (s i) (f i) r_cone hr_cone t α]
          rw [h_sub]
          exact indexedTestRapidDecay_haagRuelleDerivTail D (s i) (f i) r_cone hr_cone
        · by_cases hji : j < i
          · have h_sub : (fun t α => Ψ_j i t α - Φ_j i t α) =
                fun t => haagRuelleTailIndexedTest D (s i) (f i) r_cone hr_cone t := by
              ext t α x
              simp only [Ψ_j, Φ_j, if_neg hij, if_pos hji]
              rw [← haagRuelleIndexedTest_sub_core D (s i) (f i) r_cone hr_cone t α]
            rw [h_sub]
            exact indexedTestRapidDecay_haagRuelleTail D (s i) (f i) r_cone hr_cone
          · intro α l d M_dec
            refine ⟨0, le_rfl, fun t => ?_⟩
            have h0 : Ψ_j i t α - Φ_j i t α = 0 := by
              ext x
              simp [Ψ_j, Φ_j, hij, hji]
            change SchwartzMap.seminorm ℝ l d (Ψ_j i t α - Φ_j i t α) * (1 + |t|) ^ M_dec ≤ 0
            rw [h0, map_zero, zero_mul]
    obtain ⟨deg_poly, C_poly, hCpoly_nn, hCpoly_bd⟩ :=
      norm_indexedChain_poly_growth D.wightman.WData r Ψ_j hΨ_poly
    obtain ⟨C_diff, hCdiff_nn, hCdiff_bd⟩ :=
      norm_indexedChain_sub_rapid_decay D.wightman.WData r Ψ_j Φ_j
        hΨ_poly hΦ_poly h_diff_dec (N + 2)
    have hr_pos : 0 < r := j.pos
    let p : ℕ := r - 1
    have hp_eq : p + 1 = r := Nat.sub_add_cancel hr_pos
    have h_perm_dec : ∀ σ : { σ : Equiv.Perm (Fin r) // σ ⟨p, by omega⟩ = j },
        ∃ C_s : ℝ, 0 ≤ C_s ∧ ∀ t : ℝ,
          ‖wightmanIndexedVec D.wightman.WData (p + 1)
            (indexedChain ι (p + 1) (Function.update
              (fun i : Fin (p + 1) => Φ_j (σ.1 (Fin.cast hp_eq i)) t) (Fin.last p)
              (haagRuelleDerivTailIndexedTest D (s j) (f j) r_cone hr_cone t)))‖ *
            (1 + |t|) ^ (N + 2) ≤ C_s := by
      rintro ⟨σ, hσ_last⟩
      let Θ : Fin (p + 1) → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
        Function.update (fun i : Fin (p + 1) => Φ_j (σ (Fin.cast hp_eq i)))
          (Fin.last p) (haagRuelleDerivTailIndexedTest D (s j) (f j) r_cone hr_cone)
      have hΘ_poly : ∀ i : Fin (p + 1), IndexedTestPolyGrowth (Θ i) := fun i => by
        by_cases hi : i = Fin.last p
        · subst hi
          simpa [Θ] using indexedTestPolyGrowth_of_rapidDecay
            (indexedTestRapidDecay_haagRuelleDerivTail D (s j) (f j) r_cone hr_cone)
        · simpa [Θ, Function.update_of_ne hi] using hΦ_poly (σ (Fin.cast hp_eq i))
      have hΘ_dec : IndexedTestRapidDecay (Θ (Fin.last p)) := by
        simpa [Θ] using indexedTestRapidDecay_haagRuelleDerivTail D (s j) (f j) r_cone hr_cone
      obtain ⟨C_s, hCs_nn, hCs⟩ :=
        norm_indexedChain_rapid_decay_of_slot D.wightman.WData (p + 1) (Fin.last p) Θ
          hΘ_poly hΘ_dec (N + 2)
      refine ⟨C_s, hCs_nn, fun t => ?_⟩
      have h_upd_eq : (fun i : Fin (p + 1) => Θ i t) = Function.update
          (fun i : Fin (p + 1) => Φ_j (σ (Fin.cast hp_eq i)) t) (Fin.last p)
          (haagRuelleDerivTailIndexedTest D (s j) (f j) r_cone hr_cone t) := by
        ext i α x
        by_cases hi : i = Fin.last p
        · subst hi; simp [Θ]
        · simp [Θ, Function.update_of_ne hi]
      rw [← h_upd_eq]
      exact hCs t
    choose C_s hCs_nn hCs_bd using h_perm_dec
    let C_tail_perm : ℝ := ∑ σ : { σ : Equiv.Perm (Fin r) // σ ⟨p, by omega⟩ = j }, C_s σ
    have hCtp_nn : 0 ≤ C_tail_perm := Finset.sum_nonneg fun σ _ => hCs_nn σ
    let C_small : ℝ := C_poly * 2 ^ (deg_poly + (N + 2))
    let C_large : ℝ := C_diff + C_tail_perm
    refine ⟨max C_small C_large, le_trans (by positivity) (le_max_left _ _), fun t => ?_⟩
    have h_deriv_eq : haagRuelleDerivSlotChain D r s f j t =
        indexedChain ι r (fun i => Ψ_j i t) := rfl
    rw [h_deriv_eq]
    by_cases ht1 : |t| < 1
    · have ht2 : 1 + |t| ≤ 2 := by linarith
      have ht_nn : 0 ≤ 1 + |t| := by positivity
      calc ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t))‖ *
            (1 + |t|) ^ (N + 2)
          ≤ (C_poly * (1 + |t|) ^ deg_poly) * (1 + |t|) ^ (N + 2) :=
            mul_le_mul_of_nonneg_right (hCpoly_bd t) (pow_nonneg ht_nn _)
        _ ≤ (C_poly * 2 ^ deg_poly) * 2 ^ (N + 2) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht_nn ht2 _) hCpoly_nn)
              (pow_le_pow_left₀ ht_nn ht2 _) (pow_nonneg ht_nn _) (by positivity)
        _ = C_small := by dsimp [C_small]; rw [pow_add]; ring
        _ ≤ max C_small C_large := le_max_left _ _
    · have ht_ge : 1 ≤ |t| := not_lt.mp ht1
      let m_steps : ℕ := p - j.val
      have hm_lt : j.val + m_steps < r := by omega
      have hsp_right : ∀ u : Fin m_steps, ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
          x₁ ∈ tsupport (Φ_j j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          x₂ ∈ tsupport (Φ_j ⟨j.val + 1 + u.val, by omega⟩ t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          is_spacelike (x₁ 0 - x₂ 0) := by
        intro u α₁ α₂ x₁ x₂ hx₁ hx₂
        have hu_gt : j < ⟨j.val + 1 + u.val, by omega⟩ := by
          change j.val < j.val + 1 + u.val
          omega
        have hu_ne : j ≠ ⟨j.val + 1 + u.val, by omega⟩ := ne_of_lt hu_gt
        have hx₁_c : Φ_j j t α₁ =
            haagRuelleDerivCoreIndexedTest D (s j) (f j) r_cone hr_cone t α₁ := by
          simp [Φ_j]
        have hx₂_c : Φ_j ⟨j.val + 1 + u.val, by omega⟩ t α₂ =
            haagRuelleCoreIndexedTest D (s ⟨j.val + 1 + u.val, by omega⟩)
              (f ⟨j.val + 1 + u.val, by omega⟩) r_cone hr_cone t α₂ := by
          simp [Φ_j, hu_ne.symm, hu_gt]
        rw [hx₁_c] at hx₁
        rw [hx₂_c] at hx₂
        have hx₁' : x₁ ∈ tsupport (velocityConeCutoff m D.hm
            (dualModeWavepacket D (s j) α₁ (f j)) r_cone hr_cone t) :=
          tsupport_timeModCoreTestFn_subset D.hm
            (dualModeWavepacket D (s j) α₁ (f j)) _ _ _ r_cone hr_cone t hx₁
        have hx₂' : x₂ ∈ tsupport (velocityConeCutoff m D.hm
            (dualModeWavepacket D (s ⟨j.val + 1 + u.val, by omega⟩) α₂
              (f ⟨j.val + 1 + u.val, by omega⟩)) r_cone hr_cone t) :=
          tsupport_timeModCoreTestFn_subset D.hm
            (dualModeWavepacket D (s ⟨j.val + 1 + u.val, by omega⟩) α₂
              (f ⟨j.val + 1 + u.val, by omega⟩)) _ _ _ r_cone hr_cone t hx₂
        have hd_le : 5 * r_cone ≤ d_of ⟨j.val + 1 + u.val, by omega⟩ := by
          have h1 : d_min ≤ d_of ⟨j.val + 1 + u.val, by omega⟩ :=
            Finset.inf'_le d_of (Finset.mem_univ _)
          dsimp [r_cone]
          linarith
        have h_sep_orig :=
          (exists_pos_sep_of_velocityDisjoint D.hm (hf hu_ne)).choose_spec.2
        have h_sep_d : ∀ v₁ ∈ velocitySupport m (dualModeWavepacket D (s j) α₁ (f j)),
            ∀ v₂ ∈ velocitySupport m (dualModeWavepacket D (s ⟨j.val + 1 + u.val, by omega⟩) α₂
              (f ⟨j.val + 1 + u.val, by omega⟩)),
            d_of ⟨j.val + 1 + u.val, by omega⟩ ≤ ‖v₁ - v₂‖ := fun v₁ hv₁ v₂ hv₂ => by
          have h_eq_d : d_of ⟨j.val + 1 + u.val, by omega⟩ =
              (exists_pos_sep_of_velocityDisjoint D.hm (hf hu_ne)).choose := by
            dsimp [d_of]
            exact dif_pos hu_gt
          rw [h_eq_d]
          exact h_sep_orig v₁ (velocitySupport_dualModeWavepacket_subset D (s j) α₁ (f j) hv₁)
            v₂ (velocitySupport_dualModeWavepacket_subset D
              (s ⟨j.val + 1 + u.val, by omega⟩) α₂ (f ⟨j.val + 1 + u.val, by omega⟩) hv₂)
        exact spacelike_velocityConeCutoffs_of_radius D.hm hr_cone hd_le h_sep_d ht_ge hx₁' hx₂'
      obtain ⟨σ, ⟨hσ_j, _, _, _⟩, h_swap_eq⟩ := wightmanIndexedVec_indexedChain_move_right
        D.wightman.WData D.locality r (fun i => Φ_j i t) j m_steps hm_lt hsp_right
      have hσ_p : σ ⟨p, by omega⟩ = j := by
        refine Eq.trans (congrArg σ ?_) hσ_j
        ext
        simp [m_steps]
        omega
      let σ_sub : { σ : Equiv.Perm (Fin r) // σ ⟨p, by omega⟩ = j } := ⟨σ, hσ_p⟩
      have h_η_norm : ‖η ^ m_steps‖ = 1 := by
        rw [norm_pow]
        rcases D.mode.hη with h1 | h1 <;> simp [h1]
      have h_cast :
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j (σ i) t)) =
          wightmanIndexedVec D.wightman.WData (p + 1)
            (indexedChain ι (p + 1) (fun i => Φ_j (σ (Fin.cast hp_eq i)) t)) :=
        wightmanIndexedVec_indexedChain_congr_cast D.wightman.WData hp_eq.symm
          (fun i => Φ_j (σ i) t) (fun i => Φ_j (σ (Fin.cast hp_eq i)) t) fun i => by
            congr 2
      have h_last_val : Φ_j (σ (Fin.cast hp_eq (Fin.last p))) t =
          haagRuelleDerivCoreIndexedTest D (s j) (f j) r_cone hr_cone t := by
        have h_eq_p : (Fin.cast hp_eq (Fin.last p) : Fin r) = ⟨p, by omega⟩ := by
          ext; simp
        rw [h_eq_p, hσ_p]
        simp [Φ_j]
      let base_fn : Fin (p + 1) → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
        fun i => Φ_j (σ (Fin.cast hp_eq i)) t
      have h_split_last : base_fn = Function.update base_fn (Fin.last p)
          (haagRuelleDerivIndexedTest D (s j) (f j) t -
            haagRuelleDerivTailIndexedTest D (s j) (f j) r_cone hr_cone t) := by
        ext i α x
        by_cases hi : i = Fin.last p
        · subst hi
          rw [Function.update_self]
          change Φ_j (σ (Fin.cast hp_eq (Fin.last p))) t α x = _
          rw [h_last_val]
          change haagRuelleDerivCoreIndexedTest D (s j) (f j) r_cone hr_cone t α x =
            (haagRuelleDerivIndexedTest D (s j) (f j) t α -
              haagRuelleDerivTailIndexedTest D (s j) (f j) r_cone hr_cone t α) x
          rw [← haagRuelleDerivIndexedTest_sub_core D (s j) (f j) r_cone hr_cone t α]
          simp
        · rw [Function.update_of_ne hi]
      have h_zero_deriv : wightmanIndexedVec D.wightman.WData (p + 1)
          (indexedChain ι (p + 1) (Function.update base_fn (Fin.last p)
            (haagRuelleDerivIndexedTest D (s j) (f j) t))) = 0 := by
        have h_tail_zero : wightmanIndexedVec D.wightman.WData 1
            (indexedChain ι 1 (fun u =>
              Function.update base_fn (Fin.last p)
                (haagRuelleDerivIndexedTest D (s j) (f j) t) (Fin.natAdd p u))) =
            (0 : ℂ) • D.vacuum := by
          rw [zero_smul]
          have h_eq_d : indexedChain ι 1 (fun u =>
              Function.update base_fn (Fin.last p)
                (haagRuelleDerivIndexedTest D (s j) (f j) t) (Fin.natAdd p u)) =
              haagRuelleDerivApply D (s j) (f j) t 0 (vacuumIndexedSchwartz ι) := by
            dsimp [indexedChain, haagRuelleDerivApply]
            congr 1
            have h_lp : (Fin.natAdd p (0 : Fin 1) : Fin (p + 1)) = Fin.last p := by
              ext; simp
            rw [h_lp, Function.update_self]
          rw [h_eq_d]
          exact haagRuelleDerivVacCreate_eq_zero D (s j) (f j) t
        have h_con := wightmanIndexedVec_indexedChain_contract_right D.wightman.WData p 1
          (Function.update base_fn (Fin.last p) (haagRuelleDerivIndexedTest D (s j) (f j) t))
          h_tail_zero
        rw [zero_smul] at h_con
        exact h_con
      have h_neg_tail : wightmanIndexedVec D.wightman.WData (p + 1)
          (indexedChain ι (p + 1) base_fn) =
          -(wightmanIndexedVec D.wightman.WData (p + 1)
            (indexedChain ι (p + 1) (Function.update base_fn (Fin.last p)
              (haagRuelleDerivTailIndexedTest D (s j) (f j) r_cone hr_cone t)))) := by
        conv_lhs => rw [h_split_last]
        rw [wightmanIndexedVec_indexedChain_update_sub, h_zero_deriv, zero_sub]
      have h_core_norm :
          ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖ *
            (1 + |t|) ^ (N + 2) ≤ C_tail_perm := by
        rw [h_swap_eq, norm_smul, h_η_norm, one_mul]
        change ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j (σ i) t))‖ *
            (1 + |t|) ^ (N + 2) ≤ C_tail_perm
        rw [h_cast]
        change ‖wightmanIndexedVec D.wightman.WData (p + 1) (indexedChain ι (p + 1) base_fn)‖ *
            (1 + |t|) ^ (N + 2) ≤ C_tail_perm
        rw [h_neg_tail, norm_neg]
        refine (hCs_bd σ_sub t).trans ?_
        exact Finset.single_le_sum (fun x _ => hCs_nn x) (Finset.mem_univ σ_sub)
      have h_tri : ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t))‖ ≤
          ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t)) -
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖ +
          ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖ := by
        have heq : wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t)) =
            (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))) +
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t)) := by
          abel
        conv_lhs => rw [heq]
        exact norm_add_le _ _
      have ht_nn : 0 ≤ (1 + |t|) ^ (N + 2) := pow_nonneg (by positivity) _
      calc ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t))‖ *
            (1 + |t|) ^ (N + 2)
          ≤ (‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t)) -
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖ +
              ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖) *
              (1 + |t|) ^ (N + 2) := mul_le_mul_of_nonneg_right h_tri ht_nn
        _ = ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_j i t)) -
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖ *
                (1 + |t|) ^ (N + 2) +
              ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_j i t))‖ *
                (1 + |t|) ^ (N + 2) := by ring
        _ ≤ C_diff + C_tail_perm := add_le_add (hCdiff_bd t) h_core_norm
        _ = C_large := rfl
        _ ≤ max C_small C_large := le_max_right _ _
  choose C_j hCj_nn hCj_bd using h_slot
  refine ⟨∑ j : Fin r, C_j j, Finset.sum_nonneg fun j _ => hCj_nn j, fun t => ?_⟩
  rw [(hasDerivAt_haagRuelleChainVec D r s f t).deriv]
  have ht_nn : 0 ≤ (1 + |t|) ^ (N + 2) := pow_nonneg (by positivity) _
  calc ‖∑ j : Fin r, wightmanIndexedVec D.wightman.WData r
          (haagRuelleDerivSlotChain D r s f j t)‖ * (1 + |t|) ^ (N + 2)
      ≤ (∑ j : Fin r, ‖wightmanIndexedVec D.wightman.WData r
          (haagRuelleDerivSlotChain D r s f j t)‖) * (1 + |t|) ^ (N + 2) :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht_nn
    _ = ∑ j : Fin r, ‖wightmanIndexedVec D.wightman.WData r
          (haagRuelleDerivSlotChain D r s f j t)‖ * (1 + |t|) ^ (N + 2) := Finset.sum_mul _ _ _
    _ ≤ ∑ j : Fin r, C_j j := Finset.sum_le_sum fun j _ => hCj_bd j t

lemma exists_tendsto_atTop_atBot_of_hasDerivAt_inv_sq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Ψ Ψ' : ℝ → E) (hderiv : ∀ t : ℝ, HasDerivAt Ψ (Ψ' t) t)
    {C : ℝ} (hC : 0 ≤ C) (hbd : ∀ t : ℝ, ‖Ψ' t‖ ≤ C * (1 + |t|)⁻¹ ^ 2) :
    (∃ Φ_out : E, Tendsto Ψ atTop (𝓝 Φ_out) ∧
        ∀ t : ℝ, 0 ≤ t → ‖Ψ t - Φ_out‖ ≤ C * (1 + t)⁻¹) ∧
      (∃ Φ_in : E, Tendsto Ψ atBot (𝓝 Φ_in) ∧
        ∀ t : ℝ, t ≤ 0 → ‖Ψ t - Φ_in‖ ≤ C * (1 - t)⁻¹) := by
  have h_diff_bound : ∀ (Ψ_f Ψ_f' : ℝ → E),
      (∀ t : ℝ, HasDerivAt Ψ_f (Ψ_f' t) t) →
      (∀ t : ℝ, ‖Ψ_f' t‖ ≤ C * (1 + |t|)⁻¹ ^ 2) →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → ‖Ψ_f b - Ψ_f a‖ ≤ C * ((1 + a)⁻¹ - (1 + b)⁻¹) := by
    intro Ψ_f Ψ_f' hf_deriv hf_bd a b ha hab
    let g : ℝ → E := fun x => Ψ_f x - Ψ_f a
    let B : ℝ → ℝ := fun x => C * ((1 + a)⁻¹ - (1 + x)⁻¹)
    let B' : ℝ → ℝ := fun x => C * (1 + x)⁻¹ ^ 2
    have hg_cont : ContinuousOn g (Set.Icc a b) :=
      Continuous.continuousOn (continuous_iff_continuousAt.mpr
        fun x => ((hf_deriv x).continuousAt.sub continuousAt_const))
    have hg_deriv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt g (Ψ_f' x) (Set.Ici x) x :=
      fun x _ => ((hf_deriv x).sub_const (Ψ_f a)).hasDerivWithinAt
    have hB_cont : ContinuousOn B (Set.Icc a b) := by
      refine continuousOn_const.mul (continuousOn_const.sub ?_)
      have h1x : ContinuousOn (fun x : ℝ => 1 + x) (Set.Icc a b) :=
        continuousOn_const.add continuousOn_id
      exact h1x.inv₀ fun x hx => by linarith [hx.1, ha]
    have hB_deriv : ∀ x ∈ Set.Ico a b, HasDerivWithinAt B (B' x) (Set.Ici x) x := by
      intro x hx
      have hx_pos : 0 < 1 + x := by linarith [hx.1, ha]
      have h_lin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add 1
      have h_inv : HasDerivAt (fun y : ℝ => (1 + y)⁻¹) (-(1 + x)⁻¹ ^ 2) x := by
        refine (h_lin.inv hx_pos.ne').congr_deriv ?_
        field_simp [hx_pos.ne']
      have h_full : HasDerivAt B (B' x) x := by
        refine ((hasDerivAt_const x (1 + a)⁻¹).sub h_inv |>.const_mul C).congr_deriv ?_
        dsimp [B']
        ring
      exact h_full.hasDerivWithinAt
    have h_fenc : ∀ x ∈ Set.Ico a b, ‖Ψ_f' x‖ ≤ B' x := by
      intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      have h_abs : |x| = x := abs_of_nonneg hx0
      simpa [B', h_abs] using hf_bd x
    have h_ga : ‖g a‖ ≤ B a := by simp [g, B]
    have h_res := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      hg_cont hg_deriv h_ga hB_cont hB_deriv h_fenc (Set.right_mem_Icc.mpr hab)
    exact h_res
  have h_conv : ∀ (Ψ_f Ψ_f' : ℝ → E),
      (∀ t : ℝ, HasDerivAt Ψ_f (Ψ_f' t) t) →
      (∀ t : ℝ, ‖Ψ_f' t‖ ≤ C * (1 + |t|)⁻¹ ^ 2) →
      ∃ Φ : E, Tendsto Ψ_f atTop (𝓝 Φ) ∧ ∀ t : ℝ, 0 ≤ t → ‖Ψ_f t - Φ‖ ≤ C * (1 + t)⁻¹ := by
    intro Ψ_f Ψ_f' hf_deriv hf_bd
    have h_cauchy : Cauchy (Filter.map Ψ_f atTop) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      let M : ℝ := max 0 (2 * (C + 1) / ε)
      refine ⟨Ψ_f '' Set.Ici M,
        Filter.mem_map.mpr (Filter.mem_atTop_sets.mpr ⟨M, fun x hx => Set.mem_image_of_mem Ψ_f hx⟩),
        ?_⟩
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hM0 : 0 ≤ M := le_max_left _ _
      have hx' : M ≤ x := Set.mem_Ici.mp hx
      have hy' : M ≤ y := Set.mem_Ici.mp hy
      have ha : 0 ≤ min x y := le_trans hM0 (le_min hx' hy')
      have hb_le : min x y ≤ max x y := min_le_max
      have h_bd_sub := h_diff_bound Ψ_f Ψ_f' hf_deriv hf_bd (min x y) (max x y) ha hb_le
      have h_norm : ‖Ψ_f x - Ψ_f y‖ = ‖Ψ_f (max x y) - Ψ_f (min x y)‖ := by
        rcases le_total x y with hxy | hyx
        · rw [max_eq_right hxy, min_eq_left hxy, norm_sub_rev]
        · rw [max_eq_left hyx, min_eq_right hyx]
      have h_b_nn : 0 ≤ (1 + max x y)⁻¹ := inv_nonneg.mpr (by linarith [le_trans ha hb_le])
      have h_inv_le : (1 + min x y)⁻¹ ≤ (1 + M)⁻¹ :=
        inv_anti₀ (by linarith [hM0]) (by linarith [le_min hx' hy'])
      have h_lt_eps : C * (1 + M)⁻¹ < ε := by
        have hM_pos : 0 < 1 + M := by linarith [le_max_left 0 (2 * (C + 1) / ε)]
        have hM_big : 2 * (C + 1) / ε ≤ M := le_max_right _ _
        rw [← div_eq_mul_inv, div_lt_iff₀ hM_pos]
        have h1 : 2 * (C + 1) ≤ ε * M := by
          simpa [mul_comm] using (div_le_iff₀ hε).mp hM_big
        linarith
      rw [dist_eq_norm, h_norm]
      refine h_bd_sub.trans_lt ?_
      have h1 : C * ((1 + min x y)⁻¹ - (1 + max x y)⁻¹) ≤ C * (1 + min x y)⁻¹ :=
        mul_le_mul_of_nonneg_left (sub_le_self _ h_b_nn) hC
      have h2 : C * (1 + min x y)⁻¹ ≤ C * (1 + M)⁻¹ := mul_le_mul_of_nonneg_left h_inv_le hC
      linarith
    obtain ⟨Φ, hΦ⟩ := cauchy_map_iff_exists_tendsto.mp h_cauchy
    refine ⟨Φ, hΦ, fun t ht => ?_⟩
    have h_lim : Tendsto (fun b : ℝ => ‖Ψ_f b - Ψ_f t‖) atTop (𝓝 ‖Φ - Ψ_f t‖) :=
      (hΦ.sub_const (Ψ_f t)).norm
    have h_ev : ∀ᶠ b : ℝ in atTop, ‖Ψ_f b - Ψ_f t‖ ≤ C * (1 + t)⁻¹ := by
      filter_upwards [Filter.eventually_ge_atTop t] with b hb
      have hb_nn : 0 ≤ (1 + b)⁻¹ := inv_nonneg.mpr (by linarith)
      exact (h_diff_bound Ψ_f Ψ_f' hf_deriv hf_bd t b ht hb).trans
        (mul_le_mul_of_nonneg_left (sub_le_self _ hb_nn) hC)
    rw [norm_sub_rev]
    exact le_of_tendsto h_lim h_ev
  refine ⟨h_conv Ψ Ψ' hderiv hbd, ?_⟩
  let Ψ_neg : ℝ → E := fun s => Ψ (-s)
  let Ψ_neg' : ℝ → E := fun s => -Ψ' (-s)
  have hneg_deriv : ∀ s : ℝ, HasDerivAt Ψ_neg (Ψ_neg' s) s := fun s => by
    have h := (hderiv (-s)).scomp s (hasDerivAt_neg s)
    rw [neg_one_smul] at h
    exact h
  have hneg_bd : ∀ s : ℝ, ‖Ψ_neg' s‖ ≤ C * (1 + |s|)⁻¹ ^ 2 := fun s => by
    dsimp [Ψ_neg']
    rw [norm_neg, ← abs_neg s]
    exact hbd (-s)
  obtain ⟨Φ_in, hΦ_in, hΦ_in_bd⟩ := h_conv Ψ_neg Ψ_neg' hneg_deriv hneg_bd
  refine ⟨Φ_in, ?_, fun t ht => ?_⟩
  · refine (hΦ_in.comp Filter.tendsto_neg_atBot_atTop).congr fun t => ?_
    dsimp [Ψ_neg]
    rw [neg_neg]
  · have h := hΦ_in_bd (-t) (neg_nonneg.mpr ht)
    dsimp [Ψ_neg] at h
    rwa [neg_neg, ← sub_eq_add_neg] at h

theorem exists_haagRuelleOutState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    ∃ Φ_out : D.Hilbert,
      Tendsto (haagRuelleChainVec D r s f) atTop (𝓝 Φ_out) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
          ‖haagRuelleChainVec D r s f t - Φ_out‖ ≤ C * (1 + t)⁻¹ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := norm_deriv_haagRuelleChainVec_rapid_decay D r s f hf 0
  have h_all : ∀ t : ℝ, ‖deriv (haagRuelleChainVec D r s f) t‖ ≤ C * (1 + |t|)⁻¹ ^ 2 := by
    intro t
    have hpow : 0 < (1 + |t|) ^ 2 := pow_pos (by positivity) 2
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpow]
    simpa using hC_bd t
  have h_deriv : ∀ t : ℝ, HasDerivAt (haagRuelleChainVec D r s f)
      (deriv (haagRuelleChainVec D r s f) t) t :=
    fun t => (hasDerivAt_haagRuelleChainVec D r s f t).differentiableAt.hasDerivAt
  obtain ⟨⟨Φ_out, h_out, h_bd⟩, _⟩ :=
    exists_tendsto_atTop_atBot_of_hasDerivAt_inv_sq
      (haagRuelleChainVec D r s f) (deriv (haagRuelleChainVec D r s f)) h_deriv hC_nn h_all
  exact ⟨Φ_out, h_out, C, hC_nn, h_bd⟩

theorem exists_haagRuelleInState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    ∃ Φ_in : D.Hilbert,
      Tendsto (haagRuelleChainVec D r s f) atBot (𝓝 Φ_in) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≤ 0 →
          ‖haagRuelleChainVec D r s f t - Φ_in‖ ≤ C * (1 - t)⁻¹ := by
  obtain ⟨C, hC_nn, hC_bd⟩ := norm_deriv_haagRuelleChainVec_rapid_decay D r s f hf 0
  have h_all : ∀ t : ℝ, ‖deriv (haagRuelleChainVec D r s f) t‖ ≤ C * (1 + |t|)⁻¹ ^ 2 := by
    intro t
    have hpow : 0 < (1 + |t|) ^ 2 := pow_pos (by positivity) 2
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpow]
    simpa using hC_bd t
  have h_deriv : ∀ t : ℝ, HasDerivAt (haagRuelleChainVec D r s f)
      (deriv (haagRuelleChainVec D r s f) t) t :=
    fun t => (hasDerivAt_haagRuelleChainVec D r s f t).differentiableAt.hasDerivAt
  obtain ⟨_, ⟨Φ_in, h_in, h_bd⟩⟩ :=
    exists_tendsto_atTop_atBot_of_hasDerivAt_inv_sq
      (haagRuelleChainVec D r s f) (deriv (haagRuelleChainVec D r s f)) h_deriv hC_nn h_all
  exact ⟨Φ_in, h_in, C, hC_nn, h_bd⟩

def haagRuelleOutVec {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) : D.Hilbert :=
  (exists_haagRuelleOutState D r s f hf).choose

def haagRuelleInVec {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) : D.Hilbert :=
  (exists_haagRuelleInState D r s f hf).choose

theorem tendsto_haagRuelleChainVec_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    Tendsto (haagRuelleChainVec D r s f) atTop (𝓝 (haagRuelleOutVec D r s f hf)) :=
  (exists_haagRuelleOutState D r s f hf).choose_spec.1

theorem tendsto_haagRuelleChainVec_atBot
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    Tendsto (haagRuelleChainVec D r s f) atBot (𝓝 (haagRuelleInVec D r s f hf)) :=
  (exists_haagRuelleInState D r s f hf).choose_spec.1

theorem norm_haagRuelleChainVec_sub_outVec_le
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      ‖haagRuelleChainVec D r s f t - haagRuelleOutVec D r s f hf‖ ≤ C * (1 + t)⁻¹ :=
  (exists_haagRuelleOutState D r s f hf).choose_spec.2

theorem norm_haagRuelleChainVec_sub_inVec_le
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≤ 0 →
      ‖haagRuelleChainVec D r s f t - haagRuelleInVec D r s f hf‖ ≤ C * (1 - t)⁻¹ :=
  (exists_haagRuelleInState D r s f hf).choose_spec.2

@[simp]
lemma haagRuelleChainVec_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 0 → Fin D.mode.ν) (f : Fin 0 → SmoothWavepacket) (t : ℝ) :
    haagRuelleChainVec D 0 s f t = D.vacuum :=
  wightmanIndexedVec_vacuum D.wightman.WData

@[simp]
lemma haagRuelleChainVec_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 1 → Fin D.mode.ν) (f : Fin 1 → SmoothWavepacket) (t : ℝ) :
    haagRuelleChainVec D 1 s f t = haagRuelleVacCreate D (s 0) (f 0) 0 := by
  rw [← haagRuelleVacCreate_time_indep D (s 0) (f 0) t]
  rfl

@[simp]
theorem haagRuelleOutVec_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 0 → Fin D.mode.ν) (f : Fin 0 → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin 0 => VelocityDisjoint m (f i) (f j)) :
    haagRuelleOutVec D 0 s f hf = D.vacuum := by
  have h1 := tendsto_haagRuelleChainVec_atTop D 0 s f hf
  have h_eq : haagRuelleChainVec D 0 s f = fun _ => D.vacuum :=
    funext fun t => haagRuelleChainVec_zero D s f t
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

@[simp]
theorem haagRuelleInVec_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 0 → Fin D.mode.ν) (f : Fin 0 → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin 0 => VelocityDisjoint m (f i) (f j)) :
    haagRuelleInVec D 0 s f hf = D.vacuum := by
  have h1 := tendsto_haagRuelleChainVec_atBot D 0 s f hf
  have h_eq : haagRuelleChainVec D 0 s f = fun _ => D.vacuum :=
    funext fun t => haagRuelleChainVec_zero D s f t
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

@[simp]
theorem haagRuelleOutVec_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 1 → Fin D.mode.ν) (f : Fin 1 → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin 1 => VelocityDisjoint m (f i) (f j)) :
    haagRuelleOutVec D 1 s f hf = haagRuelleVacCreate D (s 0) (f 0) 0 := by
  have h1 := tendsto_haagRuelleChainVec_atTop D 1 s f hf
  have h_eq : haagRuelleChainVec D 1 s f = fun _ => haagRuelleVacCreate D (s 0) (f 0) 0 :=
    funext fun t => haagRuelleChainVec_one D s f t
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

@[simp]
theorem haagRuelleInVec_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 1 → Fin D.mode.ν) (f : Fin 1 → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin 1 => VelocityDisjoint m (f i) (f j)) :
    haagRuelleInVec D 1 s f hf = haagRuelleVacCreate D (s 0) (f 0) 0 := by
  have h1 := tendsto_haagRuelleChainVec_atBot D 1 s f hf
  have h_eq : haagRuelleChainVec D 1 s f = fun _ => haagRuelleVacCreate D (s 0) (f 0) 0 :=
    funext fun t => haagRuelleChainVec_one D s f t
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

theorem haagRuelleInVec_one_eq_outVec_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin 1 → Fin D.mode.ν) (f : Fin 1 → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin 1 => VelocityDisjoint m (f i) (f j)) :
    haagRuelleInVec D 1 s f hf = haagRuelleOutVec D 1 s f hf := by
  rw [haagRuelleInVec_one, haagRuelleOutVec_one]

omit [Fintype ι] [DecidableEq ι] in
lemma SmoothWavepacket.ext {f g : SmoothWavepacket} (h : f.amp = g.amp) : f = g := by
  cases f
  cases g
  simp only at h
  subst h
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_massShellVec {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ (⊤ : ℕ∞) (massShellVec m) := by
  refine contDiff_pi.mpr fun μ => ?_
  fin_cases μ
  · exact contDiff_massShellEnergy hm
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).contDiff
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).contDiff

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_fockMinkowskiPhase (b : Fin 4 → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fockMinkowskiPhase b) := by
  have h_lin : ContDiff ℝ (⊤ : ℕ∞) (fun P : Fin 4 → ℝ => minkowskiInner P b) := by
    simp only [minkowskiInner_explicit]
    have hp : ∀ μ : Fin 4, ContDiff ℝ (⊤ : ℕ∞) (fun P : Fin 4 → ℝ => P μ * b μ) :=
      fun μ => ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) μ).contDiff).mul
        contDiff_const
    exact (((hp 0).sub (hp 1)).sub (hp 2)).sub (hp 3)
  exact Complex.contDiff_exp.comp
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h_lin))

omit [Fintype ι] [DecidableEq ι] in
def translateWavepacket (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ) (f : SmoothWavepacket) :
    SmoothWavepacket where
  amp p := fockMinkowskiPhase a (massShellVec m p) * f.amp p
  smooth := ((contDiff_fockMinkowskiPhase a).comp (contDiff_massShellVec hm)).mul f.smooth
  compactSupport := f.compactSupport.mul_left

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma translateWavepacket_apply (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (f : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (translateWavepacket m hm a f).amp p =
      fockMinkowskiPhase a (massShellVec m p) * f.amp p := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma tsupport_translateWavepacket_eq (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (f : SmoothWavepacket) :
    tsupport (translateWavepacket m hm a f).amp = tsupport f.amp := by
  apply congrArg closure
  ext p
  simp only [Function.mem_support, translateWavepacket_apply, ne_eq, mul_eq_zero]
  refine ⟨fun h hf => h (Or.inr hf), fun h hor => hor.elim (fun hp => ?_) h⟩
  exact norm_ne_zero_iff.mp (by rw [norm_fockMinkowskiPhase]; exact one_ne_zero) hp

omit [Fintype ι] [DecidableEq ι] in
lemma velocitySupport_translateWavepacket_eq (m : ℝ) (hm : 0 < m) (a : Fin 4 → ℝ)
    (f : SmoothWavepacket) :
    velocitySupport m (translateWavepacket m hm a f) = velocitySupport m f := by
  unfold velocitySupport
  rw [tsupport_translateWavepacket_eq]

omit [Fintype ι] [DecidableEq ι] in
lemma velocityDisjoint_translateWavepacket_iff {m : ℝ} (hm : 0 < m) (a : Fin 4 → ℝ)
    {f₁ f₂ : SmoothWavepacket} :
    VelocityDisjoint m (translateWavepacket m hm a f₁) (translateWavepacket m hm a f₂) ↔
      VelocityDisjoint m f₁ f₂ := by
  unfold VelocityDisjoint
  rw [velocitySupport_translateWavepacket_eq, velocitySupport_translateWavepacket_eq]

lemma dualModeWavepacket_translateWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (s : Fin D.mode.ν) (α : ι) (f : SmoothWavepacket) :
    dualModeWavepacket D s α (translateWavepacket m D.hm a f) =
      translateWavepacket m D.hm a (dualModeWavepacket D s α f) := by
  apply SmoothWavepacket.ext
  funext p
  simp only [dualModeWavepacket_apply, translateWavepacket_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzDiagTranslateN_one_haagRuelleTestFn
    (m M : ℝ) (hm : 0 < m) (hM : m < M) (a : Fin 4 → ℝ)
    (f : SmoothWavepacket) (t : ℝ) :
    schwartzDiagTranslateN 1 a (haagRuelleTestFn m M hm hM f t) =
      haagRuelleTestFn m M hm hM (translateWavepacket m hm a f) (t + a 0) := by
  apply minkowskiFourier_injective
  intro p
  let q : Fin 4 → ℝ := -(p 0)
  have hp : p = fun _ : Fin 1 => -q := by
    ext i μ
    rw [Subsingleton.elim i 0]
    simp [q]
  rw [hp, minkowskiFourier_schwartzDiagTranslateN, Fin.sum_univ_one]
  rw [minkowskiFourier_haagRuelleTestFn, minkowskiFourier_haagRuelleTestFn]
  unfold timeModMomAmp haagRuelleBaseAmp
  simp only [translateWavepacket_apply]
  unfold fockMinkowskiPhase
  have h_mink : minkowskiInner (-q) a = -minkowskiInner q a := by
    simp only [minkowskiInner_explicit, Pi.neg_apply, neg_mul]
    ring
  have h_diff : minkowskiInner q a - minkowskiInner (massShellVec m (spatialPart q)) a =
      (q 0 - massShellEnergy m (spatialPart q)) * a 0 := by
    have h1 : (Fin.succ 0 : Fin 4) = 1 := rfl
    have h2 : (Fin.succ 1 : Fin 4) = 2 := rfl
    have h3 : (Fin.succ 2 : Fin 4) = 3 := rfl
    simp only [minkowskiInner_explicit, massShellVec, spatialPart, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, h1, h2, h3]
    ring
  rw [h_mink, Complex.ofReal_neg, mul_neg, neg_neg]
  calc Complex.exp (Complex.I * (minkowskiInner q a : ℂ)) *
        (f.amp (spatialPart q) * (massShellCutoff m M hm hM q : ℂ) *
          Complex.exp (Complex.I * (((q 0 - massShellEnergy m (spatialPart q)) * t : ℝ) : ℂ)))
      = f.amp (spatialPart q) * (massShellCutoff m M hm hM q : ℂ) *
          (Complex.exp (Complex.I * (minkowskiInner q a : ℂ)) *
            Complex.exp
              (Complex.I * (((q 0 - massShellEnergy m (spatialPart q)) * t : ℝ) : ℂ))) := by
        ring
    _ = f.amp (spatialPart q) * (massShellCutoff m M hm hM q : ℂ) *
          (Complex.exp (Complex.I * (minkowskiInner (massShellVec m (spatialPart q)) a : ℂ)) *
            Complex.exp (Complex.I *
              (((q 0 - massShellEnergy m (spatialPart q)) * (t + a 0) : ℝ) : ℂ))) := by
        have h_diff_c :
            (minkowskiInner q a : ℂ) -
              (minkowskiInner (massShellVec m (spatialPart q)) a : ℂ) =
                ((q 0 : ℂ) - (massShellEnergy m (spatialPart q) : ℂ)) * (a 0 : ℂ) := by
          exact_mod_cast h_diff
        congr 1
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        linear_combination Complex.I * h_diff_c
    _ = Complex.exp (Complex.I * (minkowskiInner (massShellVec m (spatialPart q)) a : ℂ)) *
          f.amp (spatialPart q) * (massShellCutoff m M hm hM q : ℂ) *
          Complex.exp
            (Complex.I * (((q 0 - massShellEnergy m (spatialPart q)) * (t + a 0) : ℝ) : ℂ)) := by
        ring

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzDiagTranslateN_schwartzPrepend (k : ℕ) (a : Fin 4 → ℝ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN (k + 1) a (schwartzPrepend k ψ F) =
      schwartzPrepend k (schwartzDiagTranslateN 1 a ψ) (schwartzDiagTranslateN k a F) := by
  ext x
  simp only [schwartzDiagTranslateN_apply, schwartzPrepend_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzDiagTranslateN_schwartzChain (r : ℕ) (a : Fin 4 → ℝ)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN r a (schwartzChain r ψ) =
      schwartzChain r (fun i => schwartzDiagTranslateN 1 a (ψ i)) := by
  induction r with
  | zero =>
    dsimp [schwartzChain]
    exact schwartzDiagTranslateN_fin0 a (momentumWavepacketSchwartz 0 0)
  | succ k ih =>
    dsimp [schwartzChain]
    rw [schwartzDiagTranslateN_schwartzPrepend, ih]
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma translateIndexedSchwartz_indexedChain (r : ℕ) (a : Fin 4 → ℝ)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    translateIndexedSchwartz r a (indexedChain ι r Ψ) =
      indexedChain ι r (fun i α => schwartzDiagTranslateN 1 a (Ψ i α)) := by
  funext γ
  dsimp [translateIndexedSchwartz]
  rw [indexedChain_apply, indexedChain_apply, schwartzDiagTranslateN_schwartzChain]

theorem translate_haagRuelleChainVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (r : ℕ) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (t : ℝ) :
    D.translate a (haagRuelleChainVec D r s f t) =
      haagRuelleChainVec D r s (fun i => translateWavepacket m D.hm a (f i)) (t + a 0) := by
  unfold haagRuelleChainVec haagRuelleChain
  dsimp [IsolatedMassShellData.translate]
  rw [wightmanTranslate_wightmanIndexedVec, translateIndexedSchwartz_indexedChain]
  congr 2
  funext i α
  dsimp [haagRuelleIndexedTest]
  rw [schwartzDiagTranslateN_one_haagRuelleTestFn, dualModeWavepacket_translateWavepacket]

theorem translate_haagRuelleOutVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    D.translate a (haagRuelleOutVec D r s f hf) =
      haagRuelleOutVec D r s (fun i => translateWavepacket m D.hm a (f i))
        (fun _ _ hij => (velocityDisjoint_translateWavepacket_iff D.hm a).mpr (hf hij)) := by
  have h1 := ((D.translate a).continuous.tendsto _).comp
    (tendsto_haagRuelleChainVec_atTop D r s f hf)
  have h_shift : Tendsto (fun t : ℝ => t + a 0) atTop atTop :=
    Filter.tendsto_atTop.mpr fun b =>
      Filter.eventually_atTop.mpr ⟨b - a 0, fun t ht => by linarith⟩
  have h2 := (tendsto_haagRuelleChainVec_atTop D r s
    (fun i => translateWavepacket m D.hm a (f i))
    (fun _ _ hij => (velocityDisjoint_translateWavepacket_iff D.hm a).mpr (hf hij))).comp h_shift
  have h_eq : (fun t : ℝ => D.translate a (haagRuelleChainVec D r s f t)) =
      fun t : ℝ => haagRuelleChainVec D r s
        (fun i => translateWavepacket m D.hm a (f i)) (t + a 0) :=
    funext fun t => translate_haagRuelleChainVec D a r s f t
  change Tendsto (fun t : ℝ => D.translate a (haagRuelleChainVec D r s f t)) atTop
    (𝓝 (D.translate a (haagRuelleOutVec D r s f hf))) at h1
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 h2

theorem translate_haagRuelleInVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    D.translate a (haagRuelleInVec D r s f hf) =
      haagRuelleInVec D r s (fun i => translateWavepacket m D.hm a (f i))
        (fun _ _ hij => (velocityDisjoint_translateWavepacket_iff D.hm a).mpr (hf hij)) := by
  have h1 := ((D.translate a).continuous.tendsto _).comp
    (tendsto_haagRuelleChainVec_atBot D r s f hf)
  have h_shift : Tendsto (fun t : ℝ => t + a 0) atBot atBot :=
    Filter.tendsto_atBot.mpr fun b =>
      Filter.eventually_atBot.mpr ⟨b - a 0, fun t ht => by linarith⟩
  have h2 := (tendsto_haagRuelleChainVec_atBot D r s
    (fun i => translateWavepacket m D.hm a (f i))
    (fun _ _ hij => (velocityDisjoint_translateWavepacket_iff D.hm a).mpr (hf hij))).comp h_shift
  have h_eq : (fun t : ℝ => D.translate a (haagRuelleChainVec D r s f t)) =
      fun t : ℝ => haagRuelleChainVec D r s
        (fun i => translateWavepacket m D.hm a (f i)) (t + a 0) :=
    funext fun t => translate_haagRuelleChainVec D a r s f t
  change Tendsto (fun t : ℝ => D.translate a (haagRuelleChainVec D r s f t)) atBot
    (𝓝 (D.translate a (haagRuelleInVec D r s f hf))) at h1
  rw [h_eq] at h1
  exact tendsto_nhds_unique h1 h2

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_inv_one_add_abs_atTop :
    Tendsto (fun t : ℝ => (1 + |t|)⁻¹) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨ε⁻¹, fun t ht => ?_⟩
  have ht0 : 0 < ε⁻¹ := inv_pos.mpr hε
  have ht_pos : 0 < t := lt_of_lt_of_le ht0 ht
  have h_den : ε⁻¹ < 1 + |t| := by
    rw [abs_of_pos ht_pos]
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  exact (inv_lt_iff_one_lt_mul₀ (by positivity)).mpr (by
    calc 1 = ε⁻¹ * ε := (inv_mul_cancel₀ hε.ne').symm
      _ < (1 + |t|) * ε := mul_lt_mul_of_pos_right h_den hε
      _ = ε * (1 + |t|) := mul_comm _ _)

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_inv_one_add_abs_atBot :
    Tendsto (fun t : ℝ => (1 + |t|)⁻¹) atBot (𝓝 0) := by
  have h := tendsto_inv_one_add_abs_atTop.comp Filter.tendsto_neg_atBot_atTop
  refine h.congr fun t => ?_
  dsimp only [Function.comp_def]
  rw [abs_neg]

lemma norm_haagRuelleChainVec_sub_perm_decay
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (σ : Equiv.Perm (Fin r)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖haagRuelleChainVec D r s f t -
        η ^ permInversions σ • haagRuelleChainVec D r (s ∘ σ) (f ∘ σ) t‖ * (1 + |t|) ^ N ≤ C := by
  rcases r with _ | _ | r'
  · have hσ : σ = 1 := by ext i; exact i.elim0
    subst hσ
    refine ⟨0, le_rfl, fun t => ?_⟩
    simp [permInversions_one]
  · have hσ : σ = 1 := by
      apply Equiv.ext
      intro i
      exact (Fin.eq_zero (σ i)).trans (Fin.eq_zero i).symm
    subst hσ
    refine ⟨0, le_rfl, fun t => ?_⟩
    simp [permInversions_one]
  · let r := r' + 2
    let d_of : Fin r × Fin r → ℝ := fun ij =>
      if hij : ij.1 ≠ ij.2 then (exists_pos_sep_of_velocityDisjoint D.hm (hf hij)).choose else 1
    have hd_pos : ∀ ij : Fin r × Fin r, 0 < d_of ij := fun ij => by
      dsimp [d_of]
      by_cases hij : ij.1 ≠ ij.2
      · rw [dif_pos hij]
        exact (exists_pos_sep_of_velocityDisjoint D.hm (hf hij)).choose_spec.1
      · rw [dif_neg hij]
        exact zero_lt_one
    let d_min : ℝ := Finset.univ.inf' ⟨(0, 0), Finset.mem_univ _⟩ d_of
    have hdmin_pos : 0 < d_min :=
      (Finset.lt_inf'_iff (Finset.univ_nonempty)).mpr fun ij _ => hd_pos ij
    let r_cone : ℝ := d_min / 6
    have hr_cone : 0 < r_cone := by positivity
    let Ψ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
      fun i t => haagRuelleIndexedTest D (s i) (f i) t
    let Φ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
      fun i t => haagRuelleCoreIndexedTest D (s i) (f i) r_cone hr_cone t
    have hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i) :=
      fun i => indexedTestPolyGrowth_haagRuelle D (s i) (f i)
    have hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ i) :=
      fun i => indexedTestPolyGrowth_haagRuelleCore D (s i) (f i) r_cone hr_cone
    have h_diff_dec : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Ψ i t α - Φ i t α) :=
      fun i => by
        have h_sub : (fun t α => Ψ i t α - Φ i t α) =
            fun t => haagRuelleTailIndexedTest D (s i) (f i) r_cone hr_cone t := by
          ext t α x
          simp only [Ψ, Φ]
          rw [← haagRuelleIndexedTest_sub_core D (s i) (f i) r_cone hr_cone t α]
        rw [h_sub]
        exact indexedTestRapidDecay_haagRuelleTail D (s i) (f i) r_cone hr_cone
    obtain ⟨C1, hC1_nn, hC1_bd⟩ := norm_indexedChain_sub_rapid_decay D.wightman.WData r Ψ Φ
      hΨ_poly hΦ_poly h_diff_dec N
    obtain ⟨C2, hC2_nn, hC2_bd⟩ := norm_indexedChain_sub_rapid_decay D.wightman.WData r
      (fun i t => Ψ (σ i) t) (fun i t => Φ (σ i) t)
      (fun i => hΨ_poly (σ i)) (fun i => hΦ_poly (σ i)) (fun i => h_diff_dec (σ i)) N
    obtain ⟨deg_p, C_p, hCp_nn, hCp_bd⟩ :=
      norm_indexedChain_poly_growth D.wightman.WData r Ψ hΨ_poly
    obtain ⟨deg_q, C_q, hCq_nn, hCq_bd⟩ :=
      norm_indexedChain_poly_growth D.wightman.WData r (fun i t => Ψ (σ i) t)
        (fun i => hΨ_poly (σ i))
    have h_η_norm : ‖η ^ permInversions σ‖ = 1 := by
      rw [norm_pow]
      rcases D.mode.hη with h1 | h1 <;> simp [h1]
    let C_small : ℝ := C_p * 2 ^ (deg_p + N) + C_q * 2 ^ (deg_q + N)
    let C_large : ℝ := C1 + C2
    refine ⟨max C_small C_large, le_trans (by positivity) (le_max_left _ _), fun t => ?_⟩
    have h_lhs : haagRuelleChainVec D r s f t =
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) := rfl
    have h_rhs : haagRuelleChainVec D r (s ∘ σ) (f ∘ σ) t =
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t)) := rfl
    rw [h_lhs, h_rhs]
    have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
    by_cases ht1 : |t| < 1
    · have ht2 : 1 + |t| ≤ 2 := by linarith
      have ht_ge0 : 0 ≤ 1 + |t| := by positivity
      calc ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
              η ^ permInversions σ •
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t))‖ *
              (1 + |t|) ^ N
          ≤ (‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t))‖ +
                ‖η ^ permInversions σ •
                  wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t))‖) *
              (1 + |t|) ^ N := mul_le_mul_of_nonneg_right (norm_sub_le _ _) ht_nn
        _ = ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t))‖ *
                (1 + |t|) ^ N +
              ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t))‖ *
                (1 + |t|) ^ N := by
            rw [norm_smul, h_η_norm, one_mul, add_mul]
        _ ≤ C_p * (1 + |t|) ^ deg_p * (1 + |t|) ^ N +
              C_q * (1 + |t|) ^ deg_q * (1 + |t|) ^ N :=
            add_le_add (mul_le_mul_of_nonneg_right (hCp_bd t) ht_nn)
              (mul_le_mul_of_nonneg_right (hCq_bd t) ht_nn)
        _ ≤ C_p * 2 ^ (deg_p + N) + C_q * 2 ^ (deg_q + N) := by
            refine add_le_add ?_ ?_
            · calc C_p * (1 + |t|) ^ deg_p * (1 + |t|) ^ N
                  ≤ C_p * 2 ^ deg_p * 2 ^ N := mul_le_mul
                      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht_ge0 ht2 _) hCp_nn)
                      (pow_le_pow_left₀ ht_ge0 ht2 _) ht_nn (by positivity)
                _ = C_p * 2 ^ (deg_p + N) := by rw [pow_add]; ring
            · calc C_q * (1 + |t|) ^ deg_q * (1 + |t|) ^ N
                  ≤ C_q * 2 ^ deg_q * 2 ^ N := mul_le_mul
                      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht_ge0 ht2 _) hCq_nn)
                      (pow_le_pow_left₀ ht_ge0 ht2 _) ht_nn (by positivity)
                _ = C_q * 2 ^ (deg_q + N) := by rw [pow_add]; ring
        _ = C_small := rfl
        _ ≤ max C_small C_large := le_max_left _ _
    · have ht_ge : 1 ≤ |t| := not_lt.mp ht1
      have hsp : Pairwise fun i j : Fin r => ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
          x₁ ∈ tsupport (Φ i t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          x₂ ∈ tsupport (Φ j t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          is_spacelike (x₁ 0 - x₂ 0) := fun i j hij α₁ α₂ x₁ x₂ hx₁ hx₂ => by
        have hx₁' : x₁ ∈ tsupport (velocityConeCutoff m D.hm
            (dualModeWavepacket D (s i) α₁ (f i)) r_cone hr_cone t) :=
          tsupport_timeModCoreTestFn_subset D.hm
            (dualModeWavepacket D (s i) α₁ (f i)) _ _ _ r_cone hr_cone t hx₁
        have hx₂' : x₂ ∈ tsupport (velocityConeCutoff m D.hm
            (dualModeWavepacket D (s j) α₂ (f j)) r_cone hr_cone t) :=
          tsupport_timeModCoreTestFn_subset D.hm
            (dualModeWavepacket D (s j) α₂ (f j)) _ _ _ r_cone hr_cone t hx₂
        have hd_le : 5 * r_cone ≤ d_of (i, j) := by
          have h1 : d_min ≤ d_of (i, j) := Finset.inf'_le d_of (Finset.mem_univ _)
          dsimp [r_cone]
          linarith
        have h_sep_orig := (exists_pos_sep_of_velocityDisjoint D.hm (hf hij)).choose_spec.2
        have h_sep_d : ∀ v₁ ∈ velocitySupport m (dualModeWavepacket D (s i) α₁ (f i)),
            ∀ v₂ ∈ velocitySupport m (dualModeWavepacket D (s j) α₂ (f j)),
            d_of (i, j) ≤ ‖v₁ - v₂‖ := fun v₁ hv₁ v₂ hv₂ => by
          have h_eq_d : d_of (i, j) =
              (exists_pos_sep_of_velocityDisjoint D.hm (hf hij)).choose := by
            dsimp [d_of]
            exact dif_pos hij
          rw [h_eq_d]
          exact h_sep_orig v₁ (velocitySupport_dualModeWavepacket_subset D (s i) α₁ (f i) hv₁)
            v₂ (velocitySupport_dualModeWavepacket_subset D (s j) α₂ (f j) hv₂)
        exact spacelike_velocityConeCutoffs_of_radius D.hm hr_cone hd_le h_sep_d ht_ge hx₁' hx₂'
      have h_perm_core := wightmanIndexedVec_indexedChain_perm_of_pairwise_spacelike
        D.wightman.WData D.locality r (fun i => Φ i t) hsp σ
      change wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) =
        η ^ permInversions σ •
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ (σ i) t))
        at h_perm_core
      have h_split :
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
            η ^ permInversions σ •
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t)) =
          (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))) -
            η ^ permInversions σ •
              (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t)) -
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ (σ i) t))) := by
        rw [smul_sub, h_perm_core]
        abel
      calc ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
              η ^ permInversions σ •
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t))‖ *
              (1 + |t|) ^ N
          ≤ (‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
                  wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))‖ +
                ‖η ^ permInversions σ •
                  (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t)) -
                    wightmanIndexedVec D.wightman.WData r
                      (indexedChain ι r (fun i => Φ (σ i) t)))‖) *
              (1 + |t|) ^ N := by
            rw [h_split]
            exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) ht_nn
        _ = ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))‖ *
                (1 + |t|) ^ N +
              ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ (σ i) t)) -
                wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ (σ i) t))‖ *
                (1 + |t|) ^ N := by
            rw [norm_smul, h_η_norm, one_mul, add_mul]
        _ ≤ C1 + C2 := add_le_add (hC1_bd t) (hC2_bd t)
        _ = C_large := rfl
        _ ≤ max C_small C_large := le_max_right _ _

lemma haagRuelleLimit_perm
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot] (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0))
    (L : ∀ (r : ℕ), (Fin r → Fin D.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → D.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec D r s f) F (𝓝 (L r s f hf)))
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (σ : Equiv.Perm (Fin r)) :
    L r s f hf =
      η ^ permInversions σ •
        L r (s ∘ σ) (f ∘ σ) (fun _ _ hij => hf (σ.injective.ne hij)) := by
  have h_lim_sub : Tendsto
      (fun t : ℝ => haagRuelleChainVec D r s f t -
        η ^ permInversions σ • haagRuelleChainVec D r (s ∘ σ) (f ∘ σ) t) F
      (𝓝 (L r s f hf - η ^ permInversions σ •
        L r (s ∘ σ) (f ∘ σ) (fun _ _ hij => hf (σ.injective.ne hij)))) :=
    (hL r s f hf).sub ((hL r (s ∘ σ) (f ∘ σ) (fun _ _ hij => hf (σ.injective.ne hij))).const_smul _)
  obtain ⟨C, hC_nn, hC_bd⟩ := norm_haagRuelleChainVec_sub_perm_decay D r s f hf σ 1
  have h_zero : Tendsto
      (fun t : ℝ => haagRuelleChainVec D r s f t -
        η ^ permInversions σ • haagRuelleChainVec D r (s ∘ σ) (f ∘ σ) t) F (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using hF_inv.const_mul C)
      (fun t => norm_nonneg _) (fun t => ?_))
    have ht_pos : 0 < 1 + |t| := by positivity
    exact (le_mul_inv_iff₀ ht_pos).mpr (by simpa [pow_one] using hC_bd t)
  exact sub_eq_zero.mp (tendsto_nhds_unique h_lim_sub h_zero)

theorem haagRuelleOutVec_perm
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (σ : Equiv.Perm (Fin r)) :
    haagRuelleOutVec D r s f hf = η ^ permInversions σ •
      haagRuelleOutVec D r (s ∘ σ) (f ∘ σ) (fun _ _ hij => hf (σ.injective.ne hij)) :=
  haagRuelleLimit_perm D tendsto_inv_one_add_abs_atTop (haagRuelleOutVec D)
    (tendsto_haagRuelleChainVec_atTop D) r s f hf σ

theorem haagRuelleInVec_perm
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (σ : Equiv.Perm (Fin r)) :
    haagRuelleInVec D r s f hf = η ^ permInversions σ •
      haagRuelleInVec D r (s ∘ σ) (f ∘ σ) (fun _ _ hij => hf (σ.injective.ne hij)) :=
  haagRuelleLimit_perm D tendsto_inv_one_add_abs_atBot (haagRuelleInVec D)
    (tendsto_haagRuelleChainVec_atBot D) r s f hf σ

lemma inner_haagRuelleChainVec_vacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s : Fin (k + 1) → Fin D.mode.ν)
    (f : Fin (k + 1) → SmoothWavepacket) (t : ℝ) :
    ⟪haagRuelleChainVec D (k + 1) s f t, D.vacuum⟫_ℂ = 0 := by
  have h_chain : haagRuelleChain D (k + 1) s f t =
      haagRuelleApply D (s 0) (f 0) t k (haagRuelleChain D k (s ∘ Fin.succ) (f ∘ Fin.succ) t) :=
    rfl
  have h_vac0 : D.vacuum = wightmanIndexedVec D.wightman.WData 0 (vacuumIndexedSchwartz ι) :=
    (wightmanIndexedVec_vacuum D.wightman.WData).symm
  dsimp [haagRuelleChainVec]
  rw [h_chain, h_vac0, inner_haagRuelleApply_eq_adj]
  change ⟪wightmanIndexedVec D.wightman.WData k _, haagRuelleAdjVacCreate D (s 0) (f 0) t⟫_ℂ = 0
  rw [haagRuelleAdjVacCreate_eq_zero, inner_zero_right]

lemma inner_haagRuelleLimit_vacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot]
    (L : ∀ (r : ℕ), (Fin r → Fin D.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → D.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec D r s f) F (𝓝 (L r s f hf)))
    (k : ℕ) (s : Fin (k + 1) → Fin D.mode.ν) (f : Fin (k + 1) → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (f i) (f j)) :
    ⟪L (k + 1) s f hf, D.vacuum⟫_ℂ = 0 := by
  have h_inn := Filter.Tendsto.inner (𝕜 := ℂ)
    (hL (k + 1) s f hf) (tendsto_const_nhds (x := D.vacuum))
  have h_z : (fun t : ℝ => ⟪haagRuelleChainVec D (k + 1) s f t, D.vacuum⟫_ℂ) = fun _ => 0 :=
    funext fun t => inner_haagRuelleChainVec_vacuum_eq_zero D k s f t
  rw [h_z] at h_inn
  exact tendsto_nhds_unique h_inn tendsto_const_nhds

theorem inner_haagRuelleOutVec_vacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s : Fin (k + 1) → Fin D.mode.ν) (f : Fin (k + 1) → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (f i) (f j)) :
    ⟪haagRuelleOutVec D (k + 1) s f hf, D.vacuum⟫_ℂ = 0 :=
  inner_haagRuelleLimit_vacuum_eq_zero D (haagRuelleOutVec D)
    (tendsto_haagRuelleChainVec_atTop D) k s f hf

theorem inner_vacuum_haagRuelleOutVec_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s : Fin (k + 1) → Fin D.mode.ν) (f : Fin (k + 1) → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (f i) (f j)) :
    ⟪D.vacuum, haagRuelleOutVec D (k + 1) s f hf⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_haagRuelleOutVec_vacuum_eq_zero, map_zero]

theorem inner_haagRuelleInVec_vacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s : Fin (k + 1) → Fin D.mode.ν) (f : Fin (k + 1) → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (f i) (f j)) :
    ⟪haagRuelleInVec D (k + 1) s f hf, D.vacuum⟫_ℂ = 0 :=
  inner_haagRuelleLimit_vacuum_eq_zero D (haagRuelleInVec D)
    (tendsto_haagRuelleChainVec_atBot D) k s f hf

theorem inner_vacuum_haagRuelleInVec_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s : Fin (k + 1) → Fin D.mode.ν) (f : Fin (k + 1) → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (f i) (f j)) :
    ⟪D.vacuum, haagRuelleInVec D (k + 1) s f hf⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_haagRuelleInVec_vacuum_eq_zero, map_zero]

omit [Fintype ι] [DecidableEq ι] in
def zeroWavepacket : SmoothWavepacket where
  amp _ := 0
  smooth := contDiff_const
  compactSupport := HasCompactSupport.zero

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma zeroWavepacket_apply (p : Fin 3 → ℝ) : zeroWavepacket.amp p = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma tsupport_zeroWavepacket : tsupport zeroWavepacket.amp = ∅ := by
  have h : zeroWavepacket.amp = 0 := rfl
  simp [h]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma velocitySupport_zeroWavepacket (m : ℝ) : velocitySupport m zeroWavepacket = ∅ := by
  unfold velocitySupport
  rw [tsupport_zeroWavepacket, Set.image_empty]

omit [Fintype ι] [DecidableEq ι] in
lemma velocityDisjoint_zeroWavepacket_left (m : ℝ) (f : SmoothWavepacket) :
    VelocityDisjoint m zeroWavepacket f := by
  unfold VelocityDisjoint
  rw [velocitySupport_zeroWavepacket]
  exact Set.empty_disjoint _

omit [Fintype ι] [DecidableEq ι] in
def addWavepacket (f₁ f₂ : SmoothWavepacket) : SmoothWavepacket where
  amp p := f₁.amp p + f₂.amp p
  smooth := f₁.smooth.add f₂.smooth
  compactSupport := f₁.compactSupport.add f₂.compactSupport

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma addWavepacket_apply (f₁ f₂ : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (addWavepacket f₁ f₂).amp p = f₁.amp p + f₂.amp p := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma tsupport_addWavepacket_subset (f₁ f₂ : SmoothWavepacket) :
    tsupport (addWavepacket f₁ f₂).amp ⊆ tsupport f₁.amp ∪ tsupport f₂.amp := by
  refine closure_minimal ?_ ((isClosed_tsupport _).union (isClosed_tsupport _))
  intro p hp
  rw [Function.mem_support, addWavepacket_apply] at hp
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  have h1 : f₁.amp p = 0 := image_eq_zero_of_notMem_tsupport hnot.1
  have h2 : f₂.amp p = 0 := image_eq_zero_of_notMem_tsupport hnot.2
  exact hp (by rw [h1, h2, add_zero])

omit [Fintype ι] [DecidableEq ι] in
def smulWavepacket (c : ℂ) (f : SmoothWavepacket) : SmoothWavepacket where
  amp p := c * f.amp p
  smooth := contDiff_const.mul f.smooth
  compactSupport := f.compactSupport.mul_left

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma smulWavepacket_apply (c : ℂ) (f : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (smulWavepacket c f).amp p = c * f.amp p := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma tsupport_smulWavepacket_subset (c : ℂ) (f : SmoothWavepacket) :
    tsupport (smulWavepacket c f).amp ⊆ tsupport f.amp :=
  tsupport_mul_subset_right

omit [Fintype ι] [DecidableEq ι] in
def finsetSumWavepacket {κ : Type*} (u : Finset κ) (g : κ → SmoothWavepacket) :
    SmoothWavepacket where
  amp p := ∑ a ∈ u, (g a).amp p
  smooth := ContDiff.sum fun a _ => (g a).smooth
  compactSupport := by
    classical
    induction u using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | insert a s ha ih =>
      have h_eq : (fun p => ∑ x ∈ insert a s, (g x).amp p) =
          (g a).amp + fun p => ∑ x ∈ s, (g x).amp p := by
        ext p
        simp [Finset.sum_insert ha]
      rw [h_eq]
      exact (g a).compactSupport.add ih

omit [Fintype ι] [DecidableEq ι] in
lemma finsetSumWavepacket_empty {κ : Type*} (g : κ → SmoothWavepacket) :
    finsetSumWavepacket ∅ g = zeroWavepacket := by
  apply SmoothWavepacket.ext
  funext p
  simp [finsetSumWavepacket]

omit [Fintype ι] [DecidableEq ι] in
lemma finsetSumWavepacket_insert {κ : Type*} [DecidableEq κ] (a : κ) (u : Finset κ)
    (ha : a ∉ u) (g : κ → SmoothWavepacket) :
    finsetSumWavepacket (insert a u) g = addWavepacket (g a) (finsetSumWavepacket u g) := by
  apply SmoothWavepacket.ext
  funext p
  simp [finsetSumWavepacket, Finset.sum_insert ha]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma finsetSumWavepacket_apply {κ : Type*} (u : Finset κ)
    (g : κ → SmoothWavepacket) (p : Fin 3 → ℝ) :
    (finsetSumWavepacket u g).amp p = ∑ a ∈ u, (g a).amp p := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma fockOneParticleVec_zero (ν : ℕ) (s : Fin ν) :
    fockOneParticleVec ν s zeroWavepacket = 0 := by
  rw [← inner_self_eq_zero (𝕜 := ℂ), inner_fockOneParticleVec_eq, if_pos rfl]
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma fockOneParticleVec_add (ν : ℕ) (s : Fin ν) (f₁ f₂ : SmoothWavepacket) :
    fockOneParticleVec ν s (addWavepacket f₁ f₂) =
      fockOneParticleVec ν s f₁ + fockOneParticleVec ν s f₂ := by
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_fockOneParticleVec_eq, ite_true]
  have hint : ∀ u v : SmoothWavepacket,
      Integrable (fun p : Fin 3 → ℝ => star (u.amp p) * v.amp p) volume := fun u v =>
    (u.smooth.continuous.star.mul v.smooth.continuous).integrable_of_hasCompactSupport
      v.compactSupport.mul_left
  have h_l : ∀ u : SmoothWavepacket,
      (∫ p : Fin 3 → ℝ, star ((addWavepacket f₁ f₂).amp p) * u.amp p) =
      (∫ p : Fin 3 → ℝ, star (f₁.amp p) * u.amp p) +
        (∫ p : Fin 3 → ℝ, star (f₂.amp p) * u.amp p) := by
    intro u
    have h_fn : (fun p : Fin 3 → ℝ => star ((addWavepacket f₁ f₂).amp p) * u.amp p) =
        fun p => star (f₁.amp p) * u.amp p + star (f₂.amp p) * u.amp p := by
      ext p
      simp [addWavepacket_apply, add_mul]
    rw [h_fn, integral_add (hint f₁ u) (hint f₂ u)]
  have h_r : ∀ u : SmoothWavepacket,
      (∫ p : Fin 3 → ℝ, star (u.amp p) * (addWavepacket f₁ f₂).amp p) =
      (∫ p : Fin 3 → ℝ, star (u.amp p) * f₁.amp p) +
        (∫ p : Fin 3 → ℝ, star (u.amp p) * f₂.amp p) := by
    intro u
    have h_fn : (fun p : Fin 3 → ℝ => star (u.amp p) * (addWavepacket f₁ f₂).amp p) =
        fun p => star (u.amp p) * f₁.amp p + star (u.amp p) * f₂.amp p := by
      ext p
      simp [addWavepacket_apply, mul_add]
    rw [h_fn, integral_add (hint u f₁) (hint u f₂)]
  rw [h_r (addWavepacket f₁ f₂), h_l f₁, h_l f₂, h_r f₁, h_r f₂]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma fockOneParticleVec_smul (ν : ℕ) (s : Fin ν) (c : ℂ) (f : SmoothWavepacket) :
    fockOneParticleVec ν s (smulWavepacket c f) = c • fockOneParticleVec ν s f := by
  rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ)]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_fockOneParticleVec_eq, ite_true]
  have h1 : (∫ p : Fin 3 → ℝ, star ((smulWavepacket c f).amp p) * (smulWavepacket c f).amp p) =
      star c * (c * ∫ p : Fin 3 → ℝ, star (f.amp p) * f.amp p) := by
    have h_fn : (fun p : Fin 3 → ℝ =>
        star ((smulWavepacket c f).amp p) * (smulWavepacket c f).amp p) =
        fun p => (star c * c) * (star (f.amp p) * f.amp p) := by
      ext p
      simp only [smulWavepacket_apply, star_mul']
      ring
    rw [h_fn, integral_const_mul, mul_assoc]
  have h2 : (∫ p : Fin 3 → ℝ, star ((smulWavepacket c f).amp p) * f.amp p) =
      star c * ∫ p : Fin 3 → ℝ, star (f.amp p) * f.amp p := by
    have h_fn : (fun p : Fin 3 → ℝ => star ((smulWavepacket c f).amp p) * f.amp p) =
        fun p => star c * (star (f.amp p) * f.amp p) := by
      ext p
      simp only [smulWavepacket_apply, star_mul']
      ring
    rw [h_fn, integral_const_mul]
  have h3 : (∫ p : Fin 3 → ℝ, star (f.amp p) * (smulWavepacket c f).amp p) =
      c * ∫ p : Fin 3 → ℝ, star (f.amp p) * f.amp p := by
    have h_fn : (fun p : Fin 3 → ℝ => star (f.amp p) * (smulWavepacket c f).amp p) =
        fun p => c * (star (f.amp p) * f.amp p) := by
      ext p
      simp only [smulWavepacket_apply]
      ring
    rw [h_fn, integral_const_mul]
  rw [h1, h2, h3]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma fockOneParticleVec_finsetSum {κ : Type*} (ν : ℕ) (s : Fin ν)
    (u : Finset κ) (g : κ → SmoothWavepacket) :
    fockOneParticleVec ν s (finsetSumWavepacket u g) =
      ∑ a ∈ u, fockOneParticleVec ν s (g a) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [finsetSumWavepacket_empty, fockOneParticleVec_zero]
  | insert a s' ha ih =>
    rw [finsetSumWavepacket_insert a s' ha, Finset.sum_insert ha, fockOneParticleVec_add, ih]

lemma dualModeWavepacket_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) :
    dualModeWavepacket D s α zeroWavepacket = zeroWavepacket := by
  apply SmoothWavepacket.ext
  funext p
  simp [dualModeWavepacket_apply]

lemma dualModeWavepacket_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) (f₁ f₂ : SmoothWavepacket) :
    dualModeWavepacket D s α (addWavepacket f₁ f₂) =
      addWavepacket (dualModeWavepacket D s α f₁) (dualModeWavepacket D s α f₂) := by
  apply SmoothWavepacket.ext
  funext p
  simp [dualModeWavepacket_apply, mul_add]

lemma dualModeWavepacket_smul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (α : ι) (c : ℂ) (f : SmoothWavepacket) :
    dualModeWavepacket D s α (smulWavepacket c f) =
      smulWavepacket c (dualModeWavepacket D s α f) := by
  apply SmoothWavepacket.ext
  funext p
  simp [dualModeWavepacket_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma haagRuelleTestFn_zero (m M : ℝ) (hm : 0 < m) (hM : m < M) (t : ℝ) :
    haagRuelleTestFn m M hm hM zeroWavepacket t = 0 := by
  apply minkowskiFourier_injective
  intro p
  let q : Fin 4 → ℝ := -(p 0)
  have hp : p = fun _ : Fin 1 => -q := by
    ext i μ
    rw [Subsingleton.elim i 0]
    simp [q]
  rw [hp, minkowskiFourier_haagRuelleTestFn, ← minkowskiFourierCLM_apply, map_zero]
  simp [timeModMomAmp, haagRuelleBaseAmp]

omit [Fintype ι] [DecidableEq ι] in
lemma haagRuelleTestFn_add (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (f₁ f₂ : SmoothWavepacket) (t : ℝ) :
    haagRuelleTestFn m M hm hM (addWavepacket f₁ f₂) t =
      haagRuelleTestFn m M hm hM f₁ t + haagRuelleTestFn m M hm hM f₂ t := by
  apply minkowskiFourier_injective
  intro p
  let q : Fin 4 → ℝ := -(p 0)
  have hp : p = fun _ : Fin 1 => -q := by
    ext i μ
    rw [Subsingleton.elim i 0]
    simp [q]
  rw [hp, minkowskiFourier_haagRuelleTestFn, ← minkowskiFourierCLM_apply, map_add,
    _root_.add_apply, minkowskiFourierCLM_apply, minkowskiFourierCLM_apply,
    minkowskiFourier_haagRuelleTestFn, minkowskiFourier_haagRuelleTestFn]
  simp only [timeModMomAmp, haagRuelleBaseAmp, addWavepacket_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma haagRuelleTestFn_smul (m M : ℝ) (hm : 0 < m) (hM : m < M)
    (c : ℂ) (f : SmoothWavepacket) (t : ℝ) :
    haagRuelleTestFn m M hm hM (smulWavepacket c f) t =
      c • haagRuelleTestFn m M hm hM f t := by
  apply minkowskiFourier_injective
  intro p
  let q : Fin 4 → ℝ := -(p 0)
  have hp : p = fun _ : Fin 1 => -q := by
    ext i μ
    rw [Subsingleton.elim i 0]
    simp [q]
  rw [hp, minkowskiFourier_haagRuelleTestFn, ← minkowskiFourierCLM_apply, map_smul,
    _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
    minkowskiFourier_haagRuelleTestFn]
  simp only [timeModMomAmp, haagRuelleBaseAmp, smulWavepacket_apply]
  ring

lemma haagRuelleChainVec_update_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (t : ℝ) :
    haagRuelleChainVec D r s (Function.update f j zeroWavepacket) t = 0 := by
  unfold haagRuelleChainVec haagRuelleChain
  have h_eq : (fun i => haagRuelleIndexedTest D (s i) (Function.update f j zeroWavepacket i) t) =
      Function.update (fun i => haagRuelleIndexedTest D (s i) (f i) t) j 0 := by
    ext i α x
    by_cases hi : i = j
    · subst hi
      simp [haagRuelleIndexedTest, dualModeWavepacket_zero, haagRuelleTestFn_zero]
    · simp [Function.update_of_ne hi]
  rw [h_eq, wightmanIndexedVec_indexedChain_update_zero]

lemma haagRuelleChainVec_update_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (g₁ g₂ : SmoothWavepacket) (t : ℝ) :
    haagRuelleChainVec D r s (Function.update f j (addWavepacket g₁ g₂)) t =
      haagRuelleChainVec D r s (Function.update f j g₁) t +
        haagRuelleChainVec D r s (Function.update f j g₂) t := by
  unfold haagRuelleChainVec haagRuelleChain
  have h_eq :
      (fun i => haagRuelleIndexedTest D (s i) (Function.update f j (addWavepacket g₁ g₂) i) t) =
      Function.update (fun i => haagRuelleIndexedTest D (s i) (f i) t) j
        (haagRuelleIndexedTest D (s j) g₁ t + haagRuelleIndexedTest D (s j) g₂ t) := by
    ext i α x
    by_cases hi : i = j
    · subst hi
      simp [haagRuelleIndexedTest, dualModeWavepacket_add, haagRuelleTestFn_add]
    · simp [Function.update_of_ne hi]
  have h1 : (fun i => haagRuelleIndexedTest D (s i) (Function.update f j g₁ i) t) =
      Function.update (fun i => haagRuelleIndexedTest D (s i) (f i) t) j
        (haagRuelleIndexedTest D (s j) g₁ t) := by
    ext i α x
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have h2 : (fun i => haagRuelleIndexedTest D (s i) (Function.update f j g₂ i) t) =
      Function.update (fun i => haagRuelleIndexedTest D (s i) (f i) t) j
        (haagRuelleIndexedTest D (s j) g₂ t) := by
    ext i α x
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h_eq, h1, h2, wightmanIndexedVec_indexedChain_update_add]

lemma haagRuelleChainVec_update_smul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (c : ℂ) (g : SmoothWavepacket) (t : ℝ) :
    haagRuelleChainVec D r s (Function.update f j (smulWavepacket c g)) t =
      c • haagRuelleChainVec D r s (Function.update f j g) t := by
  unfold haagRuelleChainVec haagRuelleChain
  have h_eq :
      (fun i => haagRuelleIndexedTest D (s i) (Function.update f j (smulWavepacket c g) i) t) =
      Function.update (fun i => haagRuelleIndexedTest D (s i) (f i) t) j
        (c • haagRuelleIndexedTest D (s j) g t) := by
    ext i α x
    by_cases hi : i = j
    · subst hi
      simp [haagRuelleIndexedTest, dualModeWavepacket_smul, haagRuelleTestFn_smul]
    · simp [Function.update_of_ne hi]
  have h1 : (fun i => haagRuelleIndexedTest D (s i) (Function.update f j g i) t) =
      Function.update (fun i => haagRuelleIndexedTest D (s i) (f i) t) j
        (haagRuelleIndexedTest D (s j) g t) := by
    ext i α x
    by_cases hi : i = j
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [h_eq, h1, wightmanIndexedVec_indexedChain_update_smul]

lemma haagRuelleChainVec_update_finset_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {κ : Type*} (u : Finset κ)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (g : κ → SmoothWavepacket) (t : ℝ) :
    haagRuelleChainVec D r s (Function.update f j (finsetSumWavepacket u g)) t =
      ∑ a ∈ u, haagRuelleChainVec D r s (Function.update f j (g a)) t := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    rw [finsetSumWavepacket_empty, Finset.sum_empty, haagRuelleChainVec_update_zero]
  | insert a s' ha ih =>
    rw [finsetSumWavepacket_insert a s' ha, Finset.sum_insert ha,
      haagRuelleChainVec_update_add, ih]

lemma haagRuelleLimit_update_finset_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot]
    (L : ∀ (r : ℕ), (Fin r → Fin D.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → D.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec D r s f) F (𝓝 (L r s f hf)))
    {κ : Type*} (u : Finset κ)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (g : κ → SmoothWavepacket)
    (hf_sum : Pairwise fun i₁ i₂ =>
      VelocityDisjoint m (Function.update f j (finsetSumWavepacket u g) i₁)
        (Function.update f j (finsetSumWavepacket u g) i₂))
    (hf_each : ∀ a ∈ u, Pairwise fun i₁ i₂ =>
      VelocityDisjoint m (Function.update f j (g a) i₁) (Function.update f j (g a) i₂)) :
    L r s (Function.update f j (finsetSumWavepacket u g)) hf_sum =
      ∑ a ∈ u.attach, L r s (Function.update f j (g a.1)) (hf_each a.1 a.2) := by
  have h1 := hL r s (Function.update f j (finsetSumWavepacket u g)) hf_sum
  have h_sum_t : (haagRuelleChainVec D r s (Function.update f j (finsetSumWavepacket u g))) =
      fun t => ∑ a ∈ u.attach, haagRuelleChainVec D r s (Function.update f j (g a.1)) t := by
    funext t
    rw [haagRuelleChainVec_update_finset_sum]
    exact (Finset.sum_attach u fun a => haagRuelleChainVec D r s (Function.update f j (g a)) t).symm
  have h2 : Tendsto
      (fun t => ∑ a ∈ u.attach, haagRuelleChainVec D r s (Function.update f j (g a.1)) t) F
      (𝓝 (∑ a ∈ u.attach, L r s (Function.update f j (g a.1)) (hf_each a.1 a.2))) :=
    tendsto_finsetSum u.attach fun a _ => hL r s (Function.update f j (g a.1)) (hf_each a.1 a.2)
  rw [h_sum_t] at h1
  exact tendsto_nhds_unique h1 h2

theorem haagRuelleOutVec_update_finset_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {κ : Type*} (u : Finset κ)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (g : κ → SmoothWavepacket)
    (hf_sum : Pairwise fun i₁ i₂ =>
      VelocityDisjoint m (Function.update f j (finsetSumWavepacket u g) i₁)
        (Function.update f j (finsetSumWavepacket u g) i₂))
    (hf_each : ∀ a ∈ u, Pairwise fun i₁ i₂ =>
      VelocityDisjoint m (Function.update f j (g a) i₁) (Function.update f j (g a) i₂)) :
    haagRuelleOutVec D r s (Function.update f j (finsetSumWavepacket u g)) hf_sum =
      ∑ a ∈ u.attach, haagRuelleOutVec D r s (Function.update f j (g a.1)) (hf_each a.1 a.2) :=
  haagRuelleLimit_update_finset_sum D (haagRuelleOutVec D) (tendsto_haagRuelleChainVec_atTop D)
    u r j s f g hf_sum hf_each

theorem haagRuelleInVec_update_finset_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {κ : Type*} (u : Finset κ)
    (r : ℕ) (j : Fin r) (s : Fin r → Fin D.mode.ν)
    (f : Fin r → SmoothWavepacket) (g : κ → SmoothWavepacket)
    (hf_sum : Pairwise fun i₁ i₂ =>
      VelocityDisjoint m (Function.update f j (finsetSumWavepacket u g) i₁)
        (Function.update f j (finsetSumWavepacket u g) i₂))
    (hf_each : ∀ a ∈ u, Pairwise fun i₁ i₂ =>
      VelocityDisjoint m (Function.update f j (g a) i₁) (Function.update f j (g a) i₂)) :
    haagRuelleInVec D r s (Function.update f j (finsetSumWavepacket u g)) hf_sum =
      ∑ a ∈ u.attach, haagRuelleInVec D r s (Function.update f j (g a.1)) (hf_each a.1 a.2) :=
  haagRuelleLimit_update_finset_sum D (haagRuelleInVec D) (tendsto_haagRuelleChainVec_atBot D)
    u r j s f g hf_sum hf_each

omit [Fintype ι] [DecidableEq ι] in
theorem exists_smoothWavepacket_partition_diam_lt
    {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (g : Fin n → SmoothWavepacket),
      (finsetSumWavepacket Finset.univ g = f) ∧
      (∀ i : Fin n, tsupport (g i).amp ⊆ tsupport f.amp) ∧
      (∀ i : Fin n, ∀ v₁ ∈ velocitySupport m (g i), ∀ v₂ ∈ velocitySupport m (g i),
        ‖v₁ - v₂‖ < ε) := by
  classical
  have hr_spec : ∀ c : Fin 3 → ℝ, ∃ r : ℝ, 0 < r ∧
      ∀ p ∈ Metric.closedBall c (2 * r), ‖velocityVec m p - velocityVec m c‖ < ε / 2 := by
    intro c
    have hcont := Metric.continuousAt_iff.mp
      ((contDiff_velocityVec hm).continuous.continuousAt (x := c)) (ε / 2) (half_pos hε)
    obtain ⟨δ, hδ_pos, hδ⟩ := hcont
    refine ⟨δ / 3, by positivity, fun p hp => ?_⟩
    rw [Metric.mem_closedBall] at hp
    have hlt : dist p c < δ := lt_of_le_of_lt hp (by linarith)
    simpa [dist_eq_norm] using hδ hlt
  choose r_of hr_pos hr_bd using hr_spec
  let b_of : ∀ c : Fin 3 → ℝ, ContDiffBump c :=
    fun c => ⟨r_of c, 2 * r_of c, hr_pos c, by linarith [hr_pos c]⟩
  let K : Set (Fin 3 → ℝ) := tsupport f.amp
  have hK_cov : K ⊆ ⋃ c : Fin 3 → ℝ, Metric.ball c (r_of c) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hr_pos x)⟩
  obtain ⟨F_centers, hF_cov⟩ := f.compactSupport.isCompact.elim_finite_subcover
    (fun c : Fin 3 → ℝ => Metric.ball c (r_of c)) (fun _ => Metric.isOpen_ball) hK_cov
  let U : Set (Fin 3 → ℝ) := ⋃ c ∈ F_centers, Metric.ball c (r_of c)
  have hU_open : IsOpen U := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  let S : (Fin 3 → ℝ) → ℝ := fun x => ∑ c ∈ F_centers, (b_of c) x
  have hS_smooth : ContDiff ℝ (⊤ : ℕ∞) S :=
    ContDiff.sum fun c _ => (b_of c).contDiff
  have hS_pos : ∀ x ∈ U, 1 ≤ S x := by
    intro x hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨c₀, hc₀, hball⟩ := hx
    have h_one : (b_of c₀) x = 1 :=
      (b_of c₀).one_of_mem_closedBall (Metric.ball_subset_closedBall hball)
    have h_le : (b_of c₀) x ≤ ∑ c ∈ F_centers, (b_of c) x :=
      Finset.single_le_sum (fun c _ => (b_of c).nonneg) hc₀
    linarith
  let piece_amp : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℂ := fun c x =>
    if x ∈ U then f.amp x * (((b_of c) x / S x : ℝ) : ℂ) else 0
  have h_supp_sub : ∀ c : Fin 3 → ℝ, Function.support (piece_amp c) ⊆ tsupport f.amp := by
    intro c x hx
    rw [Function.mem_support] at hx
    by_contra hnot
    have hf0 : f.amp x = 0 := image_eq_zero_of_notMem_tsupport hnot
    apply hx
    dsimp [piece_amp]
    split_ifs <;> simp [hf0]
  have h_ball_sub : ∀ c : Fin 3 → ℝ,
      Function.support (piece_amp c) ⊆ Metric.closedBall c (2 * r_of c) := by
    intro c x hx
    rw [Function.mem_support] at hx
    by_contra hnot
    rw [Metric.mem_closedBall, not_le] at hnot
    have hb0 : (b_of c) x = 0 := (b_of c).zero_of_le_dist hnot.le
    apply hx
    dsimp [piece_amp]
    split_ifs <;> simp [hb0]
  have h_smooth : ∀ c : Fin 3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) (piece_amp c) := by
    intro c
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxU : x ∈ U
    · have hSx : S x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hS_pos x hxU))
      have h_raw : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y : Fin 3 → ℝ => f.amp y * (((b_of c) y / S y : ℝ) : ℂ)) x := by
        refine (f.smooth.contDiffAt).mul ?_
        refine Complex.ofRealCLM.contDiff.contDiffAt.comp x ?_
        exact (b_of c).contDiff.contDiffAt.div hS_smooth.contDiffAt hSx
      refine h_raw.congr_of_eventuallyEq ?_
      filter_upwards [hU_open.mem_nhds hxU] with y hy
      dsimp [piece_amp]
      exact if_pos hy
    · have hxK : x ∈ (tsupport f.amp)ᶜ := fun hx => hxU (hF_cov hx)
      have hKc_open : IsOpen (tsupport f.amp)ᶜ := (isClosed_tsupport _).isOpen_compl
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hKc_open.mem_nhds hxK] with y hy
      have hf0 : f.amp y = 0 := image_eq_zero_of_notMem_tsupport hy
      dsimp [piece_amp]
      split_ifs <;> simp [hf0]
  let piece : (Fin 3 → ℝ) → SmoothWavepacket := fun c =>
    { amp := piece_amp c
      smooth := h_smooth c
      compactSupport := HasCompactSupport.of_support_subset_isCompact
        f.compactSupport.isCompact (h_supp_sub c) }
  let e : F_centers ≃ Fin F_centers.card := F_centers.equivFin
  let g : Fin F_centers.card → SmoothWavepacket := fun i => piece (e.symm i).1
  refine ⟨F_centers.card, g, ?_, ?_, ?_⟩
  · apply SmoothWavepacket.ext
    funext x
    rw [finsetSumWavepacket_apply]
    have h_e : (∑ i : Fin F_centers.card, (g i).amp x) =
        ∑ c ∈ F_centers, (piece c).amp x := by
      rw [← Finset.sum_coe_sort F_centers fun c => (piece c).amp x]
      exact e.symm.sum_comp fun c : F_centers => (piece c.1).amp x
    rw [h_e]
    dsimp [piece, piece_amp]
    by_cases hxU : x ∈ U
    · have hSx : S x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hS_pos x hxU))
      simp only [hxU, ↓reduceIte, ← Finset.mul_sum, ← Complex.ofReal_sum]
      have h_sum_div : (∑ c ∈ F_centers, (b_of c) x / S x) = 1 := by
        rw [← Finset.sum_div]
        exact div_self hSx
      rw [h_sum_div]
      simp
    · have hxK : x ∉ tsupport f.amp := fun hx => hxU (hF_cov hx)
      have hf0 : f.amp x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [hxU, hf0]
  · intro i
    exact closure_minimal (h_supp_sub (e.symm i).1) (isClosed_tsupport _)
  · intro i v₁ hv₁ v₂ hv₂
    obtain ⟨p₁, hp₁, rfl⟩ := hv₁
    obtain ⟨p₂, hp₂, rfl⟩ := hv₂
    let c := (e.symm i).1
    have hsub : tsupport (g i).amp ⊆ Metric.closedBall c (2 * r_of c) :=
      closure_minimal (h_ball_sub c) Metric.isClosed_closedBall
    have h1 := hr_bd c p₁ (hsub hp₁)
    have h2 := hr_bd c p₂ (hsub hp₂)
    calc ‖velocityVec m p₁ - velocityVec m p₂‖
        = ‖(velocityVec m p₁ - velocityVec m c) + (velocityVec m c - velocityVec m p₂)‖ := by
          abel_nf
      _ ≤ ‖velocityVec m p₁ - velocityVec m c‖ + ‖velocityVec m c - velocityVec m p₂‖ :=
          norm_add_le _ _
      _ = ‖velocityVec m p₁ - velocityVec m c‖ + ‖velocityVec m p₂ - velocityVec m c‖ := by
          rw [norm_sub_rev (velocityVec m c)]
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε

omit [Fintype ι] [DecidableEq ι] in
lemma exists_single_overlap_slot {m : ℝ} (k : ℕ)
    (g : Fin (k + 1) → SmoothWavepacket)
    {d_g : ℝ}
    (hd_g : ∀ u v : Fin (k + 1), u ≠ v →
      ∀ v₁ ∈ velocitySupport m (g u), ∀ v₂ ∈ velocitySupport m (g v), d_g ≤ ‖v₁ - v₂‖)
    (h₀ : SmoothWavepacket)
    (h_diam : ∀ v₁ ∈ velocitySupport m h₀, ∀ v₂ ∈ velocitySupport m h₀, ‖v₁ - v₂‖ < d_g) :
    ∃ j₀ : Fin (k + 1), ∀ u : Fin (k + 1), u ≠ j₀ → VelocityDisjoint m h₀ (g u) := by
  by_cases h_all : ∀ u : Fin (k + 1), VelocityDisjoint m h₀ (g u)
  · exact ⟨0, fun u _ => h_all u⟩
  · push Not at h_all
    obtain ⟨j₀, hj₀⟩ := h_all
    refine ⟨j₀, fun u hu => ?_⟩
    unfold VelocityDisjoint at hj₀ ⊢
    rw [Set.not_disjoint_iff] at hj₀
    obtain ⟨v_shared, hv_h, hv_j0⟩ := hj₀
    rw [Set.disjoint_left]
    intro v₁ hv₁_h hv₁_u
    have h_lt := h_diam v₁ hv₁_h v_shared hv_h
    have h_ge := hd_g u j₀ hu v₁ hv₁_u v_shared hv_j0
    exact (not_le_of_gt h_lt) h_ge

lemma tsupport_haagRuelleAdjCoreIndexedTest_subset
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (r : ℝ) (hr : 0 < r) (t : ℝ)
    (β : ι) (x : Fin 1 → Fin 4 → ℝ)
    (hx : x ∈ tsupport (haagRuelleAdjCoreIndexedTest D s f r hr t β : (Fin 1 → Fin 4 → ℝ) → ℂ)) :
    ∃ α₀ : ι, x ∈
      tsupport (haagRuelleCoreIndexedTest D s f r hr t α₀ : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
  by_contra h_none
  push Not at h_none
  let K : Set (Fin 1 → Fin 4 → ℝ) :=
    ⋃ α₀ : ι, tsupport (haagRuelleCoreIndexedTest D s f r hr t α₀ : (Fin 1 → Fin 4 → ℝ) → ℂ)
  have hK_closed : IsClosed K := isClosed_iUnion_of_finite fun _ => isClosed_tsupport _
  have h_sub : Function.support
      (haagRuelleAdjCoreIndexedTest D s f r hr t β : (Fin 1 → Fin 4 → ℝ) → ℂ) ⊆ K := by
    intro y hy
    by_contra hyK
    have hy_all : ∀ α₀ : ι, haagRuelleCoreIndexedTest D s f r hr t α₀ y = 0 := by
      intro α₀
      refine image_eq_zero_of_notMem_tsupport ?_
      intro hmem
      exact hyK (Set.mem_iUnion.mpr ⟨α₀, hmem⟩)
    apply hy
    dsimp [haagRuelleAdjCoreIndexedTest, starIndexedTest]
    rw [schwartzMap_sum_apply]
    refine Finset.sum_eq_zero fun α₀ _ => ?_
    rw [_root_.smul_apply, smul_eq_mul, schwartzConj_apply, hy_all α₀, star_zero, mul_zero]
  have hxK : x ∈ K := closure_minimal h_sub hK_closed hx
  rw [Set.mem_iUnion] at hxK
  obtain ⟨α₀, hα₀⟩ := hxK
  exact h_none α₀ hα₀

lemma norm_haagRuelleAdjApply_chain_single_overlap_sub_rapid_decay
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s₀ : Fin D.mode.ν) (h₀ : SmoothWavepacket)
    (s₂ : Fin (k + 1) → Fin D.mode.ν) (g : Fin (k + 1) → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (g i) (g j))
    (j₀ : Fin (k + 1)) (hj₀ : ∀ u : Fin (k + 1), u ≠ j₀ → VelocityDisjoint m h₀ (g u))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖wightmanIndexedVec D.wightman.WData (k + 2)
          (haagRuelleAdjApply D s₀ h₀ t (k + 1) (haagRuelleChain D (k + 1) s₂ g t)) -
        (η ^ j₀.val * ⟪fockOneParticleVec D.mode.ν s₀ h₀,
            fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ) •
          haagRuelleChainVec D k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove) t‖ *
        (1 + |t|) ^ N ≤ C := by
  let s₂' : Fin k → Fin D.mode.ν := s₂ ∘ j₀.succAbove
  let g' : Fin k → SmoothWavepacket := g ∘ j₀.succAbove
  let w_in : Fin (k + 2) → SmoothWavepacket := Fin.cons h₀ g
  let w_disj : Fin (k + 2) → Fin (k + 2) → Prop := fun a b =>
    a ≠ b ∧ ¬ (a = 0 ∧ b = j₀.succ) ∧ ¬ (a = j₀.succ ∧ b = 0)
  have h_w_disj : ∀ a b : Fin (k + 2), w_disj a b → VelocityDisjoint m (w_in a) (w_in b) := by
    rintro a b ⟨hab, h1, h2⟩
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨va, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨vb, rfl⟩
    · exact False.elim (hab rfl)
    · have hne : vb ≠ j₀ := fun h => h1 ⟨rfl, congrArg Fin.succ h⟩
      exact hj₀ vb hne
    · have hne : va ≠ j₀ := fun h => h2 ⟨congrArg Fin.succ h, rfl⟩
      exact (hj₀ va hne).symm
    · have hne : va ≠ vb := fun h => hab (congrArg Fin.succ h)
      exact hg hne
  let d_of : Fin (k + 2) × Fin (k + 2) → ℝ := fun ab =>
    if hab : w_disj ab.1 ab.2 then
      (exists_pos_sep_of_velocityDisjoint D.hm (h_w_disj ab.1 ab.2 hab)).choose
    else 1
  have hd_pos : ∀ ab : Fin (k + 2) × Fin (k + 2), 0 < d_of ab := fun ab => by
    dsimp [d_of]
    by_cases hab : w_disj ab.1 ab.2
    · rw [dif_pos hab]
      exact (exists_pos_sep_of_velocityDisjoint D.hm (h_w_disj ab.1 ab.2 hab)).choose_spec.1
    · rw [dif_neg hab]
      exact zero_lt_one
  let d_min : ℝ := Finset.univ.inf' ⟨(0, 0), Finset.mem_univ _⟩ d_of
  have hdmin_pos : 0 < d_min :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun ab _ => hd_pos ab
  let r_cone : ℝ := d_min / 6
  have hr_cone : 0 < r_cone := by positivity
  let Ψ : Fin (k + 2) → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    Fin.cons (haagRuelleAdjIndexedTest D s₀ h₀) (fun u t => haagRuelleIndexedTest D (s₂ u) (g u) t)
  let Φ : Fin (k + 2) → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    Fin.cons (haagRuelleAdjCoreIndexedTest D s₀ h₀ r_cone hr_cone)
      (fun u t => haagRuelleCoreIndexedTest D (s₂ u) (g u) r_cone hr_cone t)
  let Θ_full : Fin (k + 2) → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t =>
    if hi : i.val < k then haagRuelleIndexedTest D (s₂' ⟨i.val, hi⟩) (g' ⟨i.val, hi⟩) t
    else if i.val = k then haagRuelleAdjIndexedTest D s₀ h₀ t
    else haagRuelleIndexedTest D (s₂ j₀) (g j₀) t
  let Θ_core : Fin (k + 2) → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t =>
    if hi : i.val < k then
      haagRuelleCoreIndexedTest D (s₂' ⟨i.val, hi⟩) (g' ⟨i.val, hi⟩) r_cone hr_cone t
    else if i.val = k then haagRuelleAdjCoreIndexedTest D s₀ h₀ r_cone hr_cone t
    else haagRuelleCoreIndexedTest D (s₂ j₀) (g j₀) r_cone hr_cone t
  have hΨ_poly : ∀ i : Fin (k + 2), IndexedTestPolyGrowth (Ψ i) :=
    Fin.cases (indexedTestPolyGrowth_haagRuelleAdj D s₀ h₀)
      (fun u => indexedTestPolyGrowth_haagRuelle D (s₂ u) (g u))
  have hΦ_poly : ∀ i : Fin (k + 2), IndexedTestPolyGrowth (Φ i) :=
    Fin.cases (indexedTestPolyGrowth_haagRuelleAdjCore D s₀ h₀ r_cone hr_cone)
      (fun u => indexedTestPolyGrowth_haagRuelleCore D (s₂ u) (g u) r_cone hr_cone)
  have hΘ_full_poly : ∀ i : Fin (k + 2), IndexedTestPolyGrowth (Θ_full i) := fun i => by
    dsimp [Θ_full]
    split_ifs
    · exact indexedTestPolyGrowth_haagRuelle D _ _
    · exact indexedTestPolyGrowth_haagRuelleAdj D s₀ h₀
    · exact indexedTestPolyGrowth_haagRuelle D _ _
  have hΘ_core_poly : ∀ i : Fin (k + 2), IndexedTestPolyGrowth (Θ_core i) := fun i => by
    dsimp [Θ_core]
    split_ifs
    · exact indexedTestPolyGrowth_haagRuelleCore D _ _ r_cone hr_cone
    · exact indexedTestPolyGrowth_haagRuelleAdjCore D s₀ h₀ r_cone hr_cone
    · exact indexedTestPolyGrowth_haagRuelleCore D _ _ r_cone hr_cone
  have h_diff_ΨΦ : ∀ i : Fin (k + 2), IndexedTestRapidDecay (fun t α => Ψ i t α - Φ i t α) :=
    Fin.cases (by
        have h_sub : (fun t α => Ψ 0 t α - Φ 0 t α) =
            fun t => haagRuelleAdjTailIndexedTest D s₀ h₀ r_cone hr_cone t := by
          ext t α x
          simp only [Ψ, Φ, Fin.cons_zero]
          rw [← haagRuelleAdjIndexedTest_sub_core D s₀ h₀ r_cone hr_cone t α]
        rw [h_sub]
        exact indexedTestRapidDecay_haagRuelleAdjTail D s₀ h₀ r_cone hr_cone)
      (fun u => by
        have h_sub : (fun t α => Ψ u.succ t α - Φ u.succ t α) =
            fun t => haagRuelleTailIndexedTest D (s₂ u) (g u) r_cone hr_cone t := by
          ext t α x
          simp only [Ψ, Φ, Fin.cons_succ]
          rw [← haagRuelleIndexedTest_sub_core D (s₂ u) (g u) r_cone hr_cone t α]
        rw [h_sub]
        exact indexedTestRapidDecay_haagRuelleTail D (s₂ u) (g u) r_cone hr_cone)
  have h_diff_Θ : ∀ i : Fin (k + 2),
      IndexedTestRapidDecay (fun t α => Θ_core i t α - Θ_full i t α) := fun i => by
    have h_neg : (fun t α => Θ_core i t α - Θ_full i t α) =
        fun t α => -(Θ_full i t α - Θ_core i t α) := by
      ext t α x
      simp [neg_sub]
    rw [h_neg]
    refine indexedTestRapidDecay_neg ?_
    dsimp [Θ_full, Θ_core]
    by_cases hi : i.val < k
    · simp only [dif_pos hi]
      have h_sub : (fun t α => haagRuelleIndexedTest D (s₂' ⟨i.val, hi⟩) (g' ⟨i.val, hi⟩) t α -
          haagRuelleCoreIndexedTest D (s₂' ⟨i.val, hi⟩) (g' ⟨i.val, hi⟩) r_cone hr_cone t α) =
          fun t =>
            haagRuelleTailIndexedTest D (s₂' ⟨i.val, hi⟩) (g' ⟨i.val, hi⟩) r_cone hr_cone t := by
        ext t α x
        rw [← haagRuelleIndexedTest_sub_core]
      rw [h_sub]
      exact indexedTestRapidDecay_haagRuelleTail D _ _ r_cone hr_cone
    · by_cases hik : i.val = k
      · simp only [dif_neg hi, if_pos hik]
        have h_sub : (fun t α => haagRuelleAdjIndexedTest D s₀ h₀ t α -
            haagRuelleAdjCoreIndexedTest D s₀ h₀ r_cone hr_cone t α) =
            fun t => haagRuelleAdjTailIndexedTest D s₀ h₀ r_cone hr_cone t := by
          ext t α x
          rw [← haagRuelleAdjIndexedTest_sub_core]
        rw [h_sub]
        exact indexedTestRapidDecay_haagRuelleAdjTail D s₀ h₀ r_cone hr_cone
      · simp only [dif_neg hi, if_neg hik]
        have h_sub : (fun t α => haagRuelleIndexedTest D (s₂ j₀) (g j₀) t α -
            haagRuelleCoreIndexedTest D (s₂ j₀) (g j₀) r_cone hr_cone t α) =
            fun t => haagRuelleTailIndexedTest D (s₂ j₀) (g j₀) r_cone hr_cone t := by
          ext t α x
          rw [← haagRuelleIndexedTest_sub_core]
        rw [h_sub]
        exact indexedTestRapidDecay_haagRuelleTail D _ _ r_cone hr_cone
  obtain ⟨C1, hC1_nn, hC1_bd⟩ :=
    norm_indexedChain_sub_rapid_decay D.wightman.WData (k + 2) Ψ Φ hΨ_poly hΦ_poly h_diff_ΨΦ N
  obtain ⟨C2, hC2_nn, hC2_bd⟩ := norm_indexedChain_sub_rapid_decay D.wightman.WData (k + 2)
    Θ_core Θ_full hΘ_core_poly hΘ_full_poly h_diff_Θ N
  let η_pow : ℂ := η ^ j₀.val
  have h_η_norm : ‖η_pow‖ = 1 := by
    dsimp [η_pow]
    rw [norm_pow]
    rcases D.mode.hη with h1 | h1 <;> simp [h1]
  let c_vac : ℂ := ⟪fockOneParticleVec D.mode.ν s₀ h₀, fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ
  obtain ⟨deg_p, C_p, hCp_nn, hCp_bd⟩ :=
    norm_indexedChain_poly_growth D.wightman.WData (k + 2) Ψ hΨ_poly
  let Ψ_tail : Fin k → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun i t => haagRuelleIndexedTest D (s₂' i) (g' i) t
  obtain ⟨deg_q, C_q, hCq_nn, hCq_bd⟩ :=
    norm_indexedChain_poly_growth D.wightman.WData k Ψ_tail
      (fun i => indexedTestPolyGrowth_haagRuelle D (s₂' i) (g' i))
  let C_small : ℝ := C_p * 2 ^ (deg_p + N) + ‖c_vac‖ * (C_q * 2 ^ (deg_q + N))
  let C_large : ℝ := C1 + C2
  refine ⟨max C_small C_large, le_trans (by positivity) (le_max_left _ _), fun t => ?_⟩
  have h_lhs_eq : haagRuelleAdjApply D s₀ h₀ t (k + 1) (haagRuelleChain D (k + 1) s₂ g t) =
      indexedChain ι (k + 2) (fun i => Ψ i t) := by
    dsimp [haagRuelleAdjApply, haagRuelleChain, indexedChain, Ψ]
    rfl
  have h_contract : wightmanIndexedVec D.wightman.WData (k + 2)
      (indexedChain ι (k + 2) (fun i => Θ_full i t)) =
      c_vac • haagRuelleChainVec D k s₂' g' t := by
    have h_tail_eq :
        wightmanIndexedVec D.wightman.WData 2
          (indexedChain ι 2 (fun u => Θ_full (Fin.natAdd k u) t)) =
          c_vac • D.vacuum := by
      have h_pair : indexedChain ι 2 (fun u => Θ_full (Fin.natAdd k u) t) =
          haagRuelleAdjApply D s₀ h₀ t 1
            (haagRuelleApply D (s₂ j₀) (g j₀) t 0 (vacuumIndexedSchwartz ι)) := by
        dsimp [haagRuelleAdjApply, haagRuelleApply, indexedChain]
        have h0 : Θ_full (Fin.natAdd k 0) t = haagRuelleAdjIndexedTest D s₀ h₀ t := by
          dsimp [Θ_full]
          simp
        have h1 : Θ_full (Fin.natAdd k 1) t = haagRuelleIndexedTest D (s₂ j₀) (g j₀) t := by
          dsimp [Θ_full]
          rw [dif_neg (by omega), if_neg (by omega)]
        rw [h0]
        refine congrArg (indexedPrepend 1 (haagRuelleAdjIndexedTest D s₀ h₀ t)) ?_
        refine congrArg (fun Ψ => indexedPrepend 0 Ψ (vacuumIndexedSchwartz ι)) ?_
        have h1' : Θ_full (Fin.natAdd k (0 : Fin 1).succ) t = Θ_full (Fin.natAdd k 1) t := rfl
        exact h1'.trans h1
      rw [h_pair]
      exact haagRuelleAdjApply_haagRuelleApply_vacuum_eq_fock D s₀ (s₂ j₀) h₀ (g j₀) t t
    have h_con := wightmanIndexedVec_indexedChain_contract_right D.wightman.WData k 2
      (fun i => Θ_full i t) h_tail_eq
    rw [h_con]
    congr 1
    dsimp [haagRuelleChainVec, haagRuelleChain]
    refine congrArg (wightmanIndexedVec D.wightman.WData k ∘ indexedChain ι k) ?_
    funext i
    simp [Θ_full, Fin.castAdd, i.isLt]
  have h_rhs_eq : (η_pow * c_vac) • haagRuelleChainVec D k s₂' g' t =
      η_pow • wightmanIndexedVec D.wightman.WData (k + 2)
        (indexedChain ι (k + 2) (fun i => Θ_full i t)) := by
    rw [h_contract, smul_smul]
  rw [h_lhs_eq]
  have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
  by_cases ht1 : |t| < 1
  · have ht2 : 1 + |t| ≤ 2 := by linarith
    have ht_ge0 : 0 ≤ 1 + |t| := by positivity
    have h_tail_eq : haagRuelleChainVec D k s₂' g' t =
        wightmanIndexedVec D.wightman.WData k (indexedChain ι k (fun i => Ψ_tail i t)) := rfl
    calc ‖wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t)) -
            (η_pow * c_vac) • haagRuelleChainVec D k s₂' g' t‖ * (1 + |t|) ^ N
        ≤ (‖wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t))‖ +
              ‖(η_pow * c_vac) • haagRuelleChainVec D k s₂' g' t‖) * (1 + |t|) ^ N :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) ht_nn
      _ = ‖wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t))‖ *
              (1 + |t|) ^ N +
            ‖c_vac‖ * (‖wightmanIndexedVec D.wightman.WData k
              (indexedChain ι k (fun i => Ψ_tail i t))‖ * (1 + |t|) ^ N) := by
          rw [norm_smul, norm_mul, h_η_norm, one_mul, h_tail_eq, add_mul]
          ring
      _ ≤ C_p * (1 + |t|) ^ deg_p * (1 + |t|) ^ N +
            ‖c_vac‖ * (C_q * (1 + |t|) ^ deg_q * (1 + |t|) ^ N) :=
          add_le_add (mul_le_mul_of_nonneg_right (hCp_bd t) ht_nn)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hCq_bd t) ht_nn)
              (norm_nonneg _))
      _ ≤ C_p * 2 ^ (deg_p + N) + ‖c_vac‖ * (C_q * 2 ^ (deg_q + N)) := by
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          · calc C_p * (1 + |t|) ^ deg_p * (1 + |t|) ^ N
                ≤ C_p * 2 ^ deg_p * 2 ^ N := mul_le_mul
                    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht_ge0 ht2 _) hCp_nn)
                    (pow_le_pow_left₀ ht_ge0 ht2 _) ht_nn (by positivity)
              _ = C_p * 2 ^ (deg_p + N) := by rw [pow_add]; ring
          · calc C_q * (1 + |t|) ^ deg_q * (1 + |t|) ^ N
                ≤ C_q * 2 ^ deg_q * 2 ^ N := mul_le_mul
                    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht_ge0 ht2 _) hCq_nn)
                    (pow_le_pow_left₀ ht_ge0 ht2 _) ht_nn (by positivity)
              _ = C_q * 2 ^ (deg_q + N) := by rw [pow_add]; ring
      _ = C_small := rfl
      _ ≤ max C_small C_large := le_max_left _ _
  · have ht_ge : 1 ≤ |t| := not_lt.mp ht1
    have h_sep_cone : ∀ a b : Fin (k + 2), w_disj a b →
        ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        x₁ ∈ tsupport (Φ a t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        x₂ ∈ tsupport (Φ b t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0) := by
      intro a b hab α₁ α₂ x₁ x₂ hx₁ hx₂
      have h_core_tsup : ∀ c : Fin (k + 2), ∀ (α : ι) (y : Fin 1 → Fin 4 → ℝ),
          y ∈ tsupport (Φ c t α : (Fin 1 → Fin 4 → ℝ) → ℂ) →
          ∃ γ : ι, y ∈ tsupport (velocityConeCutoff m D.hm
            (dualModeWavepacket D (Fin.cases s₀ s₂ c) γ (w_in c)) r_cone hr_cone t) := by
        intro c α y hy
        refine Fin.cases ?_ ?_ c α y hy
        · intro α' y' hy'
          obtain ⟨γ, hγ⟩ := tsupport_haagRuelleAdjCoreIndexedTest_subset D s₀ h₀ r_cone hr_cone t
            α' y' hy'
          exact ⟨γ, tsupport_timeModCoreTestFn_subset D.hm
            (dualModeWavepacket D s₀ γ h₀) _ _ _ r_cone hr_cone t hγ⟩
        · intro uc α' y' hy'
          exact ⟨α', tsupport_timeModCoreTestFn_subset D.hm
            (dualModeWavepacket D (s₂ uc) α' (g uc)) _ _ _ r_cone hr_cone t hy'⟩
      obtain ⟨γ₁, hγ₁⟩ := h_core_tsup a α₁ x₁ hx₁
      obtain ⟨γ₂, hγ₂⟩ := h_core_tsup b α₂ x₂ hx₂
      have hd_le : 5 * r_cone ≤ d_of (a, b) := by
        have h1 : d_min ≤ d_of (a, b) := Finset.inf'_le d_of (Finset.mem_univ _)
        dsimp [r_cone]
        linarith
      have h_sep_orig := (exists_pos_sep_of_velocityDisjoint D.hm (h_w_disj a b hab)).choose_spec.2
      have h_sep_d : ∀ v₁ ∈ velocitySupport m
            (dualModeWavepacket D (Fin.cases s₀ s₂ a) γ₁ (w_in a)),
          ∀ v₂ ∈ velocitySupport m
            (dualModeWavepacket D (Fin.cases s₀ s₂ b) γ₂ (w_in b)),
          d_of (a, b) ≤ ‖v₁ - v₂‖ := fun v₁ hv₁ v₂ hv₂ => by
        have h_eq_d : d_of (a, b) =
            (exists_pos_sep_of_velocityDisjoint D.hm (h_w_disj a b hab)).choose := by
          dsimp [d_of]
          exact dif_pos hab
        rw [h_eq_d]
        exact h_sep_orig v₁ (velocitySupport_dualModeWavepacket_subset D _ γ₁ (w_in a) hv₁)
          v₂ (velocitySupport_dualModeWavepacket_subset D _ γ₂ (w_in b) hv₂)
      exact spacelike_velocityConeCutoffs_of_radius D.hm hr_cone hd_le h_sep_d ht_ge hγ₁ hγ₂
    let m₁ : ℕ := k - j₀.val
    have hm₁ : j₀.succ.val + m₁ < k + 2 := by dsimp [m₁]; omega
    have hsp₁ : ∀ u : Fin m₁, ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        x₁ ∈ tsupport (Φ j₀.succ t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        x₂ ∈ tsupport (Φ ⟨j₀.succ.val + 1 + u.val, by omega⟩ t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0) := fun u => by
      have hw : w_disj j₀.succ ⟨j₀.succ.val + 1 + u.val, by omega⟩ := by
        refine ⟨?_, ?_, ?_⟩
        · intro h; have hv := congrArg Fin.val h; simp at hv; omega
        · intro h; have hv := congrArg Fin.val h.1; simp at hv
        · intro h; have hv := congrArg Fin.val h.2; simp at hv
      exact h_sep_cone j₀.succ ⟨j₀.succ.val + 1 + u.val, by omega⟩ hw
    obtain ⟨σ₁, ⟨hσ₁_last, hσ₁_lt, hσ₁_mid, _⟩, hvec₁⟩ :=
      wightmanIndexedVec_indexedChain_move_right D.wightman.WData D.locality (k + 2)
        (fun i => Φ i t) j₀.succ m₁ hm₁ hsp₁
    have hσ₁_0 : σ₁ 0 = 0 := hσ₁_lt 0 (Nat.zero_lt_succ _)
    have hσ₁_end : σ₁ (Fin.last (k + 1)) = j₀.succ := by
      have h_eq : (Fin.last (k + 1) : Fin (k + 2)) = ⟨j₀.succ.val + m₁, hm₁⟩ := by
        ext; dsimp [m₁]; omega
      rw [h_eq, hσ₁_last]
    have hσ₁_mid_val : ∀ p : Fin k, σ₁ p.castSucc.succ = (j₀.succAbove p).succ := by
      intro p
      by_cases hpj : p.val < j₀.val
      · have hp_lt : p.castSucc.succ.val < j₀.succ.val := by simp [hpj]
        rw [hσ₁_lt p.castSucc.succ hp_lt]
        ext
        simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, hpj, ↓reduceIte]
      · have hp_ge : j₀.val ≤ p.val := not_lt.mp hpj
        let u : Fin m₁ := ⟨p.val - j₀.val, by dsimp [m₁]; omega⟩
        have h_eq : p.castSucc.succ = ⟨j₀.succ.val + u.val, by omega⟩ := by
          ext; dsimp [u]; omega
        rw [h_eq, hσ₁_mid u]
        ext
        simp only [Fin.val_succ, Fin.succAbove]
        split_ifs with hlt
        · simp [Fin.lt_def] at hlt; omega
        · dsimp [u]; omega
    let Φ₁ : Fin (k + 2) → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := (fun i => Φ i t) ∘ σ₁
    have hm₂ : (0 : Fin (k + 2)).val + k < k + 2 := by simp
    have hsp₂ : ∀ u : Fin k, ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        x₁ ∈ tsupport (Φ₁ 0 α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        x₂ ∈ tsupport (Φ₁ ⟨0 + 1 + u.val, by omega⟩ α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0) := by
      intro u α₁ α₂ x₁ x₂ hx₁ hx₂
      have hu_eq : (⟨0 + 1 + u.val, by omega⟩ : Fin (k + 2)) = u.castSucc.succ := by
        ext; dsimp; omega
      dsimp [Φ₁] at hx₁ hx₂
      rw [hσ₁_0] at hx₁
      rw [hu_eq, hσ₁_mid_val u] at hx₂
      have hw : w_disj 0 (j₀.succAbove u).succ := by
        refine ⟨(Fin.succ_ne_zero _).symm, ?_, ?_⟩
        · intro h
          exact Fin.succAbove_ne j₀ u (Fin.succ_inj.mp h.2)
        · intro h
          exact Fin.succ_ne_zero j₀ h.1.symm
      exact h_sep_cone 0 (j₀.succAbove u).succ hw α₁ α₂ x₁ x₂ hx₁ hx₂
    obtain ⟨σ₂, ⟨hσ₂_k, _, hσ₂_mid, hσ₂_gt⟩, hvec₂⟩ :=
      wightmanIndexedVec_indexedChain_move_right D.wightman.WData D.locality (k + 2)
        Φ₁ 0 k hm₂ hsp₂
    have h_final_fn : (Φ₁ ∘ σ₂) = fun i => Θ_core i t := by
      funext i α
      ext x
      dsimp [Φ₁, Θ_core]
      by_cases hi : i.val < k
      · rw [dif_pos hi]
        have hσ_val : σ₂ i = ⟨0 + 1 + i.val, by omega⟩ :=
          (congrArg σ₂ (by ext; simp)).trans (hσ₂_mid ⟨i.val, hi⟩)
        rw [hσ_val]
        have h_succ : (⟨0 + 1 + i.val, by omega⟩ : Fin (k + 2)) =
            (⟨i.val, hi⟩ : Fin k).castSucc.succ := by
          ext
          dsimp
          omega
        rw [h_succ, hσ₁_mid_val ⟨i.val, hi⟩]
        rfl
      · rw [dif_neg hi]
        by_cases hik : i.val = k
        · rw [if_pos hik]
          have hσ_val : σ₂ i = 0 := (congrArg σ₂ (by ext; dsimp; omega)).trans hσ₂_k
          rw [hσ_val, hσ₁_0]
          rfl
        · rw [if_neg hik]
          have hi_gt : (0 : Fin (k + 2)).val + k < i.val := by simp; omega
          have hi_last : i = Fin.last (k + 1) := by ext; simp; omega
          rw [hσ₂_gt i hi_gt, hi_last, hσ₁_end]
          rfl
    have h_eta_eq : η ^ m₁ * η ^ k = η_pow := by
      rw [← pow_add]
      have hexp : m₁ + k = 2 * (k - j₀.val) + j₀.val := by dsimp [m₁]; omega
      rw [hexp, pow_add, pow_mul]
      rcases D.mode.hη with h1 | h1 <;> simp [h1, η_pow]
    have h_core_eq :
        wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Φ i t)) =
          η_pow • wightmanIndexedVec D.wightman.WData (k + 2)
            (indexedChain ι (k + 2) (fun i => Θ_core i t)) := by
      rw [hvec₁]
      change η ^ m₁ • wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) Φ₁) = _
      rw [hvec₂, h_final_fn, smul_smul, h_eta_eq]
    have h_split :
        wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t)) -
          (η_pow * c_vac) • haagRuelleChainVec D k s₂' g' t =
        (wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t)) -
            wightmanIndexedVec D.wightman.WData (k + 2)
              (indexedChain ι (k + 2) (fun i => Φ i t))) +
          η_pow •
            (wightmanIndexedVec D.wightman.WData (k + 2)
                (indexedChain ι (k + 2) (fun i => Θ_core i t)) -
              wightmanIndexedVec D.wightman.WData (k + 2)
                (indexedChain ι (k + 2) (fun i => Θ_full i t))) := by
      rw [h_rhs_eq, smul_sub, ← h_core_eq]
      abel
    calc ‖wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t)) -
            (η_pow * c_vac) • haagRuelleChainVec D k s₂' g' t‖ * (1 + |t|) ^ N
        ≤ (‖wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t)) -
                wightmanIndexedVec D.wightman.WData (k + 2)
                  (indexedChain ι (k + 2) (fun i => Φ i t))‖ +
              ‖η_pow •
                (wightmanIndexedVec D.wightman.WData (k + 2)
                    (indexedChain ι (k + 2) (fun i => Θ_core i t)) -
                  wightmanIndexedVec D.wightman.WData (k + 2)
                    (indexedChain ι (k + 2) (fun i => Θ_full i t)))‖) * (1 + |t|) ^ N := by
          rw [h_split]
          exact mul_le_mul_of_nonneg_right (norm_add_le _ _) ht_nn
      _ = ‖wightmanIndexedVec D.wightman.WData (k + 2) (indexedChain ι (k + 2) (fun i => Ψ i t)) -
              wightmanIndexedVec D.wightman.WData (k + 2)
                (indexedChain ι (k + 2) (fun i => Φ i t))‖ * (1 + |t|) ^ N +
            ‖wightmanIndexedVec D.wightman.WData (k + 2)
                (indexedChain ι (k + 2) (fun i => Θ_core i t)) -
              wightmanIndexedVec D.wightman.WData (k + 2)
                (indexedChain ι (k + 2) (fun i => Θ_full i t))‖ * (1 + |t|) ^ N := by
          rw [norm_smul, h_η_norm, one_mul, add_mul]
      _ ≤ C1 + C2 := add_le_add (hC1_bd t) (hC2_bd t)
      _ = C_large := rfl
      _ ≤ max C_small C_large := le_max_right _ _

lemma tendsto_haagRuelleAdjApply_chain_single_overlap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot] (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0))
    (L : ∀ (r : ℕ), (Fin r → Fin D.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → D.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec D r s f) F (𝓝 (L r s f hf)))
    (k : ℕ) (s₀ : Fin D.mode.ν) (h₀ : SmoothWavepacket)
    (s₂ : Fin (k + 1) → Fin D.mode.ν) (g : Fin (k + 1) → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (g i) (g j))
    (j₀ : Fin (k + 1)) (hj₀ : ∀ u : Fin (k + 1), u ≠ j₀ → VelocityDisjoint m h₀ (g u)) :
    Tendsto (fun t : ℝ => wightmanIndexedVec D.wightman.WData (k + 2)
        (haagRuelleAdjApply D s₀ h₀ t (k + 1) (haagRuelleChain D (k + 1) s₂ g t))) F
      (𝓝 ((η ^ j₀.val * ⟪fockOneParticleVec D.mode.ν s₀ h₀,
          fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ) •
        L k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove)
          (fun _ _ hij => hg ((Fin.succAbove_right_injective).ne hij)))) := by
  let c : ℂ := η ^ j₀.val * ⟪fockOneParticleVec D.mode.ν s₀ h₀,
    fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ
  let v_tail := L k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove)
    (fun _ _ hij => hg ((Fin.succAbove_right_injective).ne hij))
  have h_lim_rhs : Tendsto (fun t : ℝ =>
      c • haagRuelleChainVec D k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove) t) F (𝓝 (c • v_tail)) :=
    (hL k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove)
      (fun _ _ hij => hg ((Fin.succAbove_right_injective).ne hij))).const_smul c
  obtain ⟨C, _, hC_bd⟩ :=
    norm_haagRuelleAdjApply_chain_single_overlap_sub_rapid_decay D k s₀ h₀ s₂ g hg j₀ hj₀ 1
  have h_diff : Tendsto (fun t : ℝ => wightmanIndexedVec D.wightman.WData (k + 2)
        (haagRuelleAdjApply D s₀ h₀ t (k + 1) (haagRuelleChain D (k + 1) s₂ g t)) -
      c • haagRuelleChainVec D k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove) t) F (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds (by simpa using hF_inv.const_mul C)
      (fun t => norm_nonneg _) (fun t => ?_))
    have ht_pos : 0 < 1 + |t| := by positivity
    exact (le_mul_inv_iff₀ ht_pos).mpr (by simpa [pow_one] using hC_bd t)
  simpa using h_diff.add h_lim_rhs

theorem tendsto_haagRuelleAdjApply_chain_single_overlap_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s₀ : Fin D.mode.ν) (h₀ : SmoothWavepacket)
    (s₂ : Fin (k + 1) → Fin D.mode.ν) (g : Fin (k + 1) → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (g i) (g j))
    (j₀ : Fin (k + 1)) (hj₀ : ∀ u : Fin (k + 1), u ≠ j₀ → VelocityDisjoint m h₀ (g u)) :
    Tendsto (fun t : ℝ => wightmanIndexedVec D.wightman.WData (k + 2)
        (haagRuelleAdjApply D s₀ h₀ t (k + 1) (haagRuelleChain D (k + 1) s₂ g t))) atTop
      (𝓝 ((η ^ j₀.val * ⟪fockOneParticleVec D.mode.ν s₀ h₀,
          fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ) •
        haagRuelleOutVec D k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove)
          (fun _ _ hij => hg ((Fin.succAbove_right_injective).ne hij)))) :=
  tendsto_haagRuelleAdjApply_chain_single_overlap D tendsto_inv_one_add_abs_atTop
    (haagRuelleOutVec D) (tendsto_haagRuelleChainVec_atTop D) k s₀ h₀ s₂ g hg j₀ hj₀

theorem tendsto_haagRuelleAdjApply_chain_single_overlap_atBot
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (k : ℕ) (s₀ : Fin D.mode.ν) (h₀ : SmoothWavepacket)
    (s₂ : Fin (k + 1) → Fin D.mode.ν) (g : Fin (k + 1) → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin (k + 1) => VelocityDisjoint m (g i) (g j))
    (j₀ : Fin (k + 1)) (hj₀ : ∀ u : Fin (k + 1), u ≠ j₀ → VelocityDisjoint m h₀ (g u)) :
    Tendsto (fun t : ℝ => wightmanIndexedVec D.wightman.WData (k + 2)
        (haagRuelleAdjApply D s₀ h₀ t (k + 1) (haagRuelleChain D (k + 1) s₂ g t))) atBot
      (𝓝 ((η ^ j₀.val * ⟪fockOneParticleVec D.mode.ν s₀ h₀,
          fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ) •
        haagRuelleInVec D k (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove)
          (fun _ _ hij => hg ((Fin.succAbove_right_injective).ne hij)))) :=
  tendsto_haagRuelleAdjApply_chain_single_overlap D tendsto_inv_one_add_abs_atBot
    (haagRuelleInVec D) (tendsto_haagRuelleChainVec_atBot D) k s₀ h₀ s₂ g hg j₀ hj₀

omit [Fintype ι] [DecidableEq ι] in
def finConsPermFun {k : ℕ} (j₀ : Fin (k + 1)) (τ : Equiv.Perm (Fin k)) :
    Fin (k + 1) → Fin (k + 1) :=
  Fin.cases j₀ (fun u => j₀.succAbove (τ u))

omit [Fintype ι] [DecidableEq ι] in
lemma injective_finConsPermFun {k : ℕ} (j₀ : Fin (k + 1)) (τ : Equiv.Perm (Fin k)) :
    Function.Injective (finConsPermFun j₀ τ) := by
  intro a b hab
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨u, rfl⟩ <;>
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨v, rfl⟩
  · rfl
  · exact False.elim ((Fin.succAbove_ne j₀ (τ v)).symm hab)
  · exact False.elim (Fin.succAbove_ne j₀ (τ u) hab)
  · dsimp [finConsPermFun] at hab
    exact congrArg Fin.succ (τ.injective (Fin.succAbove_right_injective hab))

omit [Fintype ι] [DecidableEq ι] in
def finConsPerm {k : ℕ} (j₀ : Fin (k + 1)) (τ : Equiv.Perm (Fin k)) :
    Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (finConsPermFun j₀ τ)
    ((Finite.injective_iff_bijective).mp (injective_finConsPermFun j₀ τ))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma finConsPerm_zero {k : ℕ} (j₀ : Fin (k + 1)) (τ : Equiv.Perm (Fin k)) :
    finConsPerm j₀ τ 0 = j₀ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma finConsPerm_succ {k : ℕ} (j₀ : Fin (k + 1)) (τ : Equiv.Perm (Fin k)) (u : Fin k) :
    finConsPerm j₀ τ u.succ = j₀.succAbove (τ u) := rfl

omit [Fintype ι] [DecidableEq ι] in
def finConsPermEquiv (k : ℕ) :
    Fin (k + 1) × Equiv.Perm (Fin k) ≃ Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (fun p : Fin (k + 1) × Equiv.Perm (Fin k) => finConsPerm p.1 p.2)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun ⟨j₁, τ₁⟩ ⟨j₂, τ₂⟩ h => by
      have hj : j₁ = j₂ := by
        have h0 := congrArg (fun σ => σ 0) h
        simpa using h0
      subst hj
      congr 1
      ext u
      have hu := congrArg (fun σ => σ u.succ) h
      simp only [finConsPerm_succ] at hu
      exact congrArg Fin.val (Fin.succAbove_right_injective hu), by
      simp [Fintype.card_prod, Fintype.card_perm, Nat.factorial_succ]⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma permInversions_finConsPerm {k : ℕ} (j₀ : Fin (k + 1)) (τ : Equiv.Perm (Fin k)) :
    permInversions (finConsPerm j₀ τ) = j₀.val + permInversions τ := by
  let S_all : Finset (Fin (k + 1) × Fin (k + 1)) :=
    Finset.univ.filter (fun ij : Fin (k + 1) × Fin (k + 1) =>
      ij.1 < ij.2 ∧ finConsPerm j₀ τ ij.2 < finConsPerm j₀ τ ij.1)
  let S_zero : Finset (Fin (k + 1) × Fin (k + 1)) := S_all.filter (fun ij => ij.1 = 0)
  let S_succ : Finset (Fin (k + 1) × Fin (k + 1)) := S_all.filter (fun ij => ij.1 ≠ 0)
  have h_part : S_all.card = S_zero.card + S_succ.card := by
    rw [← Finset.card_filter_add_card_filter_not (fun ij : Fin (k + 1) × Fin (k + 1) => ij.1 = 0)]
  have h_zero_card : S_zero.card = j₀.val := by
    let T : Finset (Fin k) := Finset.univ.filter (fun x : Fin k => x.castSucc < j₀)
    have hT_card : T.card = j₀.val := by
      have h_eq : T = Finset.univ.filter (fun x : Fin k => x.val < j₀.val) := by
        ext x
        simp [T, Fin.lt_def]
      rw [h_eq]
      symm
      conv_lhs => rw [← Finset.card_fin j₀.val]
      refine Finset.card_bij (fun (x : Fin j₀.val) _ => (⟨x.val, by omega⟩ : Fin k)) ?_ ?_ ?_
      · intro x _
        simp [x.isLt]
      · intro x₁ _ x₂ _ h
        exact Fin.ext (congrArg (Fin.val : Fin k → ℕ) h)
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨⟨y.val, hy⟩, Finset.mem_univ _, ?_⟩
        ext
        rfl
    rw [← hT_card]
    symm
    refine Finset.card_bij (fun (x : Fin k) _ => ((0 : Fin (k + 1)), (τ.symm x).succ)) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, Fin.succ_pos _, ?_⟩, rfl⟩
      rw [finConsPerm_zero, finConsPerm_succ]
      simpa using (Fin.succAbove_lt_iff_castSucc_lt j₀ x).mpr hx.2
    · intro x₁ _ x₂ _ h
      have h2 := Fin.succ_inj.mp (congrArg Prod.snd h)
      exact τ.symm.injective h2
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_zero, S_all] at hab
      rcases hab with ⟨⟨h_lt, h_inv⟩, ha0⟩
      subst ha0
      have hb_nz : b ≠ 0 := Fin.ne_zero_of_lt h_lt
      obtain ⟨u, hu⟩ := Fin.exists_succ_eq.mpr hb_nz
      subst hu
      refine ⟨τ u, ?_, by simp⟩
      rw [Finset.mem_filter]
      rw [finConsPerm_zero, finConsPerm_succ] at h_inv
      exact ⟨Finset.mem_univ _, (Fin.succAbove_lt_iff_castSucc_lt j₀ _).mp h_inv⟩
  have h_succ_card : S_succ.card = permInversions τ := by
    dsimp [permInversions]
    symm
    refine Finset.card_bij (fun (uv : Fin k × Fin k) _ => (uv.1.succ, uv.2.succ)) ?_ ?_ ?_
    · intro ⟨u, v⟩ huv
      rw [Finset.mem_filter] at huv
      rcases huv with ⟨_, h_lt, h_inv⟩
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, Fin.succ_lt_succ_iff.mpr h_lt, ?_⟩, Fin.succ_ne_zero u⟩
      simp only [finConsPerm_succ, Fin.succAbove]
      split_ifs <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega
    · intro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ h
      ext
      · exact congrArg Fin.val (Fin.succ_inj.mp (congrArg Prod.fst h))
      · exact congrArg Fin.val (Fin.succ_inj.mp (congrArg Prod.snd h))
    · intro ⟨a, b⟩ hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S_succ, S_all] at hab
      rcases hab with ⟨⟨h_lt, h_inv⟩, ha_nz⟩
      have hb_nz : b ≠ 0 := Fin.ne_zero_of_lt h_lt
      obtain ⟨u, rfl⟩ := Fin.exists_succ_eq.mpr ha_nz
      obtain ⟨v, rfl⟩ := Fin.exists_succ_eq.mpr hb_nz
      refine ⟨(u, v), ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Fin.succ_lt_succ_iff.mp h_lt, ?_⟩
      simp only [finConsPerm_succ, Fin.succAbove] at h_inv
      split_ifs at h_inv <;>
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;> omega
  exact h_part.trans (by rw [h_zero_card, h_succ_card])

omit [Fintype ι] [DecidableEq ι] in
lemma permInversions_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permInversions σ.symm = permInversions σ := by
  unfold permInversions
  refine Finset.card_nbij'
    (fun ij : Fin n × Fin n => (σ.symm ij.2, σ.symm ij.1))
    (fun ij : Fin n × Fin n => (σ ij.2, σ ij.1)) ?_ ?_ ?_ ?_
  · intro ⟨a, b⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨h.2, by simpa using h.1⟩
  · intro ⟨a, b⟩ h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
    exact ⟨h.2, by simpa using h.1⟩
  · intro ⟨a, b⟩ _
    simp
  · intro ⟨a, b⟩ _
    simp

omit [Fintype ι] [DecidableEq ι] in
lemma inner_fockOneParticleVec_eq_zero_of_disjoint (ν : ℕ) (s₁ s₂ : Fin ν)
    {m : ℝ} (hm : 0 < m) {f g : SmoothWavepacket} (hdisj : VelocityDisjoint m f g) :
    ⟪fockOneParticleVec ν s₁ f, fockOneParticleVec ν s₂ g⟫_ℂ = 0 := by
  rw [inner_fockOneParticleVec_eq]
  split_ifs with hs
  · rw [velocityDisjoint_iff_tsupport_disjoint hm] at hdisj
    have h_zero : (fun p : Fin 3 → ℝ => star (f.amp p) * g.amp p) = 0 := by
      ext p
      by_cases hp : p ∈ tsupport f.amp
      · have hg0 : g.amp p = 0 :=
          image_eq_zero_of_notMem_tsupport (Set.disjoint_left.mp hdisj hp)
        simp [hg0]
      · have hf0 : f.amp p = 0 := image_eq_zero_of_notMem_tsupport hp
        simp [hf0]
    rw [h_zero]
    simp
  · rfl

lemma inner_haagRuelleLimit_aux
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot] (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0))
    (L : ∀ (r : ℕ), (Fin r → Fin D.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → D.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec D r s f) F (𝓝 (L r s f hf)))
    (r₁ r₂ : ℕ) :
    (∀ (s₁ : Fin r₁ → Fin D.mode.ν) (f : Fin r₁ → SmoothWavepacket)
        (hf : Pairwise fun i j : Fin r₁ => VelocityDisjoint m (f i) (f j))
        (s₂ : Fin r₂ → Fin D.mode.ν) (g : Fin r₂ → SmoothWavepacket)
        (hg : Pairwise fun i j : Fin r₂ => VelocityDisjoint m (g i) (g j)),
        r₁ ≠ r₂ → ⟪L r₁ s₁ f hf, L r₂ s₂ g hg⟫_ℂ = 0) ∧
      (r₁ = r₂ → ∀ (s₁ : Fin r₁ → Fin D.mode.ν) (f : Fin r₁ → SmoothWavepacket)
        (hf : Pairwise fun i j : Fin r₁ => VelocityDisjoint m (f i) (f j))
        (s₂ : Fin r₁ → Fin D.mode.ν) (g : Fin r₁ → SmoothWavepacket)
        (hg : Pairwise fun i j : Fin r₁ => VelocityDisjoint m (g i) (g j)),
        ⟪L r₁ s₁ f hf, L r₁ s₂ g hg⟫_ℂ =
          ∑ σ : Equiv.Perm (Fin r₁), η ^ permInversions σ *
            ∏ i : Fin r₁, ⟪fockOneParticleVec D.mode.ν (s₁ i) (f i),
              fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ) := by
  induction r₁ generalizing r₂ with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro s₁ f hf s₂ g hg hne
      rcases r₂ with _ | k₂
      · exact False.elim (hne rfl)
      · have h0 : L 0 s₁ f hf = D.vacuum := by
          have h1 := hL 0 s₁ f hf
          have hz : haagRuelleChainVec D 0 s₁ f = fun _ => D.vacuum :=
            funext fun t => haagRuelleChainVec_zero D s₁ f t
          rw [hz] at h1
          exact tendsto_nhds_unique h1 tendsto_const_nhds
        rw [h0, ← inner_conj_symm, inner_haagRuelleLimit_vacuum_eq_zero D L hL k₂ s₂ g hg, map_zero]
    · intro h0 s₁ f hf s₂ g hg
      have h1 : L 0 s₁ f hf = D.vacuum := by
        have ht := hL 0 s₁ f hf
        have hz : haagRuelleChainVec D 0 s₁ f = fun _ => D.vacuum :=
          funext fun t => haagRuelleChainVec_zero D s₁ f t
        rw [hz] at ht
        exact tendsto_nhds_unique ht tendsto_const_nhds
      have h2 : L 0 s₂ g hg = D.vacuum := by
        have ht := hL 0 s₂ g hg
        have hz : haagRuelleChainVec D 0 s₂ g = fun _ => D.vacuum :=
          funext fun t => haagRuelleChainVec_zero D s₂ g t
        rw [hz] at ht
        exact tendsto_nhds_unique ht tendsto_const_nhds
      rw [h1, h2, D.inner_vacuum_self]
      simp [permInversions_one]
  | succ k₁ ih =>
    refine ⟨?_, ?_⟩
    · intro s₁ f hf s₂ g hg hne
      rcases r₂ with _ | k₂
      · have h2 : L 0 s₂ g hg = D.vacuum := by
          have ht := hL 0 s₂ g hg
          have hz : haagRuelleChainVec D 0 s₂ g = fun _ => D.vacuum :=
            funext fun t => haagRuelleChainVec_zero D s₂ g t
          rw [hz] at ht
          exact tendsto_nhds_unique ht tendsto_const_nhds
        rw [h2]
        exact inner_haagRuelleLimit_vacuum_eq_zero D L hL k₁ s₁ f hf
      · have hne' : k₁ ≠ k₂ := fun h => hne (congrArg Nat.succ h)
        let d_of : Fin (k₂ + 1) × Fin (k₂ + 1) → ℝ := fun ij =>
          if hij : ij.1 ≠ ij.2 then (exists_pos_sep_of_velocityDisjoint D.hm (hg hij)).choose else 1
        have hd_pos : ∀ ij : Fin (k₂ + 1) × Fin (k₂ + 1), 0 < d_of ij := fun ij => by
          dsimp [d_of]
          by_cases hij : ij.1 ≠ ij.2
          · rw [dif_pos hij]
            exact (exists_pos_sep_of_velocityDisjoint D.hm (hg hij)).choose_spec.1
          · rw [dif_neg hij]
            exact zero_lt_one
        let d_g : ℝ := Finset.univ.inf' ⟨(0, 0), Finset.mem_univ _⟩ d_of
        have hdg_pos : 0 < d_g :=
          (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun ij _ => hd_pos ij
        have hd_g : ∀ u v : Fin (k₂ + 1), u ≠ v →
            ∀ v₁ ∈ velocitySupport m (g u), ∀ v₂ ∈ velocitySupport m (g v), d_g ≤ ‖v₁ - v₂‖ :=
          fun u v huv v₁ hv₁ v₂ hv₂ => by
            have h1 : d_g ≤ d_of (u, v) := Finset.inf'_le d_of (Finset.mem_univ _)
            have h_eq : d_of (u, v) =
                (exists_pos_sep_of_velocityDisjoint D.hm (hg huv)).choose := by
              dsimp [d_of]
              exact dif_pos huv
            rw [h_eq] at h1
            exact h1.trans
              ((exists_pos_sep_of_velocityDisjoint D.hm (hg huv)).choose_spec.2 v₁ hv₁ v₂ hv₂)
        obtain ⟨n, h_part, h_sum_eq, h_sub_f, h_diam⟩ :=
          exists_smoothWavepacket_partition_diam_lt D.hm (f 0) hdg_pos
        have hf_each : ∀ a ∈ (Finset.univ : Finset (Fin n)),
            Pairwise fun i j : Fin (k₁ + 1) =>
              VelocityDisjoint m (Function.update f 0 (h_part a) i)
                (Function.update f 0 (h_part a) j) := by
          intro a _ i j hij
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨ia, rfl⟩ <;>
            rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨jb, rfl⟩
          · exact False.elim (hij rfl)
          · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero jb)]
            refine Set.disjoint_of_subset_left ?_ (hf (Fin.succ_ne_zero jb).symm)
            rintro v ⟨p, hp, rfl⟩
            exact ⟨p, h_sub_f a hp, rfl⟩
          · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero ia)]
            refine Set.disjoint_of_subset_right ?_ (hf (Fin.succ_ne_zero ia))
            rintro v ⟨p, hp, rfl⟩
            exact ⟨p, h_sub_f a hp, rfl⟩
          · rw [Function.update_of_ne (Fin.succ_ne_zero ia),
              Function.update_of_ne (Fin.succ_ne_zero jb)]
            exact hf (fun h => hij (congrArg Fin.succ (Fin.succ_inj.mp h)))
        have hf_sum : Pairwise fun i j : Fin (k₁ + 1) =>
            VelocityDisjoint m (Function.update f 0 (finsetSumWavepacket Finset.univ h_part) i)
              (Function.update f 0 (finsetSumWavepacket Finset.univ h_part) j) := by
          rw [h_sum_eq, Function.update_eq_self]
          exact hf
        have h_decomp := haagRuelleLimit_update_finset_sum D L hL Finset.univ (k₁ + 1) 0 s₁ f
          h_part hf_sum hf_each
        have h_orig : L (k₁ + 1) s₁ f hf =
            L (k₁ + 1) s₁ (Function.update f 0 (finsetSumWavepacket Finset.univ h_part))
              hf_sum := by
          congr 2
          rw [h_sum_eq, Function.update_eq_self]
        rw [h_orig, h_decomp, sum_inner]
        refine Finset.sum_eq_zero fun a _ => ?_
        let f_a := Function.update f 0 (h_part a.1)
        obtain ⟨j₀, hj₀⟩ := exists_single_overlap_slot k₂ g hd_g (h_part a.1) (h_diam a.1)
        have h_inn_t : Tendsto
            (fun t : ℝ => ⟪haagRuelleChainVec D (k₁ + 1) s₁ f_a t,
              haagRuelleChainVec D (k₂ + 1) s₂ g t⟫_ℂ) F
            (𝓝 ⟪L (k₁ + 1) s₁ f_a (hf_each a.1 a.2), L (k₂ + 1) s₂ g hg⟫_ℂ) :=
          Filter.Tendsto.inner (𝕜 := ℂ) (hL (k₁ + 1) s₁ f_a (hf_each a.1 a.2))
            (hL (k₂ + 1) s₂ g hg)
        have h_adj_lim := tendsto_haagRuelleAdjApply_chain_single_overlap D hF_inv L hL
          k₂ (s₁ 0) (h_part a.1) s₂ g hg j₀ hj₀
        have h_tail_lim := hL k₁ (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ)
          (fun _ _ hij => hf_each a.1 a.2 (Fin.succ_inj.ne.mpr hij))
        have h_adj_t : (fun t : ℝ => ⟪haagRuelleChainVec D (k₁ + 1) s₁ f_a t,
              haagRuelleChainVec D (k₂ + 1) s₂ g t⟫_ℂ) =
            fun t : ℝ => ⟪haagRuelleChainVec D k₁ (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ) t,
              wightmanIndexedVec D.wightman.WData (k₂ + 2)
                (haagRuelleAdjApply D (s₁ 0) (h_part a.1) t (k₂ + 1)
                  (haagRuelleChain D (k₂ + 1) s₂ g t))⟫_ℂ := by
          funext t
          have hf0 : f_a 0 = h_part a.1 := Function.update_self _ _ _
          have h_chain : haagRuelleChain D (k₁ + 1) s₁ f_a t =
              haagRuelleApply D (s₁ 0) (h_part a.1) t k₁
                (haagRuelleChain D k₁ (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ) t) := by
            dsimp [haagRuelleChain, indexedChain, haagRuelleApply, haagRuelleIndexedTest]
            rw [hf0]
            rfl
          dsimp [haagRuelleChainVec]
          rw [h_chain, inner_haagRuelleApply_eq_adj]
        have h_rhs_lim := Filter.Tendsto.inner (𝕜 := ℂ) h_tail_lim h_adj_lim
        rw [← h_adj_t] at h_rhs_lim
        have h_eq_lim := tendsto_nhds_unique h_inn_t h_rhs_lim
        rw [h_eq_lim, inner_smul_right,
          (ih k₂).1 (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ) _
            (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove) _ hne',
          mul_zero]
    · intro heq s₁ f hf s₂ g hg
      subst heq
      let d_of : Fin (k₁ + 1) × Fin (k₁ + 1) → ℝ := fun ij =>
        if hij : ij.1 ≠ ij.2 then (exists_pos_sep_of_velocityDisjoint D.hm (hg hij)).choose else 1
      have hd_pos : ∀ ij : Fin (k₁ + 1) × Fin (k₁ + 1), 0 < d_of ij := fun ij => by
        dsimp [d_of]
        by_cases hij : ij.1 ≠ ij.2
        · rw [dif_pos hij]
          exact (exists_pos_sep_of_velocityDisjoint D.hm (hg hij)).choose_spec.1
        · rw [dif_neg hij]
          exact zero_lt_one
      let d_g : ℝ := Finset.univ.inf' ⟨(0, 0), Finset.mem_univ _⟩ d_of
      have hdg_pos : 0 < d_g :=
        (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun ij _ => hd_pos ij
      have hd_g : ∀ u v : Fin (k₁ + 1), u ≠ v →
          ∀ v₁ ∈ velocitySupport m (g u), ∀ v₂ ∈ velocitySupport m (g v), d_g ≤ ‖v₁ - v₂‖ :=
        fun u v huv v₁ hv₁ v₂ hv₂ => by
          have h1 : d_g ≤ d_of (u, v) := Finset.inf'_le d_of (Finset.mem_univ _)
          have h_eq : d_of (u, v) =
              (exists_pos_sep_of_velocityDisjoint D.hm (hg huv)).choose := by
            dsimp [d_of]
            exact dif_pos huv
          rw [h_eq] at h1
          exact h1.trans
            ((exists_pos_sep_of_velocityDisjoint D.hm (hg huv)).choose_spec.2 v₁ hv₁ v₂ hv₂)
      obtain ⟨n, h_part, h_sum_eq, h_sub_f, h_diam⟩ :=
        exists_smoothWavepacket_partition_diam_lt D.hm (f 0) hdg_pos
      have hf_each : ∀ a ∈ (Finset.univ : Finset (Fin n)),
          Pairwise fun i j : Fin (k₁ + 1) =>
            VelocityDisjoint m (Function.update f 0 (h_part a) i)
              (Function.update f 0 (h_part a) j) := by
        intro a _ i j hij
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨ia, rfl⟩ <;>
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨jb, rfl⟩
        · exact False.elim (hij rfl)
        · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero jb)]
          refine Set.disjoint_of_subset_left ?_ (hf (Fin.succ_ne_zero jb).symm)
          rintro v ⟨p, hp, rfl⟩
          exact ⟨p, h_sub_f a hp, rfl⟩
        · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero ia)]
          refine Set.disjoint_of_subset_right ?_ (hf (Fin.succ_ne_zero ia))
          rintro v ⟨p, hp, rfl⟩
          exact ⟨p, h_sub_f a hp, rfl⟩
        · rw [Function.update_of_ne (Fin.succ_ne_zero ia),
            Function.update_of_ne (Fin.succ_ne_zero jb)]
          exact hf (fun h => hij (congrArg Fin.succ (Fin.succ_inj.mp h)))
      have hf_sum : Pairwise fun i j : Fin (k₁ + 1) =>
          VelocityDisjoint m (Function.update f 0 (finsetSumWavepacket Finset.univ h_part) i)
            (Function.update f 0 (finsetSumWavepacket Finset.univ h_part) j) := by
        rw [h_sum_eq, Function.update_eq_self]
        exact hf
      have h_decomp := haagRuelleLimit_update_finset_sum D L hL Finset.univ (k₁ + 1) 0 s₁ f
        h_part hf_sum hf_each
      have h_orig : L (k₁ + 1) s₁ f hf =
          L (k₁ + 1) s₁ (Function.update f 0 (finsetSumWavepacket Finset.univ h_part)) hf_sum := by
        congr 2
        rw [h_sum_eq, Function.update_eq_self]
      have h_lhs_sum : ⟪L (k₁ + 1) s₁ f hf, L (k₁ + 1) s₂ g hg⟫_ℂ =
          ∑ a ∈ (Finset.univ : Finset (Fin n)).attach,
            ⟪L (k₁ + 1) s₁ (Function.update f 0 (h_part a.1)) (hf_each a.1 a.2),
              L (k₁ + 1) s₂ g hg⟫_ℂ := by
        rw [h_orig, h_decomp, sum_inner]
      have h_f0_vec : fockOneParticleVec D.mode.ν (s₁ 0) (f 0) =
          ∑ a ∈ (Finset.univ : Finset (Fin n)).attach,
            fockOneParticleVec D.mode.ν (s₁ 0) (h_part a.1) := by
        rw [← h_sum_eq, fockOneParticleVec_finsetSum]
        exact (Finset.sum_attach (Finset.univ : Finset (Fin n))
          fun a => fockOneParticleVec D.mode.ν (s₁ 0) (h_part a)).symm
      have h_rhs_sum :
          (∑ σ : Equiv.Perm (Fin (k₁ + 1)), η ^ permInversions σ *
            ∏ i : Fin (k₁ + 1), ⟪fockOneParticleVec D.mode.ν (s₁ i) (f i),
              fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ) =
          ∑ a ∈ (Finset.univ : Finset (Fin n)).attach,
            ∑ σ : Equiv.Perm (Fin (k₁ + 1)), η ^ permInversions σ *
              ∏ i : Fin (k₁ + 1),
                ⟪fockOneParticleVec D.mode.ν (s₁ i) (Function.update f 0 (h_part a.1) i),
                  fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Fin.prod_univ_succ, h_f0_vec, sum_inner, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        rw [Fin.prod_univ_succ, Function.update_self]
        congr 1
      rw [h_lhs_sum, h_rhs_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      let f_a := Function.update f 0 (h_part a.1)
      obtain ⟨j₀, hj₀⟩ := exists_single_overlap_slot k₁ g hd_g (h_part a.1) (h_diam a.1)
      have h_inn_t : Tendsto
          (fun t : ℝ => ⟪haagRuelleChainVec D (k₁ + 1) s₁ f_a t,
            haagRuelleChainVec D (k₁ + 1) s₂ g t⟫_ℂ) F
          (𝓝 ⟪L (k₁ + 1) s₁ f_a (hf_each a.1 a.2), L (k₁ + 1) s₂ g hg⟫_ℂ) :=
        Filter.Tendsto.inner (𝕜 := ℂ) (hL (k₁ + 1) s₁ f_a (hf_each a.1 a.2))
          (hL (k₁ + 1) s₂ g hg)
      have h_adj_lim := tendsto_haagRuelleAdjApply_chain_single_overlap D hF_inv L hL
        k₁ (s₁ 0) (h_part a.1) s₂ g hg j₀ hj₀
      have h_tail_lim := hL k₁ (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ)
        (fun _ _ hij => hf_each a.1 a.2 (Fin.succ_inj.ne.mpr hij))
      have h_adj_t : (fun t : ℝ => ⟪haagRuelleChainVec D (k₁ + 1) s₁ f_a t,
            haagRuelleChainVec D (k₁ + 1) s₂ g t⟫_ℂ) =
          fun t : ℝ => ⟪haagRuelleChainVec D k₁ (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ) t,
            wightmanIndexedVec D.wightman.WData (k₁ + 2)
              (haagRuelleAdjApply D (s₁ 0) (h_part a.1) t (k₁ + 1)
                (haagRuelleChain D (k₁ + 1) s₂ g t))⟫_ℂ := by
        funext t
        have hf0 : f_a 0 = h_part a.1 := Function.update_self _ _ _
        have h_chain : haagRuelleChain D (k₁ + 1) s₁ f_a t =
            haagRuelleApply D (s₁ 0) (h_part a.1) t k₁
              (haagRuelleChain D k₁ (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ) t) := by
          dsimp [haagRuelleChain, indexedChain, haagRuelleApply, haagRuelleIndexedTest]
          rw [hf0]
          rfl
        dsimp [haagRuelleChainVec]
        rw [h_chain, inner_haagRuelleApply_eq_adj]
      have h_rhs_lim := Filter.Tendsto.inner (𝕜 := ℂ) h_tail_lim h_adj_lim
      rw [← h_adj_t] at h_rhs_lim
      have h_eq_lim := tendsto_nhds_unique h_inn_t h_rhs_lim
      have h_ih := (ih k₁).2 rfl (s₁ ∘ Fin.succ) (f_a ∘ Fin.succ)
        (fun _ _ hij => hf_each a.1 a.2 (Fin.succ_inj.ne.mpr hij))
        (s₂ ∘ j₀.succAbove) (g ∘ j₀.succAbove)
        (fun _ _ hij => hg ((Fin.succAbove_right_injective).ne hij))
      rw [h_eq_lim, inner_smul_right, h_ih]
      have h_perm_rew :
          (∑ σ : Equiv.Perm (Fin (k₁ + 1)), η ^ permInversions σ *
            ∏ i : Fin (k₁ + 1),
              ⟪fockOneParticleVec D.mode.ν (s₁ i) (f_a i),
                fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ) =
          ∑ p_pair : Fin (k₁ + 1) × Equiv.Perm (Fin k₁),
            η ^ permInversions (finConsPerm p_pair.1 p_pair.2) *
              ∏ i : Fin (k₁ + 1),
                ⟪fockOneParticleVec D.mode.ν (s₁ i) (f_a i),
                  fockOneParticleVec D.mode.ν
                    (s₂ (finConsPerm p_pair.1 p_pair.2 i))
                    (g (finConsPerm p_pair.1 p_pair.2 i))⟫_ℂ := by
        have h_inv_simp :
            (∑ σ : Equiv.Perm (Fin (k₁ + 1)), η ^ permInversions σ *
              ∏ i : Fin (k₁ + 1),
                ⟪fockOneParticleVec D.mode.ν (s₁ i) (f_a i),
                  fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ) =
            ∑ ρ : Equiv.Perm (Fin (k₁ + 1)), η ^ permInversions ρ *
              ∏ i : Fin (k₁ + 1),
                ⟪fockOneParticleVec D.mode.ν (s₁ i) (f_a i),
                  fockOneParticleVec D.mode.ν (s₂ (ρ i)) (g (ρ i))⟫_ℂ := by
          rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (k₁ + 1))))]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          have h_symm : (Equiv.inv (Equiv.Perm (Fin (k₁ + 1))) ρ).symm = ρ := rfl
          have h_inv : permInversions (Equiv.inv (Equiv.Perm (Fin (k₁ + 1))) ρ) =
              permInversions ρ := permInversions_symm ρ
          rw [h_symm, h_inv]
        rw [h_inv_simp, ← Equiv.sum_comp (finConsPermEquiv k₁)]
        rfl
      rw [h_perm_rew, Fintype.sum_prod_type]
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.mul_sum]
        dsimp only [Function.comp_apply]
        rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k₁))) (fun τ : Equiv.Perm (Fin k₁) =>
          (η ^ j₀.val * ⟪fockOneParticleVec D.mode.ν (s₁ 0) (h_part a.1),
              fockOneParticleVec D.mode.ν (s₂ j₀) (g j₀)⟫_ℂ) *
            (η ^ permInversions τ *
              ∏ u : Fin k₁, ⟪fockOneParticleVec D.mode.ν (s₁ u.succ) (f_a u.succ),
                fockOneParticleVec D.mode.ν (s₂ (j₀.succAbove (τ.symm u)))
                  (g (j₀.succAbove (τ.symm u)))⟫_ℂ))]
        refine Finset.sum_congr rfl fun τ _ => ?_
        have h_inv_symm : (Equiv.inv (Equiv.Perm (Fin k₁)) τ).symm = τ := rfl
        have h_inv_perm : permInversions (Equiv.inv (Equiv.Perm (Fin k₁)) τ) = permInversions τ :=
          permInversions_symm τ
        rw [h_inv_symm, h_inv_perm, permInversions_finConsPerm, pow_add,
          Fin.prod_univ_succ, finConsPerm_zero]
        have hf0 : f_a 0 = h_part a.1 := Function.update_self _ _ _
        rw [hf0]
        simp_rw [finConsPerm_succ]
        ring
      · intro j _ hjne
        refine Finset.sum_eq_zero fun τ _ => ?_
        rw [Fin.prod_univ_succ, finConsPerm_zero]
        have hf0 : f_a 0 = h_part a.1 := Function.update_self _ _ _
        rw [hf0, inner_fockOneParticleVec_eq_zero_of_disjoint D.mode.ν (s₁ 0) (s₂ j) D.hm
          (hj₀ j hjne), zero_mul, mul_zero]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j₀))

theorem inner_haagRuelleOutVec_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s₁ : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (s₂ : Fin r → Fin D.mode.ν) (g : Fin r → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin r => VelocityDisjoint m (g i) (g j)) :
    ⟪haagRuelleOutVec D r s₁ f hf, haagRuelleOutVec D r s₂ g hg⟫_ℂ =
      ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
        ∏ i : Fin r, ⟪fockOneParticleVec D.mode.ν (s₁ i) (f i),
          fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ :=
  (inner_haagRuelleLimit_aux D tendsto_inv_one_add_abs_atTop (haagRuelleOutVec D)
    (tendsto_haagRuelleChainVec_atTop D) r r).2 rfl s₁ f hf s₂ g hg

theorem inner_haagRuelleOutVec_ne
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    (s₁ : Fin r₁ → Fin D.mode.ν) (f : Fin r₁ → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r₁ => VelocityDisjoint m (f i) (f j))
    (s₂ : Fin r₂ → Fin D.mode.ν) (g : Fin r₂ → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin r₂ => VelocityDisjoint m (g i) (g j)) :
    ⟪haagRuelleOutVec D r₁ s₁ f hf, haagRuelleOutVec D r₂ s₂ g hg⟫_ℂ = 0 :=
  (inner_haagRuelleLimit_aux D tendsto_inv_one_add_abs_atTop (haagRuelleOutVec D)
    (tendsto_haagRuelleChainVec_atTop D) r₁ r₂).1 s₁ f hf s₂ g hg hne

theorem inner_haagRuelleInVec_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s₁ : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (s₂ : Fin r → Fin D.mode.ν) (g : Fin r → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin r => VelocityDisjoint m (g i) (g j)) :
    ⟪haagRuelleInVec D r s₁ f hf, haagRuelleInVec D r s₂ g hg⟫_ℂ =
      ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
        ∏ i : Fin r, ⟪fockOneParticleVec D.mode.ν (s₁ i) (f i),
          fockOneParticleVec D.mode.ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ :=
  (inner_haagRuelleLimit_aux D tendsto_inv_one_add_abs_atBot (haagRuelleInVec D)
    (tendsto_haagRuelleChainVec_atBot D) r r).2 rfl s₁ f hf s₂ g hg

theorem inner_haagRuelleInVec_ne
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    (s₁ : Fin r₁ → Fin D.mode.ν) (f : Fin r₁ → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r₁ => VelocityDisjoint m (f i) (f j))
    (s₂ : Fin r₂ → Fin D.mode.ν) (g : Fin r₂ → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin r₂ => VelocityDisjoint m (g i) (g j)) :
    ⟪haagRuelleInVec D r₁ s₁ f hf, haagRuelleInVec D r₂ s₂ g hg⟫_ℂ = 0 :=
  (inner_haagRuelleLimit_aux D tendsto_inv_one_add_abs_atBot (haagRuelleInVec D)
    (tendsto_haagRuelleChainVec_atBot D) r₁ r₂).1 s₁ f hf s₂ g hg hne

theorem inner_haagRuelleInVec_eq_inner_haagRuelleOutVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r₁ r₂ : ℕ)
    (s₁ : Fin r₁ → Fin D.mode.ν) (f : Fin r₁ → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r₁ => VelocityDisjoint m (f i) (f j))
    (s₂ : Fin r₂ → Fin D.mode.ν) (g : Fin r₂ → SmoothWavepacket)
    (hg : Pairwise fun i j : Fin r₂ => VelocityDisjoint m (g i) (g j)) :
    ⟪haagRuelleInVec D r₁ s₁ f hf, haagRuelleInVec D r₂ s₂ g hg⟫_ℂ =
      ⟪haagRuelleOutVec D r₁ s₁ f hf, haagRuelleOutVec D r₂ s₂ g hg⟫_ℂ := by
  by_cases h : r₁ = r₂
  · subst h
    rw [inner_haagRuelleInVec_eq, inner_haagRuelleOutVec_eq]
  · rw [inner_haagRuelleInVec_ne D h, inner_haagRuelleOutVec_ne D h]

end

def fockSectorIndicatorFn (ν r : ℕ) : FockOmega ν → ℂ :=
  fun z => if z.1 = r then 1 else 0

lemma fockSectorIndicatorFn_eq_sectorToOmega (ν r : ℕ) :
    fockSectorIndicatorFn ν r = sectorToOmega ν r (fun _ => (1 : ℂ)) := by
  ext z
  by_cases h : z.1 = r
  · simp [fockSectorIndicatorFn, sectorToOmega, h]
  · simp [fockSectorIndicatorFn, sectorToOmega, h]

lemma measurable_fockSectorIndicatorFn (ν r : ℕ) :
    Measurable (fockSectorIndicatorFn ν r) := by
  rw [fockSectorIndicatorFn_eq_sectorToOmega]
  exact measurable_sectorToOmega measurable_const

lemma norm_fockSectorIndicatorFn_le (ν r : ℕ) (z : FockOmega ν) :
    ‖fockSectorIndicatorFn ν r z‖ ≤ 1 := by
  by_cases h : z.1 = r <;> simp [fockSectorIndicatorFn, h]

def fockSectorIndicatorCLM (ν r : ℕ) : FockHilbert ν →L[ℂ] FockHilbert ν :=
  fockMultCLM (fockSectorIndicatorFn ν r) (measurable_fockSectorIndicatorFn ν r)
    zero_le_one (norm_fockSectorIndicatorFn_le ν r)

lemma fockSectorIndicatorCLM_coeFn (ν r : ℕ) (x : FockHilbert ν) :
    (fockSectorIndicatorCLM ν r x : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      fun z => fockSectorIndicatorFn ν r z * (x : FockOmega ν → ℂ) z :=
  fockMultCLM_coeFn (fockSectorIndicatorFn ν r) (measurable_fockSectorIndicatorFn ν r)
    zero_le_one (norm_fockSectorIndicatorFn_le ν r) x

def fockOmegaSectorPermFun (ν r : ℕ) (π : Equiv.Perm (Fin r))
    (z : FockOmega ν) : FockOmega ν :=
  if h : z.1 = r then ⟨r, fockSectorPermEquiv ν r π (h ▸ z.2)⟩ else z

@[simp]
lemma fockOmegaSectorPermFun_eq (ν r : ℕ) (π : Equiv.Perm (Fin r)) (x : FockSectorDom ν r) :
    fockOmegaSectorPermFun ν r π ⟨r, x⟩ = ⟨r, fockSectorPermEquiv ν r π x⟩ := by
  simp [fockOmegaSectorPermFun]

@[simp]
lemma fockOmegaSectorPermFun_ne (ν : ℕ) {r r' : ℕ} (h : r' ≠ r) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r') :
    fockOmegaSectorPermFun ν r π ⟨r', x⟩ = ⟨r', x⟩ := by
  simp [fockOmegaSectorPermFun, h]

lemma measurable_fockOmegaSectorPermFun (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    Measurable (fockOmegaSectorPermFun ν r π) := by
  intro U hU
  rw [measurableSet_fockOmega_iff]
  intro r'
  by_cases hr : r' = r
  · subst hr
    have hpre : Sigma.mk r' ⁻¹' (fockOmegaSectorPermFun ν r' π ⁻¹' U) =
        fockSectorPermEquiv ν r' π ⁻¹' (Sigma.mk r' ⁻¹' U) := by
      ext x
      simp [fockOmegaSectorPermFun]
    rw [hpre]
    exact (fockSectorPermEquiv ν r' π).measurable ((measurableSet_fockOmega_iff ν U).mp hU r')
  · have hpre : Sigma.mk r' ⁻¹' (fockOmegaSectorPermFun ν r π ⁻¹' U) = Sigma.mk r' ⁻¹' U := by
      ext x
      simp [fockOmegaSectorPermFun, hr]
    rw [hpre]
    exact (measurableSet_fockOmega_iff ν U).mp hU r'

def fockOmegaSectorPermEquiv (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    FockOmega ν ≃ᵐ FockOmega ν where
  toFun := fockOmegaSectorPermFun ν r π
  invFun := fockOmegaSectorPermFun ν r π.symm
  left_inv z := by
    rcases z with ⟨r', x⟩
    by_cases hr : r' = r
    · subst hr
      simp only [fockOmegaSectorPermFun_eq]
      exact congrArg (Sigma.mk r') ((fockSectorPermEquiv ν r' π).left_inv x)
    · simp [hr]
  right_inv z := by
    rcases z with ⟨r', x⟩
    by_cases hr : r' = r
    · subst hr
      simp only [fockOmegaSectorPermFun_eq]
      exact congrArg (Sigma.mk r') ((fockSectorPermEquiv ν r' π).right_inv x)
    · simp [hr]
  measurable_toFun := measurable_fockOmegaSectorPermFun ν r π
  measurable_invFun := measurable_fockOmegaSectorPermFun ν r π.symm

@[simp]
lemma fockOmegaSectorPermEquiv_eq (ν r : ℕ) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r) :
    fockOmegaSectorPermEquiv ν r π ⟨r, x⟩ = ⟨r, fockSectorPermEquiv ν r π x⟩ :=
  fockOmegaSectorPermFun_eq ν r π x

lemma fockOmegaSectorPermEquiv_ne (ν : ℕ) {r r' : ℕ} (h : r' ≠ r) (π : Equiv.Perm (Fin r))
    (x : FockSectorDom ν r') :
    fockOmegaSectorPermEquiv ν r π ⟨r', x⟩ = ⟨r', x⟩ :=
  fockOmegaSectorPermFun_ne ν h π x

lemma measurePreserving_fockOmegaSectorPermEquiv (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    MeasurePreserving (fockOmegaSectorPermEquiv ν r π) (fockMeasure ν) (fockMeasure ν) := by
  refine ⟨(fockOmegaSectorPermEquiv ν r π).measurable, ?_⟩
  ext S hS
  rw [Measure.map_apply (fockOmegaSectorPermEquiv ν r π).measurable hS]
  unfold fockMeasure
  rw [Measure.sum_apply _ (hS.preimage (fockOmegaSectorPermEquiv ν r π).measurable),
    Measure.sum_apply _ hS]
  refine tsum_congr fun r' => ?_
  rw [Measure.map_apply (measurable_fockSigmaMk ν r')
      (hS.preimage (fockOmegaSectorPermEquiv ν r π).measurable),
    Measure.map_apply (measurable_fockSigmaMk ν r') hS]
  by_cases hr : r' = r
  · subst hr
    have hpre : Sigma.mk r' ⁻¹' (fockOmegaSectorPermEquiv ν r' π ⁻¹' S) =
        fockSectorPermEquiv ν r' π ⁻¹' (Sigma.mk r' ⁻¹' S) := by
      ext x
      simp
    rw [hpre]
    exact (measurePreserving_fockSectorPermEquiv ν r' π).measure_preimage
      ((measurableSet_fockOmega_iff ν S).mp hS r').nullMeasurableSet
  · have hpre : Sigma.mk r' ⁻¹' (fockOmegaSectorPermEquiv ν r π ⁻¹' S) = Sigma.mk r' ⁻¹' S := by
      ext x
      simp [fockOmegaSectorPermEquiv_ne ν hr π x]
    rw [hpre]

def fockSectorPermCLM (ν r : ℕ) (π : Equiv.Perm (Fin r)) :
    FockHilbert ν →L[ℂ] FockHilbert ν :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (fockOmegaSectorPermEquiv ν r π)
    (measurePreserving_fockOmegaSectorPermEquiv ν r π)).toContinuousLinearMap

lemma fockSectorPermCLM_coeFn (ν r : ℕ) (π : Equiv.Perm (Fin r)) (x : FockHilbert ν) :
    (fockSectorPermCLM ν r π x : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      fun z => (x : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r π z) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving x
    (measurePreserving_fockOmegaSectorPermEquiv ν r π)

def SymmFockSubmodule (ν : ℕ) (η : ℂ) : Submodule ℂ (FockHilbert ν) :=
  ⨅ (r : ℕ) (σ : Equiv.Perm (Fin r)),
    LinearMap.ker
      ((fockSectorIndicatorCLM ν r ∘L fockSectorPermCLM ν r σ -
        (η ^ permInversions σ) • fockSectorIndicatorCLM ν r).toLinearMap)

theorem isClosed_symmFockSubmodule (ν : ℕ) (η : ℂ) :
    IsClosed (SymmFockSubmodule ν η : Set (FockHilbert ν)) := by
  have h_coe : (SymmFockSubmodule ν η : Set (FockHilbert ν)) =
      ⋂ r : ℕ, ⋂ σ : Equiv.Perm (Fin r),
        ((LinearMap.ker ((fockSectorIndicatorCLM ν r ∘L fockSectorPermCLM ν r σ -
          (η ^ permInversions σ) • fockSectorIndicatorCLM ν r).toLinearMap) :
          Submodule ℂ (FockHilbert ν)) : Set (FockHilbert ν)) := by
    simp [SymmFockSubmodule, Submodule.coe_iInf]
  rw [h_coe]
  refine isClosed_iInter fun r => isClosed_iInter fun σ => ?_
  let T : FockHilbert ν →L[ℂ] FockHilbert ν :=
    fockSectorIndicatorCLM ν r ∘L fockSectorPermCLM ν r σ -
      (η ^ permInversions σ) • fockSectorIndicatorCLM ν r
  change IsClosed { v : FockHilbert ν | T v = 0 }
  exact isClosed_eq T.continuous continuous_const

instance instCompleteSpaceSymmFockSubmodule (ν : ℕ) (η : ℂ) :
    CompleteSpace (SymmFockSubmodule ν η) :=
  (isClosed_symmFockSubmodule ν η).completeSpace_coe

abbrev SymmFockHilbert (ν : ℕ) (η : ℂ) : Type :=
  ↥(SymmFockSubmodule ν η)

def fockSymmProjCLM (ν : ℕ) (η : ℂ) : FockHilbert ν →L[ℂ] FockHilbert ν :=
  (SymmFockSubmodule ν η).starProjection

lemma mem_symmFockSubmodule_iff {ν : ℕ} {η : ℂ} {Ψ : FockHilbert ν} :
    Ψ ∈ SymmFockSubmodule ν η ↔
      ∀ (r : ℕ) (σ : Equiv.Perm (Fin r)),
        fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Ψ) =
          (η ^ permInversions σ) • fockSectorIndicatorCLM ν r Ψ := by
  simp [SymmFockSubmodule, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

lemma symmFockSubmodule_ae_sector {ν : ℕ} {η : ℂ} {Ψ : FockHilbert ν}
    (hΨ : Ψ ∈ SymmFockSubmodule ν η) (r : ℕ) (σ : Equiv.Perm (Fin r)) :
    ∀ᵐ x : FockSectorDom ν r ∂(fockSectorMeasure ν r),
      (Ψ : FockOmega ν → ℂ) ⟨r, fockSectorPermEquiv ν r σ x⟩ =
        η ^ permInversions σ * (Ψ : FockOmega ν → ℂ) ⟨r, x⟩ := by
  have heq := mem_symmFockSubmodule_iff.mp hΨ r σ
  have h_ae : (fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Ψ) : FockOmega ν → ℂ)
      =ᶠ[ae (fockMeasure ν)]
      (((η ^ permInversions σ) • fockSectorIndicatorCLM ν r Ψ : FockHilbert ν) :
        FockOmega ν → ℂ) := by
    rw [heq]
  have h1 := fockSectorIndicatorCLM_coeFn ν r (fockSectorPermCLM ν r σ Ψ)
  have h2 := fockSectorPermCLM_coeFn ν r σ Ψ
  have h3 := (MeasureTheory.Lp.coeFn_smul (η ^ permInversions σ) (fockSectorIndicatorCLM ν r Ψ))
  have h4 := fockSectorIndicatorCLM_coeFn ν r Ψ
  have h_z : ∀ᵐ z : FockOmega ν ∂(fockMeasure ν),
      fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) =
        η ^ permInversions σ *
          (fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) z) := by
    have h2_mp :
        (fun z : FockOmega ν =>
          (fockSectorPermCLM ν r σ Ψ : FockOmega ν → ℂ) z)
          =ᶠ[ae (fockMeasure ν)]
        fun z : FockOmega ν => (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) := h2
    filter_upwards [h_ae, h1, h2_mp, h3, h4] with z hza hz1 hz2 hz3 hz4
    have hL : (fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Ψ) : FockOmega ν → ℂ) z =
        fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) :=
      by rw [hz1, hz2]
    have hR :
        (((η ^ permInversions σ) • fockSectorIndicatorCLM ν r Ψ : FockHilbert ν) :
          FockOmega ν → ℂ) z =
        η ^ permInversions σ * (fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) z) := by
      rw [hz3, Pi.smul_apply, smul_eq_mul, hz4]
    rw [← hL, ← hR, hza]
  have h_sec := Measure.ae_sum_iff.mp h_z r
  have h_map := ae_of_ae_map (measurable_fockSigmaMk ν r).aemeasurable h_sec
  filter_upwards [h_map] with x hx
  simpa [fockSectorIndicatorFn] using hx

lemma symmSector_perm {ν r : ℕ} {η : ℂ} (hη : η = 1 ∨ η = -1)
    (F : FockSectorDom ν r → ℂ) (σ : Equiv.Perm (Fin r)) (x : FockSectorDom ν r) :
    symmSector ν r η F (fockSectorPermEquiv ν r σ x) =
      η ^ permInversions σ * symmSector ν r η F x := by
  unfold symmSector
  have h_eq :
      (∑ π : Equiv.Perm (Fin r), η ^ permInversions π *
        F (fockSectorPermEquiv ν r π (fockSectorPermEquiv ν r σ x))) =
      η ^ permInversions σ *
        ∑ ρ : Equiv.Perm (Fin r), η ^ permInversions ρ * F (fockSectorPermEquiv ν r ρ x) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft σ.symm), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hperm : fockSectorPermEquiv ν r (Equiv.mulLeft σ.symm ρ)
        (fockSectorPermEquiv ν r σ x) = fockSectorPermEquiv ν r ρ x := by
      rcases x with ⟨k, s⟩
      apply Prod.ext <;> ext a <;> simp [fockSectorPermEquiv]
    have hsign : η ^ permInversions (Equiv.mulLeft σ.symm ρ) =
        η ^ permInversions σ * η ^ permInversions ρ := by
      change η ^ permInversions (σ⁻¹ * ρ) = _
      rw [eta_pow_permInversions_mul hη σ⁻¹ ρ, eta_pow_permInversions_inv hη σ]
    rw [hperm, hsign, mul_assoc]
  rw [h_eq]
  ring

lemma fockSectorIndicatorFn_sectorToOmega_perm {ν r₀ r : ℕ} {η : ℂ}
    (g : FockSectorDom ν r₀ → ℂ)
    (hg_perm : ∀ (σ : Equiv.Perm (Fin r₀)) (x : FockSectorDom ν r₀),
      g (fockSectorPermEquiv ν r₀ σ x) = η ^ permInversions σ * g x)
    (σ : Equiv.Perm (Fin r)) (z : FockOmega ν) :
    fockSectorIndicatorFn ν r z *
        sectorToOmega ν r₀ g (fockOmegaSectorPermEquiv ν r σ z) =
      η ^ permInversions σ * (fockSectorIndicatorFn ν r z * sectorToOmega ν r₀ g z) := by
  rcases z with ⟨r', x⟩
  by_cases hr'0 : r' = r₀
  · subst hr'0
    by_cases hrr : r' = r
    · subst hrr
      simp only [fockSectorIndicatorFn, ↓reduceIte, one_mul, fockOmegaSectorPermEquiv_eq,
        sectorToOmega_sigmaMk_eq]
      exact hg_perm σ x
    · have hne : r' ≠ r := hrr
      simp [fockSectorIndicatorFn, hne]
  · by_cases hrr : r' = r
    · subst hrr
      simp [fockSectorIndicatorFn, fockOmegaSectorPermEquiv_eq, sectorToOmega_sigmaMk_ne ν hr'0]
    · simp [fockSectorIndicatorFn, hrr]

lemma liftSectorToFock_coeFn {ν r : ℕ} {g : FockSectorDom ν r → ℂ}
    (hg_meas : Measurable g) (hg : MemLp g 2 (fockSectorMeasure ν r)) :
    (liftSectorToFock ν r g hg_meas hg : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      sectorToOmega ν r g :=
  (memLp_sectorToOmega hg_meas hg).coeFn_toLp

lemma ae_comp_fockOmegaSectorPermEquiv {ν r : ℕ} (σ : Equiv.Perm (Fin r))
    {u v : FockOmega ν → ℂ} (h : u =ᶠ[ae (fockMeasure ν)] v) :
    (fun z => u (fockOmegaSectorPermEquiv ν r σ z)) =ᶠ[ae (fockMeasure ν)]
      fun z => v (fockOmegaSectorPermEquiv ν r σ z) :=
  (measurePreserving_fockOmegaSectorPermEquiv ν r σ).quasiMeasurePreserving.ae_eq_comp h

lemma fockSectorIndicatorCLM_perm_coeFn {ν r : ℕ} (σ : Equiv.Perm (Fin r))
    (Φ : FockHilbert ν) {F : FockOmega ν → ℂ}
    (hΦ : (Φ : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)] F) :
    (fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Φ) : FockOmega ν → ℂ)
      =ᶠ[ae (fockMeasure ν)]
    fun z => fockSectorIndicatorFn ν r z * F (fockOmegaSectorPermEquiv ν r σ z) := by
  have h1 : (fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Φ) : FockOmega ν → ℂ)
      =ᶠ[ae (fockMeasure ν)]
    fun z => fockSectorIndicatorFn ν r z * (fockSectorPermCLM ν r σ Φ : FockOmega ν → ℂ) z :=
    fockSectorIndicatorCLM_coeFn ν r (fockSectorPermCLM ν r σ Φ)
  have h2 : (fun z => fockSectorIndicatorFn ν r z *
        (fockSectorPermCLM ν r σ Φ : FockOmega ν → ℂ) z)
      =ᶠ[ae (fockMeasure ν)]
    fun z => fockSectorIndicatorFn ν r z * F (fockOmegaSectorPermEquiv ν r σ z) := by
    filter_upwards [fockSectorPermCLM_coeFn ν r σ Φ,
      ae_comp_fockOmegaSectorPermEquiv σ hΦ] with z hz1 hz2
    rw [hz1, hz2]
  exact h1.trans h2

lemma smul_fockSectorIndicatorCLM_coeFn {ν r : ℕ} (c : ℂ) (Φ : FockHilbert ν)
    {F : FockOmega ν → ℂ} (hΦ : (Φ : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)] F) :
    ((c • fockSectorIndicatorCLM ν r Φ : FockHilbert ν) : FockOmega ν → ℂ)
      =ᶠ[ae (fockMeasure ν)]
    fun z => c * (fockSectorIndicatorFn ν r z * F z) := by
  have h1 : ((c • fockSectorIndicatorCLM ν r Φ : FockHilbert ν) : FockOmega ν → ℂ)
      =ᶠ[ae (fockMeasure ν)]
    c • (fockSectorIndicatorCLM ν r Φ : FockOmega ν → ℂ) :=
    MeasureTheory.Lp.coeFn_smul c (fockSectorIndicatorCLM ν r Φ)
  have h2 : (c • (fockSectorIndicatorCLM ν r Φ : FockOmega ν → ℂ))
      =ᶠ[ae (fockMeasure ν)]
    fun z => c * (fockSectorIndicatorFn ν r z * F z) := by
    filter_upwards [fockSectorIndicatorCLM_coeFn ν r Φ, hΦ] with z hz1 hz2
    simp [Pi.smul_apply, smul_eq_mul, hz1, hz2]
  exact h1.trans h2

lemma liftSectorToFock_mem_symmFockSubmodule_aux {ν r₀ : ℕ} {η : ℂ}
    (g : FockSectorDom ν r₀ → ℂ) (Φ : FockHilbert ν)
    (hΦ_coe : (Φ : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)] sectorToOmega ν r₀ g)
    (hg_perm : ∀ (σ : Equiv.Perm (Fin r₀)) (x : FockSectorDom ν r₀),
      g (fockSectorPermEquiv ν r₀ σ x) = η ^ permInversions σ * g x) :
    Φ ∈ SymmFockSubmodule ν η := by
  refine mem_symmFockSubmodule_iff.mpr fun r σ => MeasureTheory.Lp.ext ?_
  refine (fockSectorIndicatorCLM_perm_coeFn σ Φ hΦ_coe).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (smul_fockSectorIndicatorCLM_coeFn (η ^ permInversions σ) Φ hΦ_coe).symm
  exact Filter.Eventually.of_forall fun z =>
    fockSectorIndicatorFn_sectorToOmega_perm g hg_perm σ z

lemma liftSectorToFock_mem_symmFockSubmodule {ν r₀ : ℕ} {η : ℂ}
    {g : FockSectorDom ν r₀ → ℂ} (hg_meas : Measurable g)
    (hg_mem : MemLp g 2 (fockSectorMeasure ν r₀))
    (hg_perm : ∀ (σ : Equiv.Perm (Fin r₀)) (x : FockSectorDom ν r₀),
      g (fockSectorPermEquiv ν r₀ σ x) = η ^ permInversions σ * g x) :
    liftSectorToFock ν r₀ g hg_meas hg_mem ∈ SymmFockSubmodule ν η :=
  liftSectorToFock_mem_symmFockSubmodule_aux g (liftSectorToFock ν r₀ g hg_meas hg_mem)
    (liftSectorToFock_coeFn hg_meas hg_mem) hg_perm

lemma liftSectorToFock_symmSector_mem {ν r : ℕ} {η : ℂ} (hη : η = 1 ∨ η = -1)
    {F : FockSectorDom ν r → ℂ} (hF_meas : Measurable F) (hF : MemLp F 2 (fockSectorMeasure ν r)) :
    liftSectorToFock ν r (symmSector ν r η F) (measurable_symmSector η hF_meas)
      (memLp_symmSector η hF) ∈ SymmFockSubmodule ν η :=
  liftSectorToFock_mem_symmFockSubmodule (measurable_symmSector η hF_meas)
    (memLp_symmSector η hF) (fun σ x => symmSector_perm hη F σ x)

def fockProdAmp (ν r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    FockSectorDom ν r → ℂ :=
  fun x => if x.2 = s then ∏ i : Fin r, (f i).amp (x.1 i) else 0

lemma measurable_fockProdAmp (ν r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    Measurable (fockProdAmp ν r s f) := by
  unfold fockProdAmp
  have h_pred : MeasurableSet { x : FockSectorDom ν r | x.2 = s } :=
    measurable_snd (measurableSet_singleton s)
  have h_prod : Measurable (fun x : FockSectorDom ν r => ∏ i : Fin r, (f i).amp (x.1 i)) :=
    Finset.measurable_prod Finset.univ fun i _ =>
      (f i).smooth.continuous.measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  exact Measurable.ite h_pred h_prod measurable_const

lemma memLp_fockProdAmp (ν r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    MemLp (fockProdAmp ν r s f) 2 (fockSectorMeasure ν r) := by
  refine (memLp_two_iff_integrable_sq_norm
    (measurable_fockProdAmp ν r s f).aestronglyMeasurable).mpr ?_
  let g_k : (Fin r → Fin 3 → ℝ) → ℝ := fun k => ∏ i : Fin r, ‖(f i).amp (k i)‖ ^ 2
  have hg_cont : Continuous g_k :=
    continuous_finsetProd Finset.univ fun i _ =>
      ((f i).smooth.continuous.comp (continuous_apply i)).norm.pow 2
  let K : Set (Fin r → Fin 3 → ℝ) := Set.pi Set.univ fun i : Fin r => tsupport (f i).amp
  have hK_cp : IsCompact K := isCompact_univ_pi fun i => (f i).compactSupport.isCompact
  have hg_supp : Function.support g_k ⊆ K := by
    intro k hk i _
    by_contra hnot
    have h0 : (f i).amp (k i) = 0 := image_eq_zero_of_notMem_tsupport hnot
    exact hk (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0]))
  have hg_cs : HasCompactSupport g_k := HasCompactSupport.of_support_subset_isCompact hK_cp hg_supp
  have hg_int : Integrable g_k volume := hg_cont.integrable_of_hasCompactSupport hg_cs
  have hg_prod : Integrable (fun x : FockSectorDom ν r => g_k x.1) (fockSectorMeasure ν r) :=
    hg_int.comp_fst Measure.count
  refine hg_prod.mono' ((measurable_fockProdAmp ν r s f).norm.pow_const 2).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ⟨k, s'⟩ => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  dsimp [fockProdAmp, g_k]
  split_ifs
  · rw [norm_prod, Finset.prod_pow]
  · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Finset.prod_nonneg fun i _ => sq_nonneg _

def symmFockMultiParticleVec (ν : ℕ) (η : ℂ) (hη : η = 1 ∨ η = -1)
    (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) : SymmFockHilbert ν η :=
  ⟨liftSectorToFock ν r (symmSector ν r η (fockProdAmp ν r s f))
      (measurable_symmSector η (measurable_fockProdAmp ν r s f))
      (memLp_symmSector η (memLp_fockProdAmp ν r s f)),
    liftSectorToFock_symmSector_mem hη (measurable_fockProdAmp ν r s f)
      (memLp_fockProdAmp ν r s f)⟩

lemma coe_symmFockMultiParticleVec (ν : ℕ) (η : ℂ) (hη : η = 1 ∨ η = -1)
    (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    (symmFockMultiParticleVec ν η hη r s f : FockHilbert ν) =
      liftSectorToFock ν r (symmSector ν r η (fockProdAmp ν r s f))
        (measurable_symmSector η (measurable_fockProdAmp ν r s f))
        (memLp_symmSector η (memLp_fockProdAmp ν r s f)) := rfl

lemma symmFockVacuum_mem (ν : ℕ) (η : ℂ) :
    fockVacuum ν ∈ SymmFockSubmodule ν η := by
  unfold fockVacuum
  refine liftSectorToFock_mem_symmFockSubmodule measurable_const (memLp_const (1 : ℂ)) ?_
  intro σ _
  have hσ : σ = 1 := Subsingleton.elim σ 1
  subst hσ
  simp [permInversions_one]

def symmFockVacuum (ν : ℕ) (η : ℂ) : SymmFockHilbert ν η :=
  ⟨fockVacuum ν, symmFockVacuum_mem ν η⟩

lemma symmFockOneParticleVec_mem (ν : ℕ) (η : ℂ) (s : Fin ν) (f : SmoothWavepacket) :
    fockOneParticleVec ν s f ∈ SymmFockSubmodule ν η := by
  unfold fockOneParticleVec
  refine liftSectorToFock_mem_symmFockSubmodule
    (measurable_fockOneParticleFun ν s f) (memLp_fockOneParticleFun ν s f) ?_
  intro σ _
  have hσ : σ = 1 := by
    apply Equiv.ext
    intro i
    exact (Fin.eq_zero (σ i)).trans (Fin.eq_zero i).symm
  subst hσ
  simp [fockSectorPermEquiv, permInversions_one]

def symmFockOneParticleVec (ν : ℕ) (η : ℂ) (s : Fin ν) (f : SmoothWavepacket) :
    SymmFockHilbert ν η :=
  ⟨fockOneParticleVec ν s f, symmFockOneParticleVec_mem ν η s f⟩

lemma symmFockMultiParticleVec_zero (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1)
    (s : Fin 0 → Fin ν) (f : Fin 0 → SmoothWavepacket) :
    symmFockMultiParticleVec ν η hη 0 s f = symmFockVacuum ν η := by
  apply Subtype.ext
  rw [coe_symmFockMultiParticleVec]
  unfold symmFockVacuum fockVacuum
  congr 1
  ext x
  have hs : x.2 = s := Subsingleton.elim x.2 s
  simp [symmSector, fockProdAmp, hs, permInversions_one]

lemma symmFockMultiParticleVec_one (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1)
    (s : Fin 1 → Fin ν) (f : Fin 1 → SmoothWavepacket) :
    symmFockMultiParticleVec ν η hη 1 s f = symmFockOneParticleVec ν η (s 0) (f 0) := by
  apply Subtype.ext
  rw [coe_symmFockMultiParticleVec]
  unfold symmFockOneParticleVec fockOneParticleVec
  congr 1
  ext ⟨k, s'⟩
  have hperm1 : ∀ σ : Equiv.Perm (Fin 1), σ = 1 := fun σ => by
    apply Equiv.ext
    intro i
    exact (Fin.eq_zero (σ i)).trans (Fin.eq_zero i).symm
  have hs_iff : s' = s ↔ s' 0 = s 0 :=
    ⟨fun h => congrFun h 0, fun h => funext fun i => by rw [Fin.eq_zero i]; exact h⟩
  dsimp [symmSector]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin 1))
    (fun σ _ hne => False.elim (hne (hperm1 σ)))
    (fun hnot => False.elim (hnot (Finset.mem_univ 1)))]
  simp only [permInversions_one, Nat.cast_one, Real.sqrt_one, inv_one, Complex.ofReal_one,
    pow_zero, one_mul, Equiv.Perm.coe_one, Function.comp_id, fockProdAmp, fockOneParticleFun,
    Fin.prod_univ_one]
  by_cases h0 : s' 0 = s 0
  · simp [hs_iff.mpr h0]
  · have hne : s' ≠ s := fun h => h0 (hs_iff.mp h)
    simp [hne, h0]

lemma fockMinkowskiTranslate_coeFn (m : ℝ) (ν : ℕ) (a : Fin 4 → ℝ) (x : FockHilbert ν) :
    (fockMinkowskiTranslate m a x : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      fun z => fockMinkowskiPhase a (fockTotalMomentum m z) * (x : FockOmega ν → ℂ) z := by
  unfold fockMinkowskiTranslate
  exact fockMultCLM_coeFn _ _ zero_le_one _ x

lemma norm_fockMinkowskiTranslate_le (m : ℝ) (ν : ℕ) (a : Fin 4 → ℝ) (x : FockHilbert ν) :
    ‖fockMinkowskiTranslate m a x‖ ≤ ‖x‖ := by
  unfold fockMinkowskiTranslate
  simpa using norm_fockMultCLM_apply_le _ _ zero_le_one _ x

lemma fockMinkowskiTranslate_mem_symmFockSubmodule (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ)
    {Ψ : FockHilbert ν} (hΨ : Ψ ∈ SymmFockSubmodule ν η) :
    fockMinkowskiTranslate m a Ψ ∈ SymmFockSubmodule ν η := by
  rw [mem_symmFockSubmodule_iff]
  intro r σ
  have hΨ_eq := mem_symmFockSubmodule_iff.mp hΨ r σ
  have hΨ_ae :
      (fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Ψ) : FockOmega ν → ℂ)
        =ᶠ[ae (fockMeasure ν)]
      ((η ^ permInversions σ) • fockSectorIndicatorCLM ν r Ψ : FockHilbert ν) := by
    rw [hΨ_eq]
  rw [MeasureTheory.Lp.ext_iff]
  have hTΨ := fockMinkowskiTranslate_coeFn m ν a Ψ
  have hTΨ_comp :=
    (measurePreserving_fockOmegaSectorPermEquiv ν r σ).quasiMeasurePreserving.ae_eq_comp hTΨ
  have hL1 := fockSectorIndicatorCLM_coeFn ν r
    (fockSectorPermCLM ν r σ (fockMinkowskiTranslate m a Ψ))
  have hL2 := fockSectorPermCLM_coeFn ν r σ (fockMinkowskiTranslate m a Ψ)
  have hL_in1 := fockSectorIndicatorCLM_coeFn ν r (fockSectorPermCLM ν r σ Ψ)
  have hL_in2 := fockSectorPermCLM_coeFn ν r σ Ψ
  have hR1 := MeasureTheory.Lp.coeFn_smul (η ^ permInversions σ)
    (fockSectorIndicatorCLM ν r (fockMinkowskiTranslate m a Ψ))
  have hR2 := fockSectorIndicatorCLM_coeFn ν r (fockMinkowskiTranslate m a Ψ)
  have hR_in1 := MeasureTheory.Lp.coeFn_smul (η ^ permInversions σ)
    (fockSectorIndicatorCLM ν r Ψ)
  have hR_in2 := fockSectorIndicatorCLM_coeFn ν r Ψ
  filter_upwards [hΨ_ae, hTΨ, hTΨ_comp, hL1, hL2, hL_in1, hL_in2, hR1, hR2, hR_in1, hR_in2] with
    z hzΨ hzT hzTc hzL1 hzL2 hzLi1 hzLi2 hzR1 hzR2 hzRi1 hzRi2
  have hz_pt :
      fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) =
        η ^ permInversions σ * (fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) z) := by
    have hA : fockSectorIndicatorFn ν r z *
        (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) =
        (fockSectorIndicatorCLM ν r (fockSectorPermCLM ν r σ Ψ) : FockOmega ν → ℂ) z := by
      rw [hzLi1, hzLi2]
    have hB : η ^ permInversions σ * (fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) z) =
        ((η ^ permInversions σ) • fockSectorIndicatorCLM ν r Ψ : FockHilbert ν) z := by
      rw [hzRi1, Pi.smul_apply, smul_eq_mul, hzRi2]
    rw [hA, hB, hzΨ]
  have hmom : fockSectorIndicatorFn ν r z *
      fockMinkowskiPhase a (fockTotalMomentum m (fockOmegaSectorPermEquiv ν r σ z)) =
      fockSectorIndicatorFn ν r z * fockMinkowskiPhase a (fockTotalMomentum m z) := by
    rcases z with ⟨r', x⟩
    by_cases hr : r' = r
    · subst hr
      simp only [fockSectorIndicatorFn, ↓reduceIte, one_mul, fockOmegaSectorPermEquiv_eq]
      rw [fockTotalMomentum_perm]
    · simp [fockSectorIndicatorFn, hr]
  have hzTc' : (fockMinkowskiTranslate m a Ψ : FockOmega ν → ℂ)
        (fockOmegaSectorPermEquiv ν r σ z) =
      fockMinkowskiPhase a (fockTotalMomentum m (fockOmegaSectorPermEquiv ν r σ z)) *
        (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) := hzTc
  rw [hzL1, hzL2, hzTc', hzR1, Pi.smul_apply, smul_eq_mul, hzR2, hzT]
  calc fockSectorIndicatorFn ν r z *
        (fockMinkowskiPhase a (fockTotalMomentum m (fockOmegaSectorPermEquiv ν r σ z)) *
          (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z))
      = (fockSectorIndicatorFn ν r z *
          fockMinkowskiPhase a (fockTotalMomentum m (fockOmegaSectorPermEquiv ν r σ z))) *
          (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z) := by ring
    _ = fockMinkowskiPhase a (fockTotalMomentum m z) *
          (fockSectorIndicatorFn ν r z *
            (Ψ : FockOmega ν → ℂ) (fockOmegaSectorPermEquiv ν r σ z)) := by
        rw [hmom]; ring
    _ = fockMinkowskiPhase a (fockTotalMomentum m z) *
          (η ^ permInversions σ * (fockSectorIndicatorFn ν r z * (Ψ : FockOmega ν → ℂ) z)) := by
        rw [hz_pt]
    _ = η ^ permInversions σ *
          (fockSectorIndicatorFn ν r z *
            (fockMinkowskiPhase a (fockTotalMomentum m z) * (Ψ : FockOmega ν → ℂ) z)) := by
        ring

def symmFockMinkowskiTranslate (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ) :
    SymmFockHilbert ν η →L[ℂ] SymmFockHilbert ν η :=
  ((LinearMap.codRestrict (SymmFockSubmodule ν η)
      ((fockMinkowskiTranslate m a).toLinearMap.comp (SymmFockSubmodule ν η).subtype)
      (fun Ψ => fockMinkowskiTranslate_mem_symmFockSubmodule m ν η a Ψ.2)).mkContinuous 1
    (fun Ψ => by
      change ‖fockMinkowskiTranslate m a Ψ.1‖ ≤ 1 * ‖Ψ.1‖
      rw [one_mul]
      exact norm_fockMinkowskiTranslate_le m ν a Ψ.1))

@[simp]
lemma coe_symmFockMinkowskiTranslate (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ)
    (Ψ : SymmFockHilbert ν η) :
    (symmFockMinkowskiTranslate m ν η a Ψ : FockHilbert ν) =
      fockMinkowskiTranslate m a (Ψ : FockHilbert ν) := rfl

lemma symmFockMinkowskiTranslate_zero (m : ℝ) (ν : ℕ) (η : ℂ) :
    symmFockMinkowskiTranslate m ν η 0 = ContinuousLinearMap.id ℂ (SymmFockHilbert ν η) := by
  ext Ψ : 1
  apply Subtype.ext
  rw [coe_symmFockMinkowskiTranslate, ContinuousLinearMap.id_apply, Lp.ext_iff]
  have h1 := fockMinkowskiTranslate_coeFn m ν 0 Ψ.1
  filter_upwards [h1] with z hz
  have hph : fockMinkowskiPhase 0 (fockTotalMomentum m z) = 1 := by
    simp [fockMinkowskiPhase, minkowskiInner_explicit]
  change (fockMinkowskiTranslate m 0 Ψ.1 : FockOmega ν → ℂ) z = (Ψ.1 : FockOmega ν → ℂ) z
  rw [hz, hph, one_mul]

lemma symmFockMinkowskiTranslate_add (m : ℝ) (ν : ℕ) (η : ℂ) (a b : Fin 4 → ℝ) :
    symmFockMinkowskiTranslate m ν η (a + b) =
      (symmFockMinkowskiTranslate m ν η a).comp (symmFockMinkowskiTranslate m ν η b) := by
  ext Ψ : 1
  apply Subtype.ext
  rw [ContinuousLinearMap.comp_apply, coe_symmFockMinkowskiTranslate,
    coe_symmFockMinkowskiTranslate, coe_symmFockMinkowskiTranslate, Lp.ext_iff]
  have hab := fockMinkowskiTranslate_coeFn m ν (a + b) Ψ.1
  have hb := fockMinkowskiTranslate_coeFn m ν b Ψ.1
  have ha := fockMinkowskiTranslate_coeFn m ν a (fockMinkowskiTranslate m b Ψ.1)
  filter_upwards [hab, hb, ha] with z hz1 hz2 hz3
  have hph : fockMinkowskiPhase (a + b) (fockTotalMomentum m z) =
      fockMinkowskiPhase a (fockTotalMomentum m z) *
        fockMinkowskiPhase b (fockTotalMomentum m z) := by
    simp only [fockMinkowskiPhase, ← Complex.exp_add]
    congr 1
    have hmink : minkowskiInner (fockTotalMomentum m z) (a + b) =
        minkowskiInner (fockTotalMomentum m z) a +
          minkowskiInner (fockTotalMomentum m z) b := by
      simp only [minkowskiInner_explicit, Pi.add_apply]
      ring
    rw [hmink, Complex.ofReal_add]
    ring
  change (fockMinkowskiTranslate m (a + b) Ψ.1 : FockOmega ν → ℂ) z =
    (fockMinkowskiTranslate m a (fockMinkowskiTranslate m b Ψ.1) : FockOmega ν → ℂ) z
  rw [hz1, hz3, hz2, hph, mul_assoc]

lemma norm_symmFockMinkowskiTranslate (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ)
    (Ψ : SymmFockHilbert ν η) :
    ‖symmFockMinkowskiTranslate m ν η a Ψ‖ = ‖Ψ‖ := by
  have h1 : ‖symmFockMinkowskiTranslate m ν η a Ψ‖ ≤ ‖Ψ‖ := by
    change ‖fockMinkowskiTranslate m a Ψ.1‖ ≤ ‖Ψ.1‖
    exact norm_fockMinkowskiTranslate_le m ν a Ψ.1
  have h2 : ‖Ψ‖ ≤ ‖symmFockMinkowskiTranslate m ν η a Ψ‖ := by
    have hid : symmFockMinkowskiTranslate m ν η (-a)
        (symmFockMinkowskiTranslate m ν η a Ψ) = Ψ := by
      have hcomp : symmFockMinkowskiTranslate m ν η (-a + a) Ψ = Ψ := by
        rw [neg_add_cancel, symmFockMinkowskiTranslate_zero, ContinuousLinearMap.id_apply]
      rw [← ContinuousLinearMap.comp_apply, ← symmFockMinkowskiTranslate_add]
      exact hcomp
    calc ‖Ψ‖ = ‖symmFockMinkowskiTranslate m ν η (-a)
          (symmFockMinkowskiTranslate m ν η a Ψ)‖ := by rw [hid]
      _ ≤ ‖symmFockMinkowskiTranslate m ν η a Ψ‖ := by
          change ‖fockMinkowskiTranslate m (-a) (symmFockMinkowskiTranslate m ν η a Ψ).1‖ ≤
            ‖(symmFockMinkowskiTranslate m ν η a Ψ).1‖
          exact norm_fockMinkowskiTranslate_le m ν (-a) _
  exact le_antisymm h1 h2

lemma inner_symmFockMinkowskiTranslate (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ)
    (Ψ Φ : SymmFockHilbert ν η) :
    ⟪symmFockMinkowskiTranslate m ν η a Ψ, symmFockMinkowskiTranslate m ν η a Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  let U : SymmFockHilbert ν η →ₗᵢ[ℂ] SymmFockHilbert ν η :=
    ⟨(symmFockMinkowskiTranslate m ν η a).toLinearMap, norm_symmFockMinkowskiTranslate m ν η a⟩
  exact U.inner_map_map Ψ Φ

lemma inner_symmFockMinkowskiTranslate_neg_left (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ)
    (Ψ Φ : SymmFockHilbert ν η) :
    ⟪symmFockMinkowskiTranslate m ν η (-a) Ψ, Φ⟫_ℂ =
      ⟪Ψ, symmFockMinkowskiTranslate m ν η a Φ⟫_ℂ := by
  rw [← inner_symmFockMinkowskiTranslate m ν η a (symmFockMinkowskiTranslate m ν η (-a) Ψ) Φ]
  have hid : symmFockMinkowskiTranslate m ν η a
      (symmFockMinkowskiTranslate m ν η (-a) Ψ) = Ψ := by
    rw [← ContinuousLinearMap.comp_apply, ← symmFockMinkowskiTranslate_add, add_neg_cancel,
      symmFockMinkowskiTranslate_zero, ContinuousLinearMap.id_apply]
  rw [hid]

lemma symmFockMinkowskiTranslate_multiParticleVec {m : ℝ} (hm : 0 < m)
    (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1) (a : Fin 4 → ℝ)
    (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    symmFockMinkowskiTranslate m ν η a (symmFockMultiParticleVec ν η hη r s f) =
      symmFockMultiParticleVec ν η hη r s (fun i => translateWavepacket m hm a (f i)) := by
  apply Subtype.ext
  rw [coe_symmFockMinkowskiTranslate, Lp.ext_iff]
  let F := symmSector ν r η (fockProdAmp ν r s f)
  let G := symmSector ν r η (fockProdAmp ν r s (fun i => translateWavepacket m hm a (f i)))
  have h1 := fockMinkowskiTranslate_coeFn m ν a (symmFockMultiParticleVec ν η hη r s f).1
  have h2 := liftSectorToFock_coeFn (measurable_symmSector η (measurable_fockProdAmp ν r s f))
    (memLp_symmSector η (memLp_fockProdAmp ν r s f))
  have h3 := liftSectorToFock_coeFn
    (measurable_symmSector η (measurable_fockProdAmp ν r s
      (fun i => translateWavepacket m hm a (f i))))
    (memLp_symmSector η (memLp_fockProdAmp ν r s
      (fun i => translateWavepacket m hm a (f i))))
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hz1, coe_symmFockMultiParticleVec, coe_symmFockMultiParticleVec, hz2, hz3]
  rcases z with ⟨r', x⟩
  by_cases hr : r' = r
  · subst hr
    simp only [sectorToOmega_sigmaMk_eq]
    dsimp [F, G, symmSector]
    rw [← mul_assoc, mul_comm (fockMinkowskiPhase a (fockTotalMomentum m ⟨r', x⟩)), mul_assoc,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun π _ => ?_
    have hmom : fockTotalMomentum m ⟨r', x⟩ =
        fockTotalMomentum m ⟨r', (x.1 ∘ π, x.2 ∘ π)⟩ :=
      (fockTotalMomentum_perm m π x).symm
    have hamp : fockProdAmp ν r' s (fun i => translateWavepacket m hm a (f i))
          (x.1 ∘ π, x.2 ∘ π) =
        fockMinkowskiPhase a (fockTotalMomentum m ⟨r', (x.1 ∘ π, x.2 ∘ π)⟩) *
          fockProdAmp ν r' s f (x.1 ∘ π, x.2 ∘ π) := by
      rcases x with ⟨k, s'⟩
      simp only [fockProdAmp, translateWavepacket_apply]
      split_ifs with hs
      · rw [Finset.prod_mul_distrib]
        congr 1
        unfold fockMinkowskiPhase fockTotalMomentum
        have h_mink : minkowskiInner (∑ i : Fin r', massShellVec m ((k ∘ π) i)) a =
            ∑ i : Fin r', minkowskiInner (massShellVec m ((k ∘ π) i)) a := by
          simp only [minkowskiInner_explicit, Finset.sum_apply, Finset.sum_mul]
          simp_rw [← Finset.sum_sub_distrib]
        rw [h_mink, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      · simp
    rw [hmom, hamp]
    ring
  · simp [sectorToOmega_sigmaMk_ne ν hr]

theorem inner_symmFockMultiParticleVec_eq (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1)
    (r : ℕ) (s₁ : Fin r → Fin ν) (f : Fin r → SmoothWavepacket)
    (s₂ : Fin r → Fin ν) (g : Fin r → SmoothWavepacket) :
    ⟪symmFockMultiParticleVec ν η hη r s₁ f, symmFockMultiParticleVec ν η hη r s₂ g⟫_ℂ =
      ∑ σ : Equiv.Perm (Fin r), η ^ permInversions σ *
        ∏ i : Fin r,
          ⟪fockOneParticleVec ν (s₁ i) (f i),
            fockOneParticleVec ν (s₂ (σ.symm i)) (g (σ.symm i))⟫_ℂ := by
  change ⟪(symmFockMultiParticleVec ν η hη r s₁ f : FockHilbert ν),
    (symmFockMultiParticleVec ν η hη r s₂ g : FockHilbert ν)⟫_ℂ = _
  rw [coe_symmFockMultiParticleVec, coe_symmFockMultiParticleVec, inner_liftSectorToFock_eq,
    inner_symmSector_eq hη (memLp_fockProdAmp ν r s₁ f) (memLp_fockProdAmp ν r s₂ g)]
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin r)))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h_inv_symm : (Equiv.inv (Equiv.Perm (Fin r)) σ).symm = σ := rfl
  have h_inv_perm : permInversions (Equiv.inv (Equiv.Perm (Fin r)) σ) = permInversions σ :=
    permInversions_symm σ
  change η ^ permInversions (Equiv.inv (Equiv.Perm (Fin r)) σ) *
      (∫ x : FockSectorDom ν r, star (fockProdAmp ν r s₁ f x) *
        fockProdAmp ν r s₂ g
          (x.1 ∘ (Equiv.inv (Equiv.Perm (Fin r)) σ).symm,
            x.2 ∘ (Equiv.inv (Equiv.Perm (Fin r)) σ).symm)
        ∂(fockSectorMeasure ν r)) = _
  rw [h_inv_symm, h_inv_perm]
  congr 1
  have h1 := memLp_fockProdAmp ν r s₁ f
  have h2 := (memLp_fockProdAmp ν r s₂ g).comp_measurePreserving
    (measurePreserving_fockSectorPermEquiv ν r σ)
  have h_prod_int : Integrable
      (fun x : FockSectorDom ν r =>
        star (fockProdAmp ν r s₁ f x) * fockProdAmp ν r s₂ g (x.1 ∘ σ, x.2 ∘ σ))
      (fockSectorMeasure ν r) := by
    have hi := L2.integrable_inner (𝕜 := ℂ) (h1.toLp _) (h2.toLp _)
    refine hi.congr ?_
    filter_upwards [h1.coeFn_toLp, h2.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [fockSectorPermEquiv, mul_comm]
  rw [integral_fockSectorMeasure_complex h_prod_int, Finset.sum_eq_single s₁]
  · have hs_iff : s₁ ∘ σ = s₂ ↔ ∀ i : Fin r, s₁ i = s₂ (σ.symm i) := by
      constructor
      · intro h i
        calc s₁ i = (s₁ ∘ σ) (σ.symm i) := by simp
          _ = s₂ (σ.symm i) := congrFun h (σ.symm i)
      · intro h
        funext i
        calc (s₁ ∘ σ) i = s₁ (σ i) := rfl
          _ = s₂ (σ.symm (σ i)) := h (σ i)
          _ = s₂ i := by simp
    by_cases hs : s₁ ∘ σ = s₂
    · have hs' := hs_iff.mp hs
      have h_fn : (fun k : Fin r → Fin 3 → ℝ =>
          star (fockProdAmp ν r s₁ f (k, s₁)) * fockProdAmp ν r s₂ g (k ∘ σ, s₁ ∘ σ)) =
          fun k : Fin r → Fin 3 → ℝ =>
            ∏ i : Fin r, star ((f i).amp (k i)) * (g (σ.symm i)).amp (k i) := by
        ext k
        simp only [fockProdAmp, ↓reduceIte, hs, star_prod, Function.comp_apply]
        rw [← Equiv.prod_comp σ.symm (fun j => (g j).amp (k (σ j))), ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp
      rw [h_fn, integral_fintype_prod_volume_eq_prod
        (fun i (p : Fin 3 → ℝ) => star ((f i).amp p) * (g (σ.symm i)).amp p)]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [inner_fockOneParticleVec_eq, if_pos (hs' i)]
    · have h_not_all : ¬ ∀ i : Fin r, s₁ i = s₂ (σ.symm i) := fun h => hs (hs_iff.mpr h)
      obtain ⟨i₀, hi₀⟩ : ∃ i : Fin r, s₁ i ≠ s₂ (σ.symm i) := by
        by_contra hnone
        exact h_not_all fun i => by
          by_contra hne
          exact hnone ⟨i, hne⟩
      have h_z : (fun k : Fin r → Fin 3 → ℝ =>
          star (fockProdAmp ν r s₁ f (k, s₁)) * fockProdAmp ν r s₂ g (k ∘ σ, s₁ ∘ σ)) =
          fun _ => 0 := by
        ext k
        simp [fockProdAmp, hs]
      rw [h_z, integral_zero]
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
      rw [inner_fockOneParticleVec_eq, if_neg hi₀]
  · intro s' _ hne
    have h_z : (fun k : Fin r → Fin 3 → ℝ =>
        star (fockProdAmp ν r s₁ f (k, s')) * fockProdAmp ν r s₂ g (k ∘ σ, s' ∘ σ)) =
        fun _ => 0 := by
      ext k
      simp [fockProdAmp, hne]
    rw [h_z, integral_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ s₁))

theorem inner_symmFockMultiParticleVec_ne (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1)
    {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂)
    (s₁ : Fin r₁ → Fin ν) (f : Fin r₁ → SmoothWavepacket)
    (s₂ : Fin r₂ → Fin ν) (g : Fin r₂ → SmoothWavepacket) :
    ⟪symmFockMultiParticleVec ν η hη r₁ s₁ f, symmFockMultiParticleVec ν η hη r₂ s₂ g⟫_ℂ = 0 := by
  change ⟪(symmFockMultiParticleVec ν η hη r₁ s₁ f : FockHilbert ν),
    (symmFockMultiParticleVec ν η hη r₂ s₂ g : FockHilbert ν)⟫_ℂ = 0
  rw [coe_symmFockMultiParticleVec, coe_symmFockMultiParticleVec]
  exact inner_liftSectorToFock_ne hne _ _ _ _

lemma measure_fockMomentumDiag_eq_zero (r : ℕ) :
    (volume : Measure (Fin r → Fin 3 → ℝ))
      { k : Fin r → Fin 3 → ℝ | ¬ Function.Injective k } = 0 := by
  let K_pair : Fin r × Fin r → Submodule ℝ (Fin r → Fin 3 → ℝ) := fun ij =>
    LinearMap.ker
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin 3 → ℝ) ij.1 -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin 3 → ℝ) ij.2).toLinearMap)
  have h_sub : { k : Fin r → Fin 3 → ℝ | ¬ Function.Injective k } ⊆
      ⋃ ij ∈ Finset.univ.filter (fun p : Fin r × Fin r => p.1 ≠ p.2),
        (K_pair ij : Set (Fin r → Fin 3 → ℝ)) := by
    intro k hk
    have h_not : ¬ ∀ i j : Fin r, k i = k j → i = j := hk
    obtain ⟨i, hi⟩ : ∃ i : Fin r, ¬ ∀ j : Fin r, k i = k j → i = j := by
      by_contra hnone
      exact h_not fun i j hij => by
        by_contra hne
        exact hnone ⟨i, fun h => hne (h j hij)⟩
    obtain ⟨j, hij_eq, hij_ne⟩ : ∃ j : Fin r, k i = k j ∧ i ≠ j := by
      by_contra hnone
      exact hi fun j h => by
        by_contra hne
        exact hnone ⟨j, h, hne⟩
    refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij_ne⟩) ?_
    change k i - k j = 0
    exact sub_eq_zero.mpr hij_eq
  refine measure_mono_null h_sub ?_
  refine (measure_biUnion_null_iff (Set.to_countable _)).mpr fun ij hij => ?_
  have hij_ne : ij.1 ≠ ij.2 := (Finset.mem_filter.mp hij).2
  have hne_top : K_pair ij ≠ ⊤ := by
    intro htop
    let v : Fin r → Fin 3 → ℝ := Function.update 0 ij.1 (fun _ => 1)
    have hv_mem : v ∈ K_pair ij := htop.symm ▸ Submodule.mem_top
    have hv_eq : v ij.1 = v ij.2 := sub_eq_zero.mp hv_mem
    have hv1 : v ij.1 = fun _ => 1 := Function.update_self _ _ _
    have hv2 : v ij.2 = 0 := Function.update_of_ne hij_ne.symm _ _
    rw [hv1, hv2] at hv_eq
    have h10 : (1 : ℝ) = 0 := congrFun hv_eq 0
    exact one_ne_zero h10
  exact Measure.addHaar_submodule volume (K_pair ij) hne_top

def bump1D (x₀ δ : ℝ) (hδ : 0 < δ) : ContDiffBump x₀ where
  rIn := δ / 2
  rOut := δ
  rIn_pos := half_pos hδ
  rIn_lt_rOut := half_lt_self hδ

def bump1DFn (x₀ δ : ℝ) (hδ : 0 < δ) : ℝ → ℝ :=
  (bump1D x₀ δ hδ).normed volume

lemma contDiff_bump1DFn (x₀ δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (bump1DFn x₀ δ hδ) :=
  (bump1D x₀ δ hδ).contDiff_normed

lemma nonneg_bump1DFn (x₀ δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    0 ≤ bump1DFn x₀ δ hδ t :=
  (bump1D x₀ δ hδ).nonneg_normed t

lemma integral_bump1DFn (x₀ δ : ℝ) (hδ : 0 < δ) :
    ∫ t : ℝ, bump1DFn x₀ δ hδ t ∂volume = 1 :=
  (bump1D x₀ δ hδ).integral_normed

lemma tsupport_bump1DFn (x₀ δ : ℝ) (hδ : 0 < δ) :
    tsupport (bump1DFn x₀ δ hδ) = Metric.closedBall x₀ δ :=
  (bump1D x₀ δ hδ).tsupport_normed_eq

lemma support_bump1DFn_subset (x₀ δ : ℝ) (hδ : 0 < δ) :
    Function.support (bump1DFn x₀ δ hδ) ⊆ Metric.closedBall x₀ δ := by
  rw [← tsupport_bump1DFn x₀ δ hδ]
  exact subset_closure

lemma bump1DFn_le (x₀ δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    bump1DFn x₀ δ hδ t ≤ 1 / δ := by
  have h1 := (bump1D x₀ δ hδ).normed_le_div_measure_closedBall_rIn volume t
  change (bump1D x₀ δ hδ).normed volume t ≤ 1 / volume.real (Metric.closedBall x₀ (δ / 2)) at h1
  have h2 : (volume : Measure ℝ).real (Metric.closedBall x₀ (δ / 2)) = δ := by
    rw [Measure.real, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]
    ring
  change (bump1D x₀ δ hδ).normed volume t ≤ _
  rwa [h2] at h1

def bump3DFn (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin 3 → ℝ) : ℝ :=
  ∏ μ : Fin 3, bump1DFn (p₀ μ) δ hδ (p μ)

lemma contDiff_bump3DFn (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (bump3DFn p₀ δ hδ) := by
  have h_eq : bump3DFn p₀ δ hδ = fun p =>
      bump1DFn (p₀ 0) δ hδ (p 0) * bump1DFn (p₀ 1) δ hδ (p 1) * bump1DFn (p₀ 2) δ hδ (p 2) := by
    ext p
    simp [bump3DFn, Fin.prod_univ_three, mul_assoc]
  rw [h_eq]
  have hf : ∀ μ : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => bump1DFn (p₀ μ) δ hδ (p μ)) :=
    fun μ => (contDiff_bump1DFn (p₀ μ) δ hδ).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) μ).contDiff
  exact ((hf 0).mul (hf 1)).mul (hf 2)

lemma nonneg_bump3DFn (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin 3 → ℝ) :
    0 ≤ bump3DFn p₀ δ hδ p :=
  Finset.prod_nonneg fun μ _ => nonneg_bump1DFn (p₀ μ) δ hδ (p μ)

lemma tsupport_bump3DFn_subset (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    tsupport (bump3DFn p₀ δ hδ) ⊆ Metric.closedBall p₀ δ := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hnot
  rw [closedBall_pi p₀ hδ.le, Set.mem_pi] at hnot
  have hex : ∃ μ : Fin 3, p μ ∉ Metric.closedBall (p₀ μ) δ := by
    by_contra h_all
    exact hnot fun μ _ => by
      by_contra h_out
      exact h_all ⟨μ, h_out⟩
  obtain ⟨μ, hμ⟩ := hex
  have h0 : bump1DFn (p₀ μ) δ hδ (p μ) = 0 := by
    by_contra hnz
    exact hμ (support_bump1DFn_subset (p₀ μ) δ hδ (Function.mem_support.mpr hnz))
  exact hp (Finset.prod_eq_zero (Finset.mem_univ μ) h0)

lemma hasCompactSupport_bump3DFn (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (bump3DFn p₀ δ hδ) :=
  IsCompact.of_isClosed_subset (isCompact_closedBall p₀ δ) (isClosed_tsupport _)
    (tsupport_bump3DFn_subset p₀ δ hδ)

lemma integral_bump3DFn (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∫ p : Fin 3 → ℝ, bump3DFn p₀ δ hδ p ∂volume = 1 := by
  unfold bump3DFn
  rw [integral_fintype_prod_volume_eq_prod fun μ (t : ℝ) => bump1DFn (p₀ μ) δ hδ t]
  refine Finset.prod_eq_one fun μ _ => integral_bump1DFn (p₀ μ) δ hδ

lemma bump3DFn_le (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) (p : Fin 3 → ℝ) :
    bump3DFn p₀ δ hδ p ≤ (1 / δ) ^ 3 := by
  unfold bump3DFn
  calc ∏ μ : Fin 3, bump1DFn (p₀ μ) δ hδ (p μ)
      ≤ ∏ _μ : Fin 3, (1 / δ) :=
        Finset.prod_le_prod (fun μ _ => nonneg_bump1DFn (p₀ μ) δ hδ (p μ))
          (fun μ _ => bump1DFn_le (p₀ μ) δ hδ (p μ))
    _ = (1 / δ) ^ 3 := by simp [Finset.prod_const]

def bump3DWavepacket (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) : SmoothWavepacket where
  amp p := (bump3DFn p₀ δ hδ p : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (contDiff_bump3DFn p₀ δ hδ)
  compactSupport := (hasCompactSupport_bump3DFn p₀ δ hδ).comp_left Complex.ofReal_zero

lemma tsupport_bump3DWavepacket_subset (p₀ : Fin 3 → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    tsupport (bump3DWavepacket p₀ δ hδ).amp ⊆ Metric.closedBall p₀ δ := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro p hp
  rw [Function.mem_support] at hp
  have hp' : bump3DFn p₀ δ hδ p ≠ 0 := fun h => hp (by simp [bump3DWavepacket, h])
  exact tsupport_bump3DFn_subset p₀ δ hδ (subset_closure (Function.mem_support.mpr hp'))

lemma memLp_sector_spin_slice {ν : ℕ} (Ψ : FockHilbert ν) (r : ℕ) (s : Fin r → Fin ν) :
    MemLp (fun k : Fin r → Fin 3 → ℝ => (Ψ : FockOmega ν → ℂ) ⟨r, (k, s)⟩) 2 volume := by
  have hΨ_sec : MemLp (fun x : FockSectorDom ν r => (Ψ : FockOmega ν → ℂ) ⟨r, x⟩) 2
      (fockSectorMeasure ν r) := by
    have h_mono := (MeasureTheory.Lp.memLp Ψ).mono_measure (Measure.le_sum
      (fun r' => (fockSectorMeasure ν r').map (Sigma.mk r')) r)
    exact (memLp_map_measure_iff h_mono.aestronglyMeasurable
      (measurable_fockSigmaMk ν r).aemeasurable).mp h_mono
  have hΨ_meas : Measurable (Ψ : FockOmega ν → ℂ) :=
    (MeasureTheory.Lp.stronglyMeasurable Ψ).measurable
  have hk_meas : Measurable (fun k : Fin r → Fin 3 → ℝ => (Ψ : FockOmega ν → ℂ) ⟨r, (k, s)⟩) :=
    (hΨ_meas.comp (measurable_fockSigmaMk ν r)).comp (measurable_id.prodMk measurable_const)
  refine ⟨hk_meas.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ENNReal.toReal 2 = 2 := by norm_num
  rw [h2]
  have h_le :
      (∫⁻ k : Fin r → Fin 3 → ℝ, (‖(Ψ : FockOmega ν → ℂ) ⟨r, (k, s)⟩‖ₑ) ^ (2 : ℝ) ∂volume) ≤
      ∫⁻ x : FockSectorDom ν r, (‖(Ψ : FockOmega ν → ℂ) ⟨r, x⟩‖ₑ) ^ (2 : ℝ)
        ∂(fockSectorMeasure ν r) := by
    unfold fockSectorMeasure
    have hx_meas : Measurable (fun x : FockSectorDom ν r =>
        (‖(Ψ : FockOmega ν → ℂ) ⟨r, x⟩‖ₑ) ^ (2 : ℝ)) :=
      ((hΨ_meas.comp (measurable_fockSigmaMk ν r)).enorm).pow_const (2 : ℝ)
    rw [lintegral_prod_symm _ hx_meas.aemeasurable, lintegral_count]
    exact ENNReal.le_tsum s
  have h_lt := hΨ_sec.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2] at h_lt
  have h_int_lt :
      (∫⁻ x : FockSectorDom ν r, (‖(Ψ : FockOmega ν → ℂ) ⟨r, x⟩‖ₑ) ^ (2 : ℝ)
        ∂(fockSectorMeasure ν r)) < ⊤ :=
    (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mp (by simpa using h_lt)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt h_le h_int_lt).ne

lemma inner_symmFockMultiParticleVec_coe_eq {ν : ℕ} {η : ℂ} (hη : η = 1 ∨ η = -1)
    {Ψ : FockHilbert ν} (hΨ : Ψ ∈ SymmFockSubmodule ν η)
    (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    ⟪Ψ, (symmFockMultiParticleVec ν η hη r s f : FockHilbert ν)⟫_ℂ =
      ((r.factorial : ℝ).sqrt : ℂ) *
        ∫ k : Fin r → Fin 3 → ℝ,
          star ((Ψ : FockOmega ν → ℂ) ⟨r, (k, s)⟩) * ∏ i : Fin r, (f i).amp (k i) ∂volume := by
  let g := symmSector ν r η (fockProdAmp ν r s f)
  have hg_meas := measurable_symmSector η (measurable_fockProdAmp ν r s f)
  have hg_mem := memLp_symmSector η (memLp_fockProdAmp ν r s f)
  rw [coe_symmFockMultiParticleVec]
  change ⟪Ψ, liftSectorToFock ν r g hg_meas hg_mem⟫_ℂ = _
  rw [MeasureTheory.L2.inner_def]
  have h_inner_int : Integrable
      (fun z : FockOmega ν =>
        ⟪(Ψ : FockOmega ν → ℂ) z, (liftSectorToFock ν r g hg_meas hg_mem : FockOmega ν → ℂ) z⟫_ℂ)
      (fockMeasure ν) :=
    MeasureTheory.L2.integrable_inner (𝕜 := ℂ) Ψ (liftSectorToFock ν r g hg_meas hg_mem)
  have h_g_coe := liftSectorToFock_coeFn hg_meas hg_mem
  have h_ae :
      (fun z : FockOmega ν =>
        ⟪(Ψ : FockOmega ν → ℂ) z, (liftSectorToFock ν r g hg_meas hg_mem : FockOmega ν → ℂ) z⟫_ℂ)
        =ᶠ[ae (fockMeasure ν)]
      fun z : FockOmega ν => star ((Ψ : FockOmega ν → ℂ) z) * sectorToOmega ν r g z := by
    filter_upwards [h_g_coe] with z hz
    rw [hz, RCLike.inner_apply, mul_comm]
    rfl
  rw [integral_congr_ae h_ae]
  have hF_int : Integrable (fun z : FockOmega ν =>
      star ((Ψ : FockOmega ν → ℂ) z) * sectorToOmega ν r g z) (fockMeasure ν) :=
    h_inner_int.congr h_ae
  have h_meas_z : Measurable (fun z : FockOmega ν =>
      star ((Ψ : FockOmega ν → ℂ) z) * sectorToOmega ν r g z) :=
    (continuous_star.measurable.comp (MeasureTheory.Lp.stronglyMeasurable Ψ).measurable).mul
      (measurable_sectorToOmega hg_meas)
  have h_sec_eq :
      (∫ z : FockOmega ν, star ((Ψ : FockOmega ν → ℂ) z) * sectorToOmega ν r g z ∂(fockMeasure ν)) =
      ∫ x : FockSectorDom ν r, star ((Ψ : FockOmega ν → ℂ) ⟨r, x⟩) * g x
        ∂(fockSectorMeasure ν r) := by
    let F_z : FockOmega ν → ℂ := fun z => star ((Ψ : FockOmega ν → ℂ) z) * sectorToOmega ν r g z
    have hF_z_int : Integrable F_z (fockMeasure ν) := hF_int
    change ∫ z : FockOmega ν, F_z z ∂(fockMeasure ν) = _
    unfold fockMeasure
    rw [integral_sum_measure hF_z_int, tsum_eq_single r]
    · rw [integral_map (measurable_fockSigmaMk ν r).aemeasurable h_meas_z.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp [F_z]
      rw [sectorToOmega_sigmaMk_eq]
      rfl
    · intro r' hne
      rw [integral_map (measurable_fockSigmaMk ν r').aemeasurable h_meas_z.aestronglyMeasurable]
      have hz : (fun x : FockSectorDom ν r' => F_z ⟨r', x⟩) = fun _ => 0 := by
        ext x
        dsimp [F_z]
        simp [sectorToOmega, hne]
      rw [hz, integral_zero]
  rw [h_sec_eq]
  have hΨ_sec : MemLp (fun x : FockSectorDom ν r => (Ψ : FockOmega ν → ℂ) ⟨r, x⟩) 2
      (fockSectorMeasure ν r) := by
    have h_mono := (MeasureTheory.Lp.memLp Ψ).mono_measure (Measure.le_sum
      (fun r' => (fockSectorMeasure ν r').map (Sigma.mk r')) r)
    exact (memLp_map_measure_iff h_mono.aestronglyMeasurable
      (measurable_fockSigmaMk ν r).aemeasurable).mp h_mono
  have h_prod_int : ∀ π : Equiv.Perm (Fin r),
      Integrable (fun x : FockSectorDom ν r =>
        η ^ permInversions π *
          (star ((Ψ : FockOmega ν → ℂ) ⟨r, x⟩) *
            fockProdAmp ν r s f (fockSectorPermEquiv ν r π x)))
        (fockSectorMeasure ν r) := fun π => by
    have hfp := (memLp_fockProdAmp ν r s f).comp_measurePreserving
      (measurePreserving_fockSectorPermEquiv ν r π)
    have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hΨ_sec.toLp _) (hfp.toLp _)
    refine (hi.const_mul (η ^ permInversions π)).congr ?_
    filter_upwards [hΨ_sec.coeFn_toLp, hfp.coeFn_toLp] with x hx1 hx2
    rw [RCLike.inner_apply, hx1, hx2]
    simp [mul_comm]
  have h_expand :
      (fun x : FockSectorDom ν r => star ((Ψ : FockOmega ν → ℂ) ⟨r, x⟩) * g x) =
      fun x => (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) *
        ∑ π : Equiv.Perm (Fin r), η ^ permInversions π *
          (star ((Ψ : FockOmega ν → ℂ) ⟨r, x⟩) *
            fockProdAmp ν r s f (fockSectorPermEquiv ν r π x)) := by
    ext x
    dsimp [g, symmSector]
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    ring
  rw [h_expand, integral_const_mul, integral_finsetSum Finset.univ fun π _ => h_prod_int π]
  have h_each : ∀ π : Equiv.Perm (Fin r),
      (∫ x : FockSectorDom ν r, η ^ permInversions π *
        (star ((Ψ : FockOmega ν → ℂ) ⟨r, x⟩) *
          fockProdAmp ν r s f (fockSectorPermEquiv ν r π x)) ∂(fockSectorMeasure ν r)) =
      ∫ y : FockSectorDom ν r, star ((Ψ : FockOmega ν → ℂ) ⟨r, y⟩) * fockProdAmp ν r s f y
        ∂(fockSectorMeasure ν r) := fun π => by
    have mp := measurePreserving_fockSectorPermEquiv ν r π.symm
    have h_comp :
        (∫ x : FockSectorDom ν r, η ^ permInversions π *
          (star ((Ψ : FockOmega ν → ℂ) ⟨r, x⟩) *
            fockProdAmp ν r s f (fockSectorPermEquiv ν r π x)) ∂(fockSectorMeasure ν r)) =
        ∫ y : FockSectorDom ν r, η ^ permInversions π *
          (star ((Ψ : FockOmega ν → ℂ) ⟨r, fockSectorPermEquiv ν r π.symm y⟩) *
            fockProdAmp ν r s f
              (fockSectorPermEquiv ν r π (fockSectorPermEquiv ν r π.symm y)))
          ∂(fockSectorMeasure ν r) :=
      (mp.integral_comp' _).symm
    rw [h_comp]
    refine integral_congr_ae ?_
    filter_upwards [symmFockSubmodule_ae_sector hΨ r π.symm] with y hy
    have hcancel : fockSectorPermEquiv ν r π (fockSectorPermEquiv ν r π.symm y) = y := by
      rcases y with ⟨k, sy⟩
      apply Prod.ext <;> ext a <;> simp [fockSectorPermEquiv]
    rw [hy, hcancel, star_mul', star_eta_pow hη, permInversions_symm π]
    have hp2 : η ^ permInversions π * η ^ permInversions π = 1 := by
      rw [← pow_two, ← pow_mul, mul_comm, pow_mul, eta_sq_eq_one hη, one_pow]
    calc η ^ permInversions π *
          (η ^ permInversions π * star ((Ψ : FockOmega ν → ℂ) ⟨r, y⟩) *
            fockProdAmp ν r s f y)
        = (η ^ permInversions π * η ^ permInversions π) *
            (star ((Ψ : FockOmega ν → ℂ) ⟨r, y⟩) * fockProdAmp ν r s f y) := by ring
      _ = star ((Ψ : FockOmega ν → ℂ) ⟨r, y⟩) * fockProdAmp ν r s f y := by
          rw [hp2, one_mul]
  simp_rw [h_each, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]
  have h_sqrt_eq : (((r.factorial : ℝ).sqrt⁻¹ : ℝ) : ℂ) * (r.factorial : ℂ) =
      ((r.factorial : ℝ).sqrt : ℂ) := by
    have hpos : (0 : ℝ) < r.factorial := Nat.cast_pos.mpr (Nat.factorial_pos r)
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    congr 1
    rw [inv_mul_eq_iff_eq_mul₀ (Real.sqrt_ne_zero'.mpr hpos), Real.mul_self_sqrt hpos.le]
  rw [← mul_assoc, h_sqrt_eq]
  congr 1
  have h_y_int : Integrable
      (fun y : FockSectorDom ν r => star ((Ψ : FockOmega ν → ℂ) ⟨r, y⟩) * fockProdAmp ν r s f y)
      (fockSectorMeasure ν r) := by
    have hi := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (hΨ_sec.toLp _)
      ((memLp_fockProdAmp ν r s f).toLp _)
    refine hi.congr ?_
    filter_upwards [hΨ_sec.coeFn_toLp, (memLp_fockProdAmp ν r s f).coeFn_toLp] with y hy1 hy2
    rw [RCLike.inner_apply, hy1, hy2]
    simp [mul_comm]
  rw [integral_fockSectorMeasure_complex h_y_int, Finset.sum_eq_single s]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp [fockProdAmp]
  · intro s' _ hne
    have hz : (fun k : Fin r → Fin 3 → ℝ =>
        star ((Ψ : FockOmega ν → ℂ) ⟨r, (k, s')⟩) * fockProdAmp ν r s f (k, s')) =
        fun _ => 0 := by
      ext k
      simp [fockProdAmp, hne]
    rw [hz, integral_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ s))

lemma exists_pos_sep_of_injective {n : ℕ} (k₀ : Fin n → Fin 3 → ℝ) (hk₀ : Function.Injective k₀) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ i j : Fin n, i ≠ j → d₀ ≤ ‖k₀ i - k₀ j‖ := by
  let offDiag : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 ≠ p.2
  by_cases hne : offDiag.Nonempty
  · refine ⟨offDiag.inf' hne fun p => ‖k₀ p.1 - k₀ p.2‖, ?_, fun i j hij => ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro p hp
      have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      exact norm_sub_pos_iff.mpr fun heq => hp_ne (hk₀ heq)
    · rw [Finset.inf'_le_iff]
      exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩, le_rfl⟩
  · refine ⟨1, zero_lt_one, fun i j hij => ?_⟩
    exact False.elim (hne ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩⟩)

lemma ae_eq_zero_of_integral_disjoint_bump_zero {m : ℝ} (hm : 0 < m) (r' : ℕ)
    (ψ : (Fin (r' + 1) → Fin 3 → ℝ) → ℂ) (hψ_mem : MemLp ψ 2 volume)
    (h_zero_int : ∀ (f : Fin (r' + 1) → SmoothWavepacket),
      Pairwise (fun i j : Fin (r' + 1) => VelocityDisjoint m (f i) (f j)) →
      (∫ k : Fin (r' + 1) → Fin 3 → ℝ,
        star (ψ k) * ∏ i : Fin (r' + 1), (f i).amp (k i) ∂volume) = 0) :
    ∀ᵐ k : Fin (r' + 1) → Fin 3 → ℝ ∂volume, ψ k = 0 := by
  have hψ_loc : LocallyIntegrable ψ volume := hψ_mem.locallyIntegrable (by norm_num)
  have h_diff_ae := (Besicovitch.vitaliFamily
    (volume : Measure (Fin (r' + 1) → Fin 3 → ℝ))).ae_tendsto_average_norm_sub hψ_loc
  have h_inj_ae : ∀ᵐ k₀ : Fin (r' + 1) → Fin 3 → ℝ ∂volume, Function.Injective k₀ := by
    rw [ae_iff]
    exact measure_fockMomentumDiag_eq_zero (r' + 1)
  filter_upwards [h_diff_ae, h_inj_ae] with k₀ hk₀_diff hk₀_inj
  have hk₀_tend := hk₀_diff.comp (Besicovitch.tendsto_filterAt volume k₀)
  have hk₀_star : Tendsto
      (fun δ : ℝ => ⨍ k in Metric.closedBall k₀ δ, ‖star (ψ k) - star (ψ k₀)‖ ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
    refine hk₀_tend.congr fun δ => setAverage_congr_fun measurableSet_closedBall
      (Filter.Eventually.of_forall fun k _ => ?_)
    rw [← star_sub, norm_star]
  obtain ⟨d₀, hd₀_pos, hd₀_sep⟩ := exists_pos_sep_of_injective k₀ hk₀_inj
  let g_wt : ℝ → (Fin (r' + 1) → Fin 3 → ℝ) → ℝ := fun δ k =>
    if hδ : 0 < δ then ∏ i : Fin (r' + 1), bump3DFn (k₀ i) δ hδ (k i) else 0
  have hg_tend : Tendsto (fun δ : ℝ => ∫ k, g_wt δ k ∂volume) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    have h_eq_fn :
        g_wt δ = fun k : Fin (r' + 1) → Fin 3 → ℝ =>
          ∏ i : Fin (r' + 1), bump3DFn (k₀ i) δ hδ_pos (k i) := by
      ext k
      exact dif_pos hδ_pos
    symm
    rw [h_eq_fn, integral_fintype_prod_volume_eq_prod
      fun i (p : Fin 3 → ℝ) => bump3DFn (k₀ i) δ hδ_pos p]
    exact Finset.prod_eq_one fun i _ => integral_bump3DFn (k₀ i) δ hδ_pos
  have hg_supp : ∀ᶠ δ in 𝓝[>] 0, Function.support (g_wt δ) ⊆ Metric.closedBall k₀ δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    intro k hk
    rw [Function.mem_support] at hk
    dsimp [g_wt] at hk
    rw [dif_pos hδ_pos] at hk
    rw [closedBall_pi k₀ hδ_pos.le, Set.mem_pi]
    intro i _
    by_contra hnot
    have h0 : bump3DFn (k₀ i) δ hδ_pos (k i) = 0 := by
      by_contra hnz
      exact hnot (tsupport_bump3DFn_subset (k₀ i) δ hδ_pos
        (subset_closure (Function.mem_support.mpr hnz)))
    exact hk (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hg_bd : ∀ᶠ δ in 𝓝[>] 0, ∀ k : Fin (r' + 1) → Fin 3 → ℝ,
      |g_wt δ k| ≤ (2 : ℝ) ^ (3 * (r' + 1)) / volume.real (Metric.closedBall k₀ δ) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ_pos : 0 < δ := hδ
    intro k
    dsimp [g_wt]
    rw [dif_pos hδ_pos, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
      nonneg_bump3DFn (k₀ i) δ hδ_pos (k i))]
    have h_vol : volume.real (Metric.closedBall k₀ δ) = (2 * δ) ^ (3 * (r' + 1)) := by
      rw [Measure.real, MeasureTheory.volume_pi_closedBall k₀ hδ_pos.le]
      simp_rw [Real.volume_pi_closedBall _ hδ_pos.le, Fintype.card_fin]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_pow (pow_nonneg (by positivity) 3),
        ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg (by positivity) 3) _),
        ← pow_mul, mul_comm 3 (r' + 1)]
    rw [h_vol]
    calc ∏ i : Fin (r' + 1), bump3DFn (k₀ i) δ hδ_pos (k i)
        ≤ ∏ _i : Fin (r' + 1), (1 / δ) ^ 3 :=
          Finset.prod_le_prod (fun i _ => nonneg_bump3DFn (k₀ i) δ hδ_pos (k i))
            (fun i _ => bump3DFn_le (k₀ i) δ hδ_pos (k i))
      _ = (1 / δ) ^ (3 * (r' + 1)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
            mul_comm 3 (r' + 1)]
      _ = (2 : ℝ) ^ (3 * (r' + 1)) / (2 * δ) ^ (3 * (r' + 1)) := by
          have h2 : ((2 : ℝ) ^ (3 * (r' + 1))) ≠ 0 := pow_ne_zero _ two_ne_zero
          rw [mul_pow, div_pow, one_pow, ← div_div, div_self h2]
  have hf_int : ∀ᶠ δ in 𝓝[>] 0,
      IntegrableOn (fun k => star (ψ k)) (Metric.closedBall k₀ δ) volume :=
    Filter.Eventually.of_forall fun δ =>
      (hψ_mem.star.locallyIntegrable (by norm_num)).integrableOn_isCompact
        (isCompact_closedBall k₀ δ)
  have h_lim_star := tendsto_integral_smul_of_tendsto_average_norm_sub
    ((2 : ℝ) ^ (3 * (r' + 1))) hk₀_star hf_int hg_tend hg_supp hg_bd
  have h_lim_zero :
      Tendsto (fun δ : ℝ => ∫ k, g_wt δ k • star (ψ k) ∂volume) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hd₀_pos)] with δ hδ
    have hδ_pos : 0 < δ := hδ.1
    have h2δ : 2 * δ < d₀ := by linarith [hδ.2]
    let f_δ : Fin (r' + 1) → SmoothWavepacket := fun i => bump3DWavepacket (k₀ i) δ hδ_pos
    have hf_δ_disj : Pairwise fun i j : Fin (r' + 1) =>
        VelocityDisjoint m (f_δ i) (f_δ j) := by
      intro i j hij
      rw [velocityDisjoint_iff_tsupport_disjoint hm, Set.disjoint_left]
      intro p hp1 hp2
      have h1 := tsupport_bump3DWavepacket_subset (k₀ i) δ hδ_pos hp1
      have h2 := tsupport_bump3DWavepacket_subset (k₀ j) δ hδ_pos hp2
      rw [Metric.mem_closedBall] at h1 h2
      have h_tri : dist (k₀ i) (k₀ j) ≤ 2 * δ := by
        calc dist (k₀ i) (k₀ j) ≤ dist (k₀ i) p + dist p (k₀ j) := dist_triangle _ _ _
          _ = dist p (k₀ i) + dist p (k₀ j) := by rw [dist_comm (k₀ i) p]
          _ ≤ δ + δ := add_le_add h1 h2
          _ = 2 * δ := by ring
      rw [dist_eq_norm] at h_tri
      linarith [hd₀_sep i j hij]
    have h_eq_int : (∫ k, g_wt δ k • star (ψ k) ∂volume) =
        ∫ k : Fin (r' + 1) → Fin 3 → ℝ,
          star (ψ k) * ∏ i : Fin (r' + 1), (f_δ i).amp (k i) ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      dsimp [g_wt, f_δ, bump3DWavepacket]
      rw [dif_pos hδ_pos, Complex.ofReal_prod]
      ring
    rw [h_eq_int, h_zero_int f_δ hf_δ_disj]
  exact star_eq_zero.mp (tendsto_nhds_unique h_lim_star h_lim_zero)

theorem ortho_disjoint_symmFockMultiParticleVec_eq_zero (ν : ℕ) {m : ℝ} (hm : 0 < m)
    {η : ℂ} (hη : η = 1 ∨ η = -1) (Ψ : SymmFockHilbert ν η)
    (hortho : ∀ (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket),
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) →
      ⟪Ψ, symmFockMultiParticleVec ν η hη r s f⟫_ℂ = 0) :
    Ψ = 0 := by
  apply Subtype.ext
  change (Ψ : FockHilbert ν) = 0
  rw [MeasureTheory.Lp.ext_iff]
  have h_sum_ae : ∀ᵐ z : FockOmega ν ∂(fockMeasure ν), (Ψ.1 : FockOmega ν → ℂ) z = 0 := by
    refine Measure.ae_sum_iff.mpr fun r => ?_
    have hΨ_meas : Measurable (Ψ.1 : FockOmega ν → ℂ) :=
      (MeasureTheory.Lp.stronglyMeasurable Ψ.1).measurable
    have hp_meas : MeasurableSet { z : FockOmega ν | (Ψ.1 : FockOmega ν → ℂ) z = 0 } :=
      hΨ_meas (measurableSet_singleton 0)
    rw [ae_map_iff (measurable_fockSigmaMk ν r).aemeasurable hp_meas]
    have h_spin : ∀ s : Fin r → Fin ν, ∀ᵐ k : Fin r → Fin 3 → ℝ ∂volume,
        (Ψ.1 : FockOmega ν → ℂ) ⟨r, (k, s)⟩ = 0 := by
      intro s
      have h_zero_int : ∀ (f : Fin r → SmoothWavepacket),
          Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) →
          (∫ k : Fin r → Fin 3 → ℝ,
            star ((Ψ.1 : FockOmega ν → ℂ) ⟨r, (k, s)⟩) * ∏ i : Fin r, (f i).amp (k i) ∂volume) =
            0 := by
        intro f hf
        have h_eq := hortho r s f hf
        change ⟪Ψ.1, (symmFockMultiParticleVec ν η hη r s f : FockHilbert ν)⟫_ℂ = 0 at h_eq
        rw [inner_symmFockMultiParticleVec_coe_eq hη Ψ.2 r s f] at h_eq
        have hc_ne : ((r.factorial : ℝ).sqrt : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
            (Nat.cast_pos.mpr (Nat.factorial_pos r)))
        exact (mul_eq_zero.mp h_eq).resolve_left hc_ne
      let ψ : (Fin r → Fin 3 → ℝ) → ℂ := fun k => (Ψ.1 : FockOmega ν → ℂ) ⟨r, (k, s)⟩
      change ∀ᵐ k : Fin r → Fin 3 → ℝ ∂volume, ψ k = 0
      cases r with
      | zero =>
        let f0 : Fin 0 → SmoothWavepacket := fun i => Fin.elim0 i
        have hf0 : Pairwise fun i j : Fin 0 => VelocityDisjoint m (f0 i) (f0 j) := fun i =>
          Fin.elim0 i
        have hi0 := h_zero_int f0 hf0
        have h_const : (fun k : Fin 0 → Fin 3 → ℝ =>
            star (ψ k) * ∏ i : Fin 0, (f0 i).amp (k i)) = fun _ => star (ψ default) := by
          ext k
          rw [Subsingleton.elim k default]
          simp
        have huniv : (volume : Measure (Fin 0 → Fin 3 → ℝ)).real Set.univ = 1 := by
          rw [Measure.real]
          have h_set : (Set.univ : Set (Fin 0 → Fin 3 → ℝ)) =
              Set.pi Set.univ fun _ : Fin 0 => (Set.univ : Set (Fin 3 → ℝ)) := by
            ext k
            simp
          have h1 : (volume : Measure (Fin 0 → Fin 3 → ℝ)) Set.univ = 1 := by
            rw [h_set, volume_pi_pi]
            simp
          rw [h1, ENNReal.toReal_one]
        rw [h_const, integral_const, huniv, one_smul] at hi0
        have hdef0 : ψ default = 0 := star_eq_zero.mp hi0
        exact Filter.Eventually.of_forall fun k => by rw [Subsingleton.elim k default, hdef0]
      | succ r' =>
        exact ae_eq_zero_of_integral_disjoint_bump_zero hm r' ψ
          (memLp_sector_spin_slice Ψ.1 (r' + 1) s) h_zero_int
    have h_ae_all : ∀ᵐ k : Fin r → Fin 3 → ℝ ∂volume, ∀ s : Fin r → Fin ν,
        (Ψ.1 : FockOmega ν → ℂ) ⟨r, (k, s)⟩ = 0 :=
      ae_all_iff.mpr h_spin
    have h_ae_prod : ∀ᵐ x : FockSectorDom ν r ∂(volume.prod Measure.count),
        (Ψ.1 : FockOmega ν → ℂ) ⟨r, x⟩ = 0 := by
      have h_m_set : MeasurableSet
          { x : FockSectorDom ν r | (Ψ.1 : FockOmega ν → ℂ) ⟨r, x⟩ = 0 } :=
        (hΨ_meas.comp (measurable_fockSigmaMk ν r)) (measurableSet_singleton 0)
      rw [Measure.ae_prod_iff_ae_ae h_m_set]
      filter_upwards [h_ae_all] with k hk
      exact Measure.ae_count_iff.mpr hk
    exact h_ae_prod
  refine Filter.EventuallyEq.trans ?_ (MeasureTheory.Lp.coeFn_zero ℂ 2 (fockMeasure ν)).symm
  filter_upwards [h_sum_ae] with z hz
  exact hz

theorem dense_span_disjoint_symmFockMultiParticleVec (ν : ℕ) {m : ℝ} (hm : 0 < m)
    {η : ℂ} (hη : η = 1 ∨ η = -1) :
    (Submodule.span ℂ { Ψ : SymmFockHilbert ν η |
      ∃ (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket),
        Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) ∧
          Ψ = symmFockMultiParticleVec ν η hη r s f }).topologicalClosure = ⊤ := by
  let S : Submodule ℂ (SymmFockHilbert ν η) :=
    Submodule.span ℂ { Ψ : SymmFockHilbert ν η |
      ∃ (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket),
        Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) ∧
          Ψ = symmFockMultiParticleVec ν η hη r s f }
  change S.topologicalClosure = ⊤
  rw [← S.orthogonal_orthogonal_eq_closure]
  suffices hbot : Sᗮ = ⊥ by
    rw [hbot, Submodule.bot_orthogonal_eq_top]
  rw [eq_bot_iff]
  intro Ψ hΨ
  rw [Submodule.mem_bot]
  refine ortho_disjoint_symmFockMultiParticleVec_eq_zero ν hm hη Ψ fun r s f hf => ?_
  have hmem : symmFockMultiParticleVec ν η hη r s f ∈ S :=
    Submodule.subset_span ⟨r, s, f, hf, rfl⟩
  exact inner_eq_zero_symm.mp (hΨ _ hmem)

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_unique_linearIsometry_of_inner_eq_of_dense
    {E F α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (x : α → E) (y : α → F)
    (hinner : ∀ a b : α, ⟪y a, y b⟫_ℂ = ⟪x a, x b⟫_ℂ)
    (hdense : Dense (Submodule.span ℂ (Set.range x) : Set E)) :
    ∃! W : E →ₗᵢ[ℂ] F, ∀ a : α, W (x a) = y a := by
  let e : (α →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ x
  let f : (α →₀ ℂ) →ₗ[ℂ] F := Finsupp.linearCombination ℂ y
  have hnorm_eq : ∀ c : α →₀ ℂ, ‖f c‖ = ‖e c‖ := by
    intro c
    have h_in : ⟪f c, f c⟫_ℂ = ⟪e c, e c⟫_ℂ := by
      dsimp [f, e]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hinner b a]
    have h_sq : ‖f c‖ ^ 2 = ‖e c‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), h_in]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h_sq
  have h_norm_le : ∀ c : α →₀ ℂ, ‖f c‖ ≤ 1 * ‖e c‖ := fun c => by
    rw [one_mul, hnorm_eq c]
  have h_denseRange : DenseRange e := by
    rw [DenseRange]
    have h_range : Set.range e = (Submodule.span ℂ (Set.range x) : Set E) := by
      ext v
      change v ∈ LinearMap.range e ↔ v ∈ Submodule.span ℂ (Set.range x)
      rw [Finsupp.range_linearCombination]
    rw [h_range]
    exact hdense
  let W_clm : E →L[ℂ] F := f.extendOfNorm e
  have hW_eq : ∀ a : α, W_clm (x a) = y a := fun a => by
    have he_a : e (Finsupp.single a (1 : ℂ)) = x a := by
      simp [e, Finsupp.linearCombination_single]
    have hf_a : f (Finsupp.single a (1 : ℂ)) = y a := by
      simp [f, Finsupp.linearCombination_single]
    rw [← he_a, LinearMap.extendOfNorm_eq h_denseRange ⟨1, h_norm_le⟩, hf_a]
  have hW_norm : ∀ v : E, ‖W_clm v‖ = ‖v‖ := by
    refine h_denseRange.induction ?_
      (isClosed_eq (continuous_norm.comp W_clm.continuous) continuous_norm)
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.extendOfNorm_eq h_denseRange ⟨1, h_norm_le⟩, hnorm_eq c]
  let W : E →ₗᵢ[ℂ] F := ⟨W_clm.toLinearMap, hW_norm⟩
  refine ⟨W, hW_eq, fun W' hW' => ?_⟩
  have hcomp : W'.toContinuousLinearMap.toLinearMap.comp e = f := by
    apply Finsupp.lhom_ext
    intro a c
    have he_s : e (Finsupp.single a c) = c • x a := by
      simp [e, Finsupp.linearCombination_single]
    have hf_s : f (Finsupp.single a c) = c • y a := by
      simp [f, Finsupp.linearCombination_single]
    change W' (e (Finsupp.single a c)) = f (Finsupp.single a c)
    rw [he_s, hf_s, map_smul, hW' a]
  have hclm : W_clm = W'.toContinuousLinearMap :=
    LinearMap.extendOfNorm_unique h_denseRange 1 h_norm_le W'.toContinuousLinearMap hcomp
  ext v
  exact (congrFun (congrArg DFunLike.coe hclm) v).symm

abbrev DisjointWavepacketConfig (ν : ℕ) (m : ℝ) : Type :=
  Σ (r : ℕ), (Fin r → Fin ν) ×
    { f : Fin r → SmoothWavepacket // Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j) }

lemma dense_range_symmFockMultiParticleVec (ν : ℕ) {m : ℝ} (hm : 0 < m)
    {η : ℂ} (hη : η = 1 ∨ η = -1) :
    Dense (Submodule.span ℂ (Set.range (fun cfg : DisjointWavepacketConfig ν m =>
      symmFockMultiParticleVec ν η hη cfg.1 cfg.2.1 cfg.2.2.1)) :
      Set (SymmFockHilbert ν η)) := by
  have h_eq : Set.range (fun cfg : DisjointWavepacketConfig ν m =>
      symmFockMultiParticleVec ν η hη cfg.1 cfg.2.1 cfg.2.2.1) =
      { Ψ : SymmFockHilbert ν η |
        ∃ (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket),
          Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) ∧
            Ψ = symmFockMultiParticleVec ν η hη r s f } := by
    ext Ψ
    constructor
    · rintro ⟨⟨r, s, f, hf⟩, rfl⟩
      exact ⟨r, s, f, hf, rfl⟩
    · rintro ⟨r, s, f, hf, rfl⟩
      exact ⟨⟨r, s, f, hf⟩, rfl⟩
  rw [h_eq, Submodule.dense_iff_topologicalClosure_eq_top]
  exact dense_span_disjoint_symmFockMultiParticleVec ν hm hη

def mollerWaveOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    SymmFockHilbert D.mode.ν η →ₗᵢ[ℂ] D.Hilbert :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1)
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      haagRuelleOutVec D cfg.1 cfg.2.1 cfg.2.2.1 cfg.2.2.2)
    (fun ⟨r₁, s₁, f₁, hf₁⟩ ⟨r₂, s₂, f₂, hf₂⟩ => by
      by_cases h : r₁ = r₂
      · subst h
        rw [inner_haagRuelleOutVec_eq, inner_symmFockMultiParticleVec_eq]
      · rw [inner_haagRuelleOutVec_ne D h, inner_symmFockMultiParticleVec_ne D.mode.ν D.mode.hη h])
    (dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη)).choose

theorem mollerWaveOut_symmFockMultiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    mollerWaveOut D (symmFockMultiParticleVec D.mode.ν η D.mode.hη r s f) =
      haagRuelleOutVec D r s f hf :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1)
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      haagRuelleOutVec D cfg.1 cfg.2.1 cfg.2.2.1 cfg.2.2.2)
    (fun ⟨r₁, s₁, f₁, hf₁⟩ ⟨r₂, s₂, f₂, hf₂⟩ => by
      by_cases h : r₁ = r₂
      · subst h
        rw [inner_haagRuelleOutVec_eq, inner_symmFockMultiParticleVec_eq]
      · rw [inner_haagRuelleOutVec_ne D h, inner_symmFockMultiParticleVec_ne D.mode.ν D.mode.hη h])
    (dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη)).choose_spec.1 ⟨r, s, f, hf⟩

theorem mollerWaveOut_unique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (W : SymmFockHilbert D.mode.ν η →ₗᵢ[ℂ] D.Hilbert)
    (hW : ∀ (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      W (symmFockMultiParticleVec D.mode.ν η D.mode.hη r s f) = haagRuelleOutVec D r s f hf) :
    W = mollerWaveOut D :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1)
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      haagRuelleOutVec D cfg.1 cfg.2.1 cfg.2.2.1 cfg.2.2.2)
    (fun ⟨r₁, s₁, f₁, hf₁⟩ ⟨r₂, s₂, f₂, hf₂⟩ => by
      by_cases h : r₁ = r₂
      · subst h
        rw [inner_haagRuelleOutVec_eq, inner_symmFockMultiParticleVec_eq]
      · rw [inner_haagRuelleOutVec_ne D h, inner_symmFockMultiParticleVec_ne D.mode.ν D.mode.hη h])
    (dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη)).choose_spec.2 W
    (fun ⟨r, s, f, hf⟩ => hW r s f hf)

def mollerWaveIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    SymmFockHilbert D.mode.ν η →ₗᵢ[ℂ] D.Hilbert :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1)
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      haagRuelleInVec D cfg.1 cfg.2.1 cfg.2.2.1 cfg.2.2.2)
    (fun ⟨r₁, s₁, f₁, hf₁⟩ ⟨r₂, s₂, f₂, hf₂⟩ => by
      by_cases h : r₁ = r₂
      · subst h
        rw [inner_haagRuelleInVec_eq, inner_symmFockMultiParticleVec_eq]
      · rw [inner_haagRuelleInVec_ne D h, inner_symmFockMultiParticleVec_ne D.mode.ν D.mode.hη h])
    (dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη)).choose

theorem mollerWaveIn_symmFockMultiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    mollerWaveIn D (symmFockMultiParticleVec D.mode.ν η D.mode.hη r s f) =
      haagRuelleInVec D r s f hf :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1)
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      haagRuelleInVec D cfg.1 cfg.2.1 cfg.2.2.1 cfg.2.2.2)
    (fun ⟨r₁, s₁, f₁, hf₁⟩ ⟨r₂, s₂, f₂, hf₂⟩ => by
      by_cases h : r₁ = r₂
      · subst h
        rw [inner_haagRuelleInVec_eq, inner_symmFockMultiParticleVec_eq]
      · rw [inner_haagRuelleInVec_ne D h, inner_symmFockMultiParticleVec_ne D.mode.ν D.mode.hη h])
    (dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη)).choose_spec.1 ⟨r, s, f, hf⟩

theorem mollerWaveIn_unique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (W : SymmFockHilbert D.mode.ν η →ₗᵢ[ℂ] D.Hilbert)
    (hW : ∀ (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      W (symmFockMultiParticleVec D.mode.ν η D.mode.hη r s f) = haagRuelleInVec D r s f hf) :
    W = mollerWaveIn D :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1)
    (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      haagRuelleInVec D cfg.1 cfg.2.1 cfg.2.2.1 cfg.2.2.2)
    (fun ⟨r₁, s₁, f₁, hf₁⟩ ⟨r₂, s₂, f₂, hf₂⟩ => by
      by_cases h : r₁ = r₂
      · subst h
        rw [inner_haagRuelleInVec_eq, inner_symmFockMultiParticleVec_eq]
      · rw [inner_haagRuelleInVec_ne D h, inner_symmFockMultiParticleVec_ne D.mode.ν D.mode.hη h])
    (dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη)).choose_spec.2 W
    (fun ⟨r, s, f, hf⟩ => hW r s f hf)

@[simp]
theorem mollerWaveOut_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    mollerWaveOut D (symmFockVacuum D.mode.ν η) = D.vacuum := by
  let s0 : Fin 0 → Fin D.mode.ν := fun i => Fin.elim0 i
  let f0 : Fin 0 → SmoothWavepacket := fun i => Fin.elim0 i
  have hf0 : Pairwise fun i j : Fin 0 => VelocityDisjoint m (f0 i) (f0 j) := fun i => Fin.elim0 i
  rw [← symmFockMultiParticleVec_zero D.mode.ν D.mode.hη s0 f0,
    mollerWaveOut_symmFockMultiParticleVec D 0 s0 f0 hf0, haagRuelleOutVec_zero]

@[simp]
theorem mollerWaveIn_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    mollerWaveIn D (symmFockVacuum D.mode.ν η) = D.vacuum := by
  let s0 : Fin 0 → Fin D.mode.ν := fun i => Fin.elim0 i
  let f0 : Fin 0 → SmoothWavepacket := fun i => Fin.elim0 i
  have hf0 : Pairwise fun i j : Fin 0 => VelocityDisjoint m (f0 i) (f0 j) := fun i => Fin.elim0 i
  rw [← symmFockMultiParticleVec_zero D.mode.ν D.mode.hη s0 f0,
    mollerWaveIn_symmFockMultiParticleVec D 0 s0 f0 hf0, haagRuelleInVec_zero]

@[simp]
theorem mollerWaveOut_oneParticle
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    mollerWaveOut D (symmFockOneParticleVec D.mode.ν η s f) =
      haagRuelleVacCreate D s f 0 := by
  let s1 : Fin 1 → Fin D.mode.ν := fun _ => s
  let f1 : Fin 1 → SmoothWavepacket := fun _ => f
  have hf1 : Pairwise fun i j : Fin 1 => VelocityDisjoint m (f1 i) (f1 j) := fun i j hij =>
    False.elim (hij (Subsingleton.elim i j))
  rw [← symmFockMultiParticleVec_one D.mode.ν D.mode.hη s1 f1,
    mollerWaveOut_symmFockMultiParticleVec D 1 s1 f1 hf1, haagRuelleOutVec_one]

@[simp]
theorem mollerWaveIn_oneParticle
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    mollerWaveIn D (symmFockOneParticleVec D.mode.ν η s f) =
      haagRuelleVacCreate D s f 0 := by
  let s1 : Fin 1 → Fin D.mode.ν := fun _ => s
  let f1 : Fin 1 → SmoothWavepacket := fun _ => f
  have hf1 : Pairwise fun i j : Fin 1 => VelocityDisjoint m (f1 i) (f1 j) := fun i j hij =>
    False.elim (hij (Subsingleton.elim i j))
  rw [← symmFockMultiParticleVec_one D.mode.ν D.mode.hη s1 f1,
    mollerWaveIn_symmFockMultiParticleVec D 1 s1 f1 hf1, haagRuelleInVec_one]

theorem mollerWaveIn_oneParticle_eq_out
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    mollerWaveIn D (symmFockOneParticleVec D.mode.ν η s f) =
      mollerWaveOut D (symmFockOneParticleVec D.mode.ν η s f) := by
  rw [mollerWaveIn_oneParticle, mollerWaveOut_oneParticle]

theorem translate_mollerWaveOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (Ψ : SymmFockHilbert D.mode.ν η) :
    D.translate a (mollerWaveOut D Ψ) =
      mollerWaveOut D (symmFockMinkowskiTranslate m D.mode.ν η a Ψ) := by
  let L : SymmFockHilbert D.mode.ν η →L[ℂ] D.Hilbert :=
    (D.translate a).comp (mollerWaveOut D).toContinuousLinearMap
  let R_op : SymmFockHilbert D.mode.ν η →L[ℂ] D.Hilbert :=
    (mollerWaveOut D).toContinuousLinearMap.comp (symmFockMinkowskiTranslate m D.mode.ν η a)
  change L Ψ = R_op Ψ
  suffices h_eq : L = R_op by rw [h_eq]
  let S_gen : Submodule ℂ (SymmFockHilbert D.mode.ν η) :=
    Submodule.span ℂ (Set.range (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1))
  have h_dense : Dense (S_gen : Set (SymmFockHilbert D.mode.ν η)) :=
    dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη
  have h_on_span : ∀ v ∈ S_gen, L v = R_op v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨r, s, f, hf⟩, rfl⟩
      dsimp [L, R_op]
      rw [mollerWaveOut_symmFockMultiParticleVec D r s f hf,
        translate_haagRuelleOutVec D a r s f hf,
        symmFockMinkowskiTranslate_multiParticleVec D.hm D.mode.ν D.mode.hη a r s f,
        mollerWaveOut_symmFockMultiParticleVec D r s _ _]
    · simp
    · intro u v _ _ hu hv
      rw [map_add, map_add, hu, hv]
    · intro c u _ hu
      rw [map_smul, map_smul, hu]
  have h_all : ∀ v : SymmFockHilbert D.mode.ν η, L v = R_op v :=
    h_dense.induction h_on_span (isClosed_eq L.continuous R_op.continuous)
  exact ContinuousLinearMap.ext h_all

theorem translate_mollerWaveIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (Ψ : SymmFockHilbert D.mode.ν η) :
    D.translate a (mollerWaveIn D Ψ) =
      mollerWaveIn D (symmFockMinkowskiTranslate m D.mode.ν η a Ψ) := by
  let L : SymmFockHilbert D.mode.ν η →L[ℂ] D.Hilbert :=
    (D.translate a).comp (mollerWaveIn D).toContinuousLinearMap
  let R_op : SymmFockHilbert D.mode.ν η →L[ℂ] D.Hilbert :=
    (mollerWaveIn D).toContinuousLinearMap.comp (symmFockMinkowskiTranslate m D.mode.ν η a)
  change L Ψ = R_op Ψ
  suffices h_eq : L = R_op by rw [h_eq]
  let S_gen : Submodule ℂ (SymmFockHilbert D.mode.ν η) :=
    Submodule.span ℂ (Set.range (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1))
  have h_dense : Dense (S_gen : Set (SymmFockHilbert D.mode.ν η)) :=
    dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη
  have h_on_span : ∀ v ∈ S_gen, L v = R_op v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨r, s, f, hf⟩, rfl⟩
      dsimp [L, R_op]
      rw [mollerWaveIn_symmFockMultiParticleVec D r s f hf, translate_haagRuelleInVec D a r s f hf,
        symmFockMinkowskiTranslate_multiParticleVec D.hm D.mode.ν D.mode.hη a r s f,
        mollerWaveIn_symmFockMultiParticleVec D r s _ _]
    · simp
    · intro u v _ _ hu hv
      rw [map_add, map_add, hu, hv]
    · intro c u _ hu
      rw [map_smul, map_smul, hu]
  have h_all : ∀ v : SymmFockHilbert D.mode.ν η, L v = R_op v :=
    h_dense.induction h_on_span (isClosed_eq L.continuous R_op.continuous)
  exact ContinuousLinearMap.ext h_all

theorem IsolatedMassShellData.inner_translate_neg_left
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (x y : D.Hilbert) :
    ⟪D.translate (-a) x, y⟫_ℂ = ⟪x, D.translate a y⟫_ℂ := by
  unfold IsolatedMassShellData.translate
  rw [inner_wightmanTranslate_adjoint D.wightman.WData D.wightman.translationInvariant (-a) x y,
    neg_neg]

def scatteringOperatorCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    SymmFockHilbert D.mode.ν η →L[ℂ] SymmFockHilbert D.mode.ν η :=
  (mollerWaveOut D).toContinuousLinearMap.adjoint.comp (mollerWaveIn D).toContinuousLinearMap

theorem inner_scatteringOperatorCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (Ψ_out Ψ_in : SymmFockHilbert D.mode.ν η) :
    ⟪Ψ_out, scatteringOperatorCLM D Ψ_in⟫_ℂ = ⟪mollerWaveOut D Ψ_out, mollerWaveIn D Ψ_in⟫_ℂ := by
  unfold scatteringOperatorCLM
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rfl

lemma norm_mollerWaveOut_toCLM_le_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    ‖(mollerWaveOut D).toContinuousLinearMap‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  exact le_of_eq ((mollerWaveOut D).norm_map v)

theorem norm_scatteringOperatorCLM_apply_le
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (Ψ : SymmFockHilbert D.mode.ν η) :
    ‖scatteringOperatorCLM D Ψ‖ ≤ ‖Ψ‖ := by
  unfold scatteringOperatorCLM
  rw [ContinuousLinearMap.comp_apply]
  have h1 : ‖(mollerWaveOut D).toContinuousLinearMap.adjoint
        ((mollerWaveIn D).toContinuousLinearMap Ψ)‖ ≤
      ‖(mollerWaveOut D).toContinuousLinearMap.adjoint‖ *
        ‖(mollerWaveIn D).toContinuousLinearMap Ψ‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖(mollerWaveOut D).toContinuousLinearMap.adjoint‖ =
      ‖(mollerWaveOut D).toContinuousLinearMap‖ :=
    LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _
  have h3 : ‖(mollerWaveIn D).toContinuousLinearMap Ψ‖ = ‖Ψ‖ := by
    rw [LinearIsometry.coe_toContinuousLinearMap]
    exact (mollerWaveIn D).norm_map Ψ
  rw [h2, h3] at h1
  exact h1.trans (mul_le_of_le_one_left (norm_nonneg Ψ) (norm_mollerWaveOut_toCLM_le_one D))

theorem norm_scatteringOperatorCLM_le_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    ‖scatteringOperatorCLM D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun Ψ => ?_
  rw [one_mul]
  exact norm_scatteringOperatorCLM_apply_le D Ψ

@[simp]
theorem scatteringOperatorCLM_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    scatteringOperatorCLM D (symmFockVacuum D.mode.ν η) = symmFockVacuum D.mode.ν η := by
  refine ext_inner_left ℂ fun Φ => ?_
  rw [inner_scatteringOperatorCLM, mollerWaveIn_vacuum, ← mollerWaveOut_vacuum D,
    (mollerWaveOut D).inner_map_map]

@[simp]
theorem scatteringOperatorCLM_oneParticle
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    scatteringOperatorCLM D (symmFockOneParticleVec D.mode.ν η s f) =
      symmFockOneParticleVec D.mode.ν η s f := by
  refine ext_inner_left ℂ fun Φ => ?_
  rw [inner_scatteringOperatorCLM, mollerWaveIn_oneParticle_eq_out, (mollerWaveOut D).inner_map_map]

theorem scatteringOperatorCLM_comm_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (Ψ : SymmFockHilbert D.mode.ν η) :
    scatteringOperatorCLM D (symmFockMinkowskiTranslate m D.mode.ν η a Ψ) =
      symmFockMinkowskiTranslate m D.mode.ν η a (scatteringOperatorCLM D Ψ) := by
  refine ext_inner_left ℂ fun Φ => ?_
  rw [inner_scatteringOperatorCLM, ← translate_mollerWaveIn D a Ψ, ← D.inner_translate_neg_left a,
    translate_mollerWaveOut D (-a) Φ, ← inner_scatteringOperatorCLM,
    inner_symmFockMinkowskiTranslate_neg_left]

def AsymptoticSubspaceIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    Submodule ℂ D.Hilbert :=
  LinearMap.range (mollerWaveIn D).toLinearMap

def AsymptoticSubspaceOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    Submodule ℂ D.Hilbert :=
  LinearMap.range (mollerWaveOut D).toLinearMap

theorem isClosed_asymptoticSubspaceIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    IsClosed (AsymptoticSubspaceIn D : Set D.Hilbert) := by
  rw [AsymptoticSubspaceIn, LinearMap.coe_range, LinearIsometry.coe_toLinearMap]
  exact (mollerWaveIn D).isometry.isUniformInducing.isComplete_range.isClosed

theorem isClosed_asymptoticSubspaceOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) :
    IsClosed (AsymptoticSubspaceOut D : Set D.Hilbert) := by
  rw [AsymptoticSubspaceOut, LinearMap.coe_range, LinearIsometry.coe_toLinearMap]
  exact (mollerWaveOut D).isometry.isUniformInducing.isComplete_range.isClosed

def WeakAsymptoticCompleteness
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) : Prop :=
  AsymptoticSubspaceIn D = AsymptoticSubspaceOut D

def AsymptoticCompleteness
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η) : Prop :=
  AsymptoticSubspaceIn D = ⊤ ∧ AsymptoticSubspaceOut D = ⊤

theorem AsymptoticCompleteness.toWeak
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} {D : IsolatedMassShellData R S m M η}
    (h : AsymptoticCompleteness D) :
    WeakAsymptoticCompleteness D :=
  h.1.trans h.2.symm

def scatteringWeakUnitary
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness D) :
    SymmFockHilbert D.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert D.mode.ν η :=
  ((mollerWaveIn D).equivRange.trans
    (LinearIsometryEquiv.ofEq (AsymptoticSubspaceIn D) (AsymptoticSubspaceOut D) hweak)).trans
    (mollerWaveOut D).equivRange.symm

theorem mollerWaveOut_scatteringWeakUnitary
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness D) (Ψ : SymmFockHilbert D.mode.ν η) :
    mollerWaveOut D (scatteringWeakUnitary D hweak Ψ) = mollerWaveIn D Ψ := by
  let u : AsymptoticSubspaceOut D :=
    LinearIsometryEquiv.ofEq (AsymptoticSubspaceIn D) (AsymptoticSubspaceOut D) hweak
      ((mollerWaveIn D).equivRange Ψ)
  have happ :
      (((mollerWaveOut D).equivRange ((mollerWaveOut D).equivRange.symm u) :
        AsymptoticSubspaceOut D) : D.Hilbert) = (u : D.Hilbert) :=
    congrArg Subtype.val ((mollerWaveOut D).equivRange.apply_symm_apply u)
  calc mollerWaveOut D (scatteringWeakUnitary D hweak Ψ)
      = (((mollerWaveOut D).equivRange ((mollerWaveOut D).equivRange.symm u) :
          AsymptoticSubspaceOut D) : D.Hilbert) := by
          rw [← LinearIsometry.equivRange_apply_coe (mollerWaveOut D)]
          rfl
    _ = (u : D.Hilbert) := happ
    _ = (((mollerWaveIn D).equivRange Ψ : AsymptoticSubspaceIn D) : D.Hilbert) := by
          dsimp [u]
    _ = mollerWaveIn D Ψ := (mollerWaveIn D).equivRange_apply_coe Ψ

theorem scatteringWeakUnitary_toContinuousLinearMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness D) :
    (scatteringWeakUnitary D hweak :
      SymmFockHilbert D.mode.ν η →L[ℂ] SymmFockHilbert D.mode.ν η) =
      scatteringOperatorCLM D := by
  apply ContinuousLinearMap.ext
  intro Ψ
  refine ext_inner_left ℂ fun Φ => ?_
  change ⟪Φ, scatteringWeakUnitary D hweak Ψ⟫_ℂ = ⟪Φ, scatteringOperatorCLM D Ψ⟫_ℂ
  rw [← (mollerWaveOut D).inner_map_map Φ (scatteringWeakUnitary D hweak Ψ),
    mollerWaveOut_scatteringWeakUnitary D hweak Ψ, ← inner_scatteringOperatorCLM]

theorem scatteringWeakUnitary_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness D) (Ψ : SymmFockHilbert D.mode.ν η) :
    scatteringWeakUnitary D hweak Ψ = scatteringOperatorCLM D Ψ :=
  ContinuousLinearMap.ext_iff.mp (scatteringWeakUnitary_toContinuousLinearMap D hweak) Ψ

theorem scatteringOperatorCLM_adjoint_comp_self
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness D) :
    (scatteringOperatorCLM D).adjoint.comp (scatteringOperatorCLM D) =
      ContinuousLinearMap.id ℂ (SymmFockHilbert D.mode.ν η) := by
  apply ContinuousLinearMap.ext
  intro Ψ
  refine ext_inner_left ℂ fun Φ => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ← scatteringWeakUnitary_apply D hweak Φ, ← scatteringWeakUnitary_apply D hweak Ψ,
    (scatteringWeakUnitary D hweak).inner_map_map, ContinuousLinearMap.id_apply]

theorem scatteringOperatorCLM_comp_adjoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness D) :
    (scatteringOperatorCLM D).comp (scatteringOperatorCLM D).adjoint =
      ContinuousLinearMap.id ℂ (SymmFockHilbert D.mode.ν η) := by
  have h_adj : ∀ v : SymmFockHilbert D.mode.ν η,
      (scatteringOperatorCLM D).adjoint v = (scatteringWeakUnitary D hweak).symm v := by
    intro v
    refine ext_inner_left ℂ fun Φ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, ← scatteringWeakUnitary_apply D hweak Φ,
      LinearIsometryEquiv.inner_map_eq_flip]
  apply ContinuousLinearMap.ext
  intro Ψ
  rw [ContinuousLinearMap.comp_apply, h_adj Ψ, ← scatteringWeakUnitary_apply D hweak,
    LinearIsometryEquiv.apply_symm_apply, ContinuousLinearMap.id_apply]

lemma surjective_mollerWaveIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    Function.Surjective (mollerWaveIn D) := fun y => by
  have hy : y ∈ AsymptoticSubspaceIn D := hcomp.1.symm ▸ Submodule.mem_top
  exact LinearMap.mem_range.mp hy

lemma surjective_mollerWaveOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    Function.Surjective (mollerWaveOut D) := fun y => by
  have hy : y ∈ AsymptoticSubspaceOut D := hcomp.2.symm ▸ Submodule.mem_top
  exact LinearMap.mem_range.mp hy

def mollerWaveInEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    SymmFockHilbert D.mode.ν η ≃ₗᵢ[ℂ] D.Hilbert :=
  LinearIsometryEquiv.ofSurjective (mollerWaveIn D) (surjective_mollerWaveIn D hcomp)

def mollerWaveOutEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    SymmFockHilbert D.mode.ν η ≃ₗᵢ[ℂ] D.Hilbert :=
  LinearIsometryEquiv.ofSurjective (mollerWaveOut D) (surjective_mollerWaveOut D hcomp)

def scatteringUnitary
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    SymmFockHilbert D.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert D.mode.ν η :=
  (mollerWaveInEquiv D hcomp).trans (mollerWaveOutEquiv D hcomp).symm

theorem mollerWaveOut_scatteringUnitary
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) (Ψ : SymmFockHilbert D.mode.ν η) :
    mollerWaveOut D (scatteringUnitary D hcomp Ψ) = mollerWaveIn D Ψ := by
  rw [← LinearIsometryEquiv.coe_ofSurjective (mollerWaveOut D) (surjective_mollerWaveOut D hcomp)]
  change mollerWaveOutEquiv D hcomp
    ((mollerWaveOutEquiv D hcomp).symm (mollerWaveInEquiv D hcomp Ψ)) = mollerWaveIn D Ψ
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem scatteringUnitary_eq_weak
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    scatteringUnitary D hcomp = scatteringWeakUnitary D hcomp.toWeak := by
  apply LinearIsometryEquiv.ext
  intro Ψ
  apply (mollerWaveOut D).injective
  rw [mollerWaveOut_scatteringUnitary, mollerWaveOut_scatteringWeakUnitary]

theorem scatteringUnitary_toContinuousLinearMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    (scatteringUnitary D hcomp :
      SymmFockHilbert D.mode.ν η →L[ℂ] SymmFockHilbert D.mode.ν η) =
      scatteringOperatorCLM D := by
  rw [scatteringUnitary_eq_weak D hcomp, scatteringWeakUnitary_toContinuousLinearMap]

theorem scatteringUnitary_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) (Ψ : SymmFockHilbert D.mode.ν η) :
    scatteringUnitary D hcomp Ψ = scatteringOperatorCLM D Ψ :=
  ContinuousLinearMap.ext_iff.mp (scatteringUnitary_toContinuousLinearMap D hcomp) Ψ

@[simp]
theorem scatteringUnitary_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) :
    scatteringUnitary D hcomp (symmFockVacuum D.mode.ν η) = symmFockVacuum D.mode.ν η := by
  rw [scatteringUnitary_apply, scatteringOperatorCLM_vacuum]

@[simp]
theorem scatteringUnitary_oneParticle
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) :
    scatteringUnitary D hcomp (symmFockOneParticleVec D.mode.ν η s f) =
      symmFockOneParticleVec D.mode.ν η s f := by
  rw [scatteringUnitary_apply, scatteringOperatorCLM_oneParticle]

theorem scatteringUnitary_comm_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness D) (a : Fin 4 → ℝ)
    (Ψ : SymmFockHilbert D.mode.ν η) :
    scatteringUnitary D hcomp (symmFockMinkowskiTranslate m D.mode.ν η a Ψ) =
      symmFockMinkowskiTranslate m D.mode.ν η a (scatteringUnitary D hcomp Ψ) := by
  rw [scatteringUnitary_apply, scatteringUnitary_apply, scatteringOperatorCLM_comm_translate]

end

end

end QFT
