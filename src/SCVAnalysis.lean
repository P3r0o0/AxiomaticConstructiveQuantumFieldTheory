import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Pi

open Complex Filter Topology Set ContinuousLinearMap ContinuousMultilinearMap MeasureTheory
open intervalIntegral
open scoped Distributions FourierTransform RealInnerProductSpace NNReal

namespace Analysis

lemma complex_multilinear_zero_of_real_zero_N {ι : Type*} [Finite ι] (k : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => (ι → ℂ)) ℂ)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h : ∀ x : Fin k → (ι → ℝ), p (fun i => ofRealN (x i)) = 0) :
    p = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  classical
  haveI := Fintype.ofFinite ι
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ ι)
  intro v
  have hx : ∀ j, (Pi.basisFun ℂ ι) (v j) = ofRealN (Pi.basisFun ℝ ι (v j)) := by
    intro j
    rw [h_ofReal]
    ext i
    dsimp [Pi.basisFun]
    by_cases hij : v j = i
    · simp [hij]
    · simp [hij]
  have h_eq : (fun j => (Pi.basisFun ℂ ι) (v j)) = (fun j => ofRealN (Pi.basisFun ℝ ι (v j))) := by
    ext j i
    rw [hx j]
  rw [h_eq]
  exact h (fun j => Pi.basisFun ℝ ι (v j))

lemma tendsto_ofReal_ne (a : ℝ) : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] a) (𝓝[≠] (a : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact continuous_ofReal.continuousAt.tendsto.comp nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ofReal_inj.not.mpr hx

lemma freq_zero_of_real_zero (h : ℂ → ℂ) (a : ℝ) (h_sub : ∀ᶠ t : ℝ in 𝓝 a, h (t : ℂ) = 0) :
    ∃ᶠ z in 𝓝[≠] (a : ℂ), h z = 0 := by
  have h_sub_ne : ∀ᶠ t : ℝ in 𝓝[≠] a, h (t : ℂ) = 0 := nhdsWithin_le_nhds h_sub
  have h_ne_bot : (𝓝[≠] a).NeBot := PerfectSpace.not_isolated a
  have h_freq_real : Filter.Frequently (fun (t : ℝ) => h (t : ℂ) = 0) (𝓝[≠] a) :=
    h_sub_ne.frequently
  have h_tendsto := tendsto_ofReal_ne a
  exact h_tendsto.frequently h_freq_real

lemma analytic_nhds_eq_of_real_eq_1D (f g : ℂ → ℂ) (a : ℝ)
    (hf : AnalyticAt ℂ f (a : ℂ)) (hg : AnalyticAt ℂ g (a : ℂ))
    (h_real : ∀ᶠ t : ℝ in 𝓝 a, f (t : ℂ) = g (t : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 (a : ℂ), f z = g z := by
  have hfg : AnalyticAt ℂ (f - g) (a : ℂ) := hf.sub hg
  have h_sub : ∀ᶠ t : ℝ in 𝓝 a, (f - g) (t : ℂ) = 0 := by
    filter_upwards [h_real] with t ht
    simp [ht]
  have h_freq := freq_zero_of_real_zero (f - g) a h_sub
  have h_zero_or_freq := hfg.eventually_eq_zero_or_eventually_ne_zero
  cases h_zero_or_freq with
  | inl h_zero =>
    filter_upwards [h_zero] with z hz
    exact sub_eq_zero.mp hz
  | inr h_ne =>
    exact (h_freq h_ne).elim

lemma symm_multilinear_real_eq_zero_of_diagonal_zero_N {ι : Type*} [Finite ι] {n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => (ι → ℝ)) ℂ)
    (h_symm : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℝ)), p (fun i => v (σ i)) = p v)
    (h_diag : ∀ x : (ι → ℝ), p (fun _ => x) = 0) :
    p = 0 := by
  haveI := Fintype.ofFinite ι
  apply ContinuousMultilinearMap.ext
  intro v
  have h_func_zero : (fun x : (ι → ℝ) => p (fun _ => x)) = fun _ => 0 := by
    ext x; exact h_diag x
  have h_deriv : iteratedFDeriv ℝ n (fun x : (ι → ℝ) => p (fun _ => x)) 0 v = 0 := by
    rw [h_func_zero]
    rw [iteratedFDeriv_fun_zero]
    simp
  have h_deriv_diag := p.iteratedFDeriv_comp_diagonal 0 v
  rw [h_deriv] at h_deriv_diag
  have h_sum : (∑ σ : Equiv.Perm (Fin n), p (fun i => v (σ i))) = (Nat.factorial n) • (p v) := by
    have h_symm_eval : ∀ σ : Equiv.Perm (Fin n), p (fun i => v (σ i)) = p v := fun σ => h_symm σ v
    rw [Finset.sum_congr rfl (fun σ _ => h_symm_eval σ)]
    rw [Finset.sum_const]
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [h_sum] at h_deriv_diag
  have h_smul_zero := h_deriv_diag.symm
  cases smul_eq_zero.mp h_smul_zero with
  | inl h =>
    have h2 : Nat.factorial n = 0 := Nat.cast_eq_zero.mp h
    exfalso
    exact Nat.factorial_ne_zero n h2
  | inr h => exact h

lemma complex_multilinear_zero_of_diagonal_real_zero_N {ι : Type*} [Finite ι] {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => (ι → ℂ)) ℂ)
    (h_symm : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℂ)), p (fun i => v (σ i)) = p v)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h_diag : ∀ x : (ι → ℝ), p (fun _ => ofRealN x) = 0) :
    p = 0 := by
  haveI := Fintype.ofFinite ι
  let p_real := (p.restrictScalars ℝ).compContinuousLinearMap (fun _ => ofRealN)
  have h_symm_real :
      ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℝ)), p_real (fun i => v (σ i)) = p_real v := by
    intro σ v
    exact h_symm σ (fun i => ofRealN (v i))
  have h_diag_real : ∀ x : (ι → ℝ), p_real (fun _ => x) = 0 := h_diag
  have p_real_zero :=
    symm_multilinear_real_eq_zero_of_diagonal_zero_N p_real h_symm_real h_diag_real
  have h_eval : ∀ v : Fin n → (ι → ℝ), p (fun i => ofRealN (v i)) = 0 := by
    intro v
    have h_zero : p_real v = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => (ι → ℝ)) ℂ) v := by
      rw [p_real_zero]
    exact h_zero
  exact complex_multilinear_zero_of_real_zero_N n p ofRealN h_ofReal h_eval

lemma ftaylorSeries_isSymmetric {ι : Type*} [Fintype ι] {n : ℕ} (f : (ι → ℂ) → ℂ) (a : ι → ℂ)
    (hf : AnalyticAt ℂ f a) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℂ)),
      (ftaylorSeries ℂ f a) n (fun i => v (σ i)) = (ftaylorSeries ℂ f a) n v := by
  intro σ v
  have h_cont : ContDiffAt ℂ ⊤ f a := hf.contDiffAt
  exact h_cont.iteratedFDeriv_comp_perm v σ

lemma ftaylorSeries_diag_zero {ι : Type*} [Fintype ι] {n : ℕ} (f : (ι → ℂ) → ℂ) (a : ι → ℂ)
    (hf : AnalyticAt ℂ f a)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h_real : ∀ᶠ t : ι → ℝ in 𝓝 0, f (a + ofRealN t) = 0) :
    ∀ x : (ι → ℝ), (ftaylorSeries ℂ f a) n (fun _ => ofRealN x) = 0 := by
  intro x
  rcases hf with ⟨p, hp⟩
  let L : ℂ →L[ℂ] (ι → ℂ) := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ofRealN x)
  have hp_shifted := hp.comp_sub (-a)
  have h_add : (a + -a) = 0 := add_neg_cancel a
  rw [h_add] at hp_shifted
  have h_simp : (fun z => f (z - -a)) = (fun z => f (a + z)) := by
    ext z
    rw [sub_neg_eq_add, add_comm]
  rw [h_simp] at hp_shifted
  have h_L_zero : L 0 = 0 := ContinuousLinearMap.map_zero L
  have hp_shifted2 : HasFPowerSeriesAt (fun z => f (a + z)) p (L 0) := by
    rw [h_L_zero]
    exact hp_shifted
  have hp_comp : HasFPowerSeriesAt (fun z => f (a + L z)) (p.compContinuousLinearMap L) 0 := by
    exact HasFPowerSeriesAt.compContinuousLinearMap (u := L) hp_shifted2
  have h_g_real : ∀ᶠ t : ℝ in 𝓝 0, f (a + L (t : ℂ)) = (fun _ : ℂ => (0 : ℂ)) t := by
    let φ : ℝ → (ι → ℝ) := fun t => t • x
    have h_φ_cont : Continuous φ := continuous_id.smul continuous_const
    have h_φ_zero : φ 0 = 0 := zero_smul ℝ x
    have h_tendsto := Continuous.tendsto h_φ_cont 0
    rw [h_φ_zero] at h_tendsto
    have h_eventually := h_tendsto.eventually h_real
    refine h_eventually.mono ?_
    intro t ht
    have h_L_t : L (t : ℂ) = (t : ℂ) • ofRealN x := rfl
    rw [h_L_t]
    have h_smul : (t : ℂ) • ofRealN x = ofRealN (t • x) := by
      ext i
      rw [h_ofReal, h_ofReal]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      rfl
    rw [h_smul]
    exact ht
  have h_g_zero : ∀ᶠ z : ℂ in 𝓝 0, f (a + L z) = 0 := by
    have h_g_ana : AnalyticAt ℂ (fun z => f (a + L z)) (0 : ℝ) := ⟨_, hp_comp⟩
    have h_zero_ana : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) (0 : ℝ) := analyticAt_const
    exact analytic_nhds_eq_of_real_eq_1D (fun z => f (a + L z)) (fun _ => 0) (0 : ℝ)
      h_g_ana h_zero_ana h_g_real
  have h_p_comp_zero : p.compContinuousLinearMap L = 0 := by
    exact HasFPowerSeriesAt.eq_zero_of_eventually hp_comp h_g_zero
  have h_pn_comp_zero : (p.compContinuousLinearMap L) n = 0 := by
    rw [h_p_comp_zero]; rfl
  have h_eval : (p.compContinuousLinearMap L) n (fun _ => 1) = p n (fun _ => L 1) := rfl
  have h_L_1 : L 1 = ofRealN x := by simp [L]
  rw [h_L_1] at h_eval
  rw [h_pn_comp_zero] at h_eval
  have h_p_zero : p n (fun _ => ofRealN x) = 0 := h_eval.symm
  rcases hp with ⟨r, hp_ball⟩
  have h_sum := hp_ball.iteratedFDeriv_eq_sum_of_completeSpace (n := n) (fun _ => ofRealN x)
  have h_sum_const : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => ofRealN x)) =
      (Fintype.card (Equiv.Perm (Fin n))) • p n (fun _ => ofRealN x) := by
    exact Finset.sum_const _
  rw [h_sum_const, h_p_zero] at h_sum
  have h_smul_zero : (Fintype.card (Equiv.Perm (Fin n))) • (0 : ℂ) = 0 := smul_zero _
  rw [h_smul_zero] at h_sum
  exact h_sum

lemma eq_zero_of_ftaylorSeries_zero {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℂ) (a : ι → ℂ)
    (hf : AnalyticAt ℂ f a)
    (h_zero : ∀ n, (ftaylorSeries ℂ f a) n = 0) :
    ∀ᶠ z in 𝓝 a, f z = 0 := by
  rcases hf with ⟨p, hp⟩
  rcases hp with ⟨r, hp_ball⟩
  have h_p_diag : ∀ n y, p n (fun _ => y) = 0 := by
    intro n y
    have h_sum := hp_ball.iteratedFDeriv_eq_sum_of_completeSpace (n := n) (fun _ => y)
    have hz := h_zero n
    have h_iter : iteratedFDeriv ℂ n f a = 0 := hz
    rw [h_iter] at h_sum
    have h_eval_zero :
        (0 : ContinuousMultilinearMap ℂ (fun _ : Fin n => (ι → ℂ)) ℂ) (fun _ => y) = 0 := rfl
    rw [h_eval_zero] at h_sum
    have h_sum_const : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => y)) =
        (Fintype.card (Equiv.Perm (Fin n))) • p n (fun _ => y) := by
      exact Finset.sum_const _
    rw [h_sum_const] at h_sum
    have h_card : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [h_card] at h_sum
    have h_symm_eq : (n.factorial) • p n (fun _ => y) = 0 := h_sum.symm
    have h_fact : n.factorial ≠ 0 := n.factorial_ne_zero
    cases smul_eq_zero.mp h_symm_eq with
    | inl h => contradiction
    | inr h => exact h
  filter_upwards [hp_ball.eventually_hasSum_sub] with z hz
  have h_zero_seq : (fun n : ℕ => p n (fun _ : Fin n => z - a)) = (fun _ : ℕ => 0) := by
    ext n
    exact h_p_diag n (z - a)
  rw [h_zero_seq] at hz
  have h_zero_sum : HasSum (fun _ : ℕ => (0 : ℂ)) 0 := hasSum_zero
  exact hz.unique h_zero_sum

lemma analytic_nhds_eq_of_real_eq_N {ι : Type*} [Fintype ι] (f g : (ι → ℂ) → ℂ)
    (a : ι → ℝ) (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (hf : AnalyticAt ℂ f (ofRealN a)) (hg : AnalyticAt ℂ g (ofRealN a))
    (h_real : ∀ᶠ t : ι → ℝ in 𝓝 a, f (ofRealN t) = g (ofRealN t)) :
    ∀ᶠ z : ι → ℂ in 𝓝 (ofRealN a), f z = g z := by
  have hfg : AnalyticAt ℂ (f - g) (ofRealN a) := hf.sub hg
  have hp_zero : ∀ n, (ftaylorSeries ℂ (f - g) (ofRealN a)) n = 0 := by
    intro n
    have h_symm := ftaylorSeries_isSymmetric (n := n) (f - g) (ofRealN a) hfg
    have h_real_zero : ∀ᶠ t : ι → ℝ in 𝓝 0, (f - g) (ofRealN a + ofRealN t) = 0 := by
      have h_cont : Continuous (fun t : ι → ℝ => a + t) := continuous_const.add continuous_id
      have h_tendsto := h_cont.tendsto 0
      have h_zero : a + 0 = a := add_zero a
      rw [h_zero] at h_tendsto
      have h_ev := h_tendsto.eventually h_real
      refine h_ev.mono ?_
      intro t ht
      have h_lin : ofRealN (a + t) = ofRealN a + ofRealN t := ofRealN.map_add a t
      rw [← h_lin]
      exact sub_eq_zero.mpr ht
    have h_diag :=
      ftaylorSeries_diag_zero (n := n) (f - g) (ofRealN a) hfg ofRealN h_ofReal h_real_zero
    exact complex_multilinear_zero_of_diagonal_real_zero_N
      ((ftaylorSeries ℂ (f - g) (ofRealN a)) n) h_symm ofRealN h_ofReal h_diag
  have h_zero_nhds := eq_zero_of_ftaylorSeries_zero (f - g) (ofRealN a) hfg hp_zero
  filter_upwards [h_zero_nhds] with z hz
  exact sub_eq_zero.mp hz

lemma analytic_eq_of_real_eq_R_N {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (_hU_open : IsOpen U) (hU_conn : IsConnected U)
    (f g : (ι → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (a : ι → ℝ) (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (ha : ofRealN a ∈ U)
    (h_real : ∀ᶠ t : ι → ℝ in 𝓝 a, f (ofRealN t) = g (ofRealN t)) :
    Set.EqOn f g U := by
  have h_nhds_eq : ∀ᶠ z : ι → ℂ in 𝓝 (ofRealN a), f z = g z := by
    apply analytic_nhds_eq_of_real_eq_N f g a ofRealN h_ofReal (hf _ ha) (hg _ ha) h_real
  have hfg : AnalyticOnNhd ℂ (f - g) U := hf.sub hg
  have h_nhds_zero : ∀ᶠ z : ι → ℂ in 𝓝 (ofRealN a), (f - g) z = 0 := by
    filter_upwards [h_nhds_eq] with z hz
    simp [hz]
  have h_eq_zero :=
    hfg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_conn.isPreconnected ha h_nhds_zero
  intro z hz
  have hz_zero := h_eq_zero hz
  exact sub_eq_zero.mp hz_zero

def upperHalfPlane : Set ℂ := {z | 0 < z.im}
def lowerHalfPlane : Set ℂ := {z | z.im < 0}

def slitDomain (I : Set ℝ) : Set ℂ := {z | z.im ≠ 0 ∨ z.re ∈ I}

lemma isOpen_slitDomain {I : Set ℝ} (hI : IsOpen I) : IsOpen (slitDomain I) := by
  have h1 : IsOpen {z : ℂ | z.im ≠ 0} := by
    have : {z : ℂ | z.im ≠ 0} = (fun z : ℂ => z.im) ⁻¹' {y : ℝ | y ≠ 0} := rfl
    rw [this]
    exact isOpen_ne.preimage continuous_im
  have h2 : IsOpen {z : ℂ | z.re ∈ I} := hI.preimage continuous_re
  exact IsOpen.union h1 h2

lemma wedgeIntegral_split_y (z w : ℂ) (y_mid : ℝ) (f : ℂ → ℂ)
    (hf_int_w : IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im y_mid ∧
                IntervalIntegrable (fun y => f (w.re + y * I)) volume y_mid w.im)
    (hf_int_z : IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im y_mid ∧
                IntervalIntegrable (fun y => f (z.re + y * I)) volume y_mid w.im) :
    wedgeIntegral z w f + wedgeIntegral w z f =
    (wedgeIntegral z (w.re + y_mid * I) f + wedgeIntegral (w.re + y_mid * I) z f) +
    (wedgeIntegral (z.re + y_mid * I) w f + wedgeIntegral w (z.re + y_mid * I) f) := by
  have h1 := wedgeIntegral_add_wedgeIntegral_eq z w f
  have h2 := wedgeIntegral_add_wedgeIntegral_eq z (w.re + y_mid * I) f
  have h3 := wedgeIntegral_add_wedgeIntegral_eq (z.re + y_mid * I) w f
  simp only [mul_re, mul_im, smul_eq_mul, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    sub_zero, zero_add, mul_zero, add_zero, mul_one] at h1 h2 h3
  rw [h1, h2, h3]
  have hw : (∫ (y : ℝ) in z.im..y_mid, f (↑w.re + ↑y * I)) +
      (∫ (y : ℝ) in y_mid..w.im, f (↑w.re + ↑y * I)) =
      (∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) :=
    intervalIntegral.integral_add_adjacent_intervals hf_int_w.1 hf_int_w.2
  have hz : (∫ (y : ℝ) in z.im..y_mid, f (↑z.re + ↑y * I)) +
      (∫ (y : ℝ) in y_mid..w.im, f (↑z.re + ↑y * I)) =
      (∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I)) :=
    intervalIntegral.integral_add_adjacent_intervals hf_int_z.1 hf_int_z.2
  generalize H1 : (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) = A at *
  generalize H2 : (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑w.im * I)) = B at *
  generalize H3 : (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑y_mid * I)) = C at *
  generalize H4 : (∫ (y : ℝ) in z.im..y_mid, f (↑w.re + ↑y * I)) = W1 at *
  generalize H5 : (∫ (y : ℝ) in y_mid..w.im, f (↑w.re + ↑y * I)) = W2 at *
  generalize H6 : (∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) = W at *
  generalize H7 : (∫ (y : ℝ) in z.im..y_mid, f (↑z.re + ↑y * I)) = Z1 at *
  generalize H8 : (∫ (y : ℝ) in y_mid..w.im, f (↑z.re + ↑y * I)) = Z2 at *
  generalize H9 : (∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I)) = Z at *
  have hw_subst : W = W1 + W2 := hw.symm
  have hz_subst : Z = Z1 + Z2 := hz.symm
  rw [hw_subst, hz_subst]
  ring

lemma wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn (f : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn f (z.Rectangle w))
    (Hd : DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  exact integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w Hc Hd

lemma intervalIntegrable_of_continuousOn_rect (z w : ℂ) (f : ℂ → ℂ) (x : ℝ)
    (hx : x ∈ uIcc z.re w.re) (y1 y2 : ℝ) (hy1 : y1 ∈ uIcc z.im w.im)
    (hy2 : y2 ∈ uIcc z.im w.im) (hf : ContinuousOn f (z.Rectangle w)) :
    IntervalIntegrable (fun y => f (x + y * I)) volume y1 y2 := by
  apply ContinuousOn.intervalIntegrable
  have h_comp : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have h_comp_on := h_comp.continuousOn (s := uIcc y1 y2)
  apply hf.comp h_comp_on
  intro y hy
  rw [Rectangle, mem_reProdIm]
  have h_re : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have h_im : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  rw [h_re, h_im]
  refine ⟨hx, ?_⟩
  exact uIcc_subset_uIcc hy1 hy2 hy

lemma differentiableOn_split_y0 (f : ℂ → ℂ) (x1 x2 y : ℝ)
    (hf_ana_neg : AnalyticOn ℂ f lowerHalfPlane)
    (hf_ana_pos : AnalyticOn ℂ f upperHalfPlane) :
    DifferentiableOn ℂ f (Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0)) := by
  rcases lt_trichotomy y 0 with h | h | h
  · have h_min : min y 0 = y := min_eq_left h.le
    have h_max : max y 0 = 0 := max_eq_right h.le
    have h_sub : Ioo (min y 0) (max y 0) ⊆ Iio 0 := by
      rw [h_min, h_max]; intro t ht; exact ht.2
    have h_sub2 : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) ⊆ lowerHalfPlane := by
      intro z hz; rw [mem_reProdIm] at hz; exact h_sub hz.2
    exact hf_ana_neg.differentiableOn.mono h_sub2
  · have h_min : min y 0 = 0 := by rw [h]; exact min_self 0
    have h_max : max y 0 = 0 := by rw [h]; exact max_self 0
    have h_empty : Ioo (min y 0) (max y 0) = ∅ := by rw [h_min, h_max]; simp
    have h_empty2 : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) = ∅ := by
      ext z; simp [mem_reProdIm, h_empty]
    rw [h_empty2]; exact differentiableOn_empty
  · have h_min : min y 0 = 0 := min_eq_right h.le
    have h_max : max y 0 = y := max_eq_left h.le
    have h_sub : Ioo (min y 0) (max y 0) ⊆ Ioi 0 := by
      rw [h_min, h_max]; intro t ht; exact ht.1
    have h_sub2 : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) ⊆ upperHalfPlane := by
      intro z hz; rw [mem_reProdIm] at hz; exact h_sub hz.2
    exact hf_ana_pos.differentiableOn.mono h_sub2

theorem isConservativeOn_slitDomain (S : Set ℝ) (_hS : IsOpen S) (f : ℂ → ℂ)
    (hf_cont : ContinuousOn f (slitDomain S))
    (hf_ana_pos : AnalyticOn ℂ f upperHalfPlane)
    (hf_ana_neg : AnalyticOn ℂ f lowerHalfPlane) :
    IsConservativeOn f (slitDomain S) := by
  intro z w hzw
  rw [eq_neg_iff_add_eq_zero]
  have h_cont_rect : ContinuousOn f (z.Rectangle w) := hf_cont.mono hzw
  by_cases h0 : (0:ℝ) ∈ uIcc z.im w.im
  · have hf_int_w : IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im 0 ∧
        IntervalIntegrable (fun y => f (w.re + y * I)) volume 0 w.im := by
      constructor
      · exact intervalIntegrable_of_continuousOn_rect z w f w.re right_mem_uIcc z.im 0
          left_mem_uIcc h0 h_cont_rect
      · exact intervalIntegrable_of_continuousOn_rect z w f w.re right_mem_uIcc 0 w.im
          h0 right_mem_uIcc h_cont_rect
    have hf_int_z : IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im 0 ∧
        IntervalIntegrable (fun y => f (z.re + y * I)) volume 0 w.im := by
      constructor
      · exact intervalIntegrable_of_continuousOn_rect z w f z.re left_mem_uIcc z.im 0
          left_mem_uIcc h0 h_cont_rect
      · exact intervalIntegrable_of_continuousOn_rect z w f z.re left_mem_uIcc 0 w.im
          h0 right_mem_uIcc h_cont_rect
    have h_split := wedgeIntegral_split_y z w 0 f hf_int_w hf_int_z
    rw [h_split]
    have h1 : wedgeIntegral z (w.re + (0:ℝ) * I) f + wedgeIntegral (w.re + (0:ℝ) * I) z f = 0 := by
      apply wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn
      · apply h_cont_rect.mono
        intro v hv
        rw [Rectangle, mem_reProdIm] at hv ⊢
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero] at hv
        refine ⟨hv.1, ?_⟩
        exact uIcc_subset_uIcc left_mem_uIcc h0 hv.2
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero]
        exact differentiableOn_split_y0 f (min z.re w.re) (max z.re w.re) z.im hf_ana_neg hf_ana_pos
    have h2 : wedgeIntegral (z.re + (0:ℝ) * I) w f + wedgeIntegral w (z.re + (0:ℝ) * I) f = 0 := by
      apply wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn
      · apply h_cont_rect.mono
        intro v hv
        rw [Rectangle, mem_reProdIm] at hv ⊢
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero] at hv
        refine ⟨hv.1, ?_⟩
        exact uIcc_subset_uIcc h0 right_mem_uIcc hv.2
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero, min_comm 0 w.im, max_comm 0 w.im]
        exact differentiableOn_split_y0 f (min z.re w.re) (max z.re w.re) w.im hf_ana_neg hf_ana_pos
    rw [h1, h2, add_zero]
  · apply wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn f z w h_cont_rect
    rcases lt_trichotomy 0 z.im with h | h | h
    · have hw_im : 0 < w.im := by
        by_contra h_contra
        push Not at h_contra
        have h_in : (0:ℝ) ∈ uIcc z.im w.im := by
          rw [mem_uIcc]
          exact Or.inr ⟨h_contra, h.le⟩
        exact h0 h_in
      have h_sub : Ioo (min z.im w.im) (max z.im w.im) ⊆ Ioi 0 := by
        intro t ht
        exact lt_trans (lt_min h hw_im) ht.1
      have h_sub2 :
          Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) ⊆
            upperHalfPlane := by
        intro v hv; rw [mem_reProdIm] at hv; exact h_sub hv.2
      exact hf_ana_pos.differentiableOn.mono h_sub2
    · rw [← h] at h0
      have h_in : (0:ℝ) ∈ uIcc 0 w.im := left_mem_uIcc
      exact False.elim (h0 h_in)
    · have hw_im : w.im < 0 := by
        by_contra h_contra
        push Not at h_contra
        have h_in : (0:ℝ) ∈ uIcc z.im w.im := by
          rw [mem_uIcc]
          exact Or.inl ⟨h.le, h_contra⟩
        exact h0 h_in
      have h_sub : Ioo (min z.im w.im) (max z.im w.im) ⊆ Iio 0 := by
        intro t ht
        exact lt_trans ht.2 (max_lt h hw_im)
      have h_sub2 :
          Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) ⊆
            lowerHalfPlane := by
        intro v hv; rw [mem_reProdIm] at hv; exact h_sub hv.2
      exact hf_ana_neg.differentiableOn.mono h_sub2

theorem eow_1d_continuous (S : Set ℝ) (hS : IsOpen S) (f : ℂ → ℂ)
    (hf_cont : ContinuousOn f (slitDomain S))
    (hf_ana_pos : AnalyticOn ℂ f upperHalfPlane)
    (hf_ana_neg : AnalyticOn ℂ f lowerHalfPlane) :
    AnalyticOn ℂ f (slitDomain S) := by
  apply DifferentiableOn.analyticOn _ (isOpen_slitDomain hS)
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn (isOpen_slitDomain hS)).mp
  constructor
  · exact isConservativeOn_slitDomain S hS f hf_cont hf_ana_pos hf_ana_neg
  · exact hf_cont

lemma complex_algebra_lemma_aux (Z I_c F W : ℂ) :
    (Z * I_c) * (W * W * F) = (Z * W) * (I_c * W) * F := by
  ring

lemma complex_algebra_lemma (Z I_c F : ℂ) (hZ : Z ≠ 0) :
    (Z * I_c) * ((1 / Z ^ 2) * F) = (I_c / Z) * F := by
  have hz2 : Z ^ 2 = Z * Z := sq Z
  rw [hz2]
  calc
    (Z * I_c) * ((1 / (Z * Z)) * F) = (Z * I_c) * ((Z * Z)⁻¹ * F) := by rw [one_div]
    _ = (Z * I_c) * ((Z⁻¹ * Z⁻¹) * F) := by rw [mul_inv_rev, mul_comm Z⁻¹ Z⁻¹]
    _ = (Z * Z⁻¹) * (I_c * Z⁻¹) * F := by rw [complex_algebra_lemma_aux Z I_c F Z⁻¹]
    _ = 1 * (I_c * Z⁻¹) * F := by rw [mul_inv_cancel₀ hZ]
    _ = (I_c / Z) * F := by rw [one_mul, div_eq_mul_inv]

lemma integrand_eq (f : ℂ × ℂ → ℂ) (x y : ℂ) (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    deriv (circleMap x R) θ • ((1 / (circleMap x R θ - x) ^ 2) * f (circleMap x R θ, y)) =
    (I / (R * exp (θ * I))) * f (x + R * exp (θ * I), y) := by
  rw [deriv_circleMap]
  rw [circleMap_sub_center]
  have h_c0 : circleMap 0 R θ = R * exp (θ * I) := by
    simp [circleMap]
  rw [h_c0]
  have h_cx : circleMap x R θ = x + R * exp (θ * I) := by
    simp [circleMap]
  rw [h_cx]
  change (↑R * exp (↑θ * I) * I) *
    ((1 / (↑R * exp (↑θ * I)) ^ 2) * f (x + ↑R * exp (↑θ * I), y)) = _
  have hZ : (R : ℂ) * exp (θ * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hR.ne') (exp_ne_zero _)
  exact complex_algebra_lemma _ I _ hZ

lemma partial_deriv_eq_intervalIntegral
    (f : ℂ × ℂ → ℂ) (x y : ℂ) (R : ℝ) (hR : 0 < R)
    (h_diff : DifferentiableOn ℂ (fun w => f (w, y)) (Metric.closedBall x R)) :
    deriv (fun w => f (w, y)) x =
      (2 * ↑Real.pi * I)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (I / (R * exp (θ * I))) * f (x + R * exp (θ * I), y) := by
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (E := ℂ)
    (f := fun w => f (w, y)) (c := x) (R := R) hR h_diff
  have hc2 : ∮ z in C(x, R), (1 / (z - x) ^ 2) * f (z, y) =
      (2 * ↑Real.pi * I) * deriv (fun w => f (w, y)) x := hc
  have hint := circleIntegral_def_Icc (fun w => (1 / (w - x) ^ 2) * f (w, y)) x R
  have h_eq_int : (∫ θ in (0:ℝ)..(2 * Real.pi),
        (I / (R * exp (θ * I))) * f (x + R * exp (θ * I), y)) =
      ∫ θ in Icc 0 (2 * Real.pi),
        deriv (circleMap x R) θ • ((1 / (circleMap x R θ - x) ^ 2) * f (circleMap x R θ, y)) := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    congr 1
    ext θ
    exact (integrand_eq f x y R hR θ).symm
  rw [hint, ← h_eq_int] at hc2
  calc deriv (fun w => f (w, y)) x
    _ = (2 * ↑Real.pi * I)⁻¹ * ((2 * ↑Real.pi * I) * deriv (fun w => f (w, y)) x) := by
      rw [← mul_assoc, inv_mul_cancel₀, one_mul]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_pos.ne')) I_ne_zero
    _ = (2 * ↑Real.pi * I)⁻¹ *
        ∫ θ in (0:ℝ)..(2 * Real.pi), (I / (↑R * exp (↑θ * I))) * f (x + ↑R * exp (↑θ * I), y) := by
      rw [← hc2]

lemma cont_aux (R : ℝ) (hR : 0 < R) (p₀ : ℂ × ℂ) (U : Set (ℂ × ℂ)) (f : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f U)
    (h_in_U : ∀ p ∈ Metric.ball p₀ R, ∀ θ : ℝ, (p.1 + R * exp (θ * I), p.2) ∈ U) :
    Continuous (Function.uncurry (fun (p : Metric.ball p₀ R) (θ : ℝ) =>
      (I / (R * exp (θ * I))) * f (p.val.1 + R * exp (θ * I), p.val.2))) := by
  have h_left : Continuous (fun (X : Metric.ball p₀ R × ℝ) => I / (R * exp (X.2 * I))) := by
    apply Continuous.div continuous_const
    · exact continuous_const.mul
        (continuous_exp.comp (continuous_ofReal.comp continuous_snd |>.mul continuous_const))
    · intro X
      exact mul_ne_zero (by exact_mod_cast hR.ne') (exp_ne_zero _)
  have h_right :
      Continuous (fun (X : Metric.ball p₀ R × ℝ) =>
        f (X.1.val.1 + R * exp (X.2 * I), X.1.val.2)) := by
    have h_inner :
        Continuous (fun (X : Metric.ball p₀ R × ℝ) =>
          (X.1.val.1 + R * exp (X.2 * I), X.1.val.2)) := by
      have h1 : Continuous (fun X : Metric.ball p₀ R × ℝ => X.1.val.1) :=
        continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
      have h2 : Continuous (fun X : Metric.ball p₀ R × ℝ => R * exp (X.2 * I)) :=
        continuous_const.mul
          (continuous_exp.comp (continuous_ofReal.comp continuous_snd |>.mul continuous_const))
      have h3 : Continuous (fun X : Metric.ball p₀ R × ℝ => X.1.val.2) :=
        continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
      exact Continuous.prodMk (h1.add h2) h3
    apply ContinuousOn.comp_continuous h_cont h_inner
    intro X
    exact h_in_U X.1.val X.1.property X.2
  exact h_left.mul h_right

lemma continuousAt_partial_deriv_of_continuous_of_analytic
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (f : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f U)
    (h_holo_x : ∀ (y : ℂ), DifferentiableOn ℂ (fun x => f (x, y)) {x | (x, y) ∈ U})
    (p₀ : ℂ × ℂ) (hp₀ : p₀ ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ => deriv (fun x => f (x, p.2)) p.1) p₀ := by
  rcases Metric.isOpen_iff.mp hU p₀ hp₀ with ⟨ε, hε, h_ball⟩
  have hR : 0 < ε / 2 := half_pos hε
  set R := ε / 2
  have hR_le : ε / 2 ≤ ε := by linarith
  have h_subset : Metric.ball p₀ (2 * R) ⊆ U := by
    have h2R : 2 * R = ε := mul_div_cancel₀ ε two_ne_zero
    rw [h2R]
    exact h_ball
  have h_in_U : ∀ p ∈ Metric.ball p₀ R, ∀ θ : ℝ, (p.1 + R * exp (θ * I), p.2) ∈ U := by
    intro p hp θ
    apply h_subset
    rw [Metric.mem_ball] at hp ⊢
    have hp1 : dist p.1 p₀.1 ≤ dist p p₀ := le_max_left _ _
    have hp2 : dist p.2 p₀.2 ≤ dist p p₀ := le_max_right _ _
    have h1 : dist p.1 p₀.1 < R := lt_of_le_of_lt hp1 hp
    have h2 : dist p.2 p₀.2 < R := lt_of_le_of_lt hp2 hp
    have h2_lt : dist p.2 p₀.2 < 2 * R := lt_trans h2 (by linarith)
    have hd1 : dist (p.1 + R * exp (θ * I)) p₀.1 ≤
        dist (p.1 + R * exp (θ * I)) p.1 + dist p.1 p₀.1 :=
      dist_triangle _ _ _
    have h_circle : dist (p.1 + R * exp (θ * I)) p.1 = R := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Real.norm_of_nonneg (le_of_lt hR),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hd1_val : dist (p.1 + R * exp (θ * I)) p₀.1 < 2 * R := by linarith
    exact max_lt hd1_val h2_lt
  let f_int (p : Metric.ball p₀ R) (θ : ℝ) : ℂ :=
    (I / (R * exp (θ * I))) * f (p.val.1 + R * exp (θ * I), p.val.2)
  have h_cont_int : Continuous (Function.uncurry f_int) :=
    cont_aux R hR p₀ U f h_cont h_in_U
  let F_int (p : ℂ × ℂ) : ℂ :=
    ∫ θ in (0:ℝ)..(2 * Real.pi), (I / (R * exp (θ * I))) * f (p.1 + R * exp (θ * I), p.2)
  have h_int_cont : Continuous (fun (p : Metric.ball p₀ R) => F_int p.val) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      h_cont_int 0 (2 * Real.pi)
  have h_int_contOn : ContinuousOn F_int (Metric.ball p₀ R) :=
    continuousOn_iff_continuous_restrict.mpr h_int_cont
  have hp₀_nhds : Metric.ball p₀ R ∈ 𝓝 p₀ := Metric.ball_mem_nhds p₀ hR
  have h_int_contAt : ContinuousAt F_int p₀ :=
    ContinuousOn.continuousAt h_int_contOn hp₀_nhds
  have h_mul : ContinuousAt (fun p => (2 * ↑Real.pi * I)⁻¹ * F_int p) p₀ :=
    ContinuousAt.mul continuousAt_const h_int_contAt
  apply ContinuousAt.congr h_mul
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  refine ⟨Metric.ball p₀ R, ?_, Metric.isOpen_ball, Metric.mem_ball_self hR⟩
  intro p hp
  have h_diff_p : DifferentiableOn ℂ (fun w => f (w, p.2)) (Metric.closedBall p.1 R) := by
    apply DifferentiableOn.mono (h_holo_x p.2)
    intro w hw
    simp only [mem_setOf_eq]
    have hw_dist : dist w p.1 ≤ R := Metric.mem_closedBall.mp hw
    have hp_dist : dist p p₀ < R := Metric.mem_ball.mp hp
    have d1 : dist w p₀.1 ≤ dist w p.1 + dist p.1 p₀.1 := dist_triangle w p.1 p₀.1
    have h1 : dist p.1 p₀.1 ≤ dist p p₀ := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have h2 : dist p.2 p₀.2 ≤ dist p p₀ := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have d1_lt : dist w p₀.1 < 2 * R := by
      calc dist w p₀.1 ≤ dist w p.1 + dist p.1 p₀.1 := d1
        _ ≤ R + dist p p₀ := add_le_add hw_dist h1
        _ < R + R := by linarith
        _ = 2 * R := by ring
    have d2_lt : dist p.2 p₀.2 < 2 * R := by
      calc dist p.2 p₀.2 ≤ dist p p₀ := h2
        _ < R := hp_dist
        _ < 2 * R := by linarith
    have h_max : dist (w, p.2) p₀ < ε := by
      rw [Prod.dist_eq]
      have h_eq : 2 * R = ε := by
        change 2 * (ε / 2) = ε
        ring
      rw [← h_eq]
      exact max_lt d1_lt d2_lt
    exact h_ball h_max
  have heq := partial_deriv_eq_intervalIntegral f p.1 p.2 R hR h_diff_p
  exact heq.symm

lemma osgood_2d {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (f : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f U)
    (h_holo_x : ∀ (y : ℂ), DifferentiableOn ℂ (fun x => f (x, y)) {x | (x, y) ∈ U})
    (h_holo_y : ∀ (x : ℂ), DifferentiableOn ℂ (fun y => f (x, y)) {y | (x, y) ∈ U}) :
    DifferentiableOn ℂ f U := by
  intro p hp
  let f₁ : ℂ → ℂ → ℂ →L[ℂ] ℂ := fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f (w, y)) x)
  let f₂ : ℂ → ℂ → ℂ →L[ℂ] ℂ := fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f (x, w)) y)
  have df₁ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => f (x, v.2)) (f₁ v.1 v.2) v.1 := by
    apply eventually_nhds_iff.mpr
    refine ⟨U, ?_, hU, hp⟩
    intro v hv
    have h_diff : DifferentiableWithinAt ℂ (fun x => f (x, v.2)) {x | (x, v.2) ∈ U} v.1 :=
      h_holo_x v.2 v.1 hv
    have hU_x : IsOpen {x | (x, v.2) ∈ U} :=
      hU.preimage (Continuous.prodMk continuous_id continuous_const)
    exact (h_diff.differentiableAt (hU_x.mem_nhds hv)).hasDerivAt.hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun y => f (v.1, y)) (f₂ v.1 v.2) v.2 := by
    apply eventually_nhds_iff.mpr
    refine ⟨U, ?_, hU, hp⟩
    intro v hv
    have h_diff : DifferentiableWithinAt ℂ (fun y => f (v.1, y)) {y | (v.1, y) ∈ U} v.2 :=
      h_holo_y v.1 v.2 hv
    have hU_y : IsOpen {y | (v.1, y) ∈ U} :=
      hU.preimage (Continuous.prodMk continuous_const continuous_id)
    exact (h_diff.differentiableAt (hU_y.mem_nhds hv)).hasDerivAt.hasFDerivAt
  have cf₁ : ContinuousAt ↿f₁ p := by
    have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU f h_cont h_holo_x p hp
    have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
    exact h_smul.continuousAt.comp hc
  have cf₂ : ContinuousAt ↿f₂ p := by
    let f_symm : ℂ × ℂ → ℂ := fun v => f (v.2, v.1)
    have hU_symm : IsOpen (Prod.swap ⁻¹' U) := hU.preimage continuous_swap
    have h_cont_symm : ContinuousOn f_symm (Prod.swap ⁻¹' U) :=
      h_cont.comp continuous_swap.continuousOn (fun _ hx => hx)
    have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU_symm f_symm h_cont_symm
      (fun x => h_holo_y x) p.swap (by simp [hp])
    have hc2 : ContinuousAt (fun v : ℂ × ℂ => deriv (fun w => f (v.1, w)) v.2) p :=
      hc.comp continuous_swap.continuousAt
    have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
    exact h_smul.continuousAt.comp hc2
  have h_strict := hasStrictFDerivAt_uncurry_coprod (f := fun x y => f (x, y)) df₁ df₂ cf₁ cf₂
  exact h_strict.hasFDerivAt.differentiableAt.differentiableWithinAt

lemma continuous_coprod_C :
    Continuous (fun (w : (ℂ →L[ℂ] ℂ) × (ℂ →L[ℂ] ℂ)) => w.1.coprod w.2) := by
  fun_prop

lemma continuous_compRight_C (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ) :
    Continuous (fun (L : ℂ × ℂ →L[ℂ] ℂ) => L.comp e) := by
  have h : (fun (L : ℂ × ℂ →L[ℂ] ℂ) => L.comp e) =
      fun L => ContinuousLinearMap.compL ℂ (Fin 2 → ℂ) (ℂ × ℂ) ℂ L e := by
    ext L x
    rfl
  rw [h]
  fun_prop

noncomputable def partial_x (f' : ℂ × ℂ → ℂ) : ℂ → ℂ → ℂ →L[ℂ] ℂ :=
  fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f' (w, y)) x)

noncomputable def partial_y (f' : ℂ × ℂ → ℂ) : ℂ → ℂ → ℂ →L[ℂ] ℂ :=
  fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f' (x, w)) y)

lemma continuousOn_fderiv_of_differentiableOn_fin2_cf1 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f' U')
    (h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'}) :
    ContinuousOn ↿(partial_x f') U' := by
  intro p hp
  have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU' f' h_cont h_holo_x p hp
  have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
  exact (h_smul.continuousAt.comp hc).continuousWithinAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_cf2 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f' U')
    (h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'}) :
    ContinuousOn ↿(partial_y f') U' := by
  intro p hp
  let f_symm : ℂ × ℂ → ℂ := fun v => f' (v.2, v.1)
  have hU_symm : IsOpen (Prod.swap ⁻¹' U') := hU'.preimage continuous_swap
  have h_cont_symm : ContinuousOn f_symm (Prod.swap ⁻¹' U') :=
    h_cont.comp continuous_swap.continuousOn (fun _ hx => hx)
  have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU_symm f_symm h_cont_symm
    (fun x => h_holo_y x) p.swap (by simp [hp])
  have hc2 : ContinuousAt (fun v : ℂ × ℂ => deriv (fun w => f' (v.1, w)) v.2) p :=
    hc.comp continuous_swap.continuousAt
  have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
  exact (h_smul.continuousAt.comp hc2).continuousWithinAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_df1 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'}) :
    ∀ p ∈ U', HasFDerivAt (fun x => f' (x, p.2)) (partial_x f' p.1 p.2) p.1 := by
  intro p hp
  have hU_x : IsOpen {x | (x, p.2) ∈ U'} :=
    hU'.preimage (Continuous.prodMk continuous_id continuous_const)
  exact ((h_holo_x p.2 p.1 hp).differentiableAt (hU_x.mem_nhds hp)).hasDerivAt.hasFDerivAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_df2 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'}) :
    ∀ p ∈ U', HasFDerivAt (fun y => f' (p.1, y)) (partial_y f' p.1 p.2) p.2 := by
  intro p hp
  have hU_y : IsOpen {y | (p.1, y) ∈ U'} :=
    hU'.preimage (Continuous.prodMk continuous_const continuous_id)
  exact ((h_holo_y p.1 p.2 hp).differentiableAt (hU_y.mem_nhds hp)).hasDerivAt.hasFDerivAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_fderiv {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (cf₁ : ContinuousOn ↿(partial_x f') U') (cf₂ : ContinuousOn ↿(partial_y f') U')
    (df₁ : ∀ p ∈ U', HasFDerivAt (fun x => f' (x, p.2)) (partial_x f' p.1 p.2) p.1)
    (df₂ : ∀ p ∈ U', HasFDerivAt (fun y => f' (p.1, y)) (partial_y f' p.1 p.2) p.2) :
    ∀ p ∈ U', fderiv ℂ f' p = (partial_x f' p.1 p.2).coprod (partial_y f' p.1 p.2) := by
  intro p hp
  have h_strict := hasStrictFDerivAt_uncurry_coprod (f := fun x y => f' (x, y))
    (by
      apply eventually_nhds_iff.mpr
      refine ⟨U', ?_, hU', hp⟩
      intro v hv
      exact df₁ v hv)
    (by
      apply eventually_nhds_iff.mpr
      refine ⟨U', ?_, hU', hp⟩
      intro v hv
      exact df₂ v hv)
    ((cf₁ p hp).continuousAt (hU'.mem_nhds hp))
    ((cf₂ p hp).continuousAt (hU'.mem_nhds hp))
  exact h_strict.hasFDerivAt.fderiv

lemma continuousOn_fderiv_of_differentiableOn_fin2_aux {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f' U')
    (h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'})
    (h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'}) :
    ContinuousOn (fderiv ℂ f') U' := by
  have cf₁ : ContinuousOn ↿(partial_x f') U' :=
    continuousOn_fderiv_of_differentiableOn_fin2_cf1 hU' f' h_cont h_holo_x
  have cf₂ : ContinuousOn ↿(partial_y f') U' :=
    continuousOn_fderiv_of_differentiableOn_fin2_cf2 hU' f' h_cont h_holo_y
  have df₁ : ∀ p ∈ U', HasFDerivAt (fun x => f' (x, p.2)) (partial_x f' p.1 p.2) p.1 :=
    continuousOn_fderiv_of_differentiableOn_fin2_df1 hU' f' h_holo_x
  have df₂ : ∀ p ∈ U', HasFDerivAt (fun y => f' (p.1, y)) (partial_y f' p.1 p.2) p.2 :=
    continuousOn_fderiv_of_differentiableOn_fin2_df2 hU' f' h_holo_y
  have h_fderiv' : ∀ p ∈ U', fderiv ℂ f' p = coprod (partial_x f' p.1 p.2) (partial_y f' p.1 p.2) :=
    continuousOn_fderiv_of_differentiableOn_fin2_fderiv hU' f' cf₁ cf₂ df₁ df₂
  have h_prod : ContinuousOn (fun p => (partial_x f' p.1 p.2, partial_y f' p.1 p.2)) U' :=
    ContinuousOn.prodMk cf₁ cf₂
  exact ContinuousOn.congr (continuous_coprod_C.comp_continuousOn h_prod) h_fderiv'

lemma continuousOn_fderiv_of_differentiableOn_fin2 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let U' := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  let f' : ℂ × ℂ → ℂ := f ∘ e.symm
  have h_cont : ContinuousOn f' U' :=
    ContinuousOn.comp hf.continuousOn e.symm.continuous.continuousOn (fun _ hx => hx)
  have h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'} := by
    intro y x hx
    let g : ℂ → ℂ × ℂ := fun x' => (x', y)
    have hg_diff : Differentiable ℂ g := by fun_prop
    have hg_diff2 : Differentiable ℂ (fun x' => e.symm (g x')) := e.symm.differentiable.comp hg_diff
    have hg_diff_at : DifferentiableWithinAt ℂ (fun x' => e.symm (g x')) {x | (x, y) ∈ U'} x :=
      hg_diff2.differentiableAt.differentiableWithinAt
    exact (hf _ hx).comp x hg_diff_at (fun x' hx' => hx')
  have h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'} := by
    intro x y hy
    let g : ℂ → ℂ × ℂ := fun y' => (x, y')
    have hg_diff : Differentiable ℂ g := by fun_prop
    have hg_diff2 : Differentiable ℂ (fun y' => e.symm (g y')) := e.symm.differentiable.comp hg_diff
    have hg_diff_at : DifferentiableWithinAt ℂ (fun y' => e.symm (g y')) {y | (x, y) ∈ U'} y :=
      hg_diff2.differentiableAt.differentiableWithinAt
    exact (hf _ hy).comp y hg_diff_at (fun y' hy' => hy')
  have h_cont_fderiv' :=
    continuousOn_fderiv_of_differentiableOn_fin2_aux hU' f' h_cont h_holo_x h_holo_y
  have h_fderiv :
      ∀ p ∈ U, fderiv ℂ f p = (fderiv ℂ f' (e p)).comp (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ) := by
    intro p hp
    have hp_U' : e p ∈ U' := by simpa [U'] using hp
    have hd_f'_aux : DifferentiableAt ℂ f (e.symm (e p)) := by
      have heq : e.symm (e p) = p := ContinuousLinearEquiv.symm_apply_apply e p
      rw [heq]
      exact hf.differentiableAt (hU.mem_nhds hp)
    have hd_f' : DifferentiableAt ℂ f' (e p) :=
      DifferentiableAt.comp (e p) hd_f'_aux e.symm.differentiableAt
    have h_fderiv_comp := fderiv_comp p hd_f' e.differentiableAt
    have h_eq_f : f = f' ∘ e := by
      ext x
      simp [f']
    rw [h_eq_f]
    rw [e.hasFDerivAt.fderiv] at h_fderiv_comp
    exact h_fderiv_comp
  have h_cont_comp :
      ContinuousOn (fun p => (fderiv ℂ f' (e p)).comp (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ)) U := by
    let F : (Fin 2 → ℂ) → ℂ × ℂ →L[ℂ] ℂ := fun p => fderiv ℂ f' (e p)
    have hF_cont : ContinuousOn F U :=
      h_cont_fderiv'.comp e.continuous.continuousOn (fun p hp => by simpa [U'] using hp)
    have step1 : ContinuousOn (fun p => (F p).comp (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ)) U :=
      (continuous_compRight_C e).comp_continuousOn hF_cont
    apply ContinuousOn.congr step1
    intro x hx
    rfl
  exact ContinuousOn.congr h_cont_comp h_fderiv

end Analysis

namespace QFT

variable {n : ℕ}
def IsCone (V : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ V, ∀ c > 0, (fun i => c * x i) ∈ V

def DualCone (V : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  { y | ∀ x ∈ V, 0 ≤ ∑ i, x i * y i }

lemma isClosed_DualCone (V : Set (Fin n → ℝ)) : IsClosed (DualCone V) := by
  have h_eq : DualCone V = ⋂ x ∈ V, { y | 0 ≤ ∑ i, x i * y i } := by
    ext y
    simp only [DualCone, mem_setOf_eq, mem_iInter]
  rw [h_eq]
  apply isClosed_biInter
  intro x _
  apply IsClosed.preimage
  · apply continuous_finsetSum Finset.univ
    intro i _
    apply Continuous.mul continuous_const (continuous_apply i)
  · exact isClosed_Ici

lemma convex_DualCone (V : Set (Fin n → ℝ)) : Convex ℝ (DualCone V) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  simp only [DualCone, mem_setOf_eq] at *
  intro x hx
  have h1 := hy₁ x hx
  have h2 := hy₂ x hx
  have h_sum : (∑ i, x i * (a * y₁ i + b * y₂ i)) =
      a * (∑ i, x i * y₁ i) + b * (∑ i, x i * y₂ i) := by
    calc
      _ = ∑ i, (a * (x i * y₁ i) + b * (x i * y₂ i)) := by
        congr 1
        ext i
        ring
      _ = (∑ i, a * (x i * y₁ i)) + (∑ i, b * (x i * y₂ i)) := Finset.sum_add_distrib
      _ = a * (∑ i, x i * y₁ i) + b * (∑ i, x i * y₂ i) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_target : (a • y₁ + b • y₂) = fun i => a * y₁ i + b * y₂ i := rfl
  rw [h_target]
  rw [h_sum]
  apply add_nonneg
  · exact mul_nonneg ha h1
  · exact mul_nonneg hb h2

lemma isCone_DualCone (V : Set (Fin n → ℝ)) : IsCone (DualCone V) := by
  intro y hy c hc
  simp only [DualCone, mem_setOf_eq] at *
  intro x hx
  have h1 := hy x hx
  have h_sum : (∑ i, x i * (c * y i)) = c * (∑ i, x i * y i) := by
    calc
      _ = ∑ i, c * (x i * y i) := by
        congr 1
        ext i
        ring
      _ = c * (∑ i, x i * y i) := by rw [← Finset.mul_sum]
  rw [h_sum]
  exact mul_nonneg (le_of_lt hc) h1

def TubeDomain (V : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  { z | (fun i => (z i).im) ∈ V }

lemma isOpen_TubeDomain {V : Set (Fin n → ℝ)} (hV : IsOpen V) :
    IsOpen (TubeDomain V) := by
  have h_eq : TubeDomain V = (fun z : Fin n → ℂ => fun i => (z i).im) ⁻¹' V := by rfl
  rw [h_eq]
  apply IsOpen.preimage
  · apply continuous_pi
    intro i
    exact Complex.continuous_im.comp (continuous_apply i)
  · exact hV

lemma convex_TubeDomain {V : Set (Fin n → ℝ)} (hV : Convex ℝ V) :
    Convex ℝ (TubeDomain V) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  simp only [TubeDomain, mem_setOf_eq] at *
  have h_im : (fun i => ((a • z₁ + b • z₂) i).im) =
      a • (fun i => (z₁ i).im) + b • (fun i => (z₂ i).im) := by
    ext i
    simp [Pi.add_apply, Pi.smul_apply, Complex.add_im]
  rw [h_im]
  exact hV hz₁ hz₂ ha hb hab

def WedgeDomain (V_plus V_minus U : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  TubeDomain V_plus ∪ TubeDomain V_minus ∪
    {z : Fin n → ℂ | (fun i => (z i).re) ∈ U ∧ (fun i => (z i).im) = 0}

def LocalTubeDomain (V U : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℂ) :=
  { z | (fun i => (z i).re) ∈ U ∧ (fun i => (z i).im) ∈ V ∧ ‖(fun i => (z i).im)‖ < r }

def LocalWedgeDomain (V_plus V_minus U : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℂ) :=
  LocalTubeDomain V_plus U r ∪ LocalTubeDomain V_minus U r ∪
    {z : Fin n → ℂ | (fun i => (z i).re) ∈ U ∧ (fun i => (z i).im) = 0}

lemma isOpen_LocalTubeDomain {V U : Set (Fin n → ℝ)} {r : ℝ} (hV : IsOpen V) (hU : IsOpen U) :
    IsOpen (LocalTubeDomain V U r) := by
  have h1 : Continuous (fun z : Fin n → ℂ => fun i => (z i).re) := by
    apply continuous_pi; intro i; exact Complex.continuous_re.comp (continuous_apply i)
  have h2 : Continuous (fun z : Fin n → ℂ => fun i => (z i).im) := by
    apply continuous_pi; intro i; exact Complex.continuous_im.comp (continuous_apply i)
  have h3 : Continuous (fun z : Fin n → ℂ => ‖fun i => (z i).im‖) :=
    continuous_norm.comp h2
  have eq : LocalTubeDomain V U r =
    ((fun z : Fin n → ℂ => fun i => (z i).re) ⁻¹' U) ∩
    ((fun z : Fin n → ℂ => fun i => (z i).im) ⁻¹' V) ∩
    ((fun z : Fin n → ℂ => ‖fun i => (z i).im‖) ⁻¹' (Set.Iio r)) := by
    ext z
    simp [LocalTubeDomain, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
    tauto
  rw [eq]
  apply IsOpen.inter
  · apply IsOpen.inter
    · exact hU.preimage h1
    · exact hV.preimage h2
  · exact isOpen_Iio.preimage h3

def EpsteinTubeDomain (V_plus V_minus : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  TubeDomain (convexHull ℝ (V_plus ∪ V_minus))

lemma isOpen_EpsteinTubeDomain {V_plus V_minus : Set (Fin n → ℝ)}
    (hV_plus : IsOpen V_plus) (hV_minus : IsOpen V_minus) :
    IsOpen (EpsteinTubeDomain V_plus V_minus) := by
  apply isOpen_TubeDomain
  apply IsOpen.convexHull
  exact IsOpen.union hV_plus hV_minus

noncomputable def supportFunction (K : Set (Fin n → ℝ)) (y : Fin n → ℝ) : ℝ :=
  sSup { ∑ i, x i * y i | x ∈ K }

lemma bddAbove_inner_of_isCompact {K : Set (Fin n → ℝ)} (hK : IsCompact K) (y : Fin n → ℝ) :
    BddAbove { ∑ i, x i * y i | x ∈ K } := by
  have h_cont : Continuous (fun x : Fin n → ℝ => ∑ i, x i * y i) := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact Continuous.mul (continuous_apply i) continuous_const
  have h_comp : IsCompact ((fun x : Fin n → ℝ => ∑ i, x i * y i) '' K) := hK.image h_cont
  have h_bdd : BddAbove ((fun x : Fin n → ℝ => ∑ i, x i * y i) '' K) := h_comp.bddAbove
  have h_eq : ((fun x : Fin n → ℝ => ∑ i, x i * y i) '' K) = { ∑ i, x i * y i | x ∈ K } := by
    ext r
    simp only [mem_image, mem_setOf_eq]
  rw [← h_eq]
  exact h_bdd

lemma supportFunction_nonpos_of_subset_dualCone
    {V K : Set (Fin n → ℝ)} (hK : K ⊆ DualCone V) (y : Fin n → ℝ) (hy : y ∈ V) :
    supportFunction K (-y) ≤ 0 := by
  unfold supportFunction
  by_cases h_emp : K = ∅
  · simp [h_emp]
  · have h_nonempty : K.Nonempty := nonempty_iff_ne_empty.mpr h_emp
    apply csSup_le
    · rcases h_nonempty with ⟨x, hx⟩
      use (∑ i, x i * (-y) i)
      simp only [mem_setOf_eq]
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hx_dual := hK hx
      simp only [DualCone, mem_setOf_eq] at hx_dual
      have h_nonneg := hx_dual y hy
      have h_eq : (∑ i, x i * (-y) i) = - (∑ i, y i * x i) := by
        calc
          (∑ i, x i * (-y) i) = ∑ i, -(x i * y i) := by simp [mul_neg]
          _ = - (∑ i, x i * y i) := by rw [Finset.sum_neg_distrib]
          _ = - (∑ i, y i * x i) := by simp [mul_comm]
      rw [h_eq]
      exact neg_nonpos.mpr h_nonneg

lemma tendsto_integral_boundary
    (V : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin n → ℝ) → ℂ)
    (g : (Fin n → ℝ) → ℂ)
    (bound : (Fin n → ℝ) → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ᶠ y in nhdsWithin 0 V, AEStronglyMeasurable (f y) volume)
    (h_bound : ∀ᶠ y in nhdsWithin 0 V, ∀ᵐ x ∂volume, ‖f y x‖ ≤ bound x)
    (h_tendsto : ∀ᵐ x ∂volume, Tendsto (fun y => f y x) (nhdsWithin 0 V) (nhds (g x))) :
    Tendsto (fun y => ∫ x, f y x) (nhdsWithin 0 V) (nhds (∫ x, g x)) := by
  exact tendsto_integral_filter_of_dominated_convergence bound
    h_f_meas h_bound h_bound_integrable h_tendsto

lemma differentiableOn_integral_of_dominated_measure_1d
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → α → ℂ)
    (f' : ℂ → α → ℂ →L[ℂ] ℂ)
    (bound : α → ℝ)
    (h_bound_integrable : Integrable bound μ)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (f z) μ)
    (h_f_int : ∀ z ∈ U, Integrable (f z) μ)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f' z) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ z ∈ U, ‖f' z x‖ ≤ bound x)
    (h_diff : ∀ᵐ x ∂μ, ∀ z ∈ U, HasFDerivAt (fun w => f w x) (f' z x) z) :
    DifferentiableOn ℂ (fun z => ∫ x, f z x ∂μ) U := by
  intro z₀ hz₀
  have hs : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (f z) μ :=
    eventually_of_mem hs h_f_meas
  have hF_int_z₀ : Integrable (f z₀) μ := h_f_int z₀ hz₀
  have hF'_meas_z₀ : AEStronglyMeasurable (f' z₀) μ := h_f'_meas z₀ hz₀
  have h_deriv := hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    hF_meas hF_int_z₀ hF'_meas_z₀ h_bound h_bound_integrable h_diff
  exact h_deriv.differentiableAt.differentiableWithinAt

lemma differentiableOn_integral_of_dominated_measure_2d
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (U : Set (Fin 2 → ℂ)) (hU : IsOpen U)
    (f : (Fin 2 → ℂ) → α → ℂ)
    (f' : (Fin 2 → ℂ) → α → (Fin 2 → ℂ) →L[ℂ] ℂ)
    (bound : α → ℝ)
    (h_bound_integrable : Integrable bound μ)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (f z) μ)
    (h_f_int : ∀ z ∈ U, Integrable (f z) μ)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f' z) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ z ∈ U, ‖f' z x‖ ≤ bound x)
    (h_diff : ∀ᵐ x ∂μ, ∀ z ∈ U, HasFDerivAt (fun w => f w x) (f' z x) z) :
    DifferentiableOn ℂ (fun z => ∫ x, f z x ∂μ) U := by
  intro z₀ hz₀
  have hs : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (f z) μ :=
    eventually_of_mem hs h_f_meas
  have hF_int_z₀ : Integrable (f z₀) μ := h_f_int z₀ hz₀
  have hF'_meas_z₀ : AEStronglyMeasurable (f' z₀) μ := h_f'_meas z₀ hz₀
  have h_deriv := hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    hF_meas hF_int_z₀ hF'_meas_z₀ h_bound h_bound_integrable h_diff
  exact h_deriv.differentiableAt.differentiableWithinAt

lemma differentiableOn_integral_of_dominated
    (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → (Fin n → ℝ) → ℂ)
    (f' : ℂ → (Fin n → ℝ) → ℂ)
    (bound : (Fin n → ℝ) → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (f z) volume)
    (h_f_int : ∀ z ∈ U, Integrable (f z) volume)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f' z) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ U, ‖f' z x‖ ≤ bound x)
    (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ U, HasDerivAt (fun w => f w x) (f' z x) z) :
    DifferentiableOn ℂ (fun z => ∫ x, f z x) U := by
  intro z₀ hz₀
  have hs : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (f z) volume :=
    eventually_of_mem hs h_f_meas
  have hF_int_z₀ : Integrable (f z₀) volume := h_f_int z₀ hz₀
  have hF'_meas_z₀ : AEStronglyMeasurable (f' z₀) volume := h_f'_meas z₀ hz₀
  have h_deriv := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hF_meas hF_int_z₀ hF'_meas_z₀ h_bound h_bound_integrable h_diff
  exact h_deriv.2.differentiableAt.differentiableWithinAt

noncomputable def fourierLaplaceTransform
    (Ω : TopologicalSpace.Opens (Fin n → ℝ)) (φ : 𝓓(Ω, ℂ)) (z : Fin n → ℂ) : ℂ :=
  ∫ x : Fin n → ℝ, (φ x) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))

def ForwardCone (n : ℕ) : Set (Fin n → ℝ) :=
  {y | ∃ h : 0 < n, 0 < y ⟨0, h⟩ ∧
    (∑ i : Fin n, if i = ⟨0, h⟩ then (0 : ℝ) else (y i) ^ 2) < (y ⟨0, h⟩) ^ 2}

def slice_fun (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (v : Fin n → ℝ) (w : ℂ) : ℂ :=
  f (fun i => x i + w * (v i : ℂ))

lemma slice_in_T_plus (V_plus : Set (Fin n → ℝ))
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) (w : ℂ) (hw : w.im > 0) :
    (fun i => x i + w * (v i : ℂ)) ∈ TubeDomain V_plus := by
  have H : (fun i => (x i + w * (v i : ℂ)).im) = (fun i => w.im * v i) := by
    ext i
    simp [Complex.add_im, Complex.mul_im, hx_real i]
  change (fun i => (x i + w * (v i : ℂ)).im) ∈ V_plus
  rw [H]
  exact hV_plus_cone v hv w.im hw

lemma slice_in_T_minus (V_plus : Set (Fin n → ℝ))
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) (w : ℂ) (hw : w.im < 0) :
    (fun i => x i + w * (v i : ℂ)) ∈ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) := by
  have H : (fun i => (x i + w * (v i : ℂ)).im) = (fun i => w.im * v i) := by
    ext i
    simp [Complex.add_im, Complex.mul_im, hx_real i]
  change (fun i => (x i + w * (v i : ℂ)).im) ∈ ((fun v : Fin n → ℝ => -v) '' V_plus)
  rw [H]
  have h_pos : -w.im > 0 := neg_pos.mpr hw
  have h_in_V : (fun i => -w.im * v i) ∈ V_plus := hV_plus_cone v hv (-w.im) h_pos
  have H2 : (fun i => w.im * v i) = (fun i => - (-w.im * v i)) := by
    ext i
    ring
  rw [H2]
  exact mem_image_of_mem (fun v => -v) h_in_V

def slice_real_set (U : Set (Fin n → ℝ)) (x : Fin n → ℂ) (v : Fin n → ℝ) : Set ℝ :=
  {w : ℝ | (fun i => (x i).re + w * v i) ∈ U}

lemma isOpen_slice_real_set
    (U : Set (Fin n → ℝ)) (hU_open : IsOpen U) (x : Fin n → ℂ) (v : Fin n → ℝ) :
    IsOpen (slice_real_set U x v) := by
  have h_cont : Continuous (fun w : ℝ => fun i => (x i).re + w * v i) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_id.mul continuous_const)
  exact hU_open.preimage h_cont

lemma slice_in_wedge (V_plus U : Set (Fin n → ℝ))
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) (w : ℂ)
    (hw : w ∈ Analysis.slitDomain (slice_real_set U x v)) :
    (fun i => x i + w * (v i : ℂ)) ∈
      WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U := by
  by_cases hw_im0 : w.im = 0
  · right
    dsimp [Analysis.slitDomain] at hw
    have hw_in : w.re ∈ slice_real_set U x v := by
      rcases hw with hw_ne | hw_in
      · exfalso; exact hw_ne hw_im0
      · exact hw_in
    have h_im : (fun i => (x i + w * (v i : ℂ)).im) = 0 := by
      ext i
      simp [Complex.add_im, Complex.mul_im, hx_real i, hw_im0]
    have h_re : (fun i => (x i + w * (v i : ℂ)).re) = (fun i => (x i).re + w.re * v i) := by
      ext i
      simp [Complex.add_re, Complex.mul_re, hw_im0]
    constructor
    · change (fun i => (x i + w * (v i : ℂ)).re) ∈ U
      rw [h_re]
      exact hw_in
    · change (fun i => (x i + w * (v i : ℂ)).im) = 0
      rw [h_im]
  · rcases lt_or_gt_of_ne hw_im0 with hw_neg | hw_pos
    · left; right; exact slice_in_T_minus V_plus hV_plus_cone x hx_real v hv w hw_neg
    · left; left; exact slice_in_T_plus V_plus hV_plus_cone x hx_real v hv w hw_pos

lemma slice_analytic (V_plus U : Set (Fin n → ℝ))
    (_hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0) (_hx_U : (fun i => (x i).re) ∈ U)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) :
    AnalyticOn ℂ (slice_fun f x v) (Analysis.slitDomain (slice_real_set U x v)) := by
  let slice_map := fun w : ℂ => (fun i => x i + w * (v i : ℂ))
  have h_slice_diff : Differentiable ℂ slice_map := by
    exact differentiable_pi.mpr (fun i => Differentiable.add
      ((differentiable_const (x i) : Differentiable ℂ (fun w : ℂ => x i)))
      (Differentiable.mul (differentiable_id : Differentiable ℂ (fun w : ℂ => w))
        ((differentiable_const (v i : ℂ) : Differentiable ℂ (fun w : ℂ => (v i : ℂ))))))
  have h_slice_cont : Continuous slice_map := h_slice_diff.continuous
  have hf_cont_slice :
      ContinuousOn (slice_fun f x v) (Analysis.slitDomain (slice_real_set U x v)) := by
    apply ContinuousOn.comp h_cont h_slice_cont.continuousOn
    intro w hw
    exact slice_in_wedge V_plus U hV_plus_cone x hx_real v hv w hw
  have h_isOpen_upper : IsOpen Analysis.upperHalfPlane := isOpen_lt continuous_const continuous_im
  have h_isOpen_lower : IsOpen Analysis.lowerHalfPlane := isOpen_lt continuous_im continuous_const
  have hf_ana_pos : AnalyticOn ℂ (slice_fun f x v) Analysis.upperHalfPlane := by
    have h_diff_on : DifferentiableOn ℂ (slice_fun f x v) Analysis.upperHalfPlane := by
      apply DifferentiableOn.comp h_holo_plus h_slice_diff.differentiableOn
      intro w hw
      exact slice_in_T_plus V_plus hV_plus_cone x hx_real v hv w hw
    exact DifferentiableOn.analyticOn h_diff_on h_isOpen_upper
  have hf_ana_neg : AnalyticOn ℂ (slice_fun f x v) Analysis.lowerHalfPlane := by
    have h_diff_on : DifferentiableOn ℂ (slice_fun f x v) Analysis.lowerHalfPlane := by
      apply DifferentiableOn.comp h_holo_minus h_slice_diff.differentiableOn
      intro w hw
      exact slice_in_T_minus V_plus hV_plus_cone x hx_real v hv w hw
    exact DifferentiableOn.analyticOn h_diff_on h_isOpen_lower
  exact Analysis.eow_1d_continuous (slice_real_set U x v)
    (isOpen_slice_real_set U hU_open x v) _ hf_cont_slice hf_ana_pos hf_ana_neg

lemma slice_analytic_at_zero (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) :
    AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) v) 0 := by
  let x_c : Fin n → ℂ := fun i => (x i : ℂ)
  have hx_real : ∀ i, (x_c i).im = 0 := fun i => by simp [x_c]
  have hx_re_U : (fun i => (x_c i).re) ∈ U := by
    have heq : (fun i => (x_c i).re) = x := by
      ext i
      simp [x_c]
    rw [heq]
    exact hx_U
  have h_ana := slice_analytic V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x_c hx_real hx_re_U v hv
  have h0_in : (0 : ℂ) ∈ Analysis.slitDomain (slice_real_set U x_c v) := by
    simp only [Analysis.slitDomain, mem_setOf_eq, Complex.zero_im, ne_eq, not_true_eq_false,
      Complex.zero_re, false_or]
    simp only [slice_real_set, mem_setOf_eq]
    have heq : (fun i => (x_c i).re + 0 * v i) = (fun i => (x_c i).re) := by
      ext i
      ring
    rw [heq]
    exact hx_re_U
  have h_open : IsOpen (Analysis.slitDomain (slice_real_set U x_c v)) :=
    Analysis.isOpen_slitDomain (isOpen_slice_real_set U hU_open x_c v)
  exact h_ana.analyticAt (h_open.mem_nhds h0_in)

noncomputable def eow_F_disc
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (v : Fin n → ℝ) (r : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ • ∮ z in C(0, r), (z - w)⁻¹ • (slice_fun f x v z)

lemma eow_F_disc_eq_slice_fun (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (v : Fin n → ℝ)
    (r : ℝ) (_hr : 0 < r)
    (h_diff : DifferentiableOn ℂ (slice_fun f x v) (Metric.closedBall 0 r))
    (w : ℂ) (hw : norm w < r) :
    eow_F_disc f x v r w = slice_fun f x v w := by
  have hw_ball : w ∈ Metric.ball (0:ℂ) r := by simpa using hw
  rw [eow_F_disc]
  have h_eq := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hw_ball h_diff.continuousOn (by
      intro z hz
      have h_nhds : Metric.closedBall (0:ℂ) r ∈ 𝓝 z :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz.1) Metric.ball_subset_closedBall
      exact h_diff.differentiableAt h_nhds)
  exact h_eq

namespace Bochner
open Complex.HadamardThreeLines

def LShape (r R : ℝ) : Set (Fin 2 → ℝ) :=
  {x | (0 < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < R) ∨ (0 < x 0 ∧ x 0 < R ∧ 0 < x 1 ∧ x 1 < r)}

def LShapeConvexHull (r R : ℝ) : Set (Fin 2 → ℝ) :=
  convexHull ℝ (LShape r R)

noncomputable def gaussianCutoff (ε : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  Complex.exp (- (ε : ℂ) * (z 0 ^ 2 + z 1 ^ 2))

lemma gaussianCutoff_diff (ε : ℝ) :
    Differentiable ℂ (gaussianCutoff ε) := by
  apply Differentiable.comp
  · exact Complex.differentiable_exp
  · apply Differentiable.mul
    · exact differentiable_const _
    · apply Differentiable.add
      · apply Differentiable.pow
        exact differentiable_apply 0
      · apply Differentiable.pow
        exact differentiable_apply 1

noncomputable def f_eps (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  f z * gaussianCutoff ε z

noncomputable def fuks_cauchy_integral_joint
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y₂_star : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∫ t : ℝ,
    (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
      ((t : ℂ) + I * (y₂_star : ℂ) - z 1)

lemma fuks_cauchy_integral_diff_joint (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y₂_star : ℝ)
    (U : Set (Fin 2 → ℂ)) (hU_open : IsOpen U)
    (_hU_z2 : ∀ z ∈ U, (z 1).im ≠ y₂_star)
    (f_eps_deriv : (Fin 2 → ℂ) → ℝ → (Fin 2 → ℂ) →L[ℂ] ℂ)
    (bound : ℝ → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ =>
      (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - z 1)) volume)
    (h_f_int : ∀ z ∈ U, Integrable (fun t : ℝ =>
      (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - z 1)) volume)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f_eps_deriv z) volume)
    (h_bound : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ U, ‖f_eps_deriv z t‖ ≤ bound t)
    (h_diff : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ U, HasFDerivAt (fun w =>
      (f_eps f ε (fun i => if i = 0 then w 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - w 1)) (f_eps_deriv z t) z) :
    DifferentiableOn ℂ (fun z => fuks_cauchy_integral_joint f ε y₂_star z) U := by
  have h_diff_int : DifferentiableOn ℂ (fun z => ∫ t : ℝ,
      (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - z 1)) U := by
    apply differentiableOn_integral_of_dominated_measure_2d U hU_open _ f_eps_deriv bound
      h_bound_integrable h_f_meas h_f_int h_f'_meas h_bound h_diff
  exact DifferentiableOn.const_smul h_diff_int (2 * Real.pi * I)⁻¹

lemma isOpen_LShape (r R : ℝ) : IsOpen (LShape r R) := by
  have h1 : IsOpen {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < R} := by
    have h_0_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    have h_0_lt_r : IsOpen {x : Fin 2 → ℝ | x 0 < r} :=
      isOpen_lt (continuous_apply 0) continuous_const
    have h_1_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 1} :=
      isOpen_lt continuous_const (continuous_apply 1)
    have h_1_lt_R : IsOpen {x : Fin 2 → ℝ | x 1 < R} :=
      isOpen_lt (continuous_apply 1) continuous_const
    exact h_0_pos.inter (h_0_lt_r.inter (h_1_pos.inter h_1_lt_R))
  have h2 : IsOpen {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < R ∧ 0 < x 1 ∧ x 1 < r} := by
    have h_0_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    have h_0_lt_R : IsOpen {x : Fin 2 → ℝ | x 0 < R} :=
      isOpen_lt (continuous_apply 0) continuous_const
    have h_1_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 1} :=
      isOpen_lt continuous_const (continuous_apply 1)
    have h_1_lt_r : IsOpen {x : Fin 2 → ℝ | x 1 < r} :=
      isOpen_lt (continuous_apply 1) continuous_const
    exact h_0_pos.inter (h_0_lt_R.inter (h_1_pos.inter h_1_lt_r))
  have h_eq : LShape r R =
      {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < R} ∪
      {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < R ∧ 0 < x 1 ∧ x 1 < r} := by
    ext x
    simp only [LShape, mem_setOf_eq, mem_union]
  rw [h_eq]
  exact h1.union h2

lemma isOpen_LShapeConvexHull (r R : ℝ) : IsOpen (LShapeConvexHull r R) :=
  (isOpen_LShape r R).convexHull

lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  match i with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

lemma kajiwara_slice_differentiableAt (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (z₁ z₂ : ℂ) (hz : (fun i => if i = 0 then z₁ else z₂) ∈ TubeDomain (LShape r R)) :
    DifferentiableAt ℂ (fun z => f (fun i => if i = 0 then z₁ else z)) z₂ := by
  let g : ℂ → (Fin 2 → ℂ) := fun z => (fun i => if i = 0 then z₁ else z)
  have hg_diff : Differentiable ℂ g := by
    intro z
    apply differentiableAt_pi.mpr
    intro i
    dsimp [g]
    by_cases hi : i = 0
    · simp only [if_pos hi]
      exact differentiableAt_const z₁
    · simp only [if_neg hi]
      exact differentiableAt_id
  have h_isOpen : IsOpen (TubeDomain (LShape r R)) := isOpen_TubeDomain (isOpen_LShape r R)
  apply DifferentiableAt.comp z₂ (hf_holo.differentiableAt (h_isOpen.mem_nhds hz)) (hg_diff z₂)

lemma kajiwara_circle_in_tube (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (w₁ : ℂ) (_hw₁ : 0 < w₁.im ∧ w₁.im < R)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt_up : ρ < R - w₁.im) (hρ_lt_down : ρ < w₁.im)
    (θ : ℝ) (z₂ : ℂ) (hz₂ : 0 < z₂.im ∧ z₂.im < r) :
    (fun i => if i = 0 then circleMap w₁ ρ θ else z₂) ∈ TubeDomain (LShape r R) := by
  simp only [TubeDomain, LShape, mem_setOf_eq]
  right
  have h_im : (circleMap w₁ ρ θ).im = w₁.im + ρ * Real.sin θ := by
    simp [circleMap, Complex.add_im, Complex.mul_im, Complex.exp_im, Complex.exp_re]
  have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h_sin_ge : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
  constructor
  · change 0 < (circleMap w₁ ρ θ).im; rw [h_im]; nlinarith
  · constructor
    · change (circleMap w₁ ρ θ).im < R; rw [h_im]; nlinarith
    · constructor
      · change 0 < z₂.im; exact hz₂.1
      · change z₂.im < r; exact hz₂.2

noncomputable def partialDeriv {n : ℕ} (f : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  deriv (fun (w : ℂ) => f (Function.update z j w)) (z j)

lemma partialDeriv_eq_cauchy_integral {n : ℕ} {U : Set (Fin n → ℂ)} (_hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U) (j : Fin n) (z₀ : Fin n → ℂ)
    (_hz₀ : z₀ ∈ U) (r : ℝ) (hr : 0 < r)
    (h_cball : Metric.closedBall (z₀ j) r ⊆ (fun w => Function.update z₀ j w) ⁻¹' U) :
    partialDeriv f j z₀ =
      (2 * Real.pi * I)⁻¹ * ∮ ζ in C(z₀ j, r), f (Function.update z₀ j ζ) / (ζ - z₀ j) ^ 2 := by
  let g : ℂ → ℂ := fun w => f (Function.update z₀ j w)
  have h_upd_diff : Differentiable ℂ (fun (w : ℂ) => Function.update z₀ j w) := by
    apply differentiable_pi.mpr
    intro i
    by_cases h : i = j
    · subst h
      have h_eq : (fun (w : ℂ) => Function.update z₀ i w i) = id := by ext w; simp
      rw [h_eq]
      exact differentiable_id
    · have h_eq : (fun (w : ℂ) => Function.update z₀ j w i) = fun w => z₀ i := by ext w; simp [h]
      rw [h_eq]
      exact differentiable_const _
  have hg_diff : DifferentiableOn ℂ g (Metric.closedBall (z₀ j) r) := by
    apply DifferentiableOn.comp hf (h_upd_diff.differentiableOn) h_cball
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (E := ℂ)
    (f := g) (c := z₀ j) (R := r) hr hg_diff
  have hc2 : ∮ z in C(z₀ j, r), (1 / (z - z₀ j) ^ 2) * g z =
      (2 * ↑Real.pi * I) * deriv g (z₀ j) := hc
  have h_eq : (fun z => (1 / (z - z₀ j) ^ 2) * g z) = (fun z => g z / (z - z₀ j) ^ 2) := by
    ext z
    ring
  rw [h_eq] at hc2
  have h_mul : (2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(z₀ j, r), g ζ / (ζ - z₀ j) ^ 2 =
      (2 * Real.pi * I : ℂ)⁻¹ * ((2 * ↑Real.pi * I) * deriv g (z₀ j)) := by
    rw [hc2]
  rw [← mul_assoc] at h_mul
  have h_inv : (2 * Real.pi * I : ℂ)⁻¹ * (2 * Real.pi * I : ℂ) = 1 := by
    apply inv_mul_cancel₀
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, I_ne_zero, or_false]
    intro h
    rcases h with h_false | h_pi
    · exact h_false
    · have h2 : (Real.pi : ℂ).re = 0 := by rw [h_pi]; rfl
      have h3 : (Real.pi : ℂ).re = Real.pi := rfl
      rw [h3] at h2
      exact Real.pi_pos.ne' h2
  rw [h_inv, one_mul] at h_mul
  exact h_mul.symm

noncomputable def bochner_f_eps (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  f z * Complex.exp (-↑ε * (z 0 ^ 2 + z 1 ^ 2))

noncomputable def bochner_fourier_transform_eps
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y : Fin 2 → ℝ) (ξ : Fin 2 → ℝ) : ℂ :=
  ∫ (x : Fin 2 → ℝ), bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
    Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))

lemma fourier_shift_1d_eps_rect (a b ε M : ℝ) (hab : a ≤ b) (_hε : 0 < ε) (_hM : 0 < M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ Set.Icc a b}) :
    (((∫ (x : ℝ) in -M..M, g (↑x + ↑a * I)) - ∫ (x : ℝ) in -M..M, g (↑x + ↑b * I)) +
     I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) -
    I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I) = 0 := by
  let z : ℂ := -↑M + ↑a * I
  let w : ℂ := ↑M + ↑b * I
  have h_z_re : z.re = -M := by simp [z]
  have h_w_re : w.re = M := by simp [w]
  have h_z_im : z.im = a := by simp [z]
  have h_w_im : w.im = b := by simp [w]
  have H := integral_boundary_rect_eq_zero_of_differentiableOn g z w
  have hd : DifferentiableOn ℂ g (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    apply hg_holo.mono
    intro ζ hζ
    simp only [Set.mem_setOf_eq]
    have hζ_im : ζ.im ∈ uIcc z.im w.im := hζ.2
    rw [h_z_im, h_w_im] at hζ_im
    have : uIcc a b = Icc a b := uIcc_of_le hab
    rwa [this] at hζ_im
  have H2 := H hd
  rw [h_z_re, h_w_re, h_z_im, h_w_im] at H2
  have h_cast : (↑(-M) : ℂ) = -↑M := by push_cast; rfl
  rw [h_cast] at H2
  exact H2

lemma tendsto_exp_neg_mul_sq_atTop (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun M : ℝ => Real.exp (-ε * M ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℝ => M ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 : Tendsto (fun M : ℝ => ε * M ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hε h1
  have h3 : Tendsto (fun M : ℝ => -ε * M ^ 2) atTop atBot := by
    have : (fun M : ℝ => -ε * M ^ 2) = (fun x => -x) ∘ (fun M : ℝ => ε * M ^ 2) := by
      ext M
      dsimp
      ring
    rw [this]
    exact tendsto_neg_atTop_atBot.comp h2
  exact Real.tendsto_exp_atBot.comp h3

lemma vertical_integral_tendsto_zero (a b ε C : ℝ) (hab : a ≤ b) (hε : 0 < ε)
    (g : ℂ → ℂ)
    (hg_bound : ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    Tendsto (fun M : ℝ => ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) atTop (𝓝 0) := by
  have h_bound_M : ∀ M : ℝ,
      ‖∫ (y : ℝ) in a..b, g (↑M + ↑y * I)‖ ≤ (C * Real.exp (-ε * M ^ 2)) * |b - a| := by
    intro M
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hab] at hy
    have hy_Icc : y ∈ Icc a b := ⟨le_of_lt hy.1, hy.2⟩
    have hz_im : (↑M + ↑y * I : ℂ).im = y := by simp
    have hz_re : (↑M + ↑y * I : ℂ).re = M := by simp
    have hz_im_mem : (↑M + ↑y * I : ℂ).im ∈ Icc a b := by rwa [hz_im]
    have hg := hg_bound (↑M + ↑y * I) hz_im_mem
    rw [hz_re] at hg
    exact hg
  apply squeeze_zero_norm (h := h_bound_M)
  have h_lim := tendsto_exp_neg_mul_sq_atTop ε hε
  have h_mul := Tendsto.mul_const (|b - a|) (Tendsto.const_mul C h_lim)
  simp only [mul_zero, zero_mul] at h_mul
  exact h_mul

lemma vertical_integral_neg_tendsto_zero (a b ε C : ℝ) (hab : a ≤ b) (hε : 0 < ε)
    (g : ℂ → ℂ)
    (hg_bound : ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    Tendsto (fun M : ℝ => ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) atTop (𝓝 0) := by
  have h_bound_M : ∀ M : ℝ,
      ‖∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)‖ ≤ (C * Real.exp (-ε * M ^ 2)) * |b - a| := by
    intro M
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hab] at hy
    have hy_Icc : y ∈ Icc a b := ⟨le_of_lt hy.1, hy.2⟩
    have hz_im : (-↑M + ↑y * I : ℂ).im = y := by simp
    have hz_re : (-↑M + ↑y * I : ℂ).re = -M := by simp
    have hz_im_mem : (-↑M + ↑y * I : ℂ).im ∈ Icc a b := by rwa [hz_im]
    have hg := hg_bound (-↑M + ↑y * I) hz_im_mem
    rw [hz_re] at hg
    have : (-M) ^ 2 = M ^ 2 := neg_sq M
    rw [this] at hg
    exact hg
  apply squeeze_zero_norm (h := h_bound_M)
  have h_lim := tendsto_exp_neg_mul_sq_atTop ε hε
  have h_mul := Tendsto.mul_const (|b - a|) (Tendsto.const_mul C h_lim)
  simp only [mul_zero, zero_mul] at h_mul
  exact h_mul

lemma integrable_of_gaussian_bound (ε C : ℝ) (hε : 0 < ε) (y : ℝ) (a b : ℝ) (hy : y ∈ Icc a b)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ Set.Icc a b})
    (hg_bound : ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    Integrable (fun x : ℝ => g (↑x + I * ↑y)) := by
  have h_cont_path : Continuous (fun x : ℝ => (↑x + I * ↑y : ℂ)) := by continuity
  have h_map : ∀ x : ℝ, (↑x + I * ↑y : ℂ).im ∈ Icc a b := by
    intro x
    have : (↑x + I * ↑y : ℂ).im = y := by simp
    rwa [this]
  have hg_conton : ContinuousOn g {z | z.im ∈ Icc a b} := hg_holo.continuousOn
  have hg_cont : Continuous (fun x : ℝ => g (↑x + I * ↑y)) :=
    ContinuousOn.comp_continuous hg_conton h_cont_path (fun x => h_map x)
  have h_meas : AEStronglyMeasurable (fun x : ℝ => g (↑x + I * ↑y)) volume :=
    hg_cont.aestronglyMeasurable
  have h_gauss : Integrable (fun x : ℝ => C * Real.exp (-ε * x ^ 2)) volume :=
    (integrable_exp_neg_mul_sq hε).const_mul C
  apply Integrable.mono' h_gauss h_meas
  filter_upwards with x
  have h_re : (↑x + I * ↑y : ℂ).re = x := by simp
  have h_bound := hg_bound (↑x + I * ↑y) (h_map x)
  rwa [h_re] at h_bound

lemma fourier_shift_1d_eps (a b ε : ℝ) (hab : a < b) (hε : 0 < ε)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ Set.Icc a b})
    (hg_bound : ∃ C : ℝ, ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    ∫ (x : ℝ), g (↑x + I * ↑a) = ∫ (x : ℝ), g (↑x + I * ↑b) := by
  rcases hg_bound with ⟨C, hg_bound⟩
  have hab_le : a ≤ b := le_of_lt hab
  have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab_le⟩
  have hb_mem : b ∈ Icc a b := ⟨hab_le, le_rfl⟩
  have hint_a := integrable_of_gaussian_bound ε C hε a a b ha_mem g hg_holo hg_bound
  have hint_b := integrable_of_gaussian_bound ε C hε b a b hb_mem g hg_holo hg_bound
  have h_comm_a : (fun x : ℝ => g (↑x + ↑a * I)) = (fun x : ℝ => g (↑x + I * ↑a)) := by
    ext x
    rw [mul_comm (a : ℂ) I]
  have h_comm_b : (fun x : ℝ => g (↑x + ↑b * I)) = (fun x : ℝ => g (↑x + I * ↑b)) := by
    ext x
    rw [mul_comm (b : ℂ) I]
  have h_tendsto_a :=
    MeasureTheory.intervalIntegral_tendsto_integral hint_a tendsto_neg_atTop_atBot tendsto_id
  have h_tendsto_b :=
    MeasureTheory.intervalIntegral_tendsto_integral hint_b tendsto_neg_atTop_atBot tendsto_id
  have h_tendsto_sub := h_tendsto_a.sub h_tendsto_b
  dsimp only [id] at h_tendsto_sub
  have h_rect_lim : Tendsto
      (fun M : ℝ => (∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b)))
      atTop (𝓝 0) := by
    have h_v_pos := vertical_integral_tendsto_zero a b ε C hab_le hε g hg_bound
    have h_v_neg := vertical_integral_neg_tendsto_zero a b ε C hab_le hε g hg_bound
    have h_rhs : Tendsto (fun M : ℝ =>
        - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) + (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)))
        atTop (𝓝 0) := by
      have h1 := (h_v_pos.const_smul I).neg
      have h2 := h_v_neg.const_smul I
      have h12 := h1.add h2
      simp only [smul_zero, neg_zero, zero_add] at h12
      exact h12
    apply Tendsto.congr' _ h_rhs
    filter_upwards [eventually_gt_atTop 0] with M hM
    have h_rect := fourier_shift_1d_eps_rect a b ε M hab_le hε hM g hg_holo
    rw [h_comm_a, h_comm_b] at h_rect
    have h_sub : (∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b)) =
        - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) + (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by
      calc
        (∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b))
        _ = (((∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b)) +
              I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) -
             I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) -
            (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) +
            (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by ring
        _ = 0 - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) +
            (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by rw [h_rect]
        _ = - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) +
            (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by ring
    exact h_sub.symm
  have h_eq_zero : (∫ (x : ℝ), g (↑x + I * ↑a)) - (∫ (x : ℝ), g (↑x + I * ↑b)) = 0 :=
    tendsto_nhds_unique h_tendsto_sub h_rect_lim
  exact sub_eq_zero.mp h_eq_zero

lemma fourier_shift_1d_eps_uIcc (a b ε : ℝ) (hε : 0 < ε)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ uIcc a b})
    (hg_bound : ∃ C : ℝ, ∀ z : ℂ, z.im ∈ uIcc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    ∫ (x : ℝ), g (↑x + I * ↑a) = ∫ (x : ℝ), g (↑x + I * ↑b) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h_uIcc : uIcc a b = Icc a b := uIcc_of_le (le_of_lt hab)
    rw [h_uIcc] at hg_holo hg_bound
    exact fourier_shift_1d_eps a b ε hab hε g hg_holo hg_bound
  · rfl
  · have h_uIcc : uIcc a b = Icc b a := uIcc_of_ge (le_of_lt hba)
    rw [h_uIcc] at hg_holo hg_bound
    have h_rev := fourier_shift_1d_eps b a ε hba hε g hg_holo hg_bound
    exact h_rev.symm

lemma exp_sub_I_mul_add (x y ξ : ℝ) :
    Complex.exp (-I * (↑x * ↑ξ)) * ↑(Real.exp (y * ξ)) =
    Complex.exp (-I * ((↑x + I * ↑y) * ↑ξ)) := by
  have h_exp_real : (↑(Real.exp (y * ξ)) : ℂ) = Complex.exp (↑(y * ξ)) := by
    exact ofReal_exp (y * ξ)
  rw [h_exp_real, ← Complex.exp_add]
  congr 1
  push_cast
  have h_I2 : I ^ 2 = -1 := I_sq
  linear_combination (↑ξ * ↑y) * h_I2

lemma exp_sub_I_mul_add_2d (x y ξ : Fin 2 → ℝ) :
    Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1))) * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) =
    Complex.exp (-I * ((↑(x 0) + I * ↑(y 0)) * ↑(ξ 0) + (↑(x 1) + I * ↑(y 1)) * ↑(ξ 1))) := by
  have h_exp_real : (↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) : ℂ) =
      Complex.exp (↑(y 0 * ξ 0 + y 1 * ξ 1)) := by
    exact ofReal_exp (y 0 * ξ 0 + y 1 * ξ 1)
  rw [h_exp_real, ← Complex.exp_add]
  congr 1
  push_cast
  have h_I2 : I ^ 2 = -1 := I_sq
  linear_combination ((↑(ξ 0) * ↑(y 0) + ↑(ξ 1) * ↑(y 1))) * h_I2

noncomputable def bochner_integrand_F
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) : ℂ :=
  bochner_f_eps f ε z * Complex.exp (-I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))

lemma bochner_fourier_mul_exp_eq_integral (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y ξ : Fin 2 → ℝ) :
    bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) := by
  unfold bochner_fourier_transform_eps bochner_integrand_F
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  ext x
  rw [mul_assoc]
  congr 1
  exact exp_sub_I_mul_add_2d x y ξ

lemma integral_finTwo_eq_integral_prod (g : (Fin 2 → ℝ) → ℂ) (hg : Integrable g) :
    ∫ (x : Fin 2 → ℝ), g x = ∫ (x₀ : ℝ), ∫ (x₁ : ℝ), g ![x₀, x₁] := by
  have h_pres := volume_preserving_finTwoArrow ℝ
  have H := h_pres.integral_comp' (fun p : ℝ × ℝ => g ![p.1, p.2])
  have h_comp : (fun x : Fin 2 → ℝ =>
      g ![(MeasurableEquiv.finTwoArrow x).1, (MeasurableEquiv.finTwoArrow x).2]) = g := by
    ext x
    rw [MeasurableEquiv.finTwoArrow_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [h_comp] at H
  rw [H]
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  have h_int_iff := h_pres.integrable_comp_emb h_emb (g := fun p : ℝ × ℝ => g ![p.1, p.2])
  have h_comp_fun : (fun p : ℝ × ℝ => g ![p.1, p.2]) ∘ (⇑MeasurableEquiv.finTwoArrow) = g := by
    ext x
    exact congr_fun h_comp x
  rw [h_comp_fun] at h_int_iff
  have h_int_prod : Integrable (fun p : ℝ × ℝ => g ![p.1, p.2]) volume := h_int_iff.mp hg
  exact integral_prod (fun p : ℝ × ℝ => g ![p.1, p.2]) h_int_prod

lemma sq_add_I_mul_re (x y : ℝ) :
    ((↑x + I * ↑y : ℂ) ^ 2).re = x ^ 2 - y ^ 2 := by
  have : (↑x + I * ↑y : ℂ) ^ 2 = (↑x + I * ↑y) * (↑x + I * ↑y) := sq (↑x + I * ↑y)
  rw [this]
  simp
  ring

lemma neg_ofReal_mul_re (ε : ℝ) (w : ℂ) :
    (- (ε : ℂ) * w).re = -ε * w.re := by
  simp

lemma norm_exp_gaussian_decay (ε : ℝ) (x y : Fin 2 → ℝ) :
    ‖Complex.exp (-↑ε * ((↑(x 0) + I * ↑(y 0)) ^ 2 + (↑(x 1) + I * ↑(y 1)) ^ 2))‖ =
    Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) := by
  rw [Complex.norm_exp]
  have h_re :
      ((- (ε : ℂ)) * (((x 0 : ℂ) + I * (y 0 : ℂ)) ^ 2 + ((x 1 : ℂ) + I * (y 1 : ℂ)) ^ 2)).re =
      -ε * (x 0 ^ 2 + x 1 ^ 2) + ε * (y 0 ^ 2 + y 1 ^ 2) := by
    rw [neg_ofReal_mul_re, add_re, sq_add_I_mul_re, sq_add_I_mul_re]
    ring
  rw [h_re, Real.exp_add]

lemma norm_exp_fourier (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    ‖Complex.exp
      (-I * (((x 0 : ℂ) + I * (y 0 : ℂ)) * (ξ 0 : ℂ) + ((x 1 : ℂ) + I * (y 1 : ℂ)) * (ξ 1 : ℂ)))‖ =
    Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  rw [Complex.norm_exp]
  congr 1
  simp

lemma bochner_integrand_norm_eq (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ =
    ‖f (fun i => ↑(x i) + I * ↑(y i))‖ * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) *
    Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  unfold bochner_integrand_F bochner_f_eps
  rw [norm_mul, norm_mul]
  have h_gauss := norm_exp_gaussian_decay ε x y
  have h_fourier := norm_exp_fourier ξ x y
  rw [h_gauss, h_fourier]
  ring

lemma integrable_gaussian_2d (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) := by
  have h_eq : (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) =
      (fun p : ℝ × ℝ => Real.exp (-ε * p.1 ^ 2) * Real.exp (-ε * p.2 ^ 2)) ∘
      (⇑MeasurableEquiv.finTwoArrow) := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_eq]
  have h_pres := volume_preserving_finTwoArrow ℝ
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  rw [h_pres.integrable_comp_emb h_emb]
  have h1 : Integrable (fun x : ℝ => Real.exp (-ε * x ^ 2)) volume := integrable_exp_neg_mul_sq hε
  have h_prod : Integrable
      (fun p : ℝ × ℝ => Real.exp (-ε * p.1 ^ 2) * Real.exp (-ε * p.2 ^ 2)) volume :=
    Integrable.mul_prod h1 h1
  exact h_prod

noncomputable def bochner_slice0
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (z₁ : ℂ) (w : ℂ) : ℂ :=
  bochner_integrand_F f ε ξ ![w, z₁]

lemma slice0_eq_integrand (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    bochner_slice0 f ε ξ (↑(x 1) + I * ↑(y 1)) (↑(x 0) + I * ↑(y 0)) =
    bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) := by
  unfold bochner_slice0
  congr 1
  ext i
  fin_cases i <;> rfl

noncomputable def bochner_slice1
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (z₀ : ℂ) (w : ℂ) : ℂ :=
  bochner_integrand_F f ε ξ ![z₀, w]

lemma slice1_eq_integrand (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    bochner_slice1 f ε ξ (↑(x 0) + I * ↑(y 0)) (↑(x 1) + I * ↑(y 1)) =
    bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) := by
  unfold bochner_slice1
  congr 1
  ext i
  fin_cases i <;> rfl

lemma mem_TubeDomain_pure_imag (V : Set (Fin 2 → ℝ)) (y : Fin 2 → ℝ) :
    (fun i => ↑(0 : ℝ) + I * ↑(y i)) ∈ TubeDomain V ↔ y ∈ V := by
  simp [TubeDomain]

lemma diff_affine_slice1 (z₀ : ℂ) :
    Differentiable ℂ (fun w : ℂ => (![z₀, w] : Fin 2 → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact differentiable_const z₀
  · exact differentiable_id

lemma bochner_slice1_diffOn (r R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (ξ : Fin 2 → ℝ) (x₀ y₀ y₁ y₁' : ℝ)
    (h_path : ∀ t ∈ uIcc y₁ y₁', ![y₀, t] ∈ LShape r R) :
    DifferentiableOn ℂ (fun w => bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w])
      {w : ℂ | w.im ∈ uIcc y₁ y₁'} := by
  let z₀ : ℂ := ↑x₀ + I * ↑y₀
  have hz₀_im : z₀.im = y₀ := by simp [z₀]
  let L : ℂ → (Fin 2 → ℂ) := fun w => ![z₀, w]
  have hL_diff : Differentiable ℂ L := diff_affine_slice1 z₀
  have h_maps : MapsTo L {w : ℂ | w.im ∈ uIcc y₁ y₁'} (TubeDomain (LShape r R)) := by
    intro w hw
    simp only [mem_setOf_eq] at hw
    simp only [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => (L w i).im) = ![y₀, w.im] := by
      ext i
      fin_cases i
      · simp [L, hz₀_im]
      · simp [L]
    rw [h_im]
    exact h_path w.im hw
  have hf_comp : DifferentiableOn ℂ (f ∘ L) {w : ℂ | w.im ∈ uIcc y₁ y₁'} :=
    hf_holo.comp hL_diff.differentiableOn h_maps
  have h_f_eps :
      DifferentiableOn ℂ (fun w => bochner_f_eps f ε (L w)) {w : ℂ | w.im ∈ uIcc y₁ y₁'} := by
    unfold bochner_f_eps
    apply DifferentiableOn.mul hf_comp
    have h_exp : Differentiable ℂ (fun w => Complex.exp (-↑ε * ((L w 0) ^ 2 + (L w 1) ^ 2))) := by
      apply Differentiable.comp Complex.differentiable_exp
      apply Differentiable.mul (differentiable_const _)
      apply Differentiable.add
      · exact (differentiable_pi.mp hL_diff 0).pow 2
      · exact (differentiable_pi.mp hL_diff 1).pow 2
    exact h_exp.differentiableOn
  unfold bochner_integrand_F
  apply DifferentiableOn.mul h_f_eps
  have h_fourier :
      Differentiable ℂ (fun w => Complex.exp (-I * (L w 0 * ↑(ξ 0) + L w 1 * ↑(ξ 1)))) := by
    apply Differentiable.comp Complex.differentiable_exp
    apply Differentiable.mul (differentiable_const _)
    apply Differentiable.add
    · exact (differentiable_pi.mp hL_diff 0).mul (differentiable_const _)
    · exact (differentiable_pi.mp hL_diff 1).mul (differentiable_const _)
  exact h_fourier.differentiableOn

lemma bound_on_uIcc (y₁ y₁' : ℝ) (t : ℝ) (ht : t ∈ uIcc y₁ y₁') :
    |t| ≤ max (|y₁|) (|y₁'|) := by
  rw [uIcc, mem_Icc] at ht
  have h1 : min y₁ y₁' ≤ t := ht.1
  have h2 : t ≤ max y₁ y₁' := ht.2
  have h_min_ge : - max (|y₁|) (|y₁'|) ≤ min y₁ y₁' := by
    rcases min_cases y₁ y₁' with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]
      have : -|y₁| ≤ y₁ := neg_abs_le y₁
      have : - max (|y₁|) (|y₁'|) ≤ -|y₁| := neg_le_neg (le_max_left _ _)
      linarith
    · rw [hmin]
      have : -|y₁'| ≤ y₁' := neg_abs_le y₁'
      have : - max (|y₁|) (|y₁'|) ≤ -|y₁'| := neg_le_neg (le_max_right _ _)
      linarith
  have h_max_le : max y₁ y₁' ≤ max (|y₁|) (|y₁'|) := by
    rcases max_cases y₁ y₁' with ⟨hmax, _⟩ | ⟨hmax, _⟩
    · rw [hmax]
      exact le_trans (le_abs_self y₁) (le_max_left _ _)
    · rw [hmax]
      exact le_trans (le_abs_self y₁') (le_max_right _ _)
  rw [abs_le]
  constructor
  · linarith
  · linarith

lemma sq_le_sq_of_bound (y₁ y₁' : ℝ) (t : ℝ) (ht : t ∈ uIcc y₁ y₁') :
    t ^ 2 ≤ (max (|y₁|) (|y₁'|)) ^ 2 := by
  have hb := bound_on_uIcc y₁ y₁' t ht
  have h_nonneg : 0 ≤ max (|y₁|) (|y₁'|) := le_max_of_le_left (abs_nonneg y₁)
  nlinarith [abs_le.mp hb]

lemma mul_le_mul_of_bound (y₁ y₁' ξ₁ : ℝ) (t : ℝ) (ht : t ∈ uIcc y₁ y₁') :
    t * ξ₁ ≤ max (|y₁|) (|y₁'|) * |ξ₁| := by
  have hb := bound_on_uIcc y₁ y₁' t ht
  have h1 : t * ξ₁ ≤ |t * ξ₁| := le_abs_self _
  rw [abs_mul] at h1
  have h2 : |t| * |ξ₁| ≤ max (|y₁|) (|y₁'|) * |ξ₁| := by
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  exact le_trans h1 h2

lemma bochner_slice1_bound_const (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε) (ξ : Fin 2 → ℝ) (x₀ y₀ y₁ y₁' : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₁ y₁' →
      ‖bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  rcases hf_bound with ⟨M, hM⟩
  let K := max (|y₁|) (|y₁'|)
  let C := max M 0 * Real.exp (-ε * x₀ ^ 2) * Real.exp (ε * (y₀ ^ 2 + K ^ 2)) *
    Real.exp (y₀ * ξ 0 + K * |ξ 1|)
  use C
  intro w hw
  have h_rep : ![↑x₀ + I * ↑y₀, w] = fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i) := by
    ext i
    fin_cases i
    · simp
    · simp [mul_comm I ↑w.im, Complex.re_add_im]
  rw [h_rep]
  rw [bochner_integrand_norm_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h_bound_f : ‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ ≤ max M 0 :=
    le_trans (hM _) (le_max_left M 0)
  have h_gauss : Real.exp (-ε * (x₀ ^ 2 + w.re ^ 2)) =
      Real.exp (-ε * x₀ ^ 2) * Real.exp (-ε * w.re ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_gauss]
  have h_sq_le : w.im ^ 2 ≤ K ^ 2 := sq_le_sq_of_bound y₁ y₁' w.im hw
  have h_exp_y : Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) ≤ Real.exp (ε * (y₀ ^ 2 + K ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_mul_le : w.im * ξ 1 ≤ K * |ξ 1| := mul_le_mul_of_bound y₁ y₁' (ξ 1) w.im hw
  have h_exp_xi : Real.exp (y₀ * ξ 0 + w.im * ξ 1) ≤ Real.exp (y₀ * ξ 0 + K * |ξ 1|) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h_rew1 : ‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ *
      (Real.exp (-ε * x₀ ^ 2) * Real.exp (-ε * w.re ^ 2)) *
      Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) * Real.exp (y₀ * ξ 0 + w.im * ξ 1) =
      (‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ *
      Real.exp (-ε * x₀ ^ 2) *
      Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) * Real.exp (y₀ * ξ 0 + w.im * ξ 1)) *
      Real.exp (-ε * w.re ^ 2) := by ring
  rw [h_rew1]
  dsimp [C]
  have h_le_core : ‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ *
      Real.exp (-ε * x₀ ^ 2) *
      Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) * Real.exp (y₀ * ξ 0 + w.im * ξ 1) ≤
      max M 0 * Real.exp (-ε * x₀ ^ 2) * Real.exp (ε * (y₀ ^ 2 + K ^ 2)) *
        Real.exp (y₀ * ξ 0 + K * |ξ 1|) := by
    have h1 : 0 ≤ Real.exp (-ε * x₀ ^ 2) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) := (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (y₀ * ξ 0 + w.im * ξ 1) := (Real.exp_pos _).le
    gcongr
  exact mul_le_mul_of_nonneg_right h_le_core (Real.exp_pos _).le

lemma bochner_slice1_bound (_r _R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (x₀ y₀ y₁ y₁' : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₁ y₁' →
      ‖bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  exact bochner_slice1_bound_const f hf_bound ε hε.le ξ x₀ y₀ y₁ y₁'

lemma bochner_integrand_integrable_of_bound (f : (Fin 2 → ℂ) → ℂ)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (C : ℝ)
    (h_bound : ∀ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ ≤
      C * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)))
    (h_meas : AEStronglyMeasurable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) volume) :
    Integrable (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) := by
  have h_int_gauss : Integrable (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    integrable_gaussian_2d ε hε
  have h_int_g : Integrable (fun x : Fin 2 → ℝ => C * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    h_int_gauss.const_mul C
  exact Integrable.mono' h_int_g h_meas (ae_of_all _ h_bound)

lemma bochner_integrand_bound_2d (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) :
    ∃ C : ℝ, ∀ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ ≤
      C * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by
  rcases hf_bound with ⟨M, hM⟩
  let C := max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)
  use C
  intro x
  rw [bochner_integrand_norm_eq]
  have hM_x : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ ≤ max M 0 := le_trans (hM _) (le_max_left M 0)
  have h_exp_nonneg : 0 ≤ Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := (Real.exp_pos _).le
  have h_exp_y_nonneg :
      0 ≤ Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by positivity
  have h_rew : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) *
    Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) =
    (‖f (fun i => ↑(x i) + I * ↑(y i))‖ *
      (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
      Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_rew]
  dsimp [C]
  have h_c_rew : max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) =
      (max M 0 * (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_c_rew]
  apply mul_le_mul_of_nonneg_right _ h_exp_nonneg
  apply mul_le_mul_of_nonneg_right hM_x h_exp_y_nonneg

lemma bochner_integrand_norm_le_gaussian (f : (Fin 2 → ℂ) → ℂ)
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by
  rw [bochner_integrand_norm_eq]
  have hM_x : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ ≤ max M 0 := le_trans (hM _) (le_max_left M 0)
  have h_exp_nonneg : 0 ≤ Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := (Real.exp_pos _).le
  have h_exp_y_nonneg :
      0 ≤ Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by positivity
  have h_rew : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) *
    Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) =
    (‖f (fun i => ↑(x i) + I * ↑(y i))‖ *
      (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
      Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_rew]
  have h_c_rew : max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) =
      (max M 0 * (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_c_rew]
  apply mul_le_mul_of_nonneg_right _ h_exp_nonneg
  apply mul_le_mul_of_nonneg_right hM_x h_exp_y_nonneg

lemma bochner_integrand_continuous_2d (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ)
    (hf_cont : Continuous (fun x : Fin 2 → ℝ => f (fun i => ↑(x i) + I * ↑(y i)))) :
    Continuous (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) := by
  unfold bochner_integrand_F bochner_f_eps
  apply Continuous.mul
  · apply Continuous.mul hf_cont
    apply Continuous.comp Complex.continuous_exp
    apply Continuous.mul continuous_const
    apply Continuous.add
    · apply Continuous.pow
      exact (Complex.continuous_ofReal.comp (continuous_apply 0)).add continuous_const
    · apply Continuous.pow
      exact (Complex.continuous_ofReal.comp (continuous_apply 1)).add continuous_const
  · apply Continuous.comp Complex.continuous_exp
    apply Continuous.mul continuous_const
    apply Continuous.add
    · apply Continuous.mul
      · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).add continuous_const
      · exact continuous_const
    · apply Continuous.mul
      · exact (Complex.continuous_ofReal.comp (continuous_apply 1)).add continuous_const
      · exact continuous_const

lemma continuous_slice_map (y : Fin 2 → ℝ) :
    Continuous (fun (x : Fin 2 → ℝ) => (fun i : Fin 2 => (x i : ℂ) + I * (y i : ℂ))) := by
  apply continuous_pi
  intro i
  exact (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const

lemma bochner_f_cont_of_holo (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Continuous (fun x : Fin 2 → ℝ => f (fun i => ↑(x i) + I * ↑(y i))) := by
  have h_maps : ∀ x : Fin 2 → ℝ,
      (fun i : Fin 2 => (x i : ℂ) + I * (y i : ℂ)) ∈ TubeDomain (LShape r R) := by
    intro x
    simp only [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => ((x i : ℂ) + I * (y i : ℂ)).im) = y := by
      ext i
      simp
    rw [h_im]
    exact hy
  exact ContinuousOn.comp_continuous hf_holo.continuousOn (continuous_slice_map y) h_maps

lemma bochner_integrand_aestronglyMeasurable_2d (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    AEStronglyMeasurable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) volume := by
  have h_cont := bochner_integrand_continuous_2d f ε ξ y (bochner_f_cont_of_holo r R f hf_holo y hy)
  exact h_cont.aestronglyMeasurable

lemma bochner_integrand_integrable_2d (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Integrable (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) := by
  rcases bochner_integrand_bound_2d f hf_bound ε ξ y with ⟨C, h_bound⟩
  have h_meas := bochner_integrand_aestronglyMeasurable_2d r R f hf_holo ε ξ y hy
  exact bochner_integrand_integrable_of_bound f ε hε ξ y C h_bound h_meas

lemma bochner_integrand_integral_norm_le (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    (∫ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖) ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
        ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  let C0 := max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2))
  have hint_gauss : Integrable (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    integrable_gaussian_2d ε hε
  have h_int_bound : Integrable (fun x : Fin 2 → ℝ =>
      (C0 * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    hint_gauss.const_mul _
  have h_meas := (bochner_integrand_aestronglyMeasurable_2d r R f hf_holo ε ξ y hy).norm
  have h_le := integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) h_int_bound
    (ae_of_all _ (bochner_integrand_norm_le_gaussian f M hM ε ξ y))
  have h_eq : (∫ (x : Fin 2 → ℝ),
        (C0 * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) =
      (C0 * ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [h_eq] at h_le
  exact h_le

lemma bochner_shift_axis1 (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ)
    (y₀ y₁ y₁' : ℝ)
    (h_path : ∀ t ∈ uIcc y₁ y₁', ![y₀, t] ∈ LShape r R) :
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁] =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁'] := by
  have hy1_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀, y₁] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hy1'_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁']) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀, y₁'] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hint1 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) := by
    rw [hy1_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀, y₁]
      (h_path y₁ left_mem_uIcc)
  have hint2 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁']) := by
    rw [hy1'_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀, y₁']
      (h_path y₁' right_mem_uIcc)
  rw [integral_finTwo_eq_integral_prod _ hint1]
  rw [integral_finTwo_eq_integral_prod _ hint2]
  congr 1
  ext x₀
  let g : ℂ → ℂ := fun w => bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w]
  have hg_holo : DifferentiableOn ℂ g {w : ℂ | w.im ∈ uIcc y₁ y₁'} :=
    bochner_slice1_diffOn r R f hf_holo ε ξ x₀ y₀ y₁ y₁' h_path
  have hg_bound : ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₁ y₁' → ‖g w‖ ≤ C * Real.exp (-ε * w.re ^ 2) :=
    bochner_slice1_bound r R f hf_bound ε hε ξ x₀ y₀ y₁ y₁'
  have h_shift := fourier_shift_1d_eps_uIcc y₁ y₁' ε hε g hg_holo hg_bound
  exact h_shift

lemma diff_affine_slice0 (z₁ : ℂ) :
    Differentiable ℂ (fun w : ℂ => (![w, z₁] : Fin 2 → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact differentiable_id
  · exact differentiable_const z₁

lemma bochner_slice0_diffOn (r R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (ξ : Fin 2 → ℝ) (x₁ y₀ y₀' y₁ : ℝ)
    (h_path : ∀ s ∈ uIcc y₀ y₀', ![s, y₁] ∈ LShape r R) :
    DifferentiableOn ℂ (fun w => bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁])
      {w : ℂ | w.im ∈ uIcc y₀ y₀'} := by
  let z₁ : ℂ := ↑x₁ + I * ↑y₁
  have hz₁_im : z₁.im = y₁ := by simp [z₁]
  let L : ℂ → (Fin 2 → ℂ) := fun w => ![w, z₁]
  have hL_diff : Differentiable ℂ L := diff_affine_slice0 z₁
  have h_maps : MapsTo L {w : ℂ | w.im ∈ uIcc y₀ y₀'} (TubeDomain (LShape r R)) := by
    intro w hw
    simp only [mem_setOf_eq] at hw
    simp only [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => (L w i).im) = ![w.im, y₁] := by
      ext i
      fin_cases i
      · simp [L]
      · simp [L, hz₁_im]
    rw [h_im]
    exact h_path w.im hw
  have hf_comp : DifferentiableOn ℂ (f ∘ L) {w : ℂ | w.im ∈ uIcc y₀ y₀'} :=
    hf_holo.comp hL_diff.differentiableOn h_maps
  have h_f_eps : DifferentiableOn ℂ (fun w => bochner_f_eps f ε (L w))
      {w : ℂ | w.im ∈ uIcc y₀ y₀'} := by
    unfold bochner_f_eps
    apply DifferentiableOn.mul hf_comp
    have h_exp : Differentiable ℂ (fun w => Complex.exp (-↑ε * ((L w 0) ^ 2 + (L w 1) ^ 2))) := by
      apply Differentiable.comp Complex.differentiable_exp
      apply Differentiable.mul (differentiable_const _)
      apply Differentiable.add
      · exact (differentiable_pi.mp hL_diff 0).pow 2
      · exact (differentiable_pi.mp hL_diff 1).pow 2
    exact h_exp.differentiableOn
  unfold bochner_integrand_F
  apply DifferentiableOn.mul h_f_eps
  have h_fourier : Differentiable ℂ
      (fun w => Complex.exp (-I * (L w 0 * ↑(ξ 0) + L w 1 * ↑(ξ 1)))) := by
    apply Differentiable.comp Complex.differentiable_exp
    apply Differentiable.mul (differentiable_const _)
    apply Differentiable.add
    · exact (differentiable_pi.mp hL_diff 0).mul (differentiable_const _)
    · exact (differentiable_pi.mp hL_diff 1).mul (differentiable_const _)
  exact h_fourier.differentiableOn

lemma bochner_slice0_bound_const (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε) (ξ : Fin 2 → ℝ) (x₁ y₀ y₀' y₁ : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₀ y₀' →
      ‖bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  rcases hf_bound with ⟨M, hM⟩
  let K := max (|y₀|) (|y₀'|)
  let C := max M 0 * Real.exp (-ε * x₁ ^ 2) * Real.exp (ε * (K ^ 2 + y₁ ^ 2)) *
    Real.exp (K * |ξ 0| + y₁ * ξ 1)
  use C
  intro w hw
  have h_rep : ![w, ↑x₁ + I * ↑y₁] = fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i) := by
    ext i
    fin_cases i
    · simp [mul_comm I ↑w.im, Complex.re_add_im]
    · simp
  rw [h_rep]
  rw [bochner_integrand_norm_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h_bound_f : ‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ ≤ max M 0 :=
    le_trans (hM _) (le_max_left M 0)
  have h_gauss : Real.exp (-ε * (w.re ^ 2 + x₁ ^ 2)) =
      Real.exp (-ε * w.re ^ 2) * Real.exp (-ε * x₁ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_gauss]
  have h_sq_le : w.im ^ 2 ≤ K ^ 2 := sq_le_sq_of_bound y₀ y₀' w.im hw
  have h_exp_y : Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) ≤ Real.exp (ε * (K ^ 2 + y₁ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_mul_le : w.im * ξ 0 ≤ K * |ξ 0| := mul_le_mul_of_bound y₀ y₀' (ξ 0) w.im hw
  have h_exp_xi : Real.exp (w.im * ξ 0 + y₁ * ξ 1) ≤ Real.exp (K * |ξ 0| + y₁ * ξ 1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h_rew1 : ‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ *
      (Real.exp (-ε * w.re ^ 2) * Real.exp (-ε * x₁ ^ 2)) *
      Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) * Real.exp (w.im * ξ 0 + y₁ * ξ 1) =
      (‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ *
      Real.exp (-ε * x₁ ^ 2) *
      Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) * Real.exp (w.im * ξ 0 + y₁ * ξ 1)) *
      Real.exp (-ε * w.re ^ 2) := by ring
  rw [h_rew1]
  dsimp [C]
  have h_le_core : ‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ *
      Real.exp (-ε * x₁ ^ 2) *
      Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) * Real.exp (w.im * ξ 0 + y₁ * ξ 1) ≤
      max M 0 * Real.exp (-ε * x₁ ^ 2) * Real.exp (ε * (K ^ 2 + y₁ ^ 2)) *
        Real.exp (K * |ξ 0| + y₁ * ξ 1) := by
    have h1 : 0 ≤ Real.exp (-ε * x₁ ^ 2) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) := (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (w.im * ξ 0 + y₁ * ξ 1) := (Real.exp_pos _).le
    gcongr
  exact mul_le_mul_of_nonneg_right h_le_core (Real.exp_pos _).le

lemma bochner_slice0_bound (_r _R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (x₁ y₀ y₀' y₁ : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₀ y₀' →
      ‖bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  exact bochner_slice0_bound_const f hf_bound ε hε.le ξ x₁ y₀ y₀' y₁

lemma integral_finTwo_eq_integral_prod_swap (g : (Fin 2 → ℝ) → ℂ) (hg : Integrable g) :
    ∫ (x : Fin 2 → ℝ), g x = ∫ (x₁ : ℝ), ∫ (x₀ : ℝ), g ![x₀, x₁] := by
  rw [integral_finTwo_eq_integral_prod g hg]
  have h_pres := volume_preserving_finTwoArrow ℝ
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  have h_int_iff := h_pres.integrable_comp_emb h_emb (g := fun p : ℝ × ℝ => g ![p.1, p.2])
  have h_comp : (fun p : ℝ × ℝ => g ![p.1, p.2]) ∘ (⇑MeasurableEquiv.finTwoArrow) = g := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [h_comp] at h_int_iff
  have h_int_prod : Integrable (fun p : ℝ × ℝ => g ![p.1, p.2]) volume := h_int_iff.mp hg
  exact integral_integral_swap (f := fun x₀ x₁ => g ![x₀, x₁]) h_int_prod

lemma bochner_shift_axis0 (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ)
    (y₀ y₀' y₁ : ℝ)
    (h_path : ∀ s ∈ uIcc y₀ y₀', ![s, y₁] ∈ LShape r R) :
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁] =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀', ↑(x 1) + I * ↑y₁] := by
  have hy0_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀, y₁] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hy0'_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀', ↑(x 1) + I * ↑y₁]) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀', y₁] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hint1 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) := by
    rw [hy0_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀, y₁]
      (h_path y₀ left_mem_uIcc)
  have hint2 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀', ↑(x 1) + I * ↑y₁]) := by
    rw [hy0'_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀', y₁]
      (h_path y₀' right_mem_uIcc)
  rw [integral_finTwo_eq_integral_prod_swap _ hint1]
  rw [integral_finTwo_eq_integral_prod_swap _ hint2]
  congr 1
  ext x₁
  let g : ℂ → ℂ := fun w => bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁]
  have hg_holo : DifferentiableOn ℂ g {w : ℂ | w.im ∈ uIcc y₀ y₀'} :=
    bochner_slice0_diffOn r R f hf_holo ε ξ x₁ y₀ y₀' y₁ h_path
  have hg_bound : ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₀ y₀' → ‖g w‖ ≤ C * Real.exp (-ε * w.re ^ 2) :=
    bochner_slice0_bound r R f hf_bound ε hε ξ x₁ y₀ y₀' y₁
  have h_shift := fourier_shift_1d_eps_uIcc y₀ y₀' ε hε g hg_holo hg_bound
  exact h_shift

lemma mem_uIcc_of_mem_Ioo {a b x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    {t : ℝ} (ht : t ∈ uIcc x y) : t ∈ Ioo a b := by
  rw [uIcc] at ht
  constructor
  · calc a < min x y := lt_min hx.1 hy.1
    _ ≤ t := ht.1
  · calc t ≤ max x y := ht.2
    _ < b := max_lt hx.2 hy.2

lemma bochner_shift_to_center (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * (r / 2)) := by
  have hr2_pos : 0 < r / 2 := by linarith
  have hr2_lt_r : r / 2 < r := by linarith
  have hr2_lt_R : r / 2 < R := by linarith
  have hr2_mem_r : r / 2 ∈ Ioo 0 r := ⟨hr2_pos, hr2_lt_r⟩
  have hr2_mem_R : r / 2 ∈ Ioo 0 R := ⟨hr2_pos, hr2_lt_R⟩
  have hy_eq : (fun (x : Fin 2 → ℝ) => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) =
      (fun (x : Fin 2 → ℝ) =>
        bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑(y 0), ↑(x 1) + I * ↑(y 1)]) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hcenter_eq :
      (fun (x : Fin 2 → ℝ) => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * (r / 2))) =
      (fun (x : Fin 2 → ℝ) =>
        bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑(r / 2), ↑(x 1) + I * ↑(r / 2)]) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> (dsimp; push_cast; rfl)
  rw [hy_eq, hcenter_eq]
  rcases hy with ⟨hy0_pos, hy0_r, hy1_pos, hy1_R⟩ | ⟨hy0_pos, hy0_R, hy1_pos, hy1_r⟩
  · have hpath1 : ∀ t ∈ uIcc (y 1) (r / 2), ![y 0, t] ∈ LShape r R := by
      intro t ht
      have ht_mem := mem_uIcc_of_mem_Ioo ⟨hy1_pos, hy1_R⟩ hr2_mem_R ht
      unfold LShape
      left
      exact ⟨hy0_pos, hy0_r, ht_mem.1, ht_mem.2⟩
    have h1 := bochner_shift_axis1 r R hr hR f hf_holo hf_bound ε hε ξ (y 0) (y 1) (r / 2) hpath1
    have hpath0 : ∀ s ∈ uIcc (y 0) (r / 2), ![s, r / 2] ∈ LShape r R := by
      intro s hs
      have hs_mem := mem_uIcc_of_mem_Ioo ⟨hy0_pos, hy0_r⟩ hr2_mem_r hs
      unfold LShape
      left
      exact ⟨hs_mem.1, hs_mem.2, hr2_pos, hr2_lt_R⟩
    have h0 := bochner_shift_axis0 r R hr hR f hf_holo hf_bound ε hε ξ (y 0) (r / 2) (r / 2) hpath0
    rw [h1, h0]
  · have hpath0 : ∀ s ∈ uIcc (y 0) (r / 2), ![s, y 1] ∈ LShape r R := by
      intro s hs
      have hs_mem := mem_uIcc_of_mem_Ioo ⟨hy0_pos, hy0_R⟩ hr2_mem_R hs
      unfold LShape
      right
      exact ⟨hs_mem.1, hs_mem.2, hy1_pos, hy1_r⟩
    have h0 := bochner_shift_axis0 r R hr hR f hf_holo hf_bound ε hε ξ (y 0) (r / 2) (y 1) hpath0
    have hpath1 : ∀ t ∈ uIcc (y 1) (r / 2), ![r / 2, t] ∈ LShape r R := by
      intro t ht
      have ht_mem := mem_uIcc_of_mem_Ioo ⟨hy1_pos, hy1_r⟩ hr2_mem_r ht
      unfold LShape
      right
      exact ⟨hr2_pos, hr2_lt_R, ht_mem.1, ht_mem.2⟩
    have h1 := bochner_shift_axis1 r R hr hR f hf_holo hf_bound ε hε ξ (r / 2) (y 1) (r / 2) hpath1
    rw [h0, h1]

lemma bochner_fourier_transform_shift_eps (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y₁ y₂ : Fin 2 → ℝ) (hy₁ : (fun i => ↑(0 : ℝ) + I * ↑(y₁ i)) ∈ TubeDomain (LShape r R))
    (hy₂ : (fun i => ↑(0 : ℝ) + I * ↑(y₂ i)) ∈ TubeDomain (LShape r R)) (ξ : Fin 2 → ℝ) :
    bochner_fourier_transform_eps f ε y₁ ξ * Real.exp (y₁ 0 * ξ 0 + y₁ 1 * ξ 1) =
    bochner_fourier_transform_eps f ε y₂ ξ * Real.exp (y₂ 0 * ξ 0 + y₂ 1 * ξ 1) := by
  have hy₁_LS : y₁ ∈ LShape r R := (mem_TubeDomain_pure_imag (LShape r R) y₁).mp hy₁
  have hy₂_LS : y₂ ∈ LShape r R := (mem_TubeDomain_pure_imag (LShape r R) y₂).mp hy₂
  have H1 := bochner_fourier_mul_exp_eq_integral f ε y₁ ξ
  have H2 := bochner_fourier_mul_exp_eq_integral f ε y₂ ξ
  have h_center1 := bochner_shift_to_center r R hr hR f hf_holo hf_bound ε hε ξ y₁ hy₁_LS
  have h_center2 := bochner_shift_to_center r R hr hR f hf_holo hf_bound ε hε ξ y₂ hy₂_LS
  have h_eq : (bochner_fourier_transform_eps f ε y₁ ξ * ↑(Real.exp (y₁ 0 * ξ 0 + y₁ 1 * ξ 1))) =
      (bochner_fourier_transform_eps f ε y₂ ξ * ↑(Real.exp (y₂ 0 * ξ 0 + y₂ 1 * ξ 1))) := by
    rw [H1, H2, h_center1, h_center2]
  exact h_eq

lemma bochner_c_eps_norm_le (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ)
    (hy : (fun i => ↑(0 : ℝ) + Complex.I * ↑(y i)) ∈ TubeDomain (LShape r R)) (ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ =
      ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ := by
  have hy0 : (fun _ : Fin 2 => r / 2) ∈ LShape r R := by
    unfold LShape
    left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hy0_tube :
      (fun i => ↑(0 : ℝ) + Complex.I * ↑((fun _ : Fin 2 => r / 2) i)) ∈
        TubeDomain (LShape r R) := by
    simp [TubeDomain, hy0]
  have h_shift := bochner_fourier_transform_shift_eps r R hr hR f hf_holo hf_bound ε hε
    (fun _ => r/2) y hy0_tube hy ξ
  rw [h_shift]

lemma bochner_fourier_mul_exp_norm_le_integral_norm
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ ≤
      ∫ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ := by
  have h_int_eq := bochner_fourier_mul_exp_eq_integral f ε y ξ
  have h_norm_eq : ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ =
      ‖∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ :=
    congr_arg norm h_int_eq
  exact h_norm_eq.le.trans (norm_integral_le_integral_norm _)

lemma bochner_fourier_mul_exp_norm_le_gaussian (r R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) (ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
        ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  have h1 := bochner_fourier_mul_exp_norm_le_integral_norm f ε y ξ
  have h2 := bochner_integrand_integral_norm_le r R f hf_holo M hM ε hε ξ y hy
  exact h1.trans h2

lemma bochner_c_eps_pointwise_bound (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) (ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
        ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  have hy_tube : (fun i => ↑(0 : ℝ) + Complex.I * ↑(y i)) ∈ TubeDomain (LShape r R) :=
    (mem_TubeDomain_pure_imag (LShape r R) y).mpr hy
  have h_shift := bochner_c_eps_norm_le r R hr hR f hf_holo ⟨M, hM⟩ ε hε y hy_tube ξ
  exact h_shift.le.trans (bochner_fourier_mul_exp_norm_le_gaussian r R f hf_holo M hM ε hε y hy ξ)

lemma bochner_c_eps_bound_of_y (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Fin 2 → ℝ,
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ ≤
        C * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  rcases hf_bound with ⟨M, hM⟩
  let C := max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
    ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))
  have hC : 0 ≤ C := by
    have hI : 0 ≤ ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    dsimp [C]
    positivity
  refine ⟨C, hC, fun ξ => bochner_c_eps_pointwise_bound r R hr hR f hf_holo M hM ε hε y hy ξ⟩

lemma box_eq_pi (R : ℝ) :
    {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} = Set.pi Set.univ (fun _ : Fin 2 => Set.Ioo 0 R) := by
  ext x
  simp [Set.mem_pi, Set.mem_Ioo]

lemma convex_box (R : ℝ) :
    Convex ℝ {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} := by
  rw [box_eq_pi]
  exact convex_pi (fun _ _ => convex_Ioo 0 R)

lemma LShape_subset_box {r R : ℝ} (hR : r < R) :
    LShape r R ⊆ {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} := by
  intro x hx i
  fin_cases i
  · rcases hx with ⟨h0, h0r, h1, h1R⟩ | ⟨h0, h0R, h1, h1r⟩
    · exact ⟨h0, h0r.trans hR⟩
    · exact ⟨h0, h0R⟩
  · rcases hx with ⟨h0, h0r, h1, h1R⟩ | ⟨h0, h0R, h1, h1r⟩
    · exact ⟨h1, h1R⟩
    · exact ⟨h1, h1r.trans hR⟩

lemma LShapeConvexHull_subset_box {r R : ℝ} (hR : r < R) :
    LShapeConvexHull r R ⊆ {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} :=
  convexHull_min (LShape_subset_box hR) (convex_box R)

lemma mem_LShapeConvexHull_bounds {r R : ℝ} (hR : r < R)
    {y : Fin 2 → ℝ} (hy : y ∈ LShapeConvexHull r R) :
    0 < y 0 ∧ y 0 < R ∧ 0 < y 1 ∧ y 1 < R := by
  have h := LShapeConvexHull_subset_box hR hy
  exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2⟩

lemma LShape_subset_sum_lt {r R : ℝ} :
    LShape r R ⊆ {x : Fin 2 → ℝ | x 0 + x 1 < r + R} := by
  intro x hx
  dsimp
  rcases hx with ⟨h0, h0r, h1, h1R⟩ | ⟨h0, h0R, h1, h1r⟩
  · linarith
  · linarith

lemma convex_halfspace_sum (c : ℝ) :
    Convex ℝ {x : Fin 2 → ℝ | x 0 + x 1 < c} := by
  intro x hx y hy a b ha hb hab
  dsimp at hx hy ⊢
  rcases ha.eq_or_lt with rfl | ha_pos
  · have : b = 1 := by linarith
    subst this
    linarith
  · rcases hb.eq_or_lt with rfl | hb_pos
    · have : a = 1 := by linarith
      subst this
      linarith
    · have h_ax : a * (x 0 + x 1) < a * c := mul_lt_mul_of_pos_left hx ha_pos
      have h_by : b * (y 0 + y 1) < b * c := mul_lt_mul_of_pos_left hy hb_pos
      have h_sum : a * (x 0 + x 1) + b * (y 0 + y 1) < c := by
        calc a * (x 0 + x 1) + b * (y 0 + y 1)
          _ < a * c + b * c := add_lt_add h_ax h_by
          _ = (a + b) * c := by ring
          _ = c := by rw [hab, one_mul]
      have h_eq : a * x 0 + b * y 0 + (a * x 1 + b * y 1) =
          a * (x 0 + x 1) + b * (y 0 + y 1) := by ring
      linarith

lemma mem_LShapeConvexHull_sum_lt {r R : ℝ}
    {y : Fin 2 → ℝ} (hy : y ∈ LShapeConvexHull r R) :
    y 0 + y 1 < r + R := by
  have h := convexHull_min LShape_subset_sum_lt (convex_halfspace_sum (r + R))
  exact h hy

lemma lshape_quadrant1_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      0 ≤ ξ 0 → 0 ≤ ξ 1 → (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (ξ 0 + ξ 1) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  let δ := min (y' 0 / 2) (min (y' 1 / 2) (r / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let y : Fin 2 → ℝ := fun _ => δ
  have hy_LS : y ∈ LShape r R := by
    unfold LShape
    left
    have hδ_lt_r : δ < r := by
      have : δ ≤ r / 2 := by
        dsimp [δ]
        exact min_le_of_right_le (min_le_right _ _)
      linarith
    have hδ_lt_R : δ < R := hδ_lt_r.trans hR
    exact ⟨hδ_pos, hδ_lt_r, hδ_pos, hδ_lt_R⟩
  refine ⟨y, hy_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  have hy0_le : y 0 - y' 0 ≤ -δ := by
    dsimp [y, δ]
    have : min (y' 0 / 2) (min (y' 1 / 2) (r / 2)) ≤ y' 0 / 2 := min_le_left _ _
    linarith
  have hy1_le : y 1 - y' 1 ≤ -δ := by
    dsimp [y, δ]
    have : min (y' 0 / 2) (min (y' 1 / 2) (r / 2)) ≤ y' 1 / 2 :=
      min_le_of_right_le (min_le_left _ _)
    linarith
  calc (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1
    _ ≤ (-δ) * ξ 0 + (-δ) * ξ 1 := by
      gcongr
    _ = -δ * (ξ 0 + ξ 1) := by ring

lemma lshape_quadrant2_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      ξ 0 ≤ 0 → 0 ≤ ξ 1 → (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (-ξ 0 + ξ 1) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  let δ := min ((R - y' 0) / 4) (min (y' 1 / 2) (r / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have : 0 < R - y' 0 := by linarith
    positivity
  let y : Fin 2 → ℝ := ![y' 0 + 2 * δ, δ]
  have hy0_val : y 0 = y' 0 + 2 * δ := rfl
  have hy1_val : y 1 = δ := rfl
  have hy_LS : y ∈ LShape r R := by
    unfold LShape
    right
    have hδ_le1 : δ ≤ (R - y' 0) / 4 := min_le_left _ _
    have hδ_le2 : δ ≤ r / 2 := min_le_of_right_le (min_le_right _ _)
    have hy0_lt : y 0 < R := by
      rw [hy0_val]
      linarith
    have hy0_gt : 0 < y 0 := by
      rw [hy0_val]
      linarith
    have hy1_lt : y 1 < r := by
      rw [hy1_val]
      linarith
    exact ⟨hy0_gt, hy0_lt, hy1_val.symm ▸ hδ_pos, hy1_lt⟩
  refine ⟨y, hy_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  have hy0_ge : δ ≤ y 0 - y' 0 := by
    rw [hy0_val]
    linarith
  have hy1_le : y 1 - y' 1 ≤ -δ := by
    rw [hy1_val]
    have : δ ≤ y' 1 / 2 := min_le_of_right_le (min_le_left _ _)
    linarith
  have h_term0 : (y 0 - y' 0) * ξ 0 ≤ δ * ξ 0 := by
    nlinarith
  have h_term1 : (y 1 - y' 1) * ξ 1 ≤ (-δ) * ξ 1 := by
    nlinarith
  calc (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1
    _ ≤ δ * ξ 0 + (-δ) * ξ 1 := add_le_add h_term0 h_term1
    _ = -δ * (-ξ 0 + ξ 1) := by ring

lemma lshape_quadrant4_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      0 ≤ ξ 0 → ξ 1 ≤ 0 → (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (ξ 0 - ξ 1) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  let δ := min (y' 0 / 2) (min ((R - y' 1) / 4) (r / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have : 0 < R - y' 1 := by linarith
    positivity
  let y : Fin 2 → ℝ := ![δ, y' 1 + 2 * δ]
  have hy0_val : y 0 = δ := rfl
  have hy1_val : y 1 = y' 1 + 2 * δ := rfl
  have hy_LS : y ∈ LShape r R := by
    unfold LShape
    left
    have hδ_le1 : δ ≤ r / 2 := min_le_of_right_le (min_le_right _ _)
    have hδ_le2 : δ ≤ (R - y' 1) / 4 := min_le_of_right_le (min_le_left _ _)
    have hy0_lt : y 0 < r := by
      rw [hy0_val]
      linarith
    have hy1_gt : 0 < y 1 := by
      rw [hy1_val]
      linarith
    have hy1_lt : y 1 < R := by
      rw [hy1_val]
      linarith
    exact ⟨hy0_val.symm ▸ hδ_pos, hy0_lt, hy1_gt, hy1_lt⟩
  refine ⟨y, hy_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  have hy0_le : y 0 - y' 0 ≤ -δ := by
    rw [hy0_val]
    have : δ ≤ y' 0 / 2 := min_le_left _ _
    linarith
  have hy1_ge : δ ≤ y 1 - y' 1 := by
    rw [hy1_val]
    linarith
  have h_term0 : (y 0 - y' 0) * ξ 0 ≤ (-δ) * ξ 0 := by
    nlinarith
  have h_term1 : (y 1 - y' 1) * ξ 1 ≤ δ * ξ 1 := by
    nlinarith
  calc (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1
    _ ≤ (-δ) * ξ 0 + δ * ξ 1 := add_le_add h_term0 h_term1
    _ = -δ * (ξ 0 - ξ 1) := by ring

lemma lshape_quadrant3_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y₁ ∈ LShape r R, ∃ y₂ ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      ξ 0 ≤ 0 → ξ 1 ≤ 0 →
        ((y₁ 0 - y' 0) * ξ 0 + (y₁ 1 - y' 1) * ξ 1 ≤ -δ * (-ξ 0 - ξ 1) ∨
         (y₂ 0 - y' 0) * ξ 0 + (y₂ 1 - y' 1) * ξ 1 ≤ -δ * (-ξ 0 - ξ 1)) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  have h_sum := mem_LShapeConvexHull_sum_lt hy'
  let rem := r + R - (y' 0 + y' 1)
  have h_rem_pos : 0 < rem := by linarith
  have h_rem_eq : y' 0 + y' 1 = r + R - rem := by dsimp [rem]; ring
  let ε := min (rem / 8) (min ((R - y' 0) / 4) (min ((R - y' 1) / 4) (r / 6)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have : 0 < R - y' 0 := by linarith
    have : 0 < R - y' 1 := by linarith
    positivity
  have hε_rem : 4 * ε ≤ rem := by
    have : ε ≤ rem / 8 := min_le_left _ _
    linarith
  have hε_R0 : 2 * ε ≤ R - y' 0 := by
    have : ε ≤ (R - y' 0) / 4 := min_le_of_right_le (min_le_left _ _)
    linarith
  have hε_R1 : 2 * ε ≤ R - y' 1 := by
    have : ε ≤ (R - y' 1) / 4 := min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
    linarith
  have hε_r : 3 * ε ≤ r := by
    have : ε ≤ r / 6 := min_le_of_right_le (min_le_of_right_le (min_le_right _ _))
    linarith
  let y₁ : Fin 2 → ℝ := ![r - 2 * ε, R - ε]
  let y₂ : Fin 2 → ℝ := ![R - ε, r - 2 * ε]
  have hy1_LS : y₁ ∈ LShape r R := by
    unfold LShape
    left
    dsimp [y₁]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hy2_LS : y₂ ∈ LShape r R := by
    unfold LShape
    right
    dsimp [y₂]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  let δ := ε / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  refine ⟨y₁, hy1_LS, y₂, hy2_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  let u0 := -ξ 0
  let u1 := -ξ 1
  have hu0 : 0 ≤ u0 := by dsimp [u0]; linarith
  have hu1 : 0 ≤ u1 := by dsimp [u1]; linarith
  by_cases h_order : u0 ≤ u1
  · left
    have h_diff1 : ε ≤ y₁ 1 - y' 1 := by
      change ε ≤ R - ε - y' 1
      linarith
    have h_sum1 : ε ≤ (y₁ 0 - y' 0) + (y₁ 1 - y' 1) := by
      change ε ≤ (r - 2 * ε - y' 0) + (R - ε - y' 1)
      linarith
    have h_ineq : δ * (u0 + u1) ≤ (y₁ 0 - y' 0) * u0 + (y₁ 1 - y' 1) * u1 := by
      calc δ * (u0 + u1)
        _ ≤ δ * (2 * u1) := by
          dsimp [δ]
          nlinarith
        _ = ε * u1 := by dsimp [δ]; ring
        _ = ((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) * u0 + (y₁ 1 - y' 1) * (u1 - u0) -
            (((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) - ε) * u0 - ((y₁ 1 - y' 1) - ε) * (u1 - u0) := by ring
        _ ≤ ((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) * u0 + (y₁ 1 - y' 1) * (u1 - u0) := by
          have : 0 ≤ (((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) - ε) * u0 := by nlinarith
          have : 0 ≤ ((y₁ 1 - y' 1) - ε) * (u1 - u0) := by nlinarith
          linarith
        _ = (y₁ 0 - y' 0) * u0 + (y₁ 1 - y' 1) * u1 := by ring
    dsimp [u0, u1] at h_ineq
    linarith
  · right
    have hu_le : u1 ≤ u0 := le_of_not_ge h_order
    have h_diff0 : ε ≤ y₂ 0 - y' 0 := by
      change ε ≤ R - ε - y' 0
      linarith
    have h_sum2 : ε ≤ (y₂ 0 - y' 0) + (y₂ 1 - y' 1) := by
      change ε ≤ (R - ε - y' 0) + (r - 2 * ε - y' 1)
      linarith
    have h_ineq : δ * (u0 + u1) ≤ (y₂ 0 - y' 0) * u0 + (y₂ 1 - y' 1) * u1 := by
      calc δ * (u0 + u1)
        _ ≤ δ * (2 * u0) := by
          dsimp [δ]
          nlinarith
        _ = ε * u0 := by dsimp [δ]; ring
        _ = ((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) * u1 + (y₂ 0 - y' 0) * (u0 - u1) -
            (((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) - ε) * u1 - ((y₂ 0 - y' 0) - ε) * (u0 - u1) := by ring
        _ ≤ ((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) * u1 + (y₂ 0 - y' 0) * (u0 - u1) := by
          have : 0 ≤ (((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) - ε) * u1 := by nlinarith
          have : 0 ≤ ((y₂ 0 - y' 0) - ε) * (u0 - u1) := by nlinarith
          linarith
        _ = (y₂ 0 - y' 0) * u0 + (y₂ 1 - y' 1) * u1 := by ring
    dsimp [u0, u1] at h_ineq
    linarith

lemma bochner_c_eps_local_exp_decay (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y' : Fin 2 → ℝ) (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ξ : Fin 2 → ℝ,
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ *
        Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) ≤
      C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
  rcases lshape_quadrant1_point hr hR hy' with ⟨y1, hy1, δ1, hδ1_pos, hq1⟩
  rcases lshape_quadrant2_point hr hR hy' with ⟨y2, hy2, δ2, hδ2_pos, hq2⟩
  rcases lshape_quadrant4_point hr hR hy' with ⟨y4, hy4, δ4, hδ4_pos, hq4⟩
  rcases lshape_quadrant3_point hr hR hy' with ⟨y3a, hy3a, y3b, hy3b, δ3, hδ3_pos, hq3⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y1 hy1 with
    ⟨C1, hC1_nonneg, h_bd1⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y2 hy2 with
    ⟨C2, hC2_nonneg, h_bd2⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y4 hy4 with
    ⟨C4, hC4_nonneg, h_bd4⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y3a hy3a with
    ⟨C3a, hC3a_nonneg, h_bd3a⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y3b hy3b with
    ⟨C3b, hC3b_nonneg, h_bd3b⟩
  let C := max C1 (max C2 (max C4 (max C3a C3b)))
  have hC_nonneg : 0 ≤ C := le_trans hC1_nonneg (le_max_left _ _)
  let δ := min δ1 (min δ2 (min δ4 δ3))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hC_ge1 : C1 ≤ C := le_max_left _ _
  have hC_ge2 : C2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_ge4 : C4 ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC_ge3a : C3a ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hC_ge3b : C3b ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨C, δ, hC_nonneg, hδ_pos, ?_⟩
  intro ξ
  let c_norm :=
    ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖
  have h_combine (y : Fin 2 → ℝ) (Cy : ℝ) (hCy : Cy ≤ C)
      (h_bdy : c_norm ≤ Cy * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))
      (h_geom : (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|)) :
      c_norm * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
    calc c_norm * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))
      _ ≤ (Cy * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) := by
        nlinarith [Real.exp_pos (-(y' 0 * ξ 0 + y' 1 * ξ 1))]
      _ = Cy * (Real.exp (y 0 * ξ 0 + y 1 * ξ 1) * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))) := by ring
      _ = Cy * Real.exp ((y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
        have h_exp : Real.exp ((y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1) ≤
            Real.exp (-δ * (|ξ 0| + |ξ 1|)) :=
          Real.exp_le_exp.mpr h_geom
        exact mul_le_mul hCy h_exp (Real.exp_pos _).le hC_nonneg
  by_cases h0 : 0 ≤ ξ 0
  · by_cases h1 : 0 ≤ ξ 1
    · have habs0 : |ξ 0| = ξ 0 := abs_of_nonneg h0
      have habs1 : |ξ 1| = ξ 1 := abs_of_nonneg h1
      have hg : (y1 0 - y' 0) * ξ 0 + (y1 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
        rw [habs0, habs1]
        have hq := hq1 ξ h0 h1
        have : -δ1 * (ξ 0 + ξ 1) ≤ -δ * (ξ 0 + ξ 1) := by
          have : δ ≤ δ1 := min_le_left _ _
          nlinarith
        linarith
      exact h_combine y1 C1 hC_ge1 (h_bd1 ξ) hg
    · have h1' : ξ 1 ≤ 0 := le_of_not_ge h1
      have habs0 : |ξ 0| = ξ 0 := abs_of_nonneg h0
      have habs1 : |ξ 1| = -ξ 1 := abs_of_nonpos h1'
      have hg : (y4 0 - y' 0) * ξ 0 + (y4 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
        have h_sum : |ξ 0| + |ξ 1| = ξ 0 - ξ 1 := by linarith
        rw [h_sum]
        have hq := hq4 ξ h0 h1'
        have : -δ4 * (ξ 0 - ξ 1) ≤ -δ * (ξ 0 - ξ 1) := by
          have : δ ≤ δ4 :=
            le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
          nlinarith
        linarith
      exact h_combine y4 C4 hC_ge4 (h_bd4 ξ) hg
  · have h0' : ξ 0 ≤ 0 := le_of_not_ge h0
    by_cases h1 : 0 ≤ ξ 1
    · have habs0 : |ξ 0| = -ξ 0 := abs_of_nonpos h0'
      have habs1 : |ξ 1| = ξ 1 := abs_of_nonneg h1
      have hg : (y2 0 - y' 0) * ξ 0 + (y2 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
        have h_sum : |ξ 0| + |ξ 1| = -ξ 0 + ξ 1 := by linarith
        rw [h_sum]
        have hq := hq2 ξ h0' h1
        have : -δ2 * (-ξ 0 + ξ 1) ≤ -δ * (-ξ 0 + ξ 1) := by
          have : δ ≤ δ2 := le_trans (min_le_right _ _) (min_le_left _ _)
          nlinarith
        linarith
      exact h_combine y2 C2 hC_ge2 (h_bd2 ξ) hg
    · have h1' : ξ 1 ≤ 0 := le_of_not_ge h1
      have habs0 : |ξ 0| = -ξ 0 := abs_of_nonpos h0'
      have habs1 : |ξ 1| = -ξ 1 := abs_of_nonpos h1'
      have h_sum : |ξ 0| + |ξ 1| = -ξ 0 - ξ 1 := by linarith
      rcases hq3 ξ h0' h1' with hq3a | hq3b
      · have hg : (y3a 0 - y' 0) * ξ 0 + (y3a 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
          rw [h_sum]
          have : -δ3 * (-ξ 0 - ξ 1) ≤ -δ * (-ξ 0 - ξ 1) := by
            have : δ ≤ δ3 :=
              le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
            nlinarith
          linarith
        exact h_combine y3a C3a hC_ge3a (h_bd3a ξ) hg
      · have hg : (y3b 0 - y' 0) * ξ 0 + (y3b 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
          rw [h_sum]
          have : -δ3 * (-ξ 0 - ξ 1) ≤ -δ * (-ξ 0 - ξ 1) := by
            have : δ ≤ δ3 :=
              le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
            nlinarith
          linarith
        exact h_combine y3b C3b hC_ge3b (h_bd3b ξ) hg

lemma exp_im_diff_le {z w : Fin 2 → ℂ} {η : ℝ} (hw : w ∈ Metric.closedBall z η) (ξ : Fin 2 → ℝ) :
    -(w 0).im * ξ 0 - (w 1).im * ξ 1 ≤
      -(z 0).im * ξ 0 - (z 1).im * ξ 1 + η * (|ξ 0| + |ξ 1|) := by
  have hw_dist : ‖w - z‖ ≤ η := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hw
  have h_im0 : |(w 0).im - (z 0).im| ≤ η := by
    calc |(w 0).im - (z 0).im|
      _ = |(w 0 - z 0).im| := by rw [sub_im]
      _ ≤ ‖w 0 - z 0‖ := abs_im_le_norm _
      _ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) 0
      _ ≤ η := hw_dist
  have h_im1 : |(w 1).im - (z 1).im| ≤ η := by
    calc |(w 1).im - (z 1).im|
      _ = |(w 1 - z 1).im| := by rw [sub_im]
      _ ≤ ‖w 1 - z 1‖ := abs_im_le_norm _
      _ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) 1
      _ ≤ η := hw_dist
  have h_term0 : (-(w 0).im + (z 0).im) * ξ 0 ≤ η * |ξ 0| := by
    have : -(w 0).im + (z 0).im = -((w 0).im - (z 0).im) := by ring
    rw [this]
    calc -((w 0).im - (z 0).im) * ξ 0
      _ ≤ |-((w 0).im - (z 0).im) * ξ 0| := le_abs_self _
      _ = |(w 0).im - (z 0).im| * |ξ 0| := by rw [abs_mul, abs_neg]
      _ ≤ η * |ξ 0| := mul_le_mul_of_nonneg_right h_im0 (abs_nonneg _)
  have h_term1 : (-(w 1).im + (z 1).im) * ξ 1 ≤ η * |ξ 1| := by
    have : -(w 1).im + (z 1).im = -((w 1).im - (z 1).im) := by ring
    rw [this]
    calc -((w 1).im - (z 1).im) * ξ 1
      _ ≤ |-((w 1).im - (z 1).im) * ξ 1| := le_abs_self _
      _ = |(w 1).im - (z 1).im| * |ξ 1| := by rw [abs_mul, abs_neg]
      _ ≤ η * |ξ 1| := mul_le_mul_of_nonneg_right h_im1 (abs_nonneg _)
  calc -(w 0).im * ξ 0 - (w 1).im * ξ 1
    _ = -(z 0).im * ξ 0 - (z 1).im * ξ 1 +
        ((-(w 0).im + (z 0).im) * ξ 0 + (-(w 1).im + (z 1).im) * ξ 1) := by ring
    _ ≤ -(z 0).im * ξ 0 - (z 1).im * ξ 1 + (η * |ξ 0| + η * |ξ 1|) := by linarith
    _ = -(z 0).im * ξ 0 - (z 1).im * ξ 1 + η * (|ξ 0| + |ξ 1|) := by ring

lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) volume := by
  have h_Ioi : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Ioi 0) := by
    refine h_Ioi.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have : |x| = x := abs_of_pos (mem_Ioi.mp hx)
    rw [this]
  have h_Iic : IntegrableOn (fun x : ℝ => Real.exp (c * x)) (Iic 0) :=
    integrableOn_exp_mul_Iic hc 0
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Iic 0) := by
    refine h_Iic.congr_fun (fun x hx => ?_) measurableSet_Iic
    have : |x| = -x := abs_of_nonpos (mem_Iic.mp hx)
    rw [this, show -c * -x = c * x by ring]
  have h_union : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Iic 0 ∪ Ioi 0) :=
    h2.union h1
  have h_univ : (Iic (0 : ℝ) ∪ Ioi (0 : ℝ)) = univ := Iic_union_Ioi
  rw [h_univ, integrableOn_univ] at h_union
  exact h_union

lemma integrable_exp_neg_abs_2d (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|))) := by
  have h_eq : (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|))) =
      (fun p : ℝ × ℝ => Real.exp (-c * |p.1|) * Real.exp (-c * |p.2|)) ∘
      (⇑MeasurableEquiv.finTwoArrow) := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_eq]
  have h_pres := volume_preserving_finTwoArrow ℝ
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  rw [h_pres.integrable_comp_emb h_emb]
  have h1 : Integrable (fun x : ℝ => Real.exp (-c * |x|)) volume := integrable_exp_neg_abs hc
  have h_prod :
      Integrable (fun p : ℝ × ℝ => Real.exp (-c * |p.1|) * Real.exp (-c * |p.2|)) volume :=
    Integrable.mul_prod h1 h1
  exact h_prod

lemma poly_le_exp_half (c : ℝ) (hc : 0 < c) (x : ℝ) :
    |x| + 1 ≤ (2 / c + 1) * Real.exp (c / 2 * |x|) := by
  have h_exp : c / 2 * |x| ≤ Real.exp (c / 2 * |x|) := by
    have : 0 ≤ c / 2 * |x| := by positivity
    linarith [Real.add_one_le_exp (c / 2 * |x|)]
  have h_pos : 0 < c / 2 := by linarith
  have h_one : 1 ≤ Real.exp (c / 2 * |x|) := by
    have : 0 ≤ c / 2 * |x| := by positivity
    exact Real.one_le_exp this
  have h_div : |x| ≤ (2 / c) * Real.exp (c / 2 * |x|) := by
    have h_cancel : (c / 2) * ((2 / c) * Real.exp (c / 2 * |x|)) = Real.exp (c / 2 * |x|) := by
      have : (c / 2) * (2 / c) = 1 := by field_simp
      calc (c / 2) * ((2 / c) * Real.exp (c / 2 * |x|))
        _ = ((c / 2) * (2 / c)) * Real.exp (c / 2 * |x|) := by ring
        _ = 1 * Real.exp (c / 2 * |x|) := by rw [this]
        _ = Real.exp (c / 2 * |x|) := by ring
    have : (c / 2) * |x| ≤ (c / 2) * ((2 / c) * Real.exp (c / 2 * |x|)) := by
      rw [h_cancel]
      exact h_exp
    exact le_of_mul_le_mul_left this h_pos
  have : (2 / c + 1) * Real.exp (c / 2 * |x|) =
      (2 / c) * Real.exp (c / 2 * |x|) + Real.exp (c / 2 * |x|) := by ring
  rw [this]
  linarith

lemma exp_poly_2d_le (c : ℝ) (hc : 0 < c) (ξ : Fin 2 → ℝ) :
    Real.exp (-c * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) ≤
      (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|ξ 0| + |ξ 1|)) := by
  have h0 := poly_le_exp_half c hc (ξ 0)
  have h1 := poly_le_exp_half c hc (ξ 1)
  have h_poly : |ξ 0| + |ξ 1| + 1 ≤ (|ξ 0| + 1) * (|ξ 1| + 1) := by
    nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1)]
  have h_prod : (|ξ 0| + 1) * (|ξ 1| + 1) ≤
      ((2 / c + 1) * Real.exp (c / 2 * |ξ 0|)) * ((2 / c + 1) * Real.exp (c / 2 * |ξ 1|)) := by
    have : 0 ≤ |ξ 0| + 1 := by positivity
    have : 0 ≤ |ξ 1| + 1 := by positivity
    gcongr
  have h_comb : |ξ 0| + |ξ 1| + 1 ≤ (2 / c + 1) ^ 2 * Real.exp (c / 2 * (|ξ 0| + |ξ 1|)) := by
    calc |ξ 0| + |ξ 1| + 1
      _ ≤ ((2 / c + 1) * Real.exp (c / 2 * |ξ 0|)) * ((2 / c + 1) * Real.exp (c / 2 * |ξ 1|)) :=
        h_poly.trans h_prod
      _ = (2 / c + 1) ^ 2 * (Real.exp (c / 2 * |ξ 0|) * Real.exp (c / 2 * |ξ 1|)) := by ring
      _ = (2 / c + 1) ^ 2 * Real.exp (c / 2 * |ξ 0| + c / 2 * |ξ 1|) := by rw [← Real.exp_add]
      _ = (2 / c + 1) ^ 2 * Real.exp (c / 2 * (|ξ 0| + |ξ 1|)) := by ring_nf
  calc Real.exp (-c * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)
    _ ≤ Real.exp (-c * (|ξ 0| + |ξ 1|)) *
        ((2 / c + 1) ^ 2 * Real.exp (c / 2 * (|ξ 0| + |ξ 1|))) := by
      gcongr
    _ = (2 / c + 1) ^ 2 *
        (Real.exp (-c * (|ξ 0| + |ξ 1|)) * Real.exp (c / 2 * (|ξ 0| + |ξ 1|))) := by ring
    _ = (2 / c + 1) ^ 2 *
        Real.exp (-c * (|ξ 0| + |ξ 1|) + c / 2 * (|ξ 0| + |ξ 1|)) := by rw [← Real.exp_add]
    _ = (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|ξ 0| + |ξ 1|)) := by ring_nf

lemma integrable_exp_neg_abs_poly_2d (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)) := by
  have h_bound : Integrable
      (fun x : Fin 2 → ℝ => (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|x 0| + |x 1|))) :=
    (integrable_exp_neg_abs_2d (c / 2) (by linarith)).const_mul _
  have h_cont :
      Continuous (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)) := by
    apply Continuous.mul
    · apply Real.continuous_exp.comp
      apply continuous_const.mul
      apply Continuous.add
      · exact (continuous_apply 0).abs
      · exact (continuous_apply 1).abs
    · apply Continuous.add
      · apply Continuous.add
        · exact (continuous_apply 0).abs
        · exact (continuous_apply 1).abs
      · exact continuous_const
  have h_meas : AEStronglyMeasurable
      (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)) volume :=
    h_cont.aestronglyMeasurable
  have h_le : ∀ᵐ x : Fin 2 → ℝ,
      ‖Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)‖ ≤
        (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|x 0| + |x 1|)) := by
    apply ae_of_all
    intro x
    have h_nonneg : 0 ≤ Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1) := by positivity
    rw [Real.norm_of_nonneg h_nonneg]
    exact exp_poly_2d_le c hc x
  exact Integrable.mono' h_bound h_meas h_le

lemma fourier_inversion_integrand_cancel (x y ξ : Fin 2 → ℝ) :
    (↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) : ℂ) *
      Complex.exp (I * ((↑(x 0) + I * ↑(y 0)) * ↑(ξ 0) + (↑(x 1) + I * ↑(y 1)) * ↑(ξ 1))) =
    Complex.exp (I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1))) := by
  have h_exp_real : (↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) : ℂ) =
      Complex.exp (↑(y 0 * ξ 0 + y 1 * ξ 1)) :=
    ofReal_exp (y 0 * ξ 0 + y 1 * ξ 1)
  rw [h_exp_real, ← Complex.exp_add]
  congr 1
  push_cast
  have h_I2 : I ^ 2 = -1 := I_sq
  linear_combination (↑(y 0) * ↑(ξ 0) + ↑(y 1) * ↑(ξ 1)) * h_I2

noncomputable def bochner_F_eps (f : (Fin 2 → ℂ) → ℂ) (ε r _R : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
    (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
    Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))

lemma bochner_fourier_integrand_differentiable (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) :
    Differentiable ℂ
      (fun z : Fin 2 → ℂ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) := by
  apply Differentiable.mul (differentiable_const _)
  apply Differentiable.comp Complex.differentiable_exp
  apply Differentiable.mul (differentiable_const _)
  apply Differentiable.add
  · exact (differentiable_apply 0).mul (differentiable_const _)
  · exact (differentiable_apply 1).mul (differentiable_const _)

lemma fourier_integrand_deriv0 (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasDerivAt (fun w : ℂ => c ξ * Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))))
      (c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) (z 0) := by
  have h1 : HasDerivAt (fun w : ℂ => I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))) (I * ↑(ξ 0)) (z 0) := by
    have h_inner : HasDerivAt (fun w : ℂ => w * ↑(ξ 0) + z 1 * ↑(ξ 1)) (1 * ↑(ξ 0) + 0) (z 0) := by
      apply HasDerivAt.add
      · exact (hasDerivAt_id (z 0)).mul_const (ξ 0 : ℂ)
      · exact hasDerivAt_const (z 0) (z 1 * (ξ 1 : ℂ))
    have h_inner2 : HasDerivAt (fun w : ℂ => w * ↑(ξ 0) + z 1 * ↑(ξ 1)) (ξ 0 : ℂ) (z 0) := by
      simpa using h_inner
    have h_mul := h_inner2.const_mul I
    simpa [mul_comm] using h_mul
  have h_exp := h1.cexp
  exact h_exp.const_mul (c ξ)

lemma fourier_integrand_deriv1 (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasDerivAt (fun w : ℂ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))))
      (c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 1)))) (z 1) := by
  have h1 : HasDerivAt (fun w : ℂ => I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))) (I * ↑(ξ 1)) (z 1) := by
    have h_inner : HasDerivAt (fun w : ℂ => z 0 * ↑(ξ 0) + w * ↑(ξ 1)) (0 + 1 * ↑(ξ 1)) (z 1) := by
      apply HasDerivAt.add
      · exact hasDerivAt_const (z 1) (z 0 * (ξ 0 : ℂ))
      · exact (hasDerivAt_id (z 1)).mul_const (ξ 1 : ℂ)
    have h_inner2 : HasDerivAt (fun w : ℂ => z 0 * ↑(ξ 0) + w * ↑(ξ 1)) (ξ 1 : ℂ) (z 1) := by
      simpa using h_inner
    have h_mul := h_inner2.const_mul I
    simpa [mul_comm] using h_mul
  have h_exp := h1.cexp
  exact h_exp.const_mul (c ξ)

lemma bochner_fourier_integral_deriv0_of_bound (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ)
    (bound : (Fin 2 → ℝ) → ℝ) (s : Set ℂ) (hs : s ∈ 𝓝 (z 0))
    (hF_meas : ∀ᶠ (w : ℂ) in 𝓝 (z 0),
      AEStronglyMeasurable (fun ξ => c ξ * Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume)
    (hF_int : Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume)
    (hF'_meas : AEStronglyMeasurable
      (fun ξ => c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) volume)
    (h_bound : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      ‖c ξ * (Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))‖ ≤ bound ξ)
    (bound_int : Integrable bound volume) :
    HasDerivAt (fun w : ℂ => ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))))
      (∫ (ξ : Fin 2 → ℝ),
        c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) (z 0) := by
  have h_diff : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      HasDerivAt (fun w' => c ξ * Complex.exp (I * (w' * ↑(ξ 0) + z 1 * ↑(ξ 1))))
        (c ξ * (Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) w := by
    apply ae_of_all
    intro ξ w _hw
    exact fourier_integrand_deriv0 c ξ ![w, z 1]
  have h_res := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound bound_int h_diff
  exact h_res.2

lemma bochner_fourier_integral_deriv1_of_bound (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ)
    (bound : (Fin 2 → ℝ) → ℝ) (s : Set ℂ) (hs : s ∈ 𝓝 (z 1))
    (hF_meas : ∀ᶠ (w : ℂ) in 𝓝 (z 1),
      AEStronglyMeasurable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1)))) volume)
    (hF_int : Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume)
    (hF'_meas : AEStronglyMeasurable
      (fun ξ => c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 1)))) volume)
    (h_bound : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      ‖c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))) * (I * ↑(ξ 1)))‖ ≤ bound ξ)
    (bound_int : Integrable bound volume) :
    HasDerivAt (fun w : ℂ => ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))))
      (∫ (ξ : Fin 2 → ℝ),
        c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 1)))) (z 1) := by
  have h_diff : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      HasDerivAt (fun w' => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w' * ↑(ξ 1))))
        (c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))) * (I * ↑(ξ 1)))) w := by
    apply ae_of_all
    intro ξ w _hw
    exact fourier_integrand_deriv1 c ξ ![z 0, w]
  have h_res := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound bound_int h_diff
  exact h_res.2

lemma bochner_fourier_integral_holo_of_bound (c : (Fin 2 → ℝ) → ℂ) (U : Set (Fin 2 → ℂ))
    (h_dom : ∀ z ∈ U, ∃ (bound : (Fin 2 → ℝ) → ℝ), Integrable bound volume ∧ ∃ s ∈ 𝓝 z,
      (∀ᶠ w in 𝓝 z, AEStronglyMeasurable
        (fun ξ => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) volume) ∧
      Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
      AEStronglyMeasurable
        (fun ξ => fderiv ℂ
          (fun w => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) volume ∧
      (∀ᵐ ξ, ∀ w ∈ s,
        ‖fderiv ℂ
          (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w‖ ≤ bound ξ)) :
    DifferentiableOn ℂ
      (fun z : Fin 2 → ℂ =>
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) U := by
  have h_diff_integrand : ∀ (ξ : Fin 2 → ℝ) (w : Fin 2 → ℂ),
      HasFDerivAt (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1))))
        (fderiv ℂ (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w) w :=
    fun ξ w => (bochner_fourier_integrand_differentiable c ξ w).hasFDerivAt
  intro z hz
  rcases h_dom z hz with ⟨bound, bound_int, s, hs, hF_meas, hF_int, hF'_meas, h_le⟩
  have h_diff_s : ∀ᵐ ξ, ∀ w ∈ s,
      HasFDerivAt (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1))))
        (fderiv ℂ (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w) w :=
    ae_of_all _ (fun ξ w _hw => h_diff_integrand ξ w)
  have h_res := hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas hF_int hF'_meas
    h_le bound_int h_diff_s
  exact h_res.differentiableAt.differentiableWithinAt

lemma continuous_exp_fourier_kernel (x : Fin 2 → ℝ) :
    Continuous (fun (ξ : Fin 2 → ℝ) => Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Continuous.add
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1))

lemma continuous_exp_fourier_kernel_x (ξ : Fin 2 → ℝ) :
    Continuous (fun (x : Fin 2 → ℝ) => Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Continuous.add
  · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).mul continuous_const
  · exact (Complex.continuous_ofReal.comp (continuous_apply 1)).mul continuous_const

lemma norm_exp_fourier_kernel_le_one (x ξ : Fin 2 → ℝ) :
    ‖Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))‖ ≤ 1 := by
  have h_re : (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1))).re = 0 := by simp
  rw [Complex.norm_exp, h_re, Real.exp_zero]

lemma continuous_bochner_fourier_transform_eps (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y : Fin 2 → ℝ)
    (hint : Integrable
      (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) volume) :
    Continuous (fun (ξ : Fin 2 → ℝ) => bochner_fourier_transform_eps f ε y ξ) := by
  unfold bochner_fourier_transform_eps
  have h_bound : ∀ (ξ : Fin 2 → ℝ), ∀ᵐ (x : Fin 2 → ℝ),
      ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
        Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))‖ ≤
      ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ := by
    intro ξ
    apply ae_of_all
    intro x
    rw [norm_mul]
    have h1 := norm_exp_fourier_kernel_le_one x ξ
    calc ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ *
        ‖Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))‖
      _ ≤ ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ := mul_one _
  have h_cont : ∀ᵐ (x : Fin 2 → ℝ),
      Continuous (fun (ξ : Fin 2 → ℝ) =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
        Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) := by
    apply ae_of_all
    intro x
    exact continuous_const.mul (continuous_exp_fourier_kernel x)
  have h_meas : ∀ (ξ : Fin 2 → ℝ), AEStronglyMeasurable
      (fun (x : Fin 2 → ℝ) =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
        Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) volume := by
    intro ξ
    apply AEStronglyMeasurable.mul hint.aestronglyMeasurable
    apply Continuous.aestronglyMeasurable
    exact continuous_exp_fourier_kernel_x ξ
  exact continuous_of_dominated h_meas h_bound hint.norm h_cont

lemma continuous_fourier_exp_phase (w : Fin 2 → ℂ) :
    Continuous (fun (ξ : Fin 2 → ℝ) => Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Continuous.add
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1))

lemma continuous_real_exp_phase (r : ℝ) :
    Continuous (fun (ξ : Fin 2 → ℝ) => Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) := by
  apply Real.continuous_exp.comp
  apply Continuous.add
  · exact continuous_const.mul (continuous_apply 0)
  · exact continuous_const.mul (continuous_apply 1)

lemma bochner_f_eps_eq_bochner_integrand_F_zero (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) :
    bochner_f_eps f ε z = bochner_integrand_F f ε 0 z := by
  unfold bochner_integrand_F
  simp

lemma continuous_bochner_c_eps (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun (ξ : Fin 2 → ℝ) =>
      bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) := by
  have hy0 : (fun _ : Fin 2 => r / 2) ∈ LShape r R := by
    unfold LShape
    left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hint0 := bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε 0 (fun _ => r/2) hy0
  have heq : (fun x : Fin 2 → ℝ =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))) =
      (fun x : Fin 2 → ℝ =>
        bochner_integrand_F f ε 0 (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))) := by
    ext x
    exact bochner_f_eps_eq_bochner_integrand_F_zero f ε
      (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))
  have hint : Integrable
      (fun x : Fin 2 → ℝ =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))) volume := by
    rw [heq]
    exact hint0
  have h_cont_ft := continuous_bochner_fourier_transform_eps f ε (fun _ => r/2) hint
  apply Continuous.mul h_cont_ft
  exact Complex.continuous_ofReal.comp (continuous_real_exp_phase r)

lemma bochner_F_eps_integrand_aestronglyMeasurable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (w : Fin 2 → ℂ) :
    AEStronglyMeasurable (fun ξ =>
      (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
      Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) volume := by
  have h_c_cont := continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  apply Continuous.aestronglyMeasurable
  exact h_c_cont.mul (continuous_fourier_exp_phase w)

noncomputable def fourier_proj (i : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) (φ := fun _ => ℂ) i

lemma smulRight_eq_smul (i : Fin 2) (c : ℂ) :
    (fourier_proj i).smulRight c = c • fourier_proj i := by
  ext v
  simp only [fourier_proj, ContinuousLinearMap.smulRight_apply, smul_apply, proj_apply, smul_eq_mul]
  exact mul_comm _ _

lemma continuous_smulRight_fourier_proj (i : Fin 2) :
    Continuous (fun ξ : Fin 2 → ℝ => (fourier_proj i).smulRight (ξ i : ℂ)) := by
  have heq : (fun ξ : Fin 2 → ℝ => (fourier_proj i).smulRight (ξ i : ℂ)) =
      (fun ξ : Fin 2 → ℝ => (ξ i : ℂ) • fourier_proj i) := by
    funext ξ
    exact smulRight_eq_smul i (ξ i : ℂ)
  rw [heq]
  exact (Complex.continuous_ofReal.comp (continuous_apply i)).smul continuous_const

noncomputable def fourier_integrand_fderiv_clm
    (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I) •
    ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ))

lemma continuous_fourier_integrand_fderiv_clm
    (c : (Fin 2 → ℝ) → ℂ) (hc : Continuous c) (z : Fin 2 → ℂ) :
    Continuous (fun ξ : Fin 2 → ℝ => fourier_integrand_fderiv_clm c ξ z) := by
  unfold fourier_integrand_fderiv_clm
  have h1 : Continuous
      (fun ξ : Fin 2 → ℝ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I) := by
    apply Continuous.mul
    · apply Continuous.mul hc
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      apply Continuous.add
      · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
      · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1))
    · exact continuous_const
  have h2 : Continuous (fun ξ : Fin 2 → ℝ =>
      (fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)) :=
    (continuous_smulRight_fourier_proj 0).add (continuous_smulRight_fourier_proj 1)
  exact h1.smul h2

lemma hasFDerivAt_phase (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasFDerivAt (fun w : Fin 2 → ℂ => w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1))
      ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)) z := by
  have h0 : HasFDerivAt (fun w : Fin 2 → ℂ => w 0 * (ξ 0 : ℂ))
      ((fourier_proj 0).smulRight (ξ 0 : ℂ)) z := by
    have h := (fourier_proj 0).hasFDerivAt (x := z)
    exact h.smul_const (ξ 0 : ℂ)
  have h1 : HasFDerivAt (fun w : Fin 2 → ℂ => w 1 * (ξ 1 : ℂ))
      ((fourier_proj 1).smulRight (ξ 1 : ℂ)) z := by
    have h := (fourier_proj 1).hasFDerivAt (x := z)
    exact h.smul_const (ξ 1 : ℂ)
  exact h0.add h1

lemma fourier_integrand_hasFDerivAt (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasFDerivAt (fun w : Fin 2 → ℂ => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1))))
      (fourier_integrand_fderiv_clm c ξ z) z := by
  have h_phase : HasFDerivAt (fun w : Fin 2 → ℂ => I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))
      (I • ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ))) z :=
    (hasFDerivAt_phase ξ z).const_mul I
  have h_exp := h_phase.cexp
  have h_mul := h_exp.const_mul (c ξ)
  unfold fourier_integrand_fderiv_clm
  have heq : c ξ • (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) •
      (I • ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)))) =
      (c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I) •
        ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)) := by
    rw [smul_smul, smul_smul, mul_assoc]
  rw [heq] at h_mul
  exact h_mul

lemma fourier_integrand_fderiv_eq (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    fderiv ℂ (fun w : Fin 2 → ℂ => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z =
      fourier_integrand_fderiv_clm c ξ z :=
  (fourier_integrand_hasFDerivAt c ξ z).fderiv

lemma bochner_F_eps_integrand_fderiv_aestronglyMeasurable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ) :
    AEStronglyMeasurable (fun ξ => fderiv ℂ (fun (w : Fin 2 → ℂ) =>
      (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
      Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) volume := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)
  have hc : Continuous c := continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  have heq : (fun ξ => fderiv ℂ (fun (w : Fin 2 → ℂ) =>
      c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) =
      (fun ξ => fourier_integrand_fderiv_clm c ξ z) := by
    funext ξ
    exact fourier_integrand_fderiv_eq c ξ z
  rw [heq]
  exact (continuous_fourier_integrand_fderiv_clm c hc z).aestronglyMeasurable

lemma norm_proj_fin2_le (i : Fin 2) :
    ‖ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) (φ := fun _ => ℂ) i‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun v => ?_
  simp only [proj_apply, one_mul]
  exact norm_le_pi_norm v i

lemma clm_fin2_norm_le (a b : ℂ) :
    ‖(fourier_proj 0).smulRight a + (fourier_proj 1).smulRight b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [smulRight_eq_smul 0 a, smulRight_eq_smul 1 b]
  refine (ContinuousLinearMap.opNorm_add_le _ _).trans ?_
  have ha : ‖a • fourier_proj 0‖ ≤ ‖a‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    calc ‖a‖ * ‖fourier_proj 0‖
      _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left (norm_proj_fin2_le 0) (norm_nonneg _)
      _ = ‖a‖ := mul_one _
  have hb : ‖b • fourier_proj 1‖ ≤ ‖b‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    calc ‖b‖ * ‖fourier_proj 1‖
      _ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left (norm_proj_fin2_le 1) (norm_nonneg _)
      _ = ‖b‖ := mul_one _
  linarith

lemma norm_fourier_integrand_fderiv_clm_le (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    ‖fourier_integrand_fderiv_clm c ξ z‖ ≤
      ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) * (|ξ 0| + |ξ 1|) := by
  unfold fourier_integrand_fderiv_clm
  have h_smul := ContinuousLinearMap.opNorm_smul_le
    (c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I)
    ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ))
  have h_clm := clm_fin2_norm_le (ξ 0 : ℂ) (ξ 1 : ℂ)
  have h_I : ‖I‖ = 1 := norm_I
  have h_exp : ‖Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
      Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    have h_re : (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))).re = - (z 0).im * ξ 0 - (z 1).im * ξ 1 := by
      simp
      ring
    rw [Complex.norm_exp, h_re]
  have h_scalar : ‖c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I‖ =
      ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    rw [norm_mul, norm_mul, h_I, mul_one, h_exp]
  rw [h_scalar] at h_smul
  have h_xi0 : ‖(ξ 0 : ℂ)‖ = |ξ 0| := Complex.norm_real (ξ 0)
  have h_xi1 : ‖(ξ 1 : ℂ)‖ = |ξ 1| := Complex.norm_real (ξ 1)
  rw [h_xi0, h_xi1] at h_clm
  refine h_smul.trans ?_
  exact mul_le_mul_of_nonneg_left h_clm (by positivity)

lemma closedBall_im_le (z : Fin 2 → ℂ) (w : Fin 2 → ℂ)
    (hw : w ∈ Metric.closedBall z 1) (i : Fin 2) :
    |(w i).im| ≤ |(z i).im| + 1 := by
  have h_dist : dist w z ≤ 1 := Metric.mem_closedBall.mp hw
  rw [dist_eq_norm] at h_dist
  have h_coord : ‖w i - z i‖ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) i
  have h_le_one : ‖w i - z i‖ ≤ 1 := h_coord.trans h_dist
  have h_im_le : |(w i - z i).im| ≤ ‖w i - z i‖ := abs_im_le_norm (w i - z i)
  have h_diff_im : (w i - z i).im = (w i).im - (z i).im := by simp
  rw [h_diff_im] at h_im_le
  have h_sub_le : |(w i).im - (z i).im| ≤ 1 := h_im_le.trans h_le_one
  calc |(w i).im|
    _ = |(z i).im + ((w i).im - (z i).im)| := by ring_nf
    _ ≤ |(z i).im| + |(w i).im - (z i).im| := abs_add_le _ _
    _ ≤ |(z i).im| + 1 := by linarith

lemma exp_im_le (z : Fin 2 → ℂ) (w : Fin 2 → ℂ) (hw : w ∈ Metric.closedBall z 1) (ξ : Fin 2 → ℝ) :
    Real.exp (- (w 0).im * ξ 0 - (w 1).im * ξ 1) ≤
      Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) := by
  apply Real.exp_le_exp.mpr
  have h0 : - (w 0).im * ξ 0 ≤ (|(z 0).im| + 1) * |ξ 0| := by
    have h_abs : - (w 0).im * ξ 0 ≤ |(w 0).im| * |ξ 0| := by
      calc - (w 0).im * ξ 0
        _ ≤ |- (w 0).im * ξ 0| := le_abs_self _
        _ = |(w 0).im| * |ξ 0| := by rw [abs_mul, abs_neg]
    have h_im := closedBall_im_le z w hw 0
    have h_le : |(w 0).im| * |ξ 0| ≤ (|(z 0).im| + 1) * |ξ 0| :=
      mul_le_mul_of_nonneg_right h_im (abs_nonneg _)
    exact h_abs.trans h_le
  have h1 : - (w 1).im * ξ 1 ≤ (|(z 1).im| + 1) * |ξ 1| := by
    have h_abs : - (w 1).im * ξ 1 ≤ |(w 1).im| * |ξ 1| := by
      calc - (w 1).im * ξ 1
        _ ≤ |- (w 1).im * ξ 1| := le_abs_self _
        _ = |(w 1).im| * |ξ 1| := by rw [abs_mul, abs_neg]
    have h_im := closedBall_im_le z w hw 1
    have h_le : |(w 1).im| * |ξ 1| ≤ (|(z 1).im| + 1) * |ξ 1| :=
      mul_le_mul_of_nonneg_right h_im (abs_nonneg _)
    exact h_abs.trans h_le
  linarith

lemma bochner_F_eps_integrand_norm_le_master (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) :
    ‖(c ξ) * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
  have h_exp : ‖Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
      Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    have h_re : (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))).re = - (z 0).im * ξ 0 - (z 1).im * ξ 1 := by
      simp
      ring
    rw [Complex.norm_exp, h_re]
  have h_norm : ‖(c ξ) * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
      ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    rw [norm_mul, h_exp]
  rw [h_norm]
  have h0 : - (z 0).im * ξ 0 ≤ |(z 0).im| * |ξ 0| := by
    calc - (z 0).im * ξ 0
      _ ≤ |- (z 0).im * ξ 0| := le_abs_self _
      _ = |(z 0).im| * |ξ 0| := by rw [abs_mul, abs_neg]
  have h0_le : |(z 0).im| * |ξ 0| ≤ (|(z 0).im| + 1) * |ξ 0| := by
    nlinarith [abs_nonneg (z 0).im, abs_nonneg (ξ 0)]
  have h0_trans : - (z 0).im * ξ 0 ≤ (|(z 0).im| + 1) * |ξ 0| := h0.trans h0_le
  have h1 : - (z 1).im * ξ 1 ≤ |(z 1).im| * |ξ 1| := by
    calc - (z 1).im * ξ 1
      _ ≤ |- (z 1).im * ξ 1| := le_abs_self _
      _ = |(z 1).im| * |ξ 1| := by rw [abs_mul, abs_neg]
  have h1_le : |(z 1).im| * |ξ 1| ≤ (|(z 1).im| + 1) * |ξ 1| := by
    nlinarith [abs_nonneg (z 1).im, abs_nonneg (ξ 1)]
  have h1_trans : - (z 1).im * ξ 1 ≤ (|(z 1).im| + 1) * |ξ 1| := h1.trans h1_le
  have h_sum :
      - (z 0).im * ξ 0 - (z 1).im * ξ 1 ≤
        (|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1| := by
    linarith
  have h_exp_le : Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) ≤
      Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) :=
    Real.exp_le_exp.mpr h_sum
  have h_mul_le : ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) :=
    mul_le_mul_of_nonneg_left h_exp_le (norm_nonneg _)
  have h_pos : 1 ≤ |ξ 0| + |ξ 1| + 1 := by
    have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
    linarith
  calc ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1)
    _ ≤ ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) * 1 := by
      rw [mul_one]
      exact h_mul_le
    _ ≤ ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
      refine mul_le_mul_of_nonneg_left h_pos ?_
      positivity

lemma bochner_F_eps_bound_le_master (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) :
    ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) * (|ξ 0| + |ξ 1|) ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
  have h_pos : |ξ 0| + |ξ 1| ≤ |ξ 0| + |ξ 1| + 1 := by linarith
  refine mul_le_mul_of_nonneg_left h_pos ?_
  positivity

lemma bochner_F_eps_bound_integrable_of_master (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ)
    (h_master : Integrable (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)) volume) :
    Integrable (fun ξ =>
      (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
      Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
    Integrable (fun ξ =>
      ‖(bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) volume := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)
  have h_meas1 := bochner_F_eps_integrand_aestronglyMeasurable r R hr hR f hf_holo hf_bound ε hε z
  have h_le1 : ∀ᵐ ξ, ‖c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
    apply ae_of_all
    intro ξ
    exact bochner_F_eps_integrand_norm_le_master c z ξ
  have hint1 : Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume :=
    Integrable.mono' h_master h_meas1 h_le1
  have h_cont_c : Continuous c :=
    continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  have h_cont_bound : Continuous (fun ξ =>
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) := by
    apply Continuous.mul
    · apply Continuous.mul h_cont_c.norm
      apply Real.continuous_exp.comp
      apply Continuous.add
      · exact continuous_const.mul (continuous_apply 0).abs
      · exact continuous_const.mul (continuous_apply 1).abs
    · apply Continuous.add
      · exact (continuous_apply 0).abs
      · exact (continuous_apply 1).abs
  have h_meas2 : AEStronglyMeasurable (fun ξ =>
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) volume :=
    h_cont_bound.aestronglyMeasurable
  have h_le2 : ∀ᵐ ξ,
      ‖‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)‖ ≤
        ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1) := by
    apply ae_of_all
    intro ξ
    have h_nonneg : 0 ≤
        ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1|) := by
      positivity
    rw [Real.norm_of_nonneg h_nonneg]
    exact bochner_F_eps_bound_le_master c z ξ
  have hint2 : Integrable (fun ξ =>
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) volume :=
    Integrable.mono' h_master h_meas2 h_le2
  exact ⟨hint1, hint2⟩

lemma poly_le_exp_add (x y : ℝ) :
    |x| + |y| + 1 ≤ Real.exp (|x| + |y|) := by
  have h_add : |x| + |y| + 1 ≤ (|x| + 1) * (|y| + 1) := by
    nlinarith [abs_nonneg x, abs_nonneg y]
  have h_exp_x : |x| + 1 ≤ Real.exp |x| := Real.add_one_le_exp |x|
  have h_exp_y : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp |y|
  have h_mul_exp : (|x| + 1) * (|y| + 1) ≤ Real.exp |x| * Real.exp |y| :=
    mul_le_mul h_exp_x h_exp_y (by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add] at h_mul_exp
  exact h_add.trans h_mul_exp

lemma exp_neg_sq_add_mul_le (α K x : ℝ) (hα : 0 < α) :
    - α * x ^ 2 + K * |x| ≤ - (α / 2) * x ^ 2 + K ^ 2 / (2 * α) := by
  have h_sq : 0 ≤ (Real.sqrt (α / 2) * |x| - K / (2 * Real.sqrt (α / 2))) ^ 2 := sq_nonneg _
  have h_pos : 0 < α / 2 := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (α / 2) := Real.sqrt_pos.mpr h_pos
  have h_sqrt_sq : (Real.sqrt (α / 2)) ^ 2 = α / 2 := Real.sq_sqrt (by linarith)
  have h_expand : (Real.sqrt (α / 2) * |x| - K / (2 * Real.sqrt (α / 2))) ^ 2 =
      (α / 2) * x ^ 2 - K * |x| + K ^ 2 / (2 * α) := by
    calc (Real.sqrt (α / 2) * |x| - K / (2 * Real.sqrt (α / 2))) ^ 2
      _ = (Real.sqrt (α / 2) * |x|) ^ 2 -
          2 * (Real.sqrt (α / 2) * |x|) * (K / (2 * Real.sqrt (α / 2))) +
          (K / (2 * Real.sqrt (α / 2))) ^ 2 := by ring
      _ = (Real.sqrt (α / 2)) ^ 2 * (|x|) ^ 2 -
          (2 * (K / 2)) * ((Real.sqrt (α / 2) / Real.sqrt (α / 2)) * |x|) +
          K ^ 2 / (4 * (Real.sqrt (α / 2)) ^ 2) := by ring
      _ = (α / 2) * x ^ 2 - K * |x| + K ^ 2 / (2 * α) := by
        rw [h_sqrt_sq, sq_abs]
        have h_div : Real.sqrt (α / 2) / Real.sqrt (α / 2) = 1 := div_self (ne_of_gt h_sqrt_pos)
        rw [h_div]
        ring
  rw [h_expand] at h_sq
  linarith

lemma gaussian_mul_exp_poly_le (α K₀ K₁ : ℝ) (hα : 0 < α) (ξ : Fin 2 → ℝ) :
    Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
      Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) ≤
      Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
      Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
  have h_poly := poly_le_exp_add (ξ 0) (ξ 1)
  have h1 : Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) ≤
      Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * Real.exp (|ξ 0| + |ξ 1|) :=
    mul_le_mul_of_nonneg_left h_poly (by positivity)
  have h_le0 := exp_neg_sq_add_mul_le α (K₀ + 1) (ξ 0) hα
  have h_le1 := exp_neg_sq_add_mul_le α (K₁ + 1) (ξ 1) hα
  have h_sum : (- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) + (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|) ≤
      ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) + (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
    linarith
  have h_exp_le :
      Real.exp ((- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) + (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|)) ≤
        Real.exp (((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) +
          (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) :=
    Real.exp_le_exp.mpr h_sum
  have h_exp_left :
      Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) * Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) *
        Real.exp (|ξ 0| + |ξ 1|) =
      Real.exp ((- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) + (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h_exp_right :
      Real.exp (((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) +
        (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) =
      Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
        Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
    rw [Real.exp_add]
  calc Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) * Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)
    _ ≤ Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) * Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) *
        Real.exp (|ξ 0| + |ξ 1|) := h1
    _ = Real.exp ((- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) +
        (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|)) := h_exp_left
    _ ≤ Real.exp (((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) +
        (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) := h_exp_le
    _ = Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
        Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := h_exp_right

lemma integrable_gaussian_mul_exp_poly (C α K₀ K₁ : ℝ) (hC : 0 ≤ C) (hα : 0 < α) :
    Integrable (fun ξ : Fin 2 → ℝ =>
      C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) volume := by
  have h_pos : 0 < α / 2 := by linarith
  have hint_gauss :
      Integrable (fun ξ : Fin 2 → ℝ => Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) volume :=
    integrable_gaussian_2d (α / 2) h_pos
  let C' := C * Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α))
  have hint_bound :
      Integrable (fun ξ : Fin 2 → ℝ => C' * Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) volume :=
    hint_gauss.const_mul C'
  have h_cont : Continuous (fun ξ : Fin 2 → ℝ =>
      C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) := by
    apply Continuous.mul
    · apply Continuous.mul
      · apply continuous_const.mul
        apply Real.continuous_exp.comp
        apply continuous_const.mul
        apply Continuous.add
        · exact (continuous_apply 0).pow 2
        · exact (continuous_apply 1).pow 2
      · apply Real.continuous_exp.comp
        apply Continuous.add
        · exact continuous_const.mul (continuous_apply 0).abs
        · exact continuous_const.mul (continuous_apply 1).abs
    · apply Continuous.add
      · apply Continuous.add
        · exact (continuous_apply 0).abs
        · exact (continuous_apply 1).abs
      · exact continuous_const
  have h_meas : AEStronglyMeasurable (fun ξ : Fin 2 → ℝ =>
      C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) volume :=
    h_cont.aestronglyMeasurable
  have h_le : ∀ᵐ ξ : Fin 2 → ℝ,
      ‖C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)‖ ≤
        C' * Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
    apply ae_of_all
    intro ξ
    have h_nonneg : 0 ≤ C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) := by
      positivity
    rw [Real.norm_of_nonneg h_nonneg]
    have h_ineq := gaussian_mul_exp_poly_le α K₀ K₁ hα ξ
    dsimp [C']
    calc C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)
      _ = C * (Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) := by ring
      _ ≤ C * (Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
          Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) :=
        mul_le_mul_of_nonneg_left h_ineq hC
      _ = C * Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
          Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by ring
  exact Integrable.mono' hint_bound h_meas h_le

lemma bochner_F_eps_integrable_master_of_decay (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ)
    (h_decay : ∃ C α : ℝ, 0 ≤ C ∧ 0 < α ∧ ∀ ξ : Fin 2 → ℝ,
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ ≤
        C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2))) :
    Integrable (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)) volume := by
  rcases h_decay with ⟨C, α, hC, hα, h_decay_le⟩
  let K₀ := |(z 0).im| + 1
  let K₁ := |(z 1).im| + 1
  have hint_bound := integrable_gaussian_mul_exp_poly C α K₀ K₁ hC hα
  have h_cont_c : Continuous (fun ξ =>
      bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) :=
    continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  have h_cont : Continuous (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
      Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) := by
    apply Continuous.mul
    · apply Continuous.mul h_cont_c.norm
      apply Real.continuous_exp.comp
      apply Continuous.add
      · exact continuous_const.mul (continuous_apply 0).abs
      · exact continuous_const.mul (continuous_apply 1).abs
    · apply Continuous.add
      · apply Continuous.add
        · exact (continuous_apply 0).abs
        · exact (continuous_apply 1).abs
      · exact continuous_const
  have h_meas : AEStronglyMeasurable (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)) volume :=
    h_cont.aestronglyMeasurable
  have h_le : ∀ᵐ ξ : Fin 2 → ℝ,
      ‖‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)‖ ≤
        C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) := by
    apply ae_of_all
    intro ξ
    have h_nonneg : 0 ≤
        ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
          Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1) := by
      positivity
    rw [Real.norm_of_nonneg h_nonneg]
    have h_dec := h_decay_le ξ
    have h_exp_nonneg : 0 ≤ Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
      positivity
    dsimp [K₀, K₁]
    calc ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
          Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1)
      _ = (‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖) *
          (Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
            (|ξ 0| + |ξ 1| + 1)) := by ring
      _ ≤ (C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2))) *
          (Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
            (|ξ 0| + |ξ 1| + 1)) :=
        mul_le_mul_of_nonneg_right h_dec h_exp_nonneg
      _ = C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1) := by ring
  exact Integrable.mono' hint_bound h_meas h_le

lemma bochner_F_eps_integrand_bound_integrable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R)) :
    ∃ (bound : (Fin 2 → ℝ) → ℝ), Integrable bound volume ∧ ∃ s ∈ 𝓝 z,
      Integrable (fun ξ =>
        (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
        Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
      (∀ᵐ ξ, ∀ w ∈ s, ‖fderiv ℂ (fun (w' : Fin 2 → ℂ) =>
        (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
        Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w‖ ≤ bound ξ) := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)
  have hc_eq (ξ : Fin 2 → ℝ) :
      bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) = c ξ := rfl
  let y' : Fin 2 → ℝ := fun i => (z i).im
  have hy' : y' ∈ LShapeConvexHull r R := hz
  rcases bochner_c_eps_local_exp_decay r R hr hR f hf_holo hf_bound ε hε y' hy' with
    ⟨C, δ, hC, hδ_pos, h_decay⟩
  let η := δ / 4
  have hη_pos : 0 < η := by positivity
  let s := Metric.closedBall z η
  have hs : s ∈ 𝓝 z := Metric.closedBall_mem_nhds z hη_pos
  let bound : (Fin 2 → ℝ) → ℝ := fun ξ =>
    C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1))
  have hδ2_pos : 0 < δ / 2 := by positivity
  have h_int_poly := integrable_exp_neg_abs_poly_2d (δ / 2) hδ2_pos
  have hbound_int : Integrable bound volume := h_int_poly.const_mul C
  have hint_z :
      Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume := by
    have h_cont_c := continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
    have h_cont : Continuous (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) := by
      apply Continuous.mul h_cont_c
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      apply Continuous.add
      · exact continuous_const.mul (continuous_ofReal.comp (continuous_apply 0))
      · exact continuous_const.mul (continuous_ofReal.comp (continuous_apply 1))
    have h_meas : AEStronglyMeasurable
        (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume :=
      h_cont.aestronglyMeasurable
    have h_le : ∀ᵐ ξ, ‖c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ ≤ bound ξ := by
      apply ae_of_all
      intro ξ
      rw [norm_mul]
      have h_norm_exp : ‖Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
          Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) := by
        have h_re : (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))).re = - (z 0).im * ξ 0 - (z 1).im * ξ 1 := by
          simp
          ring
        rw [Complex.norm_exp, h_re]
        dsimp [y']
        congr 1
        ring
      rw [h_norm_exp]
      have h_dec := h_decay ξ
      rw [hc_eq] at h_dec
      calc ‖c ξ‖ * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))
        _ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := h_dec
        _ ≤ C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)) := by
          have h_exp_le :
              Real.exp (-δ * (|ξ 0| + |ξ 1|)) ≤ Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) := by
            refine Real.exp_le_exp.mpr ?_
            have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
            nlinarith
          have h_one_le : 1 ≤ |ξ 0| + |ξ 1| + 1 := by
            have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
            linarith
          have : Real.exp (-δ * (|ξ 0| + |ξ 1|)) ≤
              Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) := by
            calc Real.exp (-δ * (|ξ 0| + |ξ 1|))
              _ = Real.exp (-δ * (|ξ 0| + |ξ 1|)) * 1 := (mul_one _).symm
              _ ≤ Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) := by
                exact mul_le_mul h_exp_le h_one_le zero_le_one (by positivity)
          exact mul_le_mul_of_nonneg_left this hC
    exact Integrable.mono' hbound_int h_meas h_le
  refine ⟨bound, hbound_int, s, hs, hint_z, ?_⟩
  apply ae_of_all
  intro ξ w hw
  rw [fourier_integrand_fderiv_eq c ξ w]
  have h_norm := norm_fourier_integrand_fderiv_clm_le c ξ w
  have h_exp_im := exp_im_diff_le hw ξ
  calc ‖fourier_integrand_fderiv_clm c ξ w‖
    _ ≤ ‖c ξ‖ * Real.exp (- (w 0).im * ξ 0 - (w 1).im * ξ 1) * (|ξ 0| + |ξ 1|) := h_norm
    _ ≤ ‖c ξ‖ * (Real.exp (-(z 0).im * ξ 0 - (z 1).im * ξ 1 + η * (|ξ 0| + |ξ 1|))) *
        (|ξ 0| + |ξ 1|) := by
      gcongr
    _ = (‖c ξ‖ * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))) *
        Real.exp (η * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      dsimp [y']
      rw [Real.exp_add]
      ring_nf
    _ ≤ (C * Real.exp (-δ * (|ξ 0| + |ξ 1|))) *
        Real.exp (η * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      have h_dec := h_decay ξ
      rw [hc_eq] at h_dec
      gcongr
    _ = C * (Real.exp (-δ * (|ξ 0| + |ξ 1|)) * Real.exp (η * (|ξ 0| + |ξ 1|))) *
        (|ξ 0| + |ξ 1|) := by ring
    _ = C * Real.exp (-δ * (|ξ 0| + |ξ 1|) + η * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      rw [← Real.exp_add]
    _ = C * Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      congr 2
      ring_nf
    _ ≤ C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)) := by
      have h_exp_le :
          Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) ≤ Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) := by
        refine Real.exp_le_exp.mpr ?_
        have : δ / 2 ≤ δ - η := by dsimp [η]; linarith
        have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
        nlinarith
      have h_poly_le : |ξ 0| + |ξ 1| ≤ |ξ 0| + |ξ 1| + 1 := by linarith
      have : Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) ≤
          Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) := by
        exact mul_le_mul h_exp_le h_poly_le (by positivity) (by positivity)
      calc C * Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|)
        _ = C * (Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|)) := by ring
        _ ≤ C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)) :=
          mul_le_mul_of_nonneg_left this hC

lemma bochner_F_eps_integrand_dom (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ z ∈ TubeDomain (LShapeConvexHull r R),
      ∃ (bound : (Fin 2 → ℝ) → ℝ), Integrable bound volume ∧ ∃ s ∈ 𝓝 z,
        (∀ᶠ w in 𝓝 z, AEStronglyMeasurable (fun ξ =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) volume) ∧
        Integrable (fun ξ =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
        AEStronglyMeasurable (fun ξ => fderiv ℂ (fun (w : Fin 2 → ℂ) =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) volume ∧
        (∀ᵐ ξ, ∀ w ∈ s, ‖fderiv ℂ (fun (w' : Fin 2 → ℂ) =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w‖ ≤ bound ξ) := by
  intro z hz
  rcases bochner_F_eps_integrand_bound_integrable r R hr hR f hf_holo hf_bound ε hε z hz with
    ⟨bound, bound_int, s, hs, hint, hle⟩
  refine ⟨bound, bound_int, s, hs, ?_, hint, ?_, hle⟩
  · exact Filter.Eventually.of_forall (fun w =>
      bochner_F_eps_integrand_aestronglyMeasurable r R hr hR f hf_holo hf_bound ε hε w)
  · exact bochner_F_eps_integrand_fderiv_aestronglyMeasurable r R hr hR f hf_holo hf_bound ε hε z

lemma bochner_F_eps_holo (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)) := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r / 2) ξ * ↑(Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1))
  have h_dom := bochner_F_eps_integrand_dom r R hr hR f hf_holo hf_bound ε hε
  have h_int := bochner_fourier_integral_holo_of_bound c (TubeDomain (LShapeConvexHull r R)) h_dom
  unfold bochner_F_eps
  have h1 : DifferentiableOn ℂ
      (fun z => (2 * Real.pi)⁻¹ *
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))))
      (TubeDomain (LShapeConvexHull r R)) := h_int.const_mul _
  have h2 : DifferentiableOn ℂ
      (fun z => (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ *
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))))
      (TubeDomain (LShapeConvexHull r R)) := h1.const_mul _
  have h_eq : (fun z : Fin 2 → ℂ => (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      (bochner_fourier_transform_eps f ε (fun x => r / 2) ξ *
        Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1)) *
        Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) =
      (fun z => (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ *
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))))) := by
    ext z
    ring
  rw [h_eq]
  exact h2

lemma bochner_F_eps_eq_standard_fourier_inv (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShape r R)) :
    bochner_F_eps f ε r R z =
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      bochner_fourier_transform_eps f ε (fun i => (z i).im) ξ *
      Complex.exp (I * (↑(z 0).re * ↑(ξ 0) + ↑(z 1).re * ↑(ξ 1))) := by
  let y : Fin 2 → ℝ := fun i => (z i).im
  let x : Fin 2 → ℝ := fun i => (z i).re
  have hy : y ∈ LShape r R := hz
  have hy_tube : (fun i => ↑(0 : ℝ) + I * ↑(y i)) ∈ TubeDomain (LShape r R) := by
    simp [TubeDomain, y, hy]
  have hy0 : (fun _ : Fin 2 => r / 2) ∈ LShape r R := by
    unfold LShape
    left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hy0_tube :
      (fun i => ↑(0 : ℝ) + I * ↑((fun _ : Fin 2 => r / 2) i)) ∈ TubeDomain (LShape r R) := by
    simp [TubeDomain, hy0]
  unfold bochner_F_eps
  congr 1
  congr 1
  ext ξ
  have h_shift := bochner_fourier_transform_shift_eps r R hr hR f hf_holo hf_bound ε hε
    (fun _ => r/2) y hy0_tube hy_tube ξ
  have h_exp :
      (bochner_fourier_transform_eps f ε (fun _ => r / 2) ξ *
        ↑(Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1))) *
        Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) =
      bochner_fourier_transform_eps f ε y ξ *
      Complex.exp (I * (↑(z 0).re * ↑(ξ 0) + ↑(z 1).re * ↑(ξ 1))) := by
    rw [h_shift]
    rw [mul_assoc]
    congr 1
    have hz_rep : ∀ i, z i = ↑(x i) + I * ↑(y i) := by
      intro i
      dsimp [x, y]
      rw [mul_comm I ↑(z i).im, Complex.re_add_im]
    have h_cancel := fourier_inversion_integrand_cancel x y ξ
    have h_z0 : z 0 = ↑(x 0) + I * ↑(y 0) := hz_rep 0
    have h_z1 : z 1 = ↑(x 1) + I * ↑(y 1) := hz_rep 1
    rw [← h_z0, ← h_z1] at h_cancel
    exact h_cancel
  exact h_exp

noncomputable def fourier_transform_2d (φ : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) : ℂ :=
  ∫ (x : Fin 2 → ℝ), φ x * Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))

lemma bochner_fourier_transform_eps_eq (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y : Fin 2 → ℝ) :
    bochner_fourier_transform_eps f ε y =
    fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
  ext ξ
  rfl

open Real FiniteDimensional VectorFourier

lemma euclidean_inner_eq (v w : EuclideanSpace ℝ (Fin 2)) :
    ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma euclidean_smul_apply (c : ℝ) (w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (c • w) i = c * w i := rfl

lemma exp_inner_eq (v w : EuclideanSpace ℝ (Fin 2)) :
    Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) =
    Complex.exp (-I * (↑(v 0) * ↑(((2 * π) • w : EuclideanSpace ℝ (Fin 2)) 0) +
                       ↑(v 1) * ↑(((2 * π) • w : EuclideanSpace ℝ (Fin 2)) 1))) := by
  rw [euclidean_inner_eq]
  congr 1
  simp only [euclidean_smul_apply]
  push_cast
  ring

lemma integral_euclidean_eq_integral (g : (Fin 2 → ℝ) → ℂ) :
    ∫ v : EuclideanSpace ℝ (Fin 2), g v = ∫ x : Fin 2 → ℝ, g x :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp' g

lemma integrable_euclidean_iff (g : (Fin 2 → ℝ) → ℂ) :
    Integrable (fun v : EuclideanSpace ℝ (Fin 2) => g v) ↔ Integrable g :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

lemma fourier_eq_fourier_transform_2d (φ : (Fin 2 → ℝ) → ℂ) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v) w =
    fourier_transform_2d φ ((2 * π) • w) := by
  rw [fourier_eq']
  dsimp [fourier_transform_2d]
  rw [← integral_euclidean_eq_integral]
  congr 1
  ext v
  rw [exp_inner_eq v w]
  simp only [euclidean_smul_apply, mul_comm]

lemma euclidean_fourierInv_eq (g : EuclideanSpace ℝ (Fin 2) → ℂ) (x₀ : EuclideanSpace ℝ (Fin 2)) :
    𝓕⁻ g x₀ = ∫ w : EuclideanSpace ℝ (Fin 2),
      Complex.exp ((↑(2 * π * ⟪w, x₀⟫) * Complex.I)) * g w := by
  rw [fourierInv_eq]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]

lemma integral_comp_two_pi_smul (H : EuclideanSpace ℝ (Fin 2) → ℂ) :
    ∫ w : EuclideanSpace ℝ (Fin 2), H ((2 * π) • w) =
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ ξ : EuclideanSpace ℝ (Fin 2), H ξ := by
  have hR : 0 ≤ 2 * Real.pi := by positivity
  have h := Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) H (2 * Real.pi) (hR := hR)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  rw [hdim] at h
  rw [h]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma fourier_comp_toLp_integrable (φ : (Fin 2 → ℝ) → ℂ)
    (hφ_hat_int : Integrable (fourier_transform_2d φ)) :
    Integrable (𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v)) := by
  have h_ne : (2 * Real.pi) ≠ 0 := by positivity
  have h_hat_euc : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) => fourier_transform_2d φ ξ) :=
    (integrable_euclidean_iff (fourier_transform_2d φ)).2 hφ_hat_int
  have h_hat_smul : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      fourier_transform_2d φ (((2 * π) • w : EuclideanSpace ℝ (Fin 2)))) :=
    h_hat_euc.comp_smul h_ne
  have h_F_f : 𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v) =
      fun w : EuclideanSpace ℝ (Fin 2) =>
        fourier_transform_2d φ (((2 * π) • w : EuclideanSpace ℝ (Fin 2))) := by
    ext w
    exact fourier_eq_fourier_transform_2d φ w
  rw [h_F_f]
  exact h_hat_smul

lemma fourierInv_fourier_eval (φ : (Fin 2 → ℝ) → ℂ) (x₀ : Fin 2 → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_int : Integrable φ)
    (hφ_hat_int : Integrable (fourier_transform_2d φ)) :
    𝓕⁻ (𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v)) (WithLp.toLp 2 x₀) = φ x₀ := by
  let f : EuclideanSpace ℝ (Fin 2) → ℂ := fun v => φ v
  have hf_cont : Continuous f := hφ_cont.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ => ℝ))
  have hf_int : Integrable f := (integrable_euclidean_iff φ).2 hφ_int
  have h_F_int : Integrable (𝓕 f) := fourier_comp_toLp_integrable φ hφ_hat_int
  have h_inv := Continuous.fourierInv_fourier_eq hf_cont hf_int h_F_int
  have h_inv_at := congr_fun h_inv (WithLp.toLp 2 x₀)
  exact h_inv_at

lemma fourierInv_as_integral_2d (φ : (Fin 2 → ℝ) → ℂ) (x₀ : Fin 2 → ℝ) :
    𝓕⁻ (𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v)) (WithLp.toLp 2 x₀) =
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      fourier_transform_2d φ ξ *
      Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) := by
  let x₀_euc : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 x₀
  let f : EuclideanSpace ℝ (Fin 2) → ℂ := fun v => φ v
  rw [euclidean_fourierInv_eq]
  let H_fin : (Fin 2 → ℝ) → ℂ := fun ξ =>
    Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) * fourier_transform_2d φ ξ
  let H : EuclideanSpace ℝ (Fin 2) → ℂ := fun ξ => H_fin ξ
  have h_int_H : (∫ (w : EuclideanSpace ℝ (Fin 2)),
      Complex.exp (↑(2 * π * ⟪w, x₀_euc⟫) * I) * 𝓕 f w) =
      ∫ (w : EuclideanSpace ℝ (Fin 2)), H ((2 * π) • w) := by
    congr 1
    ext w
    have h_F_f : 𝓕 f w = fourier_transform_2d φ (((2 * π) • w : EuclideanSpace ℝ (Fin 2))) :=
      fourier_eq_fourier_transform_2d φ w
    rw [h_F_f]
    dsimp [H, H_fin]
    congr 1
    rw [euclidean_inner_eq]
    congr 1
    simp only [x₀_euc]
    push_cast
    ring
  rw [h_int_H]
  rw [integral_comp_two_pi_smul H]
  congr 1
  dsimp [H]
  rw [integral_euclidean_eq_integral H_fin]
  congr 1
  ext ξ
  ring

lemma fourier_inversion_2d (φ : (Fin 2 → ℝ) → ℂ) (x₀ : Fin 2 → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_int : Integrable φ)
    (hφ_hat_int : Integrable (fourier_transform_2d φ)) :
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      fourier_transform_2d φ ξ *
      Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) = φ x₀ := by
  rw [← fourierInv_as_integral_2d]
  exact fourierInv_fourier_eval φ x₀ hφ_cont hφ_int hφ_hat_int

lemma bochner_f_eps_cont_of_holo (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Continuous (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
  have hf_cont := bochner_f_cont_of_holo r R f hf_holo y hy
  unfold bochner_f_eps
  have h_exp : Continuous (fun x : Fin 2 → ℝ =>
      Complex.exp (-↑ε * (((x 0 : ℂ) + I * (y 0 : ℂ)) ^ 2 + ((x 1 : ℂ) + I * (y 1 : ℂ)) ^ 2))) := by
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    apply Continuous.add
    · exact (((Complex.continuous_ofReal.comp (continuous_apply 0)).add continuous_const).pow 2)
    · exact (((Complex.continuous_ofReal.comp (continuous_apply 1)).add continuous_const).pow 2)
  exact hf_cont.mul h_exp

lemma bochner_f_eps_eq_integrand_zero (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) :
    bochner_integrand_F f ε 0 z = bochner_f_eps f ε z := by
  unfold bochner_integrand_F
  simp

lemma bochner_f_eps_integrable_of_holo (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Integrable (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
  have hint := bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε 0 y hy
  have heq : (fun x : Fin 2 → ℝ => bochner_integrand_F f ε 0 (fun i => ↑(x i) + I * ↑(y i))) =
      (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
    ext x
    exact bochner_f_eps_eq_integrand_zero f ε (fun i => ↑(x i) + I * ↑(y i))
  rw [heq] at hint
  exact hint

lemma bochner_fourier_transform_eps_integrable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Integrable
      (fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)))) := by
  have h_eq : fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) =
      bochner_fourier_transform_eps f ε y := (bochner_fourier_transform_eps_eq f ε y).symm
  rw [h_eq]
  have hy_hull : y ∈ LShapeConvexHull r R := subset_convexHull _ _ hy
  rcases bochner_c_eps_local_exp_decay r R hr hR f hf_holo hf_bound ε hε y hy_hull with
    ⟨C, δ, hC, hδ_pos, h_decay⟩
  have h_bound : Integrable (fun ξ : Fin 2 → ℝ => C * Real.exp (-δ * (|ξ 0| + |ξ 1|))) volume :=
    (integrable_exp_neg_abs_2d δ hδ_pos).const_mul C
  have hint := bochner_f_eps_integrable_of_holo r R f hf_holo hf_bound ε hε y hy
  have h_cont_c : Continuous (bochner_fourier_transform_eps f ε y) :=
    continuous_bochner_fourier_transform_eps f ε y hint
  have h_meas : AEStronglyMeasurable (bochner_fourier_transform_eps f ε y) volume :=
    h_cont_c.aestronglyMeasurable
  have h_le : ∀ᵐ ξ,
      ‖bochner_fourier_transform_eps f ε y ξ‖ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
    apply ae_of_all
    intro ξ
    have hy_tube : (fun i => ↑(0 : ℝ) + Complex.I * ↑(y i)) ∈ TubeDomain (LShape r R) :=
      (mem_TubeDomain_pure_imag (LShape r R) y).mpr hy
    have h_norm_shift := bochner_c_eps_norm_le r R hr hR f hf_holo hf_bound ε hε y hy_tube ξ
    have h_norm_prod :
        ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ =
        ‖bochner_fourier_transform_eps f ε y ξ‖ * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h_norm_prod_r2 :
        ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ =
        ‖bochner_fourier_transform_eps f ε y ξ‖ * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
      rw [h_norm_shift, h_norm_prod]
    have h_dec := h_decay ξ
    rw [h_norm_prod_r2] at h_dec
    calc ‖bochner_fourier_transform_eps f ε y ξ‖
      _ = (‖bochner_fourier_transform_eps f ε y ξ‖ * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) *
          Real.exp (-(y 0 * ξ 0 + y 1 * ξ 1)) := by
        rw [mul_assoc, ← Real.exp_add]
        have : (y 0 * ξ 0 + y 1 * ξ 1) + -(y 0 * ξ 0 + y 1 * ξ 1) = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
      _ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := h_dec
  exact Integrable.mono' h_bound h_meas h_le

lemma bochner_fourier_inversion_2d (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) (x₀ : Fin 2 → ℝ) :
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      bochner_fourier_transform_eps f ε y ξ *
      Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) =
    bochner_f_eps f ε (fun i => ↑(x₀ i) + I * ↑(y i)) := by
  have h_eq : bochner_fourier_transform_eps f ε y =
      fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) :=
    bochner_fourier_transform_eps_eq f ε y
  rw [h_eq]
  let φ : (Fin 2 → ℝ) → ℂ := fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))
  exact fourier_inversion_2d φ x₀
    (bochner_f_eps_cont_of_holo r R f hf_holo ε y hy)
    (bochner_f_eps_integrable_of_holo r R f hf_holo hf_bound ε hε y hy)
    (bochner_fourier_transform_eps_integrable r R hr hR f hf_holo hf_bound ε hε y hy)

lemma bochner_F_eps_eq_f (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R)) := by
  intro z hz
  rw [bochner_F_eps_eq_standard_fourier_inv r R hr hR f hf_holo hf_bound ε hε z hz]
  have hy : (fun i => (z i).im) ∈ LShape r R := hz
  have h_inv := bochner_fourier_inversion_2d r R hr hR f hf_holo hf_bound ε hε
    (fun i => (z i).im) hy (fun i => (z i).re)
  have hz_rep : (fun i => ↑((z i).re) + I * ↑((z i).im)) = z := by
    ext i
    rw [mul_comm I, Complex.re_add_im]
  rw [hz_rep] at h_inv
  exact h_inv

lemma bochner_f_eps_tendsto (f : (Fin 2 → ℂ) → ℂ) (z : Fin 2 → ℂ) :
    Tendsto (fun ε : ℝ => bochner_f_eps f ε z) (𝓝[>] 0) (𝓝 (f z)) := by
  unfold bochner_f_eps
  have h_exp : Tendsto (fun ε : ℝ => Complex.exp (-↑ε * (z 0 ^ 2 + z 1 ^ 2))) (𝓝[>] 0) (𝓝 1) := by
    have h_inner : Tendsto (fun ε : ℝ => - (ε : ℂ) * (z 0 ^ 2 + z 1 ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have h_cont : Continuous (fun ε : ℝ => - (ε : ℂ) * (z 0 ^ 2 + z 1 ^ 2)) :=
        (Complex.continuous_ofReal.neg).mul continuous_const
      have ht := h_cont.tendsto (0 : ℝ)
      simp only [Complex.ofReal_zero, neg_zero, zero_mul] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    have h_exp_cont := Complex.continuous_exp.tendsto (0 : ℂ)
    rw [Complex.exp_zero] at h_exp_cont
    exact h_exp_cont.comp h_inner
  have h_mul := h_exp.const_mul (f z)
  rw [mul_one] at h_mul
  exact h_mul

lemma bochner_F_eps_tendsto_on_tube (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (h_eq_eps : ∀ ε > 0, EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R)))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShape r R)) :
    Tendsto (fun ε : ℝ => bochner_F_eps f ε r R z) (𝓝[>] 0) (𝓝 (f z)) := by
  have h_eq : (fun ε : ℝ => bochner_F_eps f ε r R z) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => bochner_f_eps f ε z) := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    exact h_eq_eps ε hε hz
  exact (bochner_f_eps_tendsto f z).congr' h_eq.symm

noncomputable def bochner_F_limit (f : (Fin 2 → ℂ) → ℂ) (r R : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => bochner_F_eps f ε r R z)

lemma limUnder_congr {X α : Type*} [TopologicalSpace X] [Nonempty X]
    {F : Filter α} {g h : α → X} (h_eq : g =ᶠ[F] h) :
    limUnder F g = limUnder F h := by
  dsimp [limUnder]
  rw [Filter.map_congr h_eq]

lemma bochner_F_limit_eq_on_tube (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (h_eq_eps : ∀ ε > 0,
      EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R))) :
    EqOn (bochner_F_limit f r R) f (TubeDomain (LShape r R)) := by
  intro z hz
  dsimp [bochner_F_limit]
  have h_tendsto := bochner_F_eps_tendsto_on_tube r R f h_eq_eps z hz
  exact h_tendsto.limUnder_eq

lemma differentiableOn_cauchy_integral {f : ℂ → ℂ} {c : ℂ} {R : NNReal}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    DifferentiableOn ℂ
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (Metric.ball c R) := by
  intro w hw
  have hw' : w ∈ Metric.eball c R := by
    rw [Metric.eball_coe]
    exact hw
  have h_series := hasFPowerSeriesOn_cauchy_integral hf hR
  have h_an : AnalyticAt ℂ (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w :=
    h_series.analyticAt_of_mem hw'
  exact h_an.differentiableAt.differentiableWithinAt

lemma differentiableOn_circleIntegral_sub_inv_smul {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    DifferentiableOn ℂ
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (Metric.ball c R) := by
  lift R to NNReal using hR.le
  exact differentiableOn_cauchy_integral hf hR

lemma differentiableAt_circleIntegral_sub_inv_smul {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hR : 0 < R) {w : ℂ} (hw : w ∈ Metric.ball c R) :
    DifferentiableAt ℂ (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
  have hd := differentiableOn_circleIntegral_sub_inv_smul hf hR
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hw)

lemma isOpen_slice0 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U) (z : Fin 2 → ℂ) :
    IsOpen {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ U} := by
  let g : ℂ → (Fin 2 → ℂ) := fun w i => if i = 0 then w else z 1
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    dsimp [g]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  exact hU.preimage hg

lemma exists_ball_subset_slice0 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (z : Fin 2 → ℂ) (hz : z ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (z 0) ρ ⊆
      {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ U} := by
  have h_open := isOpen_slice0 hU z
  have hz0_mem : z 0 ∈ {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ U} := by
    dsimp
    have hz_eq : (fun i => if i = 0 then z 0 else z 1) = z := by
      ext i
      fin_cases i <;> simp
    rw [hz_eq]
    exact hz
  rcases Metric.isOpen_iff.mp h_open (z 0) hz0_mem with ⟨ρ, hρ, h_sub⟩
  exact ⟨ρ, hρ, h_sub⟩

lemma isOpen_slice1 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U) (z : Fin 2 → ℂ) :
    IsOpen {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ U} := by
  let g : ℂ → (Fin 2 → ℂ) := fun w i => if i = 1 then w else z 0
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    dsimp [g]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  exact hU.preimage hg

lemma exists_ball_subset_slice1 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (z : Fin 2 → ℂ) (hz : z ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (z 1) ρ ⊆
      {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ U} := by
  have h_open := isOpen_slice1 hU z
  have hz1_mem : z 1 ∈ {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ U} := by
    dsimp
    have hz_eq : (fun i => if i = 1 then z 1 else z 0) = z := by
      ext i
      fin_cases i <;> simp
    rw [hz_eq]
    exact hz
  rcases Metric.isOpen_iff.mp h_open (z 1) hz1_mem with ⟨ρ, hρ, h_sub⟩
  exact ⟨ρ, hρ, h_sub⟩

lemma differentiable_slice_of_cauchy_representation (U : Set (Fin 2 → ℂ))
    (F : (Fin 2 → ℂ) → ℂ)
    (h_slice0 : ∀ z ∈ U, ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      z 0 ∈ Metric.ball c R ∧
      ∃ g : ℂ → ℂ, CircleIntegrable g c R ∧
        ∀ w ∈ Metric.ball c R, F (fun i => if i = 0 then w else z 1) =
          (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) :
    ∀ z ∈ U, DifferentiableAt ℂ (fun w => F (fun i => if i = 0 then w else z 1)) (z 0) := by
  intro z hz
  rcases h_slice0 z hz with ⟨c, R, hR, hz0, g, hg, hF⟩
  have hd := differentiableAt_circleIntegral_sub_inv_smul hg hR hz0
  have h_nhds : Metric.ball c R ∈ 𝓝 (z 0) := Metric.isOpen_ball.mem_nhds hz0
  have h_eq : (fun w => F (fun i => if i = 0 then w else z 1)) =ᶠ[𝓝 (z 0)]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) := by
    apply Filter.eventually_of_mem h_nhds
    intro w hw
    exact hF w hw
  exact hd.congr_of_eventuallyEq h_eq

lemma differentiable_slice1_of_cauchy_representation (U : Set (Fin 2 → ℂ))
    (F : (Fin 2 → ℂ) → ℂ)
    (h_slice1 : ∀ z ∈ U, ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      z 1 ∈ Metric.ball c R ∧
      ∃ g : ℂ → ℂ, CircleIntegrable g c R ∧
        ∀ w ∈ Metric.ball c R, F (fun i => if i = 1 then w else z 0) =
          (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) :
    ∀ z ∈ U, DifferentiableAt ℂ (fun w => F (fun i => if i = 1 then w else z 0)) (z 1) := by
  intro z hz
  rcases h_slice1 z hz with ⟨c, R, hR, hz1, g, hg, hF⟩
  have hd := differentiableAt_circleIntegral_sub_inv_smul hg hR hz1
  have h_nhds : Metric.ball c R ∈ 𝓝 (z 1) := Metric.isOpen_ball.mem_nhds hz1
  have h_eq : (fun w => F (fun i => if i = 1 then w else z 0)) =ᶠ[𝓝 (z 1)]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) := by
    apply Filter.eventually_of_mem h_nhds
    intro w hw
    exact hF w hw
  exact hd.congr_of_eventuallyEq h_eq

lemma differentiableOn_of_differentiableAt_all (U : Set (Fin 2 → ℂ))
    (F : (Fin 2 → ℂ) → ℂ) (h_diff : ∀ z ∈ U, DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F U := by
  intro z hz
  exact (h_diff z hz).differentiableWithinAt

lemma bochner_F_eps_slice0_cauchy_rep (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      z 0 ∈ Metric.ball c ρ ∧
      let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 0 then w else z 1)
      CircleIntegrable F_slice c ρ ∧
      ∀ w ∈ Metric.ball c ρ, F_slice w =
        (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ), (ζ - w)⁻¹ • F_slice ζ := by
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases exists_ball_subset_slice0 hU_open z hz with ⟨ρ0, hρ0, h_sub0⟩
  let ρ := ρ0 / 2
  have hρ : 0 < ρ := half_pos hρ0
  refine ⟨z 0, ρ, hρ, Metric.mem_ball_self hρ, ?_⟩
  dsimp
  let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 0 then w else z 1)
  have h_cball : Metric.closedBall (z 0) ρ ⊆ Metric.ball (z 0) ρ0 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    dsimp [ρ] at hw
    linarith
  have h_cball_sub : Metric.closedBall (z 0) ρ ⊆
      {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ TubeDomain (LShapeConvexHull r R)} :=
    h_cball.trans h_sub0
  have h_diff_slice : DifferentiableOn ℂ F_slice (Metric.closedBall (z 0) ρ) := by
    let φ : ℂ → (Fin 2 → ℂ) := fun w i => if i = 0 then w else z 1
    have hφ_diff : Differentiable ℂ φ := by
      apply differentiable_pi.mpr
      intro i
      dsimp [φ]
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    have h_comp : F_slice = (bochner_F_eps f ε r R) ∘ φ := rfl
    rw [h_comp]
    apply (h_holo_eps ε hε).comp hφ_diff.differentiableOn h_cball_sub
  have h_ci : CircleIntegrable F_slice (z 0) ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    exact h_diff_slice.continuousOn.mono Metric.sphere_subset_closedBall
  refine ⟨h_ci, ?_⟩
  intro w hw
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff_slice hw
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  calc F_slice w
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) • F_slice w) := by
      rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 0, ρ), (ζ - w)⁻¹ • F_slice ζ := by
      rw [h_cauchy]

lemma bochner_F_eps_slice1_cauchy_rep (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      z 1 ∈ Metric.ball c ρ ∧
      let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 1 then w else z 0)
      CircleIntegrable F_slice c ρ ∧
      ∀ w ∈ Metric.ball c ρ, F_slice w =
        (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ), (ζ - w)⁻¹ • F_slice ζ := by
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases exists_ball_subset_slice1 hU_open z hz with ⟨ρ0, hρ0, h_sub0⟩
  let ρ := ρ0 / 2
  have hρ : 0 < ρ := half_pos hρ0
  refine ⟨z 1, ρ, hρ, Metric.mem_ball_self hρ, ?_⟩
  dsimp
  let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 1 then w else z 0)
  have h_cball : Metric.closedBall (z 1) ρ ⊆ Metric.ball (z 1) ρ0 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    dsimp [ρ] at hw
    linarith
  have h_cball_sub : Metric.closedBall (z 1) ρ ⊆
      {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ TubeDomain (LShapeConvexHull r R)} :=
    h_cball.trans h_sub0
  have h_diff_slice : DifferentiableOn ℂ F_slice (Metric.closedBall (z 1) ρ) := by
    let φ : ℂ → (Fin 2 → ℂ) := fun w i => if i = 1 then w else z 0
    have hφ_diff : Differentiable ℂ φ := by
      apply differentiable_pi.mpr
      intro i
      dsimp [φ]
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    have h_comp : F_slice = (bochner_F_eps f ε r R) ∘ φ := rfl
    rw [h_comp]
    apply (h_holo_eps ε hε).comp hφ_diff.differentiableOn h_cball_sub
  have h_ci : CircleIntegrable F_slice (z 1) ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    exact h_diff_slice.continuousOn.mono Metric.sphere_subset_closedBall
  refine ⟨h_ci, ?_⟩
  intro w hw
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff_slice hw
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  calc F_slice w
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) • F_slice w) := by
      rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 1, ρ), (ζ - w)⁻¹ • F_slice ζ := by
      rw [h_cauchy]

lemma osgood_fin2 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ) (h_cont : ContinuousOn f U)
    (h_diff0 : ∀ z ∈ U,
      DifferentiableAt ℂ (fun w => f (fun i => if i = 0 then w else z 1)) (z 0))
    (h_diff1 : ∀ z ∈ U,
      DifferentiableAt ℂ (fun w => f (fun i => if i = 1 then w else z 0)) (z 1))
    (z : Fin 2 → ℂ) (hz : z ∈ U) : DifferentiableAt ℂ f z := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let U' : Set (ℂ × ℂ) := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  let f' : ℂ × ℂ → ℂ := f ∘ e.symm
  have h_cont' : ContinuousOn f' U' :=
    h_cont.comp e.symm.continuous.continuousOn (fun _ hx => hx)
  have h_holo_x : ∀ (y : ℂ), DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'} := by
    intro y x hx
    have hx_U : (e.symm (x, y)) ∈ U := hx
    have hd := h_diff0 (e.symm (x, y)) hx_U
    have heq : (fun w => f' (w, y)) =
        (fun w => f (fun i => if i = 0 then w else (e.symm (x, y)) 1)) := by
      ext w
      change f (e.symm (w, y)) = f (fun i => if i = 0 then w else (e.symm (x, y)) 1)
      congr 1
      ext i
      fin_cases i <;> simp [e]
    rw [heq]
    have hz0 : (e.symm (x, y)) 0 = x := by simp [e]
    rw [← hz0]
    exact hd.differentiableWithinAt
  have h_holo_y : ∀ (x : ℂ), DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'} := by
    intro x y hy
    have hy_U : (e.symm (x, y)) ∈ U := hy
    have hd := h_diff1 (e.symm (x, y)) hy_U
    have heq : (fun w => f' (x, w)) =
        (fun w => f (fun i => if i = 1 then w else (e.symm (x, y)) 0)) := by
      ext w
      change f (e.symm (x, w)) = f (fun i => if i = 1 then w else (e.symm (x, y)) 0)
      congr 1
      ext i
      fin_cases i <;> simp [e]
    rw [heq]
    have hz1 : (e.symm (x, y)) 1 = y := by simp [e]
    rw [← hz1]
    exact hd.differentiableWithinAt
  have h_diff_f' : DifferentiableOn ℂ f' U' := Analysis.osgood_2d hU' f' h_cont' h_holo_x h_holo_y
  have hz_U' : e z ∈ U' := by
    simp only [U', mem_preimage, ContinuousLinearEquiv.symm_apply_apply, hz]
  have hd_at' : DifferentiableAt ℂ f' (e z) :=
    (h_diff_f' (e z) hz_U').differentiableAt (hU'.mem_nhds hz_U')
  have heq : f = f' ∘ e := by
    ext w
    change f w = f (e.symm (e w))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [heq]
  exact hd_at'.comp z e.differentiableAt

lemma norm_le_on_horizontal_strip_of_bdd {a b C K : ℝ} (hab : a < b)
    {g : ℂ → ℂ}
    (hg_diff : DifferentiableOn ℂ g (Complex.im ⁻¹' Set.Ioo a b))
    (hg_cont : ContinuousOn g (Complex.im ⁻¹' Set.Icc a b))
    (hg_bdd : ∀ w : ℂ, w.im ∈ Set.Ioo a b → ‖g w‖ ≤ K)
    (hle_a : ∀ w : ℂ, w.im = a → ‖g w‖ ≤ C)
    (hle_b : ∀ w : ℂ, w.im = b → ‖g w‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.im) (hzb : z.im ≤ b) :
    ‖g z‖ ≤ C := by
  have h_cl : closure (Complex.im ⁻¹' Set.Ioo a b) ⊆ Complex.im ⁻¹' Set.Icc a b :=
    closure_minimal (fun _ hw => ⟨hw.1.le, hw.2.le⟩) (isClosed_Icc.preimage Complex.continuous_im)
  have hfd : DiffContOnCl ℂ g (Complex.im ⁻¹' Set.Ioo a b) := ⟨hg_diff, hg_cont.mono h_cl⟩
  have hB : ∃ c < Real.pi / (b - a), ∃ B,
      g =O[Filter.comap (abs ∘ Complex.re) Filter.atTop ⊓ 𝓟 (Complex.im ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.re|)) := by
    refine ⟨0, div_pos Real.pi_pos (sub_pos.mpr hab), 0, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨max K 0,
      Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun w hw => ?_)⟩
    simp only [zero_mul, Real.exp_zero, Real.norm_eq_abs, abs_one, mul_one]
    exact (hg_bdd w hw).trans (le_max_left K 0)
  exact PhragmenLindelof.horizontal_strip hfd hB hle_a hle_b hza hzb

def bochner_diag_map (z : Fin 2 → ℂ) (w : ℂ) : Fin 2 → ℂ :=
  ![z 0 + w, z 1 - w]

lemma differentiable_bochner_diag_map (z : Fin 2 → ℂ) :
    Differentiable ℂ (bochner_diag_map z) := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact (differentiable_const (z 0)).add differentiable_id
  · exact (differentiable_const (z 1)).sub differentiable_id

lemma bochner_diag_map_zero (z : Fin 2 → ℂ) :
    bochner_diag_map z 0 = z := by
  ext i
  fin_cases i <;> simp [bochner_diag_map]

lemma bochner_diag_map_im (z : Fin 2 → ℂ) (w : ℂ) :
    (fun i => (bochner_diag_map z w i).im) = ![(z 0).im + w.im, (z 1).im - w.im] := by
  ext i
  fin_cases i <;> simp [bochner_diag_map]

lemma bochner_F_eps_strip_bdd_fixed_eps (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ) {t₁ t₂ : ℝ}
    (ht_hull : ∀ t ∈ Set.Icc t₁ t₂, ![(z 0).im + t, (z 1).im - t] ∈ LShapeConvexHull r R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, w.im ∈ Set.Icc t₁ t₂ →
      ‖bochner_F_eps f ε r R (bochner_diag_map z w)‖ ≤ K := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r / 2) ξ *
      ↑(Real.exp ((r / 2) * ξ 0 + (r / 2) * ξ 1))
  have h_loc : ∀ t : Set.Icc t₁ t₂, ∃ ρ > 0, ∃ B ≥ 0,
      ∀ w : ℂ, w.im ∈ Metric.ball (t : ℝ) ρ →
        ‖bochner_F_eps f ε r R (bochner_diag_map z w)‖ ≤ B := by
    intro ⟨t, ht⟩
    let yt : Fin 2 → ℝ := ![(z 0).im + t, (z 1).im - t]
    rcases bochner_c_eps_local_exp_decay r R hr hR f hf_holo hf_bound ε hε yt (ht_hull t ht) with
      ⟨Ct, δt, hCt, hδt, h_dec⟩
    let ρ := δt / 4
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hδt2 : 0 < δt / 2 := half_pos hδt
    let g_dom : (Fin 2 → ℝ) → ℝ := fun ξ => Ct * Real.exp (-(δt / 2) * (|ξ 0| + |ξ 1|))
    have hg_int : Integrable g_dom volume := (integrable_exp_neg_abs_2d (δt / 2) hδt2).const_mul Ct
    let B := (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ ξ, g_dom ξ
    have hB : 0 ≤ B := by
      have h_int_nn : 0 ≤ ∫ ξ, g_dom ξ :=
        integral_nonneg fun ξ => mul_nonneg hCt (Real.exp_pos _).le
      dsimp [B]
      positivity
    refine ⟨ρ, hρ, B, hB, ?_⟩
    intro w hw
    have hw_abs : |w.im - t| < δt / 4 := by
      simpa [Metric.mem_ball, Real.dist_eq, ρ] using hw
    unfold bochner_F_eps
    have h_pi_nn : 0 ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ := by positivity
    have h_inv_nn : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h_inv_nn]
    refine mul_le_mul_of_nonneg_left ?_ h_pi_nn
    refine norm_integral_le_of_norm_le hg_int (Filter.Eventually.of_forall fun ξ => ?_)
    have hc_eq : bochner_fourier_transform_eps f ε (fun _ => r / 2) ξ *
        ↑(Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1)) = c ξ := rfl
    rw [hc_eq, norm_mul]
    have h_exp_norm : ‖Complex.exp (I * (bochner_diag_map z w 0 * ↑(ξ 0) +
        bochner_diag_map z w 1 * ↑(ξ 1)))‖ =
        Real.exp (-(((z 0).im + w.im) * ξ 0 + ((z 1).im - w.im) * ξ 1)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [bochner_diag_map]
    rw [h_exp_norm]
    have h_diff_im : -(((z 0).im + w.im) * ξ 0 + ((z 1).im - w.im) * ξ 1) ≤
        -(yt 0 * ξ 0 + yt 1 * ξ 1) + (δt / 2) * (|ξ 0| + |ξ 1|) := by
      have h0 : -(w.im - t) * ξ 0 ≤ |w.im - t| * |ξ 0| := by
        calc -(w.im - t) * ξ 0 ≤ |-(w.im - t) * ξ 0| := le_abs_self _
          _ = |w.im - t| * |ξ 0| := by rw [abs_mul, abs_neg]
      have h1 : (w.im - t) * ξ 1 ≤ |w.im - t| * |ξ 1| := by
        calc (w.im - t) * ξ 1 ≤ |(w.im - t) * ξ 1| := le_abs_self _
          _ = |w.im - t| * |ξ 1| := abs_mul _ _
      have h_lin : -(((z 0).im + w.im) * ξ 0 + ((z 1).im - w.im) * ξ 1) =
          -(yt 0 * ξ 0 + yt 1 * ξ 1) + (-(w.im - t) * ξ 0 + (w.im - t) * ξ 1) := by
        dsimp [yt]
        ring
      rw [h_lin]
      have h_nonneg : 0 ≤ |ξ 0| + |ξ 1| := by positivity
      nlinarith
    calc ‖c ξ‖ * Real.exp (-(((z 0).im + w.im) * ξ 0 + ((z 1).im - w.im) * ξ 1))
      _ ≤ ‖c ξ‖ * Real.exp (-(yt 0 * ξ 0 + yt 1 * ξ 1) + (δt / 2) * (|ξ 0| + |ξ 1|)) := by
        gcongr
      _ = (‖c ξ‖ * Real.exp (-(yt 0 * ξ 0 + yt 1 * ξ 1))) *
          Real.exp ((δt / 2) * (|ξ 0| + |ξ 1|)) := by
        rw [Real.exp_add, mul_assoc]
      _ ≤ (Ct * Real.exp (-δt * (|ξ 0| + |ξ 1|))) *
          Real.exp ((δt / 2) * (|ξ 0| + |ξ 1|)) :=
        mul_le_mul_of_nonneg_right (h_dec ξ) (Real.exp_pos _).le
      _ = g_dom ξ := by
        dsimp [g_dom]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  choose ρ hρ B hB hB_bd using h_loc
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun i : Set.Icc t₁ t₂ => Metric.ball (i : ℝ) (ρ i))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hρ ⟨x, hx⟩)⟩)
  refine ⟨∑ i ∈ s, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro w hw
  have hw_cov := hs hw
  rw [Set.mem_iUnion₂] at hw_cov
  rcases hw_cov with ⟨i, hi_s, hw_ball⟩
  exact (hB_bd i w hw_ball).trans (Finset.single_le_sum (fun j _ => hB j) hi_s)

lemma bochner_F_eps_norm_le_on_LShape (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    {M : ℝ} (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1)
    {z : Fin 2 → ℂ} (hz : z ∈ TubeDomain (LShape r R)) :
    ‖bochner_F_eps f ε r R z‖ ≤ max M 0 * Real.exp (2 * R ^ 2) := by
  rw [bochner_F_eps_eq_f r R hr hR f hf_holo ⟨M, hM⟩ ε hε hz]
  unfold bochner_f_eps
  rw [norm_mul]
  let x : Fin 2 → ℝ := fun i => (z i).re
  let y : Fin 2 → ℝ := fun i => (z i).im
  have hz_rep : z = fun i => (x i : ℂ) + I * (y i : ℂ) := by
    ext i
    dsimp [x, y]
    rw [mul_comm I, Complex.re_add_im]
  have h_gauss : ‖Complex.exp (-↑ε * (z 0 ^ 2 + z 1 ^ 2))‖ =
      Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) := by
    conv_lhs => rw [hz_rep]
    exact norm_exp_gaussian_decay ε x y
  rw [h_gauss]
  have hy_box := LShape_subset_box hR (show y ∈ LShape r R from hz)
  have hy0_pos : 0 < y 0 := (hy_box 0).1
  have hy0_lt : y 0 < R := (hy_box 0).2
  have hy1_pos : 0 < y 1 := (hy_box 1).1
  have hy1_lt : y 1 < R := (hy_box 1).2
  have h_re_le : Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    nlinarith
  have h_im_le : Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) ≤ Real.exp (2 * R ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hy0_sq : y 0 ^ 2 ≤ R ^ 2 := by nlinarith
    have hy1_sq : y 1 ^ 2 ≤ R ^ 2 := by nlinarith
    nlinarith
  have hf_le : ‖f z‖ ≤ max M 0 := (hM z).trans (le_max_left M 0)
  calc ‖f z‖ * (Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)))
    _ ≤ max M 0 * (1 * Real.exp (2 * R ^ 2)) := by
      refine mul_le_mul hf_le (mul_le_mul h_re_le h_im_le (Real.exp_pos _).le zero_le_one)
        (by positivity) (le_max_right M 0)
    _ = max M 0 * Real.exp (2 * R ^ 2) := by ring

lemma bochner_f_eps_diff_le_on_LShape (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    {M : ℝ} (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    {ε₁ ε₂ S : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hS₁ : ε₁ * S ≤ 1) (hS₂ : ε₂ * S ≤ 1)
    {z : Fin 2 → ℂ} (hz : z ∈ TubeDomain (LShape r R))
    (hz_sq : ‖z 0 ^ 2 + z 1 ^ 2‖ ≤ S) :
    ‖bochner_F_eps f ε₁ r R z - bochner_F_eps f ε₂ r R z‖ ≤
      max M 0 * (2 * (ε₁ * S) + 2 * (ε₂ * S)) := by
  rw [bochner_F_eps_eq_f r R hr hR f hf_holo ⟨M, hM⟩ ε₁ hε₁ hz,
      bochner_F_eps_eq_f r R hr hR f hf_holo ⟨M, hM⟩ ε₂ hε₂ hz]
  unfold bochner_f_eps
  let s : ℂ := z 0 ^ 2 + z 1 ^ 2
  have h_alg : f z * Complex.exp (-↑ε₁ * s) - f z * Complex.exp (-↑ε₂ * s) =
      f z * ((Complex.exp (-↑ε₁ * s) - 1) - (Complex.exp (-↑ε₂ * s) - 1)) := by ring
  change ‖f z * Complex.exp (-↑ε₁ * s) - f z * Complex.exp (-↑ε₂ * s)‖ ≤ _
  rw [h_alg, norm_mul]
  have hn1 : ‖-↑ε₁ * s‖ ≤ ε₁ * S := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε₁.le]
    exact mul_le_mul_of_nonneg_left hz_sq hε₁.le
  have hn2 : ‖-↑ε₂ * s‖ ≤ ε₂ * S := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε₂.le]
    exact mul_le_mul_of_nonneg_left hz_sq hε₂.le
  have he1 : ‖Complex.exp (-↑ε₁ * s) - 1‖ ≤ 2 * (ε₁ * S) :=
    (Complex.norm_exp_sub_one_le (hn1.trans hS₁)).trans (by linarith)
  have he2 : ‖Complex.exp (-↑ε₂ * s) - 1‖ ≤ 2 * (ε₂ * S) :=
    (Complex.norm_exp_sub_one_le (hn2.trans hS₂)).trans (by linarith)
  have h_sub : ‖(Complex.exp (-↑ε₁ * s) - 1) - (Complex.exp (-↑ε₂ * s) - 1)‖ ≤
      2 * (ε₁ * S) + 2 * (ε₂ * S) :=
    (norm_sub_le _ _).trans (add_le_add he1 he2)
  exact mul_le_mul ((hM z).trans (le_max_left M 0)) h_sub (norm_nonneg _) (le_max_right M 0)

lemma bochner_F_eps_hull_strip_setup (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    {M : ℝ} (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (zstar : Fin 2 → ℂ) (hzstar : zstar ∈ TubeDomain (LShapeConvexHull r R))
    (hz_LS : zstar ∉ TubeDomain (LShape r R)) :
    ∃ (t₁ t₂ σ η : ℝ), t₁ < 0 ∧ 0 < t₂ ∧ 0 < σ ∧ 0 < η ∧
      Metric.ball zstar η ⊆ TubeDomain (LShapeConvexHull r R) ∧
      (∀ z ∈ Metric.ball zstar η,
        ![(z 0).im + t₁, (z 1).im - t₁] ∈ LShape r R ∧
        ![(z 0).im + t₂, (z 1).im - t₂] ∈ LShape r R) ∧
      (∀ ε > 0, ∀ z ∈ Metric.ball zstar η,
        DifferentiableOn ℂ (fun w => bochner_F_eps f ε r R (bochner_diag_map z w))
          (Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ))) ∧
      (∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ z ∈ Metric.ball zstar η, ∀ w : ℂ, w.im ∈ Set.Icc t₁ t₂ →
        ‖bochner_F_eps f ε r R (bochner_diag_map z w)‖ ≤ max M 0 * Real.exp (2 * R ^ 2)) := by
  have h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)) :=
    fun ε hε => bochner_F_eps_holo r R hr hR f hf_holo ⟨M, hM⟩ ε hε
  let ystar : Fin 2 → ℝ := fun i => (zstar i).im
  have hystar_bounds := mem_LShapeConvexHull_bounds hR hzstar
  have hystar_sum := mem_LShapeConvexHull_sum_lt hzstar
  have hystar0_ge_r : r ≤ ystar 0 := by
    by_contra hlt
    push Not at hlt
    exact hz_LS (Or.inl ⟨hystar_bounds.1, hlt, hystar_bounds.2.2.1, hystar_bounds.2.2.2⟩)
  have hystar1_ge_r : r ≤ ystar 1 := by
    by_contra hlt
    push Not at hlt
    exact hz_LS (Or.inr ⟨hystar_bounds.1, hystar_bounds.2.1, hystar_bounds.2.2.1, hlt⟩)
  let rem := r + R - (ystar 0 + ystar 1)
  have hrem_pos : 0 < rem := by dsimp [rem]; linarith
  let δ := (1 / 8 : ℝ) * min r rem
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have h8δ_r : 8 * δ ≤ r := by
    have : min r rem ≤ r := min_le_left _ _
    dsimp [δ]; linarith
  have h8δ_rem : 8 * δ ≤ rem := by
    have : min r rem ≤ rem := min_le_right _ _
    dsimp [δ]; linarith
  let t₁ := (r - 2 * δ) - ystar 0
  let t₂ := ystar 1 - (r - 2 * δ)
  have ht₁_neg : t₁ < 0 := by dsimp [t₁]; linarith
  have ht₂_pos : 0 < t₂ := by dsimp [t₂]; linarith
  have ht₁_lt_t₂ : t₁ < t₂ := ht₁_neg.trans ht₂_pos
  let σ := δ / 2
  have hσ_pos : 0 < σ := half_pos hδ_pos
  have h_open_hull : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases Metric.isOpen_iff.mp h_open_hull zstar hzstar with ⟨η_open, hη_open, h_sub_hull0⟩
  let η := min (δ / 2) η_open
  have hη_pos : 0 < η := lt_min (half_pos hδ_pos) hη_open
  have h_sub_hull : Metric.ball zstar η ⊆ TubeDomain (LShapeConvexHull r R) :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans h_sub_hull0
  have hz_im_close : ∀ z ∈ Metric.ball zstar η,
      |(z 0).im - ystar 0| < δ / 2 ∧ |(z 1).im - ystar 1| < δ / 2 := by
    intro z hz
    have hdist : ‖z - zstar‖ < δ / 2 := by
      have hlt := (Metric.mem_ball.mp hz).trans_le (min_le_left _ _)
      simpa [dist_eq_norm] using hlt
    constructor
    · calc |(z 0).im - ystar 0| = |(z 0 - zstar 0).im| := by simp [ystar]
        _ ≤ ‖z 0 - zstar 0‖ := Complex.abs_im_le_norm _
        _ ≤ ‖z - zstar‖ := norm_le_pi_norm (z - zstar) 0
        _ < δ / 2 := hdist
    · calc |(z 1).im - ystar 1| = |(z 1 - zstar 1).im| := by simp [ystar]
        _ ≤ ‖z 1 - zstar 1‖ := Complex.abs_im_le_norm _
        _ ≤ ‖z - zstar‖ := norm_le_pi_norm (z - zstar) 1
        _ < δ / 2 := hdist
  have h_end_low : ∀ z ∈ Metric.ball zstar η, ∀ s ∈ Set.Icc (t₁ - σ) t₁,
      ![(z 0).im + s, (z 1).im - s] ∈ LShape r R := by
    intro z hz s ⟨hs1, hs2⟩
    have ⟨hc0, hc1⟩ := hz_im_close z hz
    have hc0' := abs_lt.mp hc0
    have hc1' := abs_lt.mp hc1
    left
    dsimp [LShape, t₁, σ, rem, ystar] at hs1 hs2 h8δ_rem hystar0_ge_r hystar1_ge_r hc0' hc1' ⊢
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have h_end_high : ∀ z ∈ Metric.ball zstar η, ∀ s ∈ Set.Icc t₂ (t₂ + σ),
      ![(z 0).im + s, (z 1).im - s] ∈ LShape r R := by
    intro z hz s ⟨hs1, hs2⟩
    have ⟨hc0, hc1⟩ := hz_im_close z hz
    have hc0' := abs_lt.mp hc0
    have hc1' := abs_lt.mp hc1
    right
    dsimp [LShape, t₂, σ, rem, ystar] at hs1 hs2 h8δ_rem hystar0_ge_r hystar1_ge_r hc0' hc1' ⊢
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have h_seg_hull : ∀ z ∈ Metric.ball zstar η, ∀ t ∈ Set.Icc (t₁ - σ) (t₂ + σ),
      ![(z 0).im + t, (z 1).im - t] ∈ LShapeConvexHull r R := by
    intro z hz t ht
    let a := t₁ - σ
    let b := t₂ + σ
    have hab : a < b := by dsimp [a, b]; linarith
    have ha_LS : ![(z 0).im + a, (z 1).im - a] ∈ LShapeConvexHull r R :=
      subset_convexHull ℝ (LShape r R) (h_end_low z hz a ⟨le_rfl, by dsimp [a]; linarith⟩)
    have hb_LS : ![(z 0).im + b, (z 1).im - b] ∈ LShapeConvexHull r R :=
      subset_convexHull ℝ (LShape r R) (h_end_high z hz b ⟨by dsimp [b]; linarith, le_rfl⟩)
    let θ := (t - a) / (b - a)
    have hθ0 : 0 ≤ θ := div_nonneg (by dsimp [a] at ht ⊢; linarith [ht.1]) (sub_nonneg.mpr hab.le)
    have hθ1 : 0 ≤ 1 - θ := by
      have : θ ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by dsimp [b] at ht ⊢; linarith [ht.2])
      linarith
    have h_conv := (convex_convexHull ℝ (LShape r R)) ha_LS hb_LS hθ1 hθ0 (by ring)
    have h_pt_eq : (1 - θ) • ![(z 0).im + a, (z 1).im - a] +
        θ • ![(z 0).im + b, (z 1).im - b] = ![(z 0).im + t, (z 1).im - t] := by
      have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
      ext i
      fin_cases i
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        dsimp [θ]
        field_simp [hba]
        ring
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        dsimp [θ]
        field_simp [hba]
        ring
    rwa [h_pt_eq] at h_conv
  have h_strip_diff : ∀ ε > 0, ∀ z ∈ Metric.ball zstar η,
      DifferentiableOn ℂ (fun w => bochner_F_eps f ε r R (bochner_diag_map z w))
        (Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ)) := by
    intro ε hε z hz
    apply (h_holo_eps ε hε).comp (differentiable_bochner_diag_map z).differentiableOn
    intro w hw
    change (fun i => (bochner_diag_map z w i).im) ∈ LShapeConvexHull r R
    rw [bochner_diag_map_im]
    exact h_seg_hull z hz w.im ⟨hw.1.le, hw.2.le⟩
  refine ⟨t₁, t₂, σ, η, ht₁_neg, ht₂_pos, hσ_pos, hη_pos, h_sub_hull,
    fun z hz => ⟨h_end_low z hz t₁ ⟨by linarith, le_rfl⟩,
      h_end_high z hz t₂ ⟨le_rfl, by linarith⟩⟩,
    h_strip_diff, ?_⟩
  intro ε ⟨hε_pos, hε_le⟩ z hz w hw
  have hd_wide := h_strip_diff ε hε_pos z hz
  have h_sub_Ioo : Complex.im ⁻¹' Set.Ioo t₁ t₂ ⊆ Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h_sub_Icc : Complex.im ⁻¹' Set.Icc t₁ t₂ ⊆ Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
    fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  rcases bochner_F_eps_strip_bdd_fixed_eps r R hr hR f hf_holo ⟨M, hM⟩ ε hε_pos z
    (t₁ := t₁) (t₂ := t₂)
    (fun t ht => h_seg_hull z hz t ⟨by linarith [ht.1], by linarith [ht.2]⟩) with ⟨K, _, hK⟩
  refine norm_le_on_horizontal_strip_of_bdd ht₁_lt_t₂
    (hd_wide.mono h_sub_Ioo)
    (hd_wide.continuousOn.mono h_sub_Icc)
    (fun u hu => hK u ⟨hu.1.le, hu.2.le⟩)
    (fun u hu => ?_) (fun u hu => ?_) hw.1 hw.2
  · apply bochner_F_eps_norm_le_on_LShape r R hr hR f hf_holo hM hε_pos hε_le
    change (fun i => (bochner_diag_map z u i).im) ∈ LShape r R
    rw [bochner_diag_map_im, hu]
    exact h_end_low z hz t₁ ⟨by linarith, le_rfl⟩
  · apply bochner_F_eps_norm_le_on_LShape r R hr hR f hf_holo hM hε_pos hε_le
    change (fun i => (bochner_diag_map z u i).im) ∈ LShape r R
    rw [bochner_diag_map_im, hu]
    exact h_end_high z hz t₂ ⟨le_rfl, by linarith⟩

lemma bochner_F_eps_local_uniform_cauchy (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (zstar : Fin 2 → ℂ) (hzstar : zstar ∈ TubeDomain (LShapeConvexHull r R)) :
    ∃ η > 0, Metric.ball zstar η ⊆ TubeDomain (LShapeConvexHull r R) ∧
      ∀ γ > 0, ∃ ε₀ > 0, ∀ ε₁ ∈ Set.Ioo 0 ε₀, ∀ ε₂ ∈ Set.Ioo 0 ε₀,
        ∀ z ∈ Metric.ball zstar η,
          ‖bochner_F_eps f ε₁ r R z - bochner_F_eps f ε₂ r R z‖ ≤ γ := by
  rcases hf_bound with ⟨M, hM⟩
  by_cases hz_LS : zstar ∈ TubeDomain (LShape r R)
  · have h_open_LS : IsOpen (TubeDomain (LShape r R)) := isOpen_TubeDomain (isOpen_LShape r R)
    rcases Metric.isOpen_iff.mp h_open_LS zstar hz_LS with ⟨η, hη, h_sub_LS⟩
    have h_sub_hull : Metric.ball zstar η ⊆ TubeDomain (LShapeConvexHull r R) :=
      fun z hz => subset_convexHull ℝ (LShape r R) (h_sub_LS hz)
    refine ⟨η, hη, h_sub_hull, ?_⟩
    intro γ hγ
    let S : ℝ := 2 * (‖zstar‖ + η) ^ 2 + 1
    have hS_pos : 0 < S := by dsimp [S]; positivity
    let ε₀ : ℝ := min (1 / S) (γ / (4 * (max M 0 + 1) * S))
    have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
    refine ⟨ε₀, hε₀, ?_⟩
    intro ε₁ hε₁ ε₂ hε₂ z hz
    have hz_in_LS : z ∈ TubeDomain (LShape r R) := h_sub_LS hz
    have hz_norm : ‖z‖ < ‖zstar‖ + η := by
      have hd : ‖z - zstar‖ < η := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
      calc ‖z‖ = ‖(z - zstar) + zstar‖ := by ring_nf
        _ ≤ ‖z - zstar‖ + ‖zstar‖ := norm_add_le _ _
        _ < η + ‖zstar‖ := by linarith
        _ = ‖zstar‖ + η := by ring
    have hz0 : ‖z 0‖ ≤ ‖zstar‖ + η := (norm_le_pi_norm z 0).trans hz_norm.le
    have hz1 : ‖z 1‖ ≤ ‖zstar‖ + η := (norm_le_pi_norm z 1).trans hz_norm.le
    have hz_sq : ‖z 0 ^ 2 + z 1 ^ 2‖ ≤ S := by
      calc ‖z 0 ^ 2 + z 1 ^ 2‖ ≤ ‖z 0 ^ 2‖ + ‖z 1 ^ 2‖ := norm_add_le _ _
        _ = ‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 := by simp [norm_pow]
        _ ≤ (‖zstar‖ + η) ^ 2 + (‖zstar‖ + η) ^ 2 := by
          nlinarith [norm_nonneg (z 0), norm_nonneg (z 1)]
        _ ≤ S := by dsimp [S]; linarith
    have hε₁_S : ε₁ * S ≤ 1 := by
      have hle : ε₁ ≤ 1 / S := hε₁.2.le.trans (min_le_left _ _)
      exact (mul_le_mul_of_nonneg_right hle hS_pos.le).trans
        (by rw [one_div, inv_mul_cancel₀ hS_pos.ne'])
    have hε₂_S : ε₂ * S ≤ 1 := by
      have hle : ε₂ ≤ 1 / S := hε₂.2.le.trans (min_le_left _ _)
      exact (mul_le_mul_of_nonneg_right hle hS_pos.le).trans
        (by rw [one_div, inv_mul_cancel₀ hS_pos.ne'])
    have h_bd := bochner_f_eps_diff_le_on_LShape r R hr hR f hf_holo hM hε₁.1 hε₂.1
      hε₁_S hε₂_S hz_in_LS hz_sq
    have h_lt_cap : ε₀ ≤ γ / (4 * (max M 0 + 1) * S) := min_le_right _ _
    have h_denom_pos : 0 < 4 * (max M 0 + 1) * S := by positivity
    have h_cap : 4 * (max M 0 + 1) * S * ε₀ ≤ γ := by
      have := (le_div_iff₀ h_denom_pos).mp h_lt_cap
      linarith
    calc ‖bochner_F_eps f ε₁ r R z - bochner_F_eps f ε₂ r R z‖
      _ ≤ max M 0 * (2 * (ε₁ * S) + 2 * (ε₂ * S)) := h_bd
      _ ≤ (max M 0 + 1) * (2 * (ε₀ * S) + 2 * (ε₀ * S)) := by
        have hε₁_pos : 0 < ε₁ := hε₁.1
        have hε₂_pos : 0 < ε₂ := hε₂.1
        have h1 : ε₁ * S ≤ ε₀ * S := mul_le_mul_of_nonneg_right hε₁.2.le hS_pos.le
        have h2 : ε₂ * S ≤ ε₀ * S := mul_le_mul_of_nonneg_right hε₂.2.le hS_pos.le
        have h_sum_le : 2 * (ε₁ * S) + 2 * (ε₂ * S) ≤ 2 * (ε₀ * S) + 2 * (ε₀ * S) := by linarith
        exact mul_le_mul (by linarith) h_sum_le (by positivity) (by positivity)
      _ = 4 * (max M 0 + 1) * S * ε₀ := by ring
      _ ≤ γ := h_cap
  · rcases bochner_F_eps_hull_strip_setup r R hr hR f hf_holo hM zstar hzstar hz_LS with
      ⟨t₁, t₂, σ, η, ht₁_neg, ht₂_pos, hσ_pos, hη_pos, h_sub_hull, h_ends,
        h_strip_diff, h_strip_unif_bd⟩
    have ht₁_lt_t₂ : t₁ < t₂ := ht₁_neg.trans ht₂_pos
    let M₀ := max M 0 * Real.exp (2 * R ^ 2)
    have hM₀_nonneg : 0 ≤ M₀ := by dsimp [M₀]; positivity
    refine ⟨η, hη_pos, h_sub_hull, ?_⟩
    intro γ hγ
    let T := max |t₁| |t₂|
    let E_T := Real.exp (T ^ 2)
    have hE_T_pos : 0 < E_T := Real.exp_pos _
    let L := max 1 ((2 * M₀ * E_T + 1) / γ)
    have hL_ge1 : 1 ≤ L := le_max_left _ _
    have hL_pos : 0 < L := zero_lt_one.trans_le hL_ge1
    let S := 2 * (‖zstar‖ + η + L + T) ^ 2 + 1
    have hS_pos : 0 < S := by dsimp [S]; positivity
    let ε₀ := min (1 : ℝ) (min (1 / S) (γ / (4 * (max M 0 + 1) * S * E_T)))
    have hε₀_pos : 0 < ε₀ := by dsimp [ε₀]; positivity
    refine ⟨ε₀, hε₀_pos, ?_⟩
    intro ε₁ hε₁ ε₂ hε₂ z hz
    have hε₁_pos : 0 < ε₁ := hε₁.1
    have hε₂_pos : 0 < ε₂ := hε₂.1
    have hε₁_le1 : ε₁ ≤ 1 := hε₁.2.le.trans (min_le_left _ _)
    have hε₂_le1 : ε₂ ≤ 1 := hε₂.2.le.trans (min_le_left _ _)
    let d : ℂ → ℂ := fun w =>
      (bochner_F_eps f ε₁ r R (bochner_diag_map z w) -
        bochner_F_eps f ε₂ r R (bochner_diag_map z w)) * Complex.exp (- w ^ 2)
    have hd_zero : bochner_F_eps f ε₁ r R z - bochner_F_eps f ε₂ r R z = d 0 := by
      simp [d, bochner_diag_map_zero]
    rw [hd_zero]
    have hd_wide : DifferentiableOn ℂ d (Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ)) := by
      have hexp : Differentiable ℂ (fun w : ℂ => Complex.exp (- w ^ 2)) :=
        Complex.differentiable_exp.comp ((differentiable_id.pow 2).neg)
      exact ((h_strip_diff ε₁ hε₁.1 z hz).sub
        (h_strip_diff ε₂ hε₂.1 z hz)).mul hexp.differentiableOn
    have h_sub_Ioo : Complex.im ⁻¹' Set.Ioo t₁ t₂ ⊆ Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h_sub_Icc : Complex.im ⁻¹' Set.Icc t₁ t₂ ⊆ Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h_im_T : ∀ w : ℂ, w.im ∈ Set.Icc t₁ t₂ → w.im ^ 2 ≤ T ^ 2 := by
      intro w hw
      have habs : |w.im| ≤ T := by
        rw [abs_le]
        constructor
        · have : -T ≤ -|t₁| := neg_le_neg (le_max_left _ _)
          linarith [le_abs_self (-t₁), abs_neg t₁, hw.1]
        · have : |t₂| ≤ T := le_max_right _ _
          linarith [le_abs_self t₂, hw.2]
      have hT_nn : 0 ≤ T := (abs_nonneg t₁).trans (le_max_left _ _)
      nlinarith [abs_nonneg w.im, sq_abs w.im]
    have hexp_norm : ∀ w : ℂ, ‖Complex.exp (- w ^ 2)‖ = Real.exp (- w.re ^ 2 + w.im ^ 2) := by
      intro w
      rw [Complex.norm_exp]
      congr 1
      have hw_eq : w = ↑w.re + I * ↑w.im := by rw [mul_comm I, Complex.re_add_im]
      conv_lhs => rw [hw_eq]
      rw [neg_re, sq_add_I_mul_re]
      ring
    have hd_bdd : ∀ w : ℂ, w.im ∈ Set.Ioo t₁ t₂ → ‖d w‖ ≤ 2 * M₀ * E_T := by
      intro w hw
      have hw_Icc : w.im ∈ Set.Icc t₁ t₂ := ⟨hw.1.le, hw.2.le⟩
      have hb1 := h_strip_unif_bd ε₁ ⟨hε₁.1, hε₁_le1⟩ z hz w hw_Icc
      have hb2 := h_strip_unif_bd ε₂ ⟨hε₂.1, hε₂_le1⟩ z hz w hw_Icc
      have hsub : ‖bochner_F_eps f ε₁ r R (bochner_diag_map z w) -
          bochner_F_eps f ε₂ r R (bochner_diag_map z w)‖ ≤ 2 * M₀ :=
        (norm_sub_le _ _).trans (by linarith)
      have hexp_le : ‖Complex.exp (- w ^ 2)‖ ≤ E_T := by
        rw [hexp_norm]
        apply Real.exp_le_exp.mpr
        have : 0 ≤ w.re ^ 2 := sq_nonneg _
        linarith [h_im_T w hw_Icc]
      dsimp [d]
      rw [norm_mul]
      calc ‖bochner_F_eps f ε₁ r R (bochner_diag_map z w) -
            bochner_F_eps f ε₂ r R (bochner_diag_map z w)‖ * ‖Complex.exp (- w ^ 2)‖
        _ ≤ (2 * M₀) * E_T := mul_le_mul hsub hexp_le (norm_nonneg _) (by positivity)
        _ = 2 * M₀ * E_T := by ring
    have hd_edge : ∀ w : ℂ,
        (w.im = t₁ ∨ w.im = t₂) →
        bochner_diag_map z w ∈ TubeDomain (LShape r R) →
        ‖d w‖ ≤ γ := by
      intro w hw_im hw_LS
      have hw_Icc : w.im ∈ Set.Icc t₁ t₂ := by
        rcases hw_im with h | h <;> rw [h]
        · exact ⟨le_rfl, ht₁_lt_t₂.le⟩
        · exact ⟨ht₁_lt_t₂.le, le_rfl⟩
      by_cases hw_re : L ≤ |w.re|
      · have hb1 := h_strip_unif_bd ε₁ ⟨hε₁.1, hε₁_le1⟩ z hz w hw_Icc
        have hb2 := h_strip_unif_bd ε₂ ⟨hε₂.1, hε₂_le1⟩ z hz w hw_Icc
        have hsub : ‖bochner_F_eps f ε₁ r R (bochner_diag_map z w) -
            bochner_F_eps f ε₂ r R (bochner_diag_map z w)‖ ≤ 2 * M₀ :=
          (norm_sub_le _ _).trans (by linarith)
        have hre_sq : L ^ 2 ≤ w.re ^ 2 := by
          have := mul_le_mul hw_re hw_re hL_pos.le (abs_nonneg w.re)
          rwa [← sq, ← sq, sq_abs] at this
        have hexp_le : ‖Complex.exp (- w ^ 2)‖ ≤ E_T * Real.exp (- L ^ 2) := by
          rw [hexp_norm, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          linarith [h_im_T w hw_Icc]
        have hL_exp : L ≤ Real.exp (L ^ 2) := by
          have h1 : L ≤ L ^ 2 := by nlinarith
          have h2 : L ^ 2 + 1 ≤ Real.exp (L ^ 2) := Real.add_one_le_exp (L ^ 2)
          linarith
        have hL_cap : 2 * M₀ * E_T ≤ γ * L := by
          have hdiv : (2 * M₀ * E_T + 1) / γ ≤ L := le_max_right _ _
          have := (div_le_iff₀ hγ).mp hdiv
          linarith
        have h_tail : 2 * M₀ * E_T * Real.exp (- L ^ 2) ≤ γ := by
          have h_le_prod : 2 * M₀ * E_T ≤ γ * Real.exp (L ^ 2) :=
            hL_cap.trans (mul_le_mul_of_nonneg_left hL_exp hγ.le)
          calc 2 * M₀ * E_T * Real.exp (- L ^ 2)
            _ ≤ (γ * Real.exp (L ^ 2)) * Real.exp (- L ^ 2) :=
              mul_le_mul_of_nonneg_right h_le_prod (Real.exp_pos _).le
            _ = γ * Real.exp (L ^ 2 + (- L ^ 2)) := by rw [mul_assoc, ← Real.exp_add]
            _ = γ := by simp
        dsimp [d]
        rw [norm_mul]
        calc ‖bochner_F_eps f ε₁ r R (bochner_diag_map z w) -
              bochner_F_eps f ε₂ r R (bochner_diag_map z w)‖ * ‖Complex.exp (- w ^ 2)‖
          _ ≤ (2 * M₀) * (E_T * Real.exp (- L ^ 2)) :=
            mul_le_mul hsub hexp_le (norm_nonneg _) (by positivity)
          _ = 2 * M₀ * E_T * Real.exp (- L ^ 2) := by ring
          _ ≤ γ := h_tail
      · push Not at hw_re
        have hw_norm : ‖w‖ ≤ L + T := by
          have hw_im_abs : |w.im| ≤ T := by
            rcases hw_im with h | h <;> rw [h]
            · exact le_max_left _ _
            · exact le_max_right _ _
          have hw_eq : w = ↑w.re + I * ↑w.im := by rw [mul_comm I, Complex.re_add_im]
          calc ‖w‖ = ‖(w.re : ℂ) + I * (w.im : ℂ)‖ := by conv_lhs => rw [hw_eq]
            _ ≤ ‖(w.re : ℂ)‖ + ‖I * (w.im : ℂ)‖ := norm_add_le _ _
            _ = |w.re| + |w.im| := by simp [Complex.norm_real]
            _ ≤ L + T := by linarith
        have hz_norm : ‖z‖ ≤ ‖zstar‖ + η := by
          have hd : ‖z - zstar‖ < η := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
          calc ‖z‖ = ‖(z - zstar) + zstar‖ := by ring_nf
            _ ≤ ‖z - zstar‖ + ‖zstar‖ := norm_add_le _ _
            _ ≤ η + ‖zstar‖ := by linarith
            _ = ‖zstar‖ + η := by ring
        have h_zw0 : ‖bochner_diag_map z w 0‖ ≤ ‖zstar‖ + η + L + T := by
          dsimp [bochner_diag_map]
          calc ‖z 0 + w‖ ≤ ‖z 0‖ + ‖w‖ := norm_add_le _ _
            _ ≤ ‖z‖ + ‖w‖ := add_le_add (norm_le_pi_norm z 0) le_rfl
            _ ≤ (‖zstar‖ + η) + (L + T) := add_le_add hz_norm hw_norm
            _ = ‖zstar‖ + η + L + T := by ring
        have h_zw1 : ‖bochner_diag_map z w 1‖ ≤ ‖zstar‖ + η + L + T := by
          dsimp [bochner_diag_map]
          calc ‖z 1 - w‖ ≤ ‖z 1‖ + ‖w‖ := norm_sub_le _ _
            _ ≤ ‖z‖ + ‖w‖ := add_le_add (norm_le_pi_norm z 1) le_rfl
            _ ≤ (‖zstar‖ + η) + (L + T) := add_le_add hz_norm hw_norm
            _ = ‖zstar‖ + η + L + T := by ring
        have hz_sq : ‖bochner_diag_map z w 0 ^ 2 + bochner_diag_map z w 1 ^ 2‖ ≤ S := by
          calc ‖bochner_diag_map z w 0 ^ 2 + bochner_diag_map z w 1 ^ 2‖
            _ ≤ ‖bochner_diag_map z w 0 ^ 2‖ + ‖bochner_diag_map z w 1 ^ 2‖ := norm_add_le _ _
            _ = ‖bochner_diag_map z w 0‖ ^ 2 + ‖bochner_diag_map z w 1‖ ^ 2 := by simp [norm_pow]
            _ ≤ (‖zstar‖ + η + L + T) ^ 2 + (‖zstar‖ + η + L + T) ^ 2 :=
              add_le_add (pow_le_pow_left₀ (norm_nonneg _) h_zw0 2)
                (pow_le_pow_left₀ (norm_nonneg _) h_zw1 2)
            _ ≤ S := by dsimp [S]; linarith
        have hε₁_S : ε₁ * S ≤ 1 := by
          have hle : ε₁ ≤ 1 / S :=
            hε₁.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
          exact (mul_le_mul_of_nonneg_right hle hS_pos.le).trans
            (by rw [one_div, inv_mul_cancel₀ hS_pos.ne'])
        have hε₂_S : ε₂ * S ≤ 1 := by
          have hle : ε₂ ≤ 1 / S :=
            hε₂.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
          exact (mul_le_mul_of_nonneg_right hle hS_pos.le).trans
            (by rw [one_div, inv_mul_cancel₀ hS_pos.ne'])
        have h_bd := bochner_f_eps_diff_le_on_LShape r R hr hR f hf_holo hM hε₁.1 hε₂.1
          hε₁_S hε₂_S hw_LS hz_sq
        have hexp_le : ‖Complex.exp (- w ^ 2)‖ ≤ E_T := by
          rw [hexp_norm]
          apply Real.exp_le_exp.mpr
          have : 0 ≤ w.re ^ 2 := sq_nonneg _
          linarith [h_im_T w hw_Icc]
        have h_lt_cap : ε₀ ≤ γ / (4 * (max M 0 + 1) * S * E_T) :=
          (min_le_right _ _).trans (min_le_right _ _)
        have h_denom_pos : 0 < 4 * (max M 0 + 1) * S * E_T := by positivity
        have h_cap : 4 * (max M 0 + 1) * S * E_T * ε₀ ≤ γ := by
          have := (le_div_iff₀ h_denom_pos).mp h_lt_cap
          linarith
        dsimp [d]
        rw [norm_mul]
        calc ‖bochner_F_eps f ε₁ r R (bochner_diag_map z w) -
              bochner_F_eps f ε₂ r R (bochner_diag_map z w)‖ * ‖Complex.exp (- w ^ 2)‖
          _ ≤ (max M 0 * (2 * (ε₁ * S) + 2 * (ε₂ * S))) * E_T :=
            mul_le_mul h_bd hexp_le (norm_nonneg _) (by positivity)
          _ ≤ (max M 0 + 1) * (4 * (ε₀ * S)) * E_T := by
            have h1 : ε₁ * S ≤ ε₀ * S := mul_le_mul_of_nonneg_right hε₁.2.le hS_pos.le
            have h2 : ε₂ * S ≤ ε₀ * S := mul_le_mul_of_nonneg_right hε₂.2.le hS_pos.le
            have h_sum_le : 2 * (ε₁ * S) + 2 * (ε₂ * S) ≤ 4 * (ε₀ * S) := by linarith
            have h_prod : max M 0 * (2 * (ε₁ * S) + 2 * (ε₂ * S)) ≤
                (max M 0 + 1) * (4 * (ε₀ * S)) :=
              mul_le_mul (by linarith) h_sum_le (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right h_prod hE_T_pos.le
          _ = 4 * (max M 0 + 1) * S * E_T * ε₀ := by ring
          _ ≤ γ := h_cap
    refine norm_le_on_horizontal_strip_of_bdd ht₁_lt_t₂
      (hd_wide.mono h_sub_Ioo)
      (hd_wide.continuousOn.mono h_sub_Icc)
      hd_bdd
      (fun u hu => hd_edge u (Or.inl hu) ?_)
      (fun u hu => hd_edge u (Or.inr hu) ?_)
      (by simpa using ht₁_neg.le) (by simpa using ht₂_pos.le)
    · change (fun i => (bochner_diag_map z u i).im) ∈ LShape r R
      rw [bochner_diag_map_im, hu]
      exact (h_ends z hz).1
    · change (fun i => (bochner_diag_map z u i).im) ∈ LShape r R
      rw [bochner_diag_map_im, hu]
      exact (h_ends z hz).2

lemma tendstoUniformlyOn_limUnder_of_uniform_cauchy {α : Type*} {s : Set α}
    (F : ℝ → α → ℂ)
    (h_cauchy : ∀ γ > 0, ∃ ε₀ > 0, ∀ ε₁ ∈ Set.Ioo 0 ε₀, ∀ ε₂ ∈ Set.Ioo 0 ε₀,
      ∀ z ∈ s, ‖F ε₁ z - F ε₂ z‖ ≤ γ) :
    TendstoUniformlyOn F (fun z => limUnder (𝓝[>] (0 : ℝ)) (fun ε => F ε z))
      (𝓝[>] (0 : ℝ)) s := by
  have h_ioo_mem : ∀ ε₀ > 0, Set.Ioo (0 : ℝ) ε₀ ∈ 𝓝[>] (0 : ℝ) := fun ε₀ hε₀ =>
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Iio ε₀, Iio_mem_nhds hε₀, fun x hx => ⟨hx.2, hx.1⟩⟩
  have h_pt : ∀ z ∈ s,
      Tendsto (fun ε => F ε z) (𝓝[>] (0 : ℝ))
        (𝓝 (limUnder (𝓝[>] (0 : ℝ)) (fun ε => F ε z))) := by
    intro z hz
    have hcau : Cauchy (Filter.map (fun ε => F ε z) (𝓝[>] (0 : ℝ))) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun γ hγ => ?_⟩
      rcases h_cauchy (γ / 2) (half_pos hγ) with ⟨ε₀, hε₀, hbd⟩
      refine ⟨(fun ε => F ε z) '' Set.Ioo 0 ε₀,
        Filter.image_mem_map (h_ioo_mem ε₀ hε₀), ?_⟩
      rintro _ ⟨ε₁, hε₁, rfl⟩ _ ⟨ε₂, hε₂, rfl⟩
      rw [dist_eq_norm]
      exact (hbd ε₁ hε₁ ε₂ hε₂ z hz).trans_lt (half_lt_self hγ)
    rcases cauchy_map_iff_exists_tendsto.mp hcau with ⟨L, hL⟩
    rwa [hL.limUnder_eq]
  rw [Metric.tendstoUniformlyOn_iff]
  intro γ hγ
  rcases h_cauchy (γ / 2) (half_pos hγ) with ⟨ε₀, hε₀, hbd⟩
  filter_upwards [h_ioo_mem ε₀ hε₀] with ε₁ hε₁ z hz
  have h_le : dist (limUnder (𝓝[>] (0 : ℝ)) (fun ε => F ε z)) (F ε₁ z) ≤ γ / 2 := by
    refine le_of_tendsto ((h_pt z hz).dist tendsto_const_nhds) ?_
    filter_upwards [h_ioo_mem ε₀ hε₀] with ε₂ hε₂
    rw [dist_eq_norm]
    exact hbd ε₂ hε₂ ε₁ hε₁ z hz
  exact h_le.trans_lt (half_lt_self hγ)

lemma bochner_F_eps_tendstoLocallyUniformlyOn (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M) :
    TendstoLocallyUniformlyOn (fun ε z => bochner_F_eps f ε r R z) (bochner_F_limit f r R)
      (𝓝[>] (0 : ℝ)) (TubeDomain (LShapeConvexHull r R)) := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun zstar hzstar => ?_
  rcases bochner_F_eps_local_uniform_cauchy r R hr hR f hf_holo hf_bound zstar hzstar with
    ⟨η, hη, _, h_cauchy⟩
  refine ⟨Metric.ball zstar η, nhdsWithin_le_nhds (Metric.ball_mem_nhds zstar hη), ?_⟩
  exact tendstoUniformlyOn_limUnder_of_uniform_cauchy (fun ε z => bochner_F_eps f ε r R z) h_cauchy

lemma bochner_F_limit_holo (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M) :
    DifferentiableOn ℂ (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)) := by
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  have h_loc := bochner_F_eps_tendstoLocallyUniformlyOn r R hr hR f hf_holo hf_bound
  have h_ev_holo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)) :=
    eventually_nhdsWithin_of_forall fun ε hε => bochner_F_eps_holo r R hr hR f hf_holo hf_bound ε hε
  have h_cont : ContinuousOn (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)) := by
    intro zstar hzstar
    rcases bochner_F_eps_local_uniform_cauchy r R hr hR f hf_holo hf_bound zstar hzstar with
      ⟨η, hη, h_sub, h_cauchy⟩
    have h_unif := tendstoUniformlyOn_limUnder_of_uniform_cauchy
      (fun ε z => bochner_F_eps f ε r R z) h_cauchy
    have h_ev_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ContinuousOn (bochner_F_eps f ε r R) (Metric.ball zstar η) :=
      h_ev_holo.mono fun ε hε => hε.continuousOn.mono h_sub
    have h_cont_ball : ContinuousOn (bochner_F_limit f r R) (Metric.ball zstar η) :=
      h_unif.continuousOn h_ev_cont.frequently
    exact (h_cont_ball.continuousAt (Metric.ball_mem_nhds zstar hη)).continuousWithinAt
  have h_diff0 : ∀ z ∈ TubeDomain (LShapeConvexHull r R),
      DifferentiableAt ℂ
        (fun w => bochner_F_limit f r R (fun i => if i = 0 then w else z 1)) (z 0) := by
    intro z hz
    let φ : ℂ → (Fin 2 → ℂ) := fun w i => if i = 0 then w else z 1
    let S : Set ℂ := {w : ℂ | φ w ∈ TubeDomain (LShapeConvexHull r R)}
    have hS_open : IsOpen S := isOpen_slice0 hU_open z
    have hφ_diff : Differentiable ℂ φ := by
      apply differentiable_pi.mpr
      intro i
      dsimp [φ]
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    have h_loc_slice : TendstoLocallyUniformlyOn
        (fun ε w => bochner_F_eps f ε r R (φ w))
        (fun w => bochner_F_limit f r R (φ w)) (𝓝[>] (0 : ℝ)) S :=
      h_loc.comp φ (fun _ hw => hw) hφ_diff.continuous.continuousOn
    have h_ev_slice : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        DifferentiableOn ℂ (fun w => bochner_F_eps f ε r R (φ w)) S :=
      h_ev_holo.mono fun ε hε => hε.comp hφ_diff.differentiableOn (fun _ hw => hw)
    have h_diffOn := h_loc_slice.differentiableOn h_ev_slice hS_open
    have hz0_S : z 0 ∈ S := by
      change φ (z 0) ∈ TubeDomain (LShapeConvexHull r R)
      have hφz : φ (z 0) = z := by ext i; fin_cases i <;> simp [φ]
      rwa [hφz]
    exact (h_diffOn (z 0) hz0_S).differentiableAt (hS_open.mem_nhds hz0_S)
  have h_diff1 : ∀ z ∈ TubeDomain (LShapeConvexHull r R),
      DifferentiableAt ℂ
        (fun w => bochner_F_limit f r R (fun i => if i = 1 then w else z 0)) (z 1) := by
    intro z hz
    let φ : ℂ → (Fin 2 → ℂ) := fun w i => if i = 1 then w else z 0
    let S : Set ℂ := {w : ℂ | φ w ∈ TubeDomain (LShapeConvexHull r R)}
    have hS_open : IsOpen S := isOpen_slice1 hU_open z
    have hφ_diff : Differentiable ℂ φ := by
      apply differentiable_pi.mpr
      intro i
      dsimp [φ]
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    have h_loc_slice : TendstoLocallyUniformlyOn
        (fun ε w => bochner_F_eps f ε r R (φ w))
        (fun w => bochner_F_limit f r R (φ w)) (𝓝[>] (0 : ℝ)) S :=
      h_loc.comp φ (fun _ hw => hw) hφ_diff.continuous.continuousOn
    have h_ev_slice : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        DifferentiableOn ℂ (fun w => bochner_F_eps f ε r R (φ w)) S :=
      h_ev_holo.mono fun ε hε => hε.comp hφ_diff.differentiableOn (fun _ hw => hw)
    have h_diffOn := h_loc_slice.differentiableOn h_ev_slice hS_open
    have hz1_S : z 1 ∈ S := by
      change φ (z 1) ∈ TubeDomain (LShapeConvexHull r R)
      have hφz : φ (z 1) = z := by ext i; fin_cases i <;> simp [φ]
      rwa [hφz]
    exact (h_diffOn (z 1) hz1_S).differentiableAt (hS_open.mem_nhds hz1_S)
  apply differentiableOn_of_differentiableAt_all
  intro z hz
  exact osgood_fin2 hU_open (bochner_F_limit f r R) h_cont h_diff0 h_diff1 z hz

theorem bochner_tube_theorem (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M) :
    ∃ (F : (Fin 2 → ℂ) → ℂ),
      DifferentiableOn ℂ F (TubeDomain (LShapeConvexHull r R)) ∧
      EqOn F f (TubeDomain (LShape r R)) := by
  refine ⟨bochner_F_limit f r R, bochner_F_limit_holo r R hr hR f hf_holo hf_bound, ?_⟩
  exact bochner_F_limit_eq_on_tube r R f
    (fun ε hε => bochner_F_eps_eq_f r R hr hR f hf_holo hf_bound ε hε)
end Bochner

lemma isOpen_TubeDomain_minus (V_plus : Set (Fin n → ℝ)) (hV_open : IsOpen V_plus) :
    IsOpen (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
  have h_img : ((fun v => -v) '' V_plus) = (fun v => -v) ⁻¹' V_plus := by
    ext v
    simp
  rw [h_img]
  have h_minus_open : IsOpen ((fun v => -v) ⁻¹' V_plus) := hV_open.preimage continuous_neg
  exact isOpen_TubeDomain h_minus_open

lemma isOpen_wedge_neighborhood (V_plus U : Set (Fin n → ℝ)) (hV_open : IsOpen V_plus)
    (r : (Fin n → ℝ) → ℝ) :
    IsOpen (TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)) := by
  apply IsOpen.union
  · exact (isOpen_TubeDomain hV_open).union (isOpen_TubeDomain_minus V_plus hV_open)
  · exact isOpen_biUnion (fun x _ => Metric.isOpen_ball)

lemma wedge_subset_union_balls (V_plus U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ U, 0 < r x) :
    WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U ⊆
    TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x) := by
  intro z hz
  rcases hz with (hz_plus | hz_minus) | hz_edge
  · left; left; exact hz_plus
  · left; right; exact hz_minus
  · right
    rcases hz_edge with ⟨hx_U, hx_im⟩
    let x : Fin n → ℝ := fun i => (z i).re
    have hx_eq : (fun i => (x i : ℂ)) = z := by
      ext i
      have h_im : (z i).im = 0 := congr_fun hx_im i
      exact Complex.ext rfl (by simp [x, h_im])
    simp only [mem_iUnion]
    refine ⟨x, hx_U, ?_⟩
    rw [hx_eq]
    exact Metric.mem_ball_self (hr x hx_U)

lemma dist_real_le_dist {n : ℕ} (z : Fin n → ℂ) (x : Fin n → ℝ) :
    dist (fun i => (((z i).re : ℝ) : ℂ)) (fun i => (x i : ℂ)) ≤ dist z (fun i => (x i : ℂ)) := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  have h_le : dist (((z i).re : ℝ) : ℂ) (x i : ℂ) ≤ dist (z i) (x i : ℂ) := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : (((z i).re : ℝ) : ℂ) - (x i : ℂ) = (((z i - (x i : ℂ)).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq, Complex.norm_real]
    exact Complex.abs_re_le_norm (z i - (x i : ℂ))
  exact h_le.trans (dist_le_pi_dist z (fun i => (x i : ℂ)) i)

lemma real_point_in_ball_inter {n : ℕ} {x y : Fin n → ℝ} {rx ry : ℝ}
    {z : Fin n → ℂ} (hzx : z ∈ Metric.ball (fun i => (x i : ℂ)) rx)
    (hzy : z ∈ Metric.ball (fun i => (y i : ℂ)) ry) :
    (fun i => (((z i).re : ℝ) : ℂ)) ∈ Metric.ball (fun i => (x i : ℂ)) rx ∧
    (fun i => (((z i).re : ℝ) : ℂ)) ∈ Metric.ball (fun i => (y i : ℂ)) ry := by
  constructor
  · have h := Metric.mem_ball.mp hzx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (dist_real_le_dist z x) h)
  · have h := Metric.mem_ball.mp hzy
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (dist_real_le_dist z y) h)

noncomputable def ofRealPi (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

lemma ofRealPi_apply {n : ℕ} (x : Fin n → ℝ) : ofRealPi n x = (fun i => (x i : ℂ)) := by
  ext i
  simp [ofRealPi]

lemma dist_ofReal_eq_dist {n : ℕ} (x y : Fin n → ℝ) :
    dist (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) = dist x y := by
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    have heq : dist (x i : ℂ) (y i : ℂ) = dist (x i) (y i) := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (x i : ℂ) - (y i : ℂ) = ((x i - y i : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub, Complex.norm_real]
    rw [heq]
    exact dist_le_pi_dist x y i
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    have heq : dist (x i : ℂ) (y i : ℂ) = dist (x i) (y i) := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (x i : ℂ) - (y i : ℂ) = ((x i - y i : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub, Complex.norm_real]
    rw [← heq]
    exact dist_le_pi_dist (fun j => (x j : ℂ)) (fun j => (y j : ℂ)) i

lemma mem_wedgeDomain_of_real {n : ℕ} {V_plus V_minus U : Set (Fin n → ℝ)}
    {t : Fin n → ℝ} (ht_U : t ∈ U) :
    (fun i => (t i : ℂ)) ∈ WedgeDomain V_plus V_minus U := by
  right
  simp only [mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · have heq : (fun i => ((t i : ℂ).re)) = t := by
      ext i; simp
    rw [heq]
    exact ht_U
  · ext i
    simp

def HasLocalExtensionAt (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (r_x : ℝ) (F_x : (Fin n → ℂ) → ℂ) : Prop :=
  0 < r_x ∧
  Metric.ball x r_x ⊆ U ∧
  AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
  EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
    WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U)

lemma isConnected_ball_inter {n : ℕ} (c1 c2 : Fin n → ℂ) (r1 r2 : ℝ)
    (h_ne : (Metric.ball c1 r1 ∩ Metric.ball c2 r2).Nonempty) :
    IsConnected (Metric.ball c1 r1 ∩ Metric.ball c2 r2) := by
  have h_conv : Convex ℝ (Metric.ball c1 r1 ∩ Metric.ball c2 r2) :=
    (convex_ball c1 r1).inter (convex_ball c2 r2)
  exact h_conv.isConnected h_ne

lemma eow_local_compat (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (x y : U) (rx ry : ℝ) (Fx Fy : (Fin n → ℂ) → ℂ)
    (hx_ext : HasLocalExtensionAt V_plus U f x.1 rx Fx)
    (hy_ext : HasLocalExtensionAt V_plus U f y.1 ry Fy) :
    EqOn Fx Fy (Metric.ball (fun i => (x.1 i : ℂ)) rx ∩ Metric.ball (fun i => (y.1 i : ℂ)) ry) := by
  let cx : Fin n → ℂ := fun i => (x.1 i : ℂ)
  let cy : Fin n → ℂ := fun i => (y.1 i : ℂ)
  let W : Set (Fin n → ℂ) := Metric.ball cx rx ∩ Metric.ball cy ry
  by_cases h_inter : W.Nonempty
  · rcases h_inter with ⟨z, hzx, hzy⟩
    have ⟨hzx_re, hzy_re⟩ := real_point_in_ball_inter hzx hzy
    let a : Fin n → ℝ := fun i => (z i).re
    have ha_cx : (fun i => (a i : ℂ)) ∈ Metric.ball cx rx := hzx_re
    have ha_cy : (fun i => (a i : ℂ)) ∈ Metric.ball cy ry := hzy_re
    have ha_W : ofRealPi n a ∈ W := by
      rw [ofRealPi_apply]
      exact ⟨ha_cx, ha_cy⟩
    have ha_ball_x : a ∈ Metric.ball x.1 rx := by
      rw [Metric.mem_ball] at ha_cx ⊢
      rw [← dist_ofReal_eq_dist]
      exact ha_cx
    have ha_ball_y : a ∈ Metric.ball y.1 ry := by
      rw [Metric.mem_ball] at ha_cy ⊢
      rw [← dist_ofReal_eq_dist]
      exact ha_cy
    have hW_open : IsOpen W := (Metric.isOpen_ball).inter Metric.isOpen_ball
    have hW_conn : IsConnected W := isConnected_ball_inter cx cy rx ry ⟨z, hzx, hzy⟩
    have hf_ana : AnalyticOnNhd ℂ Fx W := hx_ext.2.2.1.mono inter_subset_left
    have hg_ana : AnalyticOnNhd ℂ Fy W := hy_ext.2.2.1.mono inter_subset_right
    have h_real_nhds : ∀ᶠ t : Fin n → ℝ in 𝓝 a, Fx (ofRealPi n t) = Fy (ofRealPi n t) := by
      have h_open_ball_inter : IsOpen (Metric.ball x.1 rx ∩ Metric.ball y.1 ry) :=
        Metric.isOpen_ball.inter Metric.isOpen_ball
      have ha_in_inter : a ∈ Metric.ball x.1 rx ∩ Metric.ball y.1 ry := ⟨ha_ball_x, ha_ball_y⟩
      have h_mem_nhds : Metric.ball x.1 rx ∩ Metric.ball y.1 ry ∈ 𝓝 a :=
        h_open_ball_inter.mem_nhds ha_in_inter
      filter_upwards [h_mem_nhds] with t ht
      rw [ofRealPi_apply]
      have ht_ball_x : (fun i => (t i : ℂ)) ∈ Metric.ball cx rx := by
        rw [Metric.mem_ball]
        rw [dist_ofReal_eq_dist]
        exact ht.1
      have ht_ball_y : (fun i => (t i : ℂ)) ∈ Metric.ball cy ry := by
        rw [Metric.mem_ball]
        rw [dist_ofReal_eq_dist]
        exact ht.2
      have ht_U : t ∈ U := hx_ext.2.1 ht.1
      have ht_wedge : (fun i => (t i : ℂ)) ∈
          WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U :=
        mem_wedgeDomain_of_real ht_U
      have h_eq_x := hx_ext.2.2.2 ⟨ht_ball_x, ht_wedge⟩
      have h_eq_y := hy_ext.2.2.2 ⟨ht_ball_y, ht_wedge⟩
      rw [h_eq_x, h_eq_y]
    exact Analysis.analytic_eq_of_real_eq_R_N hW_open hW_conn Fx Fy hf_ana hg_ana
      a (ofRealPi n) ofRealPi_apply ha_W h_real_nhds
  · intro w hw
    exfalso
    exact h_inter ⟨w, hw⟩

lemma local_extension_assembly (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (h_exists : ∀ x ∈ U, ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_compat : ∀ (x y : U) (rx ry : ℝ) (Fx Fy : (Fin n → ℂ) → ℂ),
      HasLocalExtensionAt V_plus U f x.1 rx Fx →
      HasLocalExtensionAt V_plus U f y.1 ry Fy →
      EqOn Fx Fy (Metric.ball (fun i => (x.1 i : ℂ)) rx ∩ Metric.ball (fun i => (y.1 i : ℂ)) ry)) :
    ∃ (r : (Fin n → ℝ) → ℝ) (_hr : ∀ x ∈ U, 0 < r x) (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x))) ∧
      (∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U)) ∧
      (∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
          Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) := by
  choose! r_x hr_x h_sub F_x hF_x using h_exists
  refine ⟨r_x, hr_x, F_x, ?_, ?_, ?_⟩
  · intro x hx
    exact (hF_x x hx).1.differentiableOn
  · intro x hx
    exact (hF_x x hx).2
  · intro x y
    have hx_ext : HasLocalExtensionAt V_plus U f x.1 (r_x x.1) (F_x x.1) :=
      ⟨hr_x x.1 x.2, h_sub x.1 x.2, (hF_x x.1 x.2).1, (hF_x x.1 x.2).2⟩
    have hy_ext : HasLocalExtensionAt V_plus U f y.1 (r_x y.1) (F_x y.1) :=
      ⟨hr_x y.1 y.2, h_sub y.1 y.2, (hF_x y.1 y.2).1, (hF_x y.1 y.2).2⟩
    exact h_compat x y (r_x x.1) (r_x y.1) (F_x x.1) (F_x y.1) hx_ext hy_ext

lemma analyticOnNhd_ball_of_analyticAt {n : ℕ} {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (h : AnalyticAt ℂ f x) :
    ∃ r > 0, AnalyticOnNhd ℂ f (Metric.ball x r) := by
  have h_open : IsOpen {y | AnalyticAt ℂ f y} := isOpen_analyticAt ℂ f
  have h_in : x ∈ {y | AnalyticAt ℂ f y} := h
  rcases Metric.isOpen_iff.mp h_open x h_in with ⟨r, hr_pos, hr_sub⟩
  exact ⟨r, hr_pos, fun y hy => hr_sub hy⟩

lemma exists_ball_subset_and_analyticOnNhd {n : ℕ} {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hx_U : x ∈ U)
    (h_ana : AnalyticAt ℂ f (fun i => (x i : ℂ))) :
    ∃ r > 0, Metric.ball x r ⊆ U ∧
      AnalyticOnNhd ℂ f (Metric.ball (fun i => (x i : ℂ)) r) := by
  rcases Metric.isOpen_iff.mp hU x hx_U with ⟨r1, hr1_pos, hr1_sub⟩
  rcases analyticOnNhd_ball_of_analyticAt h_ana with ⟨r2, hr2_pos, hr2_ana⟩
  let r := min r1 r2
  have hr_pos : 0 < r := lt_min hr1_pos hr2_pos
  refine ⟨r, hr_pos, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_left r1 r2)).trans hr1_sub
  · exact hr2_ana.mono (Metric.ball_subset_ball (min_le_right r1 r2))

lemma analyticAt_cauchy_integral {f : ℂ → ℂ} {c : ℂ} {R : NNReal} (hR : 0 < R)
    (hf : CircleIntegrable f c R) :
    AnalyticAt ℂ (fun w => (2 * ↑Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) c := by
  have h_series := hasFPowerSeriesOn_cauchy_integral hf hR
  have hc_mem : c ∈ Metric.eball c R := by
    rw [Metric.eball_coe]
    exact Metric.mem_ball_self hR
  exact h_series.analyticAt_of_mem hc_mem

lemma analyticAt_comp_clm {n : ℕ} (g : ℂ → ℂ) (L : (Fin n → ℂ) →L[ℂ] ℂ) (x : Fin n → ℂ)
    (hg : AnalyticAt ℂ g (L x)) :
    AnalyticAt ℂ (g ∘ L) x :=
  hg.comp (L.analyticAt x)

lemma exists_ne_zero_of_open_cone_1d (V : Set (Fin 1 → ℝ)) (hV : IsOpen V)
    (_hV_cone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (hV_ne : V.Nonempty) : ∃ v ∈ V, v 0 ≠ 0 := by
  rcases hV_ne with ⟨v, hv⟩
  by_cases h0 : v 0 = 0
  · have hveq : v = 0 := by ext i; fin_cases i; exact h0
    rw [hveq] at hv
    rcases Metric.isOpen_iff.mp hV 0 hv with ⟨ε, hε_pos, hε_sub⟩
    let v' : Fin 1 → ℝ := fun _ => ε / 2
    have hv'_mem : v' ∈ Metric.ball (0 : Fin 1 → ℝ) ε := by
      rw [Metric.mem_ball]
      apply (dist_pi_lt_iff hε_pos).mpr
      intro i
      fin_cases i
      dsimp [v']
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε_pos)]
      exact half_lt_self hε_pos
    have hv' : v' ∈ V := hε_sub hv'_mem
    have hv'0 : v' 0 ≠ 0 := (half_pos hε_pos).ne'
    exact ⟨v', hv', hv'0⟩
  · exact ⟨v, hv, h0⟩

lemma slice_fun_eq_f_1d (f : (Fin 1 → ℂ) → ℂ) (x : Fin 1 → ℝ) (v : Fin 1 → ℝ)
    (hv0 : v 0 ≠ 0) (z : Fin 1 → ℂ) :
    slice_fun f (fun i => (x i : ℂ)) v ((z 0 - (x 0 : ℂ)) / (v 0 : ℂ)) = f z := by
  dsimp [slice_fun]
  have heq : (fun i : Fin 1 => (x i : ℂ) + ((z 0 - (x 0 : ℂ)) / (v 0 : ℂ)) * (v i : ℂ)) = z := by
    ext i
    fin_cases i
    dsimp
    have hv : (v 0 : ℂ) ≠ 0 := by exact_mod_cast hv0
    calc (x 0 : ℂ) + ((z 0 - (x 0 : ℂ)) / (v 0 : ℂ)) * (v 0 : ℂ)
      _ = (x 0 : ℂ) + (z 0 - (x 0 : ℂ)) := by rw [div_mul_cancel₀ _ hv]
      _ = z 0 := by ring
  rw [heq]

lemma exists_local_analytic_extension_cauchy_1d (V_plus U : Set (Fin 1 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin 1 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)))
    (x : Fin 1 → ℝ) (hx_U : x ∈ U) (r : ℝ) (_hr : 0 < r)
    (_h_ball_U : Metric.ball x r ⊆ U) :
    ∃ F_x : (Fin 1 → ℂ) → ℂ,
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r ∩
        WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U) := by
  rcases exists_ne_zero_of_open_cone_1d V_plus hV_plus_open hV_plus_cone hV_plus_ne with
    ⟨v, hv, hv0⟩
  have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hv
  let g : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) v
  let L : (Fin 1 → ℂ) → ℂ := fun z => (z 0 - (x 0 : ℂ)) / (v 0 : ℂ)
  have hL_ana : AnalyticAt ℂ L (fun i => (x i : ℂ)) := by
    dsimp [L]
    apply AnalyticAt.div_const
    apply AnalyticAt.sub
    · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)).analyticAt (fun i => (x i : ℂ))
    · exact analyticAt_const
  have hL_x : L (fun i => (x i : ℂ)) = 0 := by
    dsimp [L]
    simp
  let F_x : (Fin 1 → ℂ) → ℂ := g ∘ L
  have hF_ana : AnalyticAt ℂ F_x (fun i => (x i : ℂ)) := by
    rw [← hL_x] at h_slice
    exact h_slice.comp hL_ana
  use F_x
  refine ⟨hF_ana, ?_⟩
  intro z _hz
  dsimp [F_x, g, L]
  exact slice_fun_eq_f_1d f x v hv0 z

def LocalEOWCore {n : ℕ} (V_plus : Set (Fin n → ℝ)) (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ F : (Fin n → ℂ) → ℂ,
    AnalyticOnNhd ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus ∧ EqOn F f W) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∧ EqOn F f W)

lemma eqOn_zero_of_convex_differentiableOn {n : ℕ} {S W : Set (Fin n → ℂ)}
    (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g S)
    (hW_open : IsOpen W) (hWS : W ⊆ S) (hW_ne : W.Nonempty)
    (hgW : EqOn g 0 W) : EqOn g 0 S := by
  obtain ⟨w, hw⟩ := hW_ne
  intro p hp
  let φ : ℂ → (Fin n → ℂ) := fun t => w + t • (p - w)
  have hφ_diff : Differentiable ℂ φ := by
    unfold φ
    fun_prop
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hφ0 : φ 0 = w := by simp [φ]
  have hφ1 : φ 1 = p := by simp [φ]
  let T : Set ℂ := φ ⁻¹' S
  have hT_open : IsOpen T := hS_open.preimage hφ_cont
  have hT_conv : Convex ℝ T := by
    intro t₁ ht₁ t₂ ht₂ a b ha hb hab
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have h : φ (a • t₁ + b • t₂) = a • φ t₁ + b • φ t₂ := by
      ext i
      simp only [φ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, smul_eq_mul]
      linear_combination (-(w i)) * hab'
    change φ (a • t₁ + b • t₂) ∈ S
    rw [h]
    exact hS_conv ht₁ ht₂ ha hb hab
  have h_an : AnalyticOnNhd ℂ (g ∘ φ) T :=
    (hg.comp hφ_diff.differentiableOn (fun t ht => ht)).analyticOnNhd hT_open
  have h0T : (0 : ℂ) ∈ T := by
    change φ 0 ∈ S
    rw [hφ0]
    exact hWS hw
  have h1T : (1 : ℂ) ∈ T := by
    change φ 1 ∈ S
    rw [hφ1]
    exact hp
  have h_ev : (g ∘ φ) =ᶠ[nhds (0 : ℂ)] 0 := by
    have hWn : W ∈ nhds (φ 0) := by
      rw [hφ0]
      exact hW_open.mem_nhds hw
    filter_upwards [hφ_cont.continuousAt.preimage_mem_nhds hWn] with t ht
    exact hgW ht
  have h_zero := h_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hT_conv.isPreconnected h0T h_ev
  simpa [Function.comp, hφ1] using h_zero h1T

lemma exists_local_analytic_extension_of_core {n : ℕ} (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (h_core : LocalEOWCore V_plus f x) :
    ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  classical
  obtain ⟨ρ, hρ, F, hF_an, ⟨W₁, hW₁o, hW₁n, hW₁s, hW₁e⟩, ⟨W₂, hW₂o, hW₂n, hW₂s, hW₂e⟩⟩ := h_core
  have hF_diff : DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ) :=
    hF_an.differentiableOn
  have hB_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ) := Metric.isOpen_ball
  have hB_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ) := convex_ball _ _
  have hVm_conv : Convex ℝ ((fun v : Fin n → ℝ => -v) '' V_plus) := by
    rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ a b ha hb hab
    exact ⟨a • v₁ + b • v₂, hV_plus_convex hv₁ hv₂ ha hb hab, by simp [add_comm]⟩
  have h_eq₁ : EqOn F f (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) := by
    have hS_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) :=
      hB_open.inter (isOpen_TubeDomain hV_plus_open)
    have hS_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) :=
      hB_conv.inter (convex_TubeDomain hV_plus_convex)
    have hd : DifferentiableOn ℂ (F - f)
        (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) :=
      (hF_diff.mono Set.inter_subset_left).sub (h_holo_plus.mono Set.inter_subset_right)
    have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW₁o hW₁s hW₁n
      (fun z hz => by simp [hW₁e hz])
    intro z hz
    simpa [sub_eq_zero] using h0 hz
  have h_eq₂ : EqOn F f (Metric.ball (fun i => (x i : ℂ)) ρ ∩
      TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
    have hS_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      hB_open.inter (isOpen_TubeDomain_minus V_plus hV_plus_open)
    have hS_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      hB_conv.inter (convex_TubeDomain hVm_conv)
    have hd : DifferentiableOn ℂ (F - f) (Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      (hF_diff.mono Set.inter_subset_left).sub (h_holo_minus.mono Set.inter_subset_right)
    have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW₂o hW₂s hW₂n
      (fun z hz => by simp [hW₂e hz])
    intro z hz
    simpa [sub_eq_zero] using h0 hz
  obtain ⟨w₀, hw₀⟩ := hW₁n
  let v₀ : Fin n → ℝ := fun i => (w₀ i).im
  have hv₀ : v₀ ∈ V_plus := (hW₁s hw₀).2
  have h_real : ∀ z ∈ Metric.ball (fun i => (x i : ℂ)) ρ,
      z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U → F z = f z := by
    intro z hzB hzW
    rcases hzW with (hzT | hzT) | ⟨hz_re, hz_im⟩
    · exact h_eq₁ ⟨hzB, hzT⟩
    · exact h_eq₂ ⟨hzB, hzT⟩
    · let zt : ℝ → (Fin n → ℂ) := fun t i => z i + (t : ℂ) * Complex.I * (v₀ i : ℂ)
      have hzt_cont : Continuous zt := by
        unfold zt
        fun_prop
      have hzt0 : zt 0 = z := by
        ext i
        simp [zt]
      have hzt_tend : Filter.Tendsto zt (nhdsWithin 0 (Set.Ioi 0)) (nhds z) :=
        (hzt_cont.tendsto' 0 z hzt0).mono_left nhdsWithin_le_nhds
      have h_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
        self_mem_nhdsWithin
      have h_inB : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          zt t ∈ Metric.ball (fun i => (x i : ℂ)) ρ :=
        hzt_tend.eventually (hB_open.mem_nhds hzB)
      have h_inT : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), zt t ∈ TubeDomain V_plus := by
        filter_upwards [h_pos] with t ht
        have hzi : ∀ i, (z i).im = 0 := fun i => congr_fun hz_im i
        have him : (fun i => (zt t i).im) = fun i => t * v₀ i := by
          ext i
          simp [zt, Complex.mul_im, hzi i]
        change (fun i => (zt t i).im) ∈ V_plus
        rw [him]
        exact hV_plus_cone v₀ hv₀ t ht
      have h_ev : (fun t => F (zt t)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun t => f (zt t)) := by
        filter_upwards [h_inB, h_inT] with t htB htT
        exact h_eq₁ ⟨htB, htT⟩
      have hF_t : Filter.Tendsto (fun t => F (zt t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (F z)) :=
        (hF_an z hzB).continuousAt.tendsto.comp hzt_tend
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U :=
        Or.inr ⟨hz_re, hz_im⟩
      have hf_t : Filter.Tendsto (fun t => f (zt t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f z)) := by
        refine (h_cont z hz_wedge).tendsto.comp ?_
        refine tendsto_nhdsWithin_iff.mpr ⟨hzt_tend, ?_⟩
        filter_upwards [h_inT] with t htT
        exact Or.inl (Or.inl htT)
      exact tendsto_nhds_unique_of_eventuallyEq hF_t hf_t h_ev
  refine ⟨fun z => if z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U
    then f z else F z, ?_, ?_⟩
  · have h_ev_eq : F =ᶠ[nhds (fun i => (x i : ℂ))] (fun z =>
        if z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U then f z else F z) := by
      filter_upwards [hB_open.mem_nhds (Metric.mem_ball_self hρ)] with z hzB
      by_cases hzW : z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U
      · rw [if_pos hzW]
        exact h_real z hzB hzW
      · rw [if_neg hzW]
    exact (hF_an _ (Metric.mem_ball_self hρ)).congr h_ev_eq
  · intro z hz
    dsimp
    rw [if_pos hz]

lemma exists_linearIndependent_mem_open {n : ℕ} {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (hne : V.Nonempty) :
    ∃ v : Fin n → (Fin n → ℝ), LinearIndependent ℝ v ∧ ∀ i, v i ∈ V := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV v₀ hv₀
  have h_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ Submodule.span ℝ V := by
    intro i
    have h1 : v₀ + Pi.single i (ε / 2) ∈ V := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have e : (Pi.single i (1 : ℝ) : Fin n → ℝ) =
        (ε / 2)⁻¹ • ((v₀ + Pi.single i (ε / 2)) - v₀) := by
      ext j
      by_cases h : j = i
      · subst h
        simp [hε.ne']
      · simp [h]
    rw [e]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.subset_span h1) (Submodule.subset_span hv₀))
  have h_span : Submodule.span ℝ V = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simpa using h_basis i
  obtain ⟨b, hbV, hbspan, hbli⟩ := exists_linearIndependent ℝ V
  have hb_top : Submodule.span ℝ b = ⊤ := hbspan.trans h_span
  let B : Module.Basis b ℝ (Fin n → ℝ) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hb_top])
  haveI : Finite b := Module.Finite.finite_basis B
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    have h := Module.finrank_eq_card_basis B
    simpa using h.symm
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => (e i : Fin n → ℝ), hbli.comp e e.injective, fun i => hbV (e i).2⟩

noncomputable def cAffine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (w : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (x i : ℂ) + Matrix.mulVec (M.map (algebraMap ℝ ℂ)) w i

lemma cAffine_im {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (w : Fin n → ℂ) :
    (fun i => (cAffine M x w i).im) = Matrix.mulVec M (fun j => (w j).im) := by
  ext i
  simp [cAffine, Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

lemma cAffine_re {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (w : Fin n → ℂ) :
    (fun i => (cAffine M x w i).re) = x + Matrix.mulVec M (fun j => (w j).re) := by
  ext i
  simp [cAffine, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

lemma differentiable_cAffine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Differentiable ℂ (cAffine M x) := by
  unfold cAffine
  apply differentiable_pi.mpr
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

noncomputable def matrixMulVecCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ j, (A i j) • (ContinuousLinearMap.proj (R := ℂ) j)

lemma matrixMulVecCLM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    matrixMulVecCLM A z = Matrix.mulVec A z := by
  ext i
  simp [matrixMulVecCLM, Matrix.mulVec, dotProduct]

lemma exists_inverse_cAffine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M)
    (x : Fin n → ℝ) :
    ∃ Ψ : (Fin n → ℂ) → (Fin n → ℂ), Differentiable ℂ Ψ ∧ (∀ z, AnalyticAt ℂ Ψ z) ∧
      (∀ z, cAffine M x (Ψ z) = z) ∧ (∀ w, Ψ (cAffine M x w) = w) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have h1 : M.map (algebraMap ℝ ℂ) * (M⁻¹).map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M hdet,
      Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : (M⁻¹).map (algebraMap ℝ ℂ) * M.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul M hdet,
      Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  let A := (M⁻¹).map (algebraMap ℝ ℂ)
  let xc : Fin n → ℂ := fun i => (x i : ℂ)
  refine ⟨fun z => Matrix.mulVec A (z - xc), ?_, ?_, ?_, ?_⟩
  · apply differentiable_pi.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  · intro z
    have heq : (fun w => Matrix.mulVec A (w - xc)) = fun w => (matrixMulVecCLM A) (w - xc) := by
      ext w
      simp [matrixMulVecCLM_apply]
    rw [heq]
    have h := ((matrixMulVecCLM A).analyticAt (z - xc)).comp_sub xc
    rwa [sub_add_cancel] at h
  · intro z
    ext i
    have heq : cAffine M x (Matrix.mulVec A (z - xc)) i =
        (xc i) + Matrix.mulVec ((M.map (algebraMap ℝ ℂ)) * A) (z - xc) i := by
      simp [cAffine, Matrix.mulVec_mulVec, xc]
    rw [heq, h1, Matrix.one_mulVec]
    simp [xc]
  · intro w
    ext i
    have heq : (cAffine M x w - xc) = Matrix.mulVec (M.map (algebraMap ℝ ℂ)) w := by
      ext j
      simp [cAffine, xc]
    change (A.mulVec (cAffine M x w - xc)) i = w i
    rw [heq]
    have hmul : A.mulVec ((M.map (algebraMap ℝ ℂ)).mulVec w) =
        (A * M.map (algebraMap ℝ ℂ)).mulVec w := by
      simp [Matrix.mulVec_mulVec]
    rw [hmul, h2, Matrix.one_mulVec]

lemma isUnit_of_linearIndependent_cols {n : ℕ} (v : Fin n → (Fin n → ℝ))
    (hv : LinearIndependent ℝ v) : IsUnit (Matrix.of fun i j => v j i) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact hv

lemma sum_pos_smul_mem_of_convex_cone {n : ℕ} (hn : 0 < n) {V : Set (Fin n → ℝ)}
    (hconv : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V) (y : Fin n → ℝ) (hy : ∀ j, 0 < y j) :
    ∑ j, y j • v j ∈ V := by
  have hs : 0 < ∑ j, y j :=
    Finset.sum_pos (fun j _ => hy j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmem : ∑ j, (y j / ∑ k, y k) • v j ∈ V :=
    hconv.sum_mem (fun j _ => (div_pos (hy j) hs).le)
      (by rw [← Finset.sum_div, div_self hs.ne']) (fun j _ => hv j)
  have h := hcone _ hmem (∑ k, y k) hs
  convert h using 1
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  field_simp

lemma cAffine_mem_tube_plus {n : ℕ} (hn : 0 < n) {V : Set (Fin n → ℝ)}
    (hconv : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V) (x : Fin n → ℝ) (w : Fin n → ℂ)
    (hw : ∀ j, 0 < (w j).im) :
    cAffine (Matrix.of fun i j => v j i) x w ∈ TubeDomain V := by
  change (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).im) ∈ V
  rw [cAffine_im]
  have h : Matrix.mulVec (Matrix.of fun i j => v j i) (fun j => (w j).im) =
      ∑ j, (w j).im • v j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h]
  exact sum_pos_smul_mem_of_convex_cone hn hconv hcone v hv _ hw

lemma cAffine_mem_tube_minus {n : ℕ} (hn : 0 < n) {V : Set (Fin n → ℝ)}
    (hconv : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V) (x : Fin n → ℝ) (w : Fin n → ℂ)
    (hw : ∀ j, (w j).im < 0) :
    cAffine (Matrix.of fun i j => v j i) x w ∈
      TubeDomain ((fun u : Fin n → ℝ => -u) '' V) := by
  change (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).im) ∈
    ((fun u : Fin n → ℝ => -u) '' V)
  rw [cAffine_im]
  have h : Matrix.mulVec (Matrix.of fun i j => v j i) (fun j => (w j).im) =
      -∑ j, (-(w j).im) • v j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Finset.sum_neg_distrib]
  rw [h]
  exact ⟨_, sum_pos_smul_mem_of_convex_cone hn hconv hcone v hv _ (fun j => neg_pos.mpr (hw j)),
    rfl⟩

def PosOrthant (n : ℕ) : Set (Fin n → ℝ) := {y | ∀ j, 0 < y j}

def NegOrthant (n : ℕ) : Set (Fin n → ℝ) := {y | ∀ j, y j < 0}

lemma isOpen_PosOrthant (n : ℕ) : IsOpen (PosOrthant n) := by
  have : PosOrthant n = ⋂ j, (fun y : Fin n → ℝ => y j) ⁻¹' Set.Ioi (0 : ℝ) := by
    ext y; simp [PosOrthant]
  rw [this]
  exact isOpen_iInter_of_finite (fun j => isOpen_Ioi.preimage (continuous_apply j))

lemma isOpen_NegOrthant (n : ℕ) : IsOpen (NegOrthant n) := by
  have : NegOrthant n = ⋂ j, (fun y : Fin n → ℝ => y j) ⁻¹' Set.Iio (0 : ℝ) := by
    ext y; simp [NegOrthant]
  rw [this]
  exact isOpen_iInter_of_finite (fun j => isOpen_Iio.preimage (continuous_apply j))

def OrthantEOWCore (n : ℕ) (g : (Fin n → ℂ) → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : (Fin n → ℂ) → ℂ,
    AnalyticOnNhd ℂ G (Metric.ball 0 ρ) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n) ∧ EqOn G g W) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n) ∧ EqOn G g W)

lemma convex_PosOrthant (n : ℕ) : Convex ℝ (PosOrthant n) := by
  intro x hx y hy a b ha hb _hab j
  dsimp [PosOrthant] at hx hy ⊢
  change 0 < a * x j + b * y j
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1
    nlinarith [hy j]
  · have : 0 ≤ b * y j := mul_nonneg hb (hy j).le
    have : 0 < a * x j := mul_pos ha_pos (hx j)
    linarith

lemma convex_NegOrthant (n : ℕ) : Convex ℝ (NegOrthant n) := by
  intro x hx y hy a b ha hb _hab j
  dsimp [NegOrthant] at hx hy ⊢
  change a * x j + b * y j < 0
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1
    nlinarith [hy j]
  · have : b * y j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (hy j).le
    have : a * x j < 0 := mul_neg_of_pos_of_neg ha_pos (hx j)
    linarith

lemma orthantEOWCore_eqOn_plus {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (hg_diff : DifferentiableOn ℂ g (TubeDomain (PosOrthant n)))
    {ρ : ℝ} (_hρ : 0 < ρ) {G : (Fin n → ℂ) → ℂ}
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ))
    {W : Set (Fin n → ℂ)} (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n))
    (hW_eq : EqOn G g W) :
    EqOn G g (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) := by
  have hS_open : IsOpen (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) :=
    Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant n))
  have hS_conv : Convex ℝ (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) :=
    (convex_ball 0 ρ).inter (convex_TubeDomain (convex_PosOrthant n))
  have hd : DifferentiableOn ℂ (G - g) (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) :=
    (hG_an.differentiableOn.mono Set.inter_subset_left).sub
      (hg_diff.mono Set.inter_subset_right)
  have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW_open hW_sub hW_ne
    (fun z hz => by simp [hW_eq hz])
  intro z hz
  simpa [sub_eq_zero] using h0 hz

lemma orthantEOWCore_eqOn_minus {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (hg_diff : DifferentiableOn ℂ g (TubeDomain (NegOrthant n)))
    {ρ : ℝ} (_hρ : 0 < ρ) {G : (Fin n → ℂ) → ℂ}
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ))
    {W : Set (Fin n → ℂ)} (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n))
    (hW_eq : EqOn G g W) :
    EqOn G g (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) := by
  have hS_open : IsOpen (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) :=
    Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant n))
  have hS_conv : Convex ℝ (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) :=
    (convex_ball 0 ρ).inter (convex_TubeDomain (convex_NegOrthant n))
  have hd : DifferentiableOn ℂ (G - g) (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) :=
    (hG_an.differentiableOn.mono Set.inter_subset_left).sub
      (hg_diff.mono Set.inter_subset_right)
  have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW_open hW_sub hW_ne
    (fun z hz => by simp [hW_eq hz])
  intro z hz
  simpa [sub_eq_zero] using h0 hz

lemma eow_local_core_of_orthant {n : ℕ} (hn : 0 < n) (V_plus : Set (Fin n → ℝ))
    (_hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ)
    (v : Fin n → (Fin n → ℝ)) (hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus)
    (h_core : OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x)) :
    LocalEOWCore V_plus f x := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => v j i
  have hM_unit : IsUnit M := isUnit_of_linearIndependent_cols v hli
  obtain ⟨Ψ, hΨ_diff, hΨ_an, hcAffine_inv, hΨ_inv⟩ := exists_inverse_cAffine M hM_unit x
  rcases h_core with ⟨ρ, hρ_pos, G, hG_an,
    ⟨W₁, hW₁o, hW₁n, hW₁s, hW₁e⟩, ⟨W₂, hW₂o, hW₂n, hW₂s, hW₂e⟩⟩
  have hΨ_cont : Continuous Ψ := hΨ_diff.continuous
  have hcAffine_0 : cAffine M x 0 = fun i => (x i : ℂ) := by
    ext i; simp [cAffine]
  have hΨ_xc : Ψ (fun i => (x i : ℂ)) = 0 := by
    rw [← hcAffine_0, hΨ_inv 0]
  have h_open_pre : IsOpen (Ψ ⁻¹' (Metric.ball 0 ρ)) := Metric.isOpen_ball.preimage hΨ_cont
  have h_xc_in : (fun i => (x i : ℂ)) ∈ Ψ ⁻¹' (Metric.ball 0 ρ) := by
    simp [hΨ_xc, Metric.mem_ball_self hρ_pos]
  rcases Metric.isOpen_iff.mp h_open_pre _ h_xc_in with ⟨r, hr_pos, hr_sub⟩
  let F : (Fin n → ℂ) → ℂ := G ∘ Ψ
  have hF_an : AnalyticOnNhd ℂ F (Metric.ball (fun i => (x i : ℂ)) r) := by
    intro z hz
    have hz_in : Ψ z ∈ Metric.ball 0 ρ := hr_sub hz
    exact (hG_an (Ψ z) hz_in).comp (hΨ_an z)
  have hg_diff_plus : DifferentiableOn ℂ (f ∘ cAffine M x) (TubeDomain (PosOrthant n)) :=
    h_holo_plus.comp (differentiable_cAffine M x).differentiableOn
      (fun w hw => cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hw)
  have h_eq₁ := orthantEOWCore_eqOn_plus (f ∘ cAffine M x)
    hg_diff_plus hρ_pos hG_an hW₁o hW₁n hW₁s hW₁e
  have hg_diff_minus : DifferentiableOn ℂ (f ∘ cAffine M x) (TubeDomain (NegOrthant n)) :=
    h_holo_minus.comp (differentiable_cAffine M x).differentiableOn
      (fun w hw => cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hw)
  have h_eq₂ := orthantEOWCore_eqOn_minus (f ∘ cAffine M x)
    hg_diff_minus hρ_pos hG_an hW₂o hW₂n hW₂s hW₂e
  refine ⟨r, hr_pos, F, hF_an, ?_, ?_⟩
  · let W₁' : Set (Fin n → ℂ) :=
      Ψ ⁻¹' (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) ∩ Metric.ball (fun i => (x i : ℂ)) r
    have hW₁'_open : IsOpen W₁' :=
      (Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant n))).preimage
        hΨ_cont |>.inter Metric.isOpen_ball
    have hW₁'_sub : W₁' ⊆ Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_plus := by
      rintro z ⟨⟨_hz_ball_ρ, hz_tube_orth⟩, hz_ball_r⟩
      refine ⟨hz_ball_r, ?_⟩
      have h := cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x (Ψ z) hz_tube_orth
      rwa [hcAffine_inv z] at h
    have hW₁'_eq : EqOn F f W₁' := by
      rintro z ⟨hz_orth, _⟩
      dsimp [F]
      have h1 := h_eq₁ hz_orth
      dsimp [Function.comp] at h1
      rw [h1, hcAffine_inv z]
    have h_cAff_cont : Continuous (cAffine M x) := (differentiable_cAffine M x).continuous
    have h_tend : Filter.Tendsto (cAffine M x) (nhds 0) (nhds (fun i => (x i : ℂ))) := by
      rw [← hcAffine_0]
      exact h_cAff_cont.continuousAt
    have h_ball_nhd : Metric.ball (fun i => (x i : ℂ)) r ∈ nhds (fun i => (x i : ℂ)) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)
    have h_pre_nhd : Metric.ball 0 ρ ∈ nhds (0 : Fin n → ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ_pos)
    let curve : ℝ → (Fin n → ℂ) := fun t => fun _ => (t : ℂ) * Complex.I
    have hcurve_cont : Continuous curve := by
      unfold curve; fun_prop
    have hcurve_0 : curve 0 = 0 := by ext i; simp [curve]
    have h_ev_ball_ρ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), curve t ∈ Metric.ball 0 ρ := by
      have htend : Filter.Tendsto curve (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_pre_nhd
    have h_ev_ball_r : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        cAffine M x (curve t) ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      have htend : Filter.Tendsto (cAffine M x ∘ curve) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (fun i => (x i : ℂ))) := by
        refine h_tend.comp ?_
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_ball_nhd
    have h_ev_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ⟨ht_bρ, ht_br⟩, ht_pos⟩ := (h_ev_ball_ρ.and h_ev_ball_r).and h_ev_pos |>.exists
    have hw₀_pos : ∀ j, 0 < (curve t j).im := by
      intro j
      dsimp [curve]
      simp [Complex.mul_im, ht_pos]
    have hz₀_in : cAffine M x (curve t) ∈ W₁' := by
      refine ⟨?_, ht_br⟩
      rw [Set.mem_preimage, hΨ_inv (curve t)]
      exact ⟨ht_bρ, hw₀_pos⟩
    exact ⟨W₁', hW₁'_open, ⟨cAffine M x (curve t), hz₀_in⟩, hW₁'_sub, hW₁'_eq⟩
  · let W₂' : Set (Fin n → ℂ) :=
      Ψ ⁻¹' (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) ∩ Metric.ball (fun i => (x i : ℂ)) r
    have hW₂'_open : IsOpen W₂' :=
      (Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant n))).preimage
        hΨ_cont |>.inter Metric.isOpen_ball
    have hW₂'_sub : W₂' ⊆
        Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain ((fun v => -v) '' V_plus) := by
      rintro z ⟨⟨_hz_ball_ρ, hz_tube_orth⟩, hz_ball_r⟩
      refine ⟨hz_ball_r, ?_⟩
      have h := cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x (Ψ z) hz_tube_orth
      rwa [hcAffine_inv z] at h
    have hW₂'_eq : EqOn F f W₂' := by
      rintro z ⟨hz_orth, _⟩
      dsimp [F]
      have h1 := h_eq₂ hz_orth
      dsimp [Function.comp] at h1
      rw [h1, hcAffine_inv z]
    have h_cAff_cont : Continuous (cAffine M x) := (differentiable_cAffine M x).continuous
    have h_tend : Filter.Tendsto (cAffine M x) (nhds 0) (nhds (fun i => (x i : ℂ))) := by
      rw [← hcAffine_0]
      exact h_cAff_cont.continuousAt
    have h_ball_nhd : Metric.ball (fun i => (x i : ℂ)) r ∈ nhds (fun i => (x i : ℂ)) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)
    have h_pre_nhd : Metric.ball 0 ρ ∈ nhds (0 : Fin n → ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ_pos)
    let curve : ℝ → (Fin n → ℂ) := fun t => fun _ => - ((t : ℂ) * Complex.I)
    have hcurve_cont : Continuous curve := by
      unfold curve; fun_prop
    have hcurve_0 : curve 0 = 0 := by ext i; simp [curve]
    have h_ev_ball_ρ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), curve t ∈ Metric.ball 0 ρ := by
      have htend : Filter.Tendsto curve (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_pre_nhd
    have h_ev_ball_r : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        cAffine M x (curve t) ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      have htend : Filter.Tendsto (cAffine M x ∘ curve) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (fun i => (x i : ℂ))) := by
        refine h_tend.comp ?_
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_ball_nhd
    have h_ev_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ⟨ht_bρ, ht_br⟩, ht_pos⟩ := (h_ev_ball_ρ.and h_ev_ball_r).and h_ev_pos |>.exists
    have hw₀_neg : ∀ j, (curve t j).im < 0 := by
      intro j
      dsimp [curve]
      simp [Complex.mul_im, ht_pos]
    have hz₀_in : cAffine M x (curve t) ∈ W₂' := by
      refine ⟨?_, ht_br⟩
      rw [Set.mem_preimage, hΨ_inv (curve t)]
      exact ⟨ht_bρ, hw₀_neg⟩
    exact ⟨W₂', hW₂'_open, ⟨cAffine M x (curve t), hz₀_in⟩, hW₂'_sub, hW₂'_eq⟩

lemma div_add_one_mul_lt {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    ((r / 2) / (v + 1)) * v < r := by
  have hv1 : 0 < v + 1 := by linarith
  have h1 : v / (v + 1) < 1 := (div_lt_one hv1).mpr (lt_add_one v)
  have h2 : ((r / 2) / (v + 1)) * v = (r / 2) * (v / (v + 1)) := by ring
  rw [h2]
  calc (r / 2) * (v / (v + 1))
    _ < (r / 2) * 1 := mul_lt_mul_of_pos_left h1 (half_pos hr)
    _ = r / 2 := mul_one _
    _ < r := half_lt_self hr

lemma eow_local_core_0d (V_plus _U : Set (Fin 0 → ℝ))
    (hV_plus_ne : V_plus.Nonempty)
    (f : (Fin 0 → ℂ) → ℂ)
    (x : Fin 0 → ℝ) :
    LocalEOWCore V_plus f x := by
  refine ⟨1, by positivity, f, ?_, ?_, ?_⟩
  · have heq : f = fun _ => f (fun _ => 0) := by
      ext y; congr; ext i; exact Fin.elim0 i
    rw [heq]
    intro z _hz
    exact analyticAt_const
  · refine ⟨Metric.ball (fun i => (x i : ℂ)) 1, Metric.isOpen_ball,
      Metric.nonempty_ball.mpr (by positivity), ?_, fun z _ => rfl⟩
    intro z hz
    refine ⟨hz, ?_⟩
    change (fun i => (z i).im) ∈ V_plus
    obtain ⟨v0, hv0⟩ := hV_plus_ne
    have hv0_eq : v0 = (fun i => (z i).im) := by ext i; exact Fin.elim0 i
    rw [← hv0_eq]
    exact hv0
  · refine ⟨Metric.ball (fun i => (x i : ℂ)) 1, Metric.isOpen_ball,
      Metric.nonempty_ball.mpr (by positivity), ?_, fun z _ => rfl⟩
    intro z hz
    refine ⟨hz, ?_⟩
    obtain ⟨v0, hv0⟩ := hV_plus_ne
    refine ⟨v0, hv0, ?_⟩
    ext i
    exact Fin.elim0 i

lemma eow_local_core_1d (V_plus U : Set (Fin 1 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin 1 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)))
    (x : Fin 1 → ℝ) (hx_U : x ∈ U) :
    LocalEOWCore V_plus f x := by
  rcases Metric.isOpen_iff.mp hU_open x hx_U with ⟨r_U, hr_U_pos, hr_U_sub⟩
  rcases exists_local_analytic_extension_cauchy_1d V_plus U hV_plus_open hV_plus_cone
    hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U r_U hr_U_pos hr_U_sub with
    ⟨F_1, hF_ana, hF_eq⟩
  rcases analyticOnNhd_ball_of_analyticAt hF_ana with ⟨ρ, hρ_pos, hF_nhd⟩
  let r := min ρ r_U
  have hr_pos : 0 < r := lt_min hρ_pos hr_U_pos
  refine ⟨r, hr_pos, F_1, hF_nhd.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_, ?_⟩
  · let W₁ := Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_plus
    have hW₁_open : IsOpen W₁ := Metric.isOpen_ball.inter (isOpen_TubeDomain hV_plus_open)
    obtain ⟨v, hv, _⟩ := exists_ne_zero_of_open_cone_1d V_plus hV_plus_open hV_plus_cone hV_plus_ne
    have h_norm_v : 0 < ‖v 0‖ + 1 := by positivity
    let t := (r / 2) / (‖v 0‖ + 1)
    have ht_pos : 0 < t := div_pos (half_pos hr_pos) h_norm_v
    let z : Fin 1 → ℂ := fun i => (x i : ℂ) + (t : ℂ) * Complex.I * (v i : ℂ)
    have hz_im : (fun i => (z i).im) = fun i => t * v i := by
      ext i; simp [z, Complex.mul_im]
    have hz_tube : z ∈ TubeDomain V_plus := by
      change (fun i => (z i).im) ∈ V_plus
      rw [hz_im]
      exact hV_plus_cone v hv t ht_pos
    have hz_ball : z ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      rw [Metric.mem_ball]
      apply (dist_pi_lt_iff hr_pos).mpr
      intro i
      fin_cases i
      dsimp [z]
      rw [dist_eq_norm]
      have heq : (x 0 : ℂ) + (t : ℂ) * Complex.I * (v 0 : ℂ) - (x 0 : ℂ) =
          (t : ℂ) * Complex.I * (v 0 : ℂ) := by ring
      rw [heq, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht_pos.le, Complex.norm_real]
      exact div_add_one_mul_lt hr_pos (norm_nonneg _)
    have hW₁_ne : W₁.Nonempty := ⟨z, hz_ball, hz_tube⟩
    refine ⟨W₁, hW₁_open, hW₁_ne, subset_rfl, ?_⟩
    intro w hw
    have hw_ball_rU : w ∈ Metric.ball (fun i => (x i : ℂ)) r_U :=
      (Metric.ball_subset_ball (min_le_right ρ r_U)) hw.1
    have hw_wedge : w ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U :=
      Or.inl (Or.inl hw.2)
    exact hF_eq ⟨hw_ball_rU, hw_wedge⟩
  · let W₂ := Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain ((fun v => -v) '' V_plus)
    have hW₂_open : IsOpen W₂ :=
      Metric.isOpen_ball.inter (isOpen_TubeDomain_minus V_plus hV_plus_open)
    obtain ⟨v, hv, _⟩ := exists_ne_zero_of_open_cone_1d V_plus hV_plus_open hV_plus_cone hV_plus_ne
    have h_norm_v : 0 < ‖v 0‖ + 1 := by positivity
    let t := (r / 2) / (‖v 0‖ + 1)
    have ht_pos : 0 < t := div_pos (half_pos hr_pos) h_norm_v
    let z : Fin 1 → ℂ := fun i => (x i : ℂ) - (t : ℂ) * Complex.I * (v i : ℂ)
    have hz_im : (fun i => (z i).im) = fun i => - (t * v i) := by
      ext i; simp [z, Complex.sub_im, Complex.mul_im]
    have hz_tube : z ∈ TubeDomain ((fun v => -v) '' V_plus) := by
      change (fun i => (z i).im) ∈ ((fun v => -v) '' V_plus)
      rw [hz_im]
      refine ⟨fun i => t * v i, hV_plus_cone v hv t ht_pos, ?_⟩
      ext i; simp
    have hz_ball : z ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      rw [Metric.mem_ball]
      apply (dist_pi_lt_iff hr_pos).mpr
      intro i
      fin_cases i
      dsimp [z]
      rw [dist_eq_norm]
      have heq : (x 0 : ℂ) - (t : ℂ) * Complex.I * (v 0 : ℂ) - (x 0 : ℂ) =
          - ((t : ℂ) * Complex.I * (v 0 : ℂ)) := by ring
      rw [heq, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht_pos.le, Complex.norm_real]
      exact div_add_one_mul_lt hr_pos (norm_nonneg _)
    have hW₂_ne : W₂.Nonempty := ⟨z, hz_ball, hz_tube⟩
    refine ⟨W₂, hW₂_open, hW₂_ne, subset_rfl, ?_⟩
    intro w hw
    have hw_ball_rU : w ∈ Metric.ball (fun i => (x i : ℂ)) r_U :=
      (Metric.ball_subset_ball (min_le_right ρ r_U)) hw.1
    have hw_wedge : w ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U :=
      Or.inl (Or.inr hw.2)
    exact hF_eq ⟨hw_ball_rU, hw_wedge⟩

lemma orthant_eow_core_1d
    (V_plus U : Set (Fin 1 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 1 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)))
    (x : Fin 1 → ℝ) (hx_U : x ∈ U)
    (v : Fin 1 → (Fin 1 → ℝ)) (_hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus) :
    OrthantEOWCore 1 (f ∘ cAffine (Matrix.of fun i j => v j i) x) := by
  let M : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun i j => v j i
  have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (v 0) (hv 0)
  rcases Metric.mem_nhds_iff.mp h_slice.eventually_analyticAt with ⟨ρ, hρ_pos, hg_an⟩
  let G : (Fin 1 → ℂ) → ℂ := fun w => slice_fun f (fun i => (x i : ℂ)) (v 0) (w 0)
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ) := by
    intro w hw
    have hw0 : w 0 ∈ Metric.ball 0 ρ := by
      rw [Metric.mem_ball] at hw ⊢
      have hle := dist_le_pi_dist w 0 0
      exact lt_of_le_of_lt hle hw
    let P : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (0 : Fin 1)
    have hP : AnalyticAt ℂ P w := P.analyticAt w
    exact AnalyticAt.comp (f := P) (hg_an hw0) hP
  refine ⟨ρ, hρ_pos, G, hG_an, ?_, ?_⟩
  · let W₁ := Metric.ball (0 : Fin 1 → ℂ) ρ ∩ TubeDomain (PosOrthant 1)
    have hW₁_open : IsOpen W₁ := Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant 1))
    have hW₁_ne : W₁.Nonempty := by
      let z : Fin 1 → ℂ := fun _ => ((ρ / 2 : ℝ) : ℂ) * Complex.I
      refine ⟨z, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball]
        apply (dist_pi_lt_iff hρ_pos).mpr
        intro i; fin_cases i
        dsimp [z]
        rw [dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (half_pos hρ_pos).le]
        exact half_lt_self hρ_pos
      · intro i; fin_cases i
        dsimp [z]
        simp [Complex.mul_im, half_pos hρ_pos]
    refine ⟨W₁, hW₁_open, hW₁_ne, subset_rfl, ?_⟩
    intro w _hw
    dsimp [G, Function.comp, slice_fun]
    congr 1
    ext i; fin_cases i
    simp [cAffine, Matrix.mulVec, dotProduct]
    ring
  · let W₂ := Metric.ball (0 : Fin 1 → ℂ) ρ ∩ TubeDomain (NegOrthant 1)
    have hW₂_open : IsOpen W₂ := Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant 1))
    have hW₂_ne : W₂.Nonempty := by
      let z : Fin 1 → ℂ := fun _ => - (((ρ / 2 : ℝ) : ℂ) * Complex.I)
      refine ⟨z, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball]
        apply (dist_pi_lt_iff hρ_pos).mpr
        intro i; fin_cases i
        dsimp [z]
        rw [dist_zero_right, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (half_pos hρ_pos).le]
        exact half_lt_self hρ_pos
      · intro i; fin_cases i
        dsimp [z]
        simp [Complex.mul_im, half_pos hρ_pos]
    refine ⟨W₂, hW₂_open, hW₂_ne, subset_rfl, ?_⟩
    intro w _hw
    dsimp [G, Function.comp, slice_fun]
    congr 1
    ext i; fin_cases i
    simp [cAffine, Matrix.mulVec, dotProduct]
    ring

lemma eow_orthant_core {n : ℕ} (hn : n = 1)
    (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U)
    (v : Fin n → (Fin n → ℝ)) (hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus) :
    OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x) := by
  subst hn
  exact orthant_eow_core_1d V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hli hv

lemma eow_local_core {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (_hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    LocalEOWCore V_plus f x := by
  by_cases h0 : n = 0
  · subst h0
    exact eow_local_core_0d V_plus U hV_plus_ne f x
  · have h1 : n = 1 := by omega
    subst h1
    exact eow_local_core_1d V_plus U hV_plus_open hV_plus_cone hV_plus_ne hU_open f
      h_cont h_holo_plus h_holo_minus x hx_U

lemma exists_local_analytic_extension_cauchy {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (_hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) (r : ℝ) (hr : 0 < r)
    (h_ball_U : Metric.ball x r ⊆ U) :
    ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  by_cases h_dim0 : n = 0
  · subst h_dim0
    use f
    refine ⟨?_, fun z _ => rfl⟩
    have heq : f = fun _ => f (fun _ => 0) := by
      ext y; congr; ext i; exact Fin.elim0 i
    rw [heq]
    exact analyticAt_const
  · have h_dim1 : n = 1 := by omega
    subst h_dim1
    exact exists_local_analytic_extension_cauchy_1d V_plus U hV_plus_open hV_plus_cone
      hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U r hr h_ball_U

lemma eow_local_analytic_at {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    ∃ (F_x : (Fin n → ℂ) → ℂ) (r : ℝ), 0 < r ∧
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  rcases Metric.isOpen_iff.mp hU_open x hx_U with ⟨r_U, hr_U_pos, hr_U_sub⟩
  have ⟨v, hv⟩ := hV_plus_ne
  by_cases h_dim : n = 0
  · subst h_dim
    use f, 1
    refine ⟨by positivity, ?_, ?_⟩
    · have heq : f = fun _ => f (fun _ => 0) := by
        ext y
        congr
        ext i
        exact Fin.elim0 i
      rw [heq]
      exact analyticAt_const
    · intro z _
      rfl
  · have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
      h_holo_plus h_holo_minus x hx_U v hv
    have h_open : IsOpen {w | AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) v) w} :=
      isOpen_analyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) v)
    rcases Metric.isOpen_iff.mp h_open 0 h_slice with ⟨ρ, hρ_pos, hρ_sub⟩
    let r := min (r_U / 2) (ρ / 2)
    have hr_pos : 0 < r := lt_min (half_pos hr_U_pos) (half_pos hρ_pos)
    have h_ball_U : Metric.ball x r ⊆ U := by
      intro y hy
      have h1 : dist y x < r_U := lt_of_lt_of_le (Metric.mem_ball.mp hy)
        ((min_le_left (r_U / 2) (ρ / 2)).trans (half_le_self hr_U_pos.le))
      exact hr_U_sub (Metric.mem_ball.mpr h1)
    have h_exists_loc := exists_local_analytic_extension_cauchy hn_le V_plus U hV_plus_open
      hV_plus_convex hV_plus_cone hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U r
      hr_pos h_ball_U
    rcases h_exists_loc with ⟨F_x, hF_ana, hF_eq⟩
    exact ⟨F_x, r, hr_pos, hF_ana, hF_eq⟩

lemma eow_local_exists {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  rcases eow_local_analytic_at hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
    hU_open f h_cont h_holo_plus h_holo_minus x hx_U with ⟨F_x, r_eq, hr_eq_pos, hF_ana, hF_eq⟩
  rcases exists_ball_subset_and_analyticOnNhd hU_open hx_U hF_ana with
    ⟨r_ball, hr_ball_pos, h_sub, h_ana_nhd⟩
  let r_x := min r_eq r_ball
  have hr_x_pos : 0 < r_x := lt_min hr_eq_pos hr_ball_pos
  refine ⟨r_x, hr_x_pos, (Metric.ball_subset_ball (min_le_right r_eq r_ball)).trans h_sub,
    F_x, ?_, ?_⟩
  · exact h_ana_nhd.mono (Metric.ball_subset_ball (min_le_right r_eq r_ball))
  · have h_ball_sub : Metric.ball (fun i => (x i : ℂ)) r_x ⊆
        Metric.ball (fun i => (x i : ℂ)) r_eq :=
      Metric.ball_subset_ball (min_le_left r_eq r_ball)
    exact hF_eq.mono (inter_subset_inter_left _ h_ball_sub)

lemma eow_nd_local_extension {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ (r : (Fin n → ℝ) → ℝ) (_hr : ∀ x ∈ U, 0 < r x) (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x))) ∧
      (∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U)) ∧
      (∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
          Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) := by
  have h_exists : ∀ x ∈ U, ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
    intro x hx
    exact eow_local_exists hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
      hU_open f h_cont h_holo_plus h_holo_minus x hx
  exact local_extension_assembly V_plus U f h_exists (eow_local_compat V_plus U f)

lemma differentiableOn_iUnion_of_locally_differentiable {ι : Type*} (s : ι → Set (Fin n → ℂ))
    (hs : ∀ i, IsOpen (s i)) (F_i : ι → (Fin n → ℂ) → ℂ)
    (h_diff : ∀ i, DifferentiableOn ℂ (F_i i) (s i))
    (h_compat : ∀ i j, EqOn (F_i i) (F_i j) (s i ∩ s j)) :
    ∃ F : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ F (⋃ i, s i) ∧
      ∀ i, EqOn F (F_i i) (s i) := by
  classical
  let F : (Fin n → ℂ) → ℂ := fun z =>
    if h : ∃ i, z ∈ s i then F_i (Classical.choose h) z else 0
  have hF_eq : ∀ i, EqOn F (F_i i) (s i) := by
    intro i z hz
    have h : ∃ j, z ∈ s j := ⟨i, hz⟩
    dsimp [F]
    rw [dif_pos h]
    let j := Classical.choose h
    have hj : z ∈ s j := Classical.choose_spec h
    have hz_inter : z ∈ s j ∩ s i := ⟨hj, hz⟩
    exact h_compat j i hz_inter
  refine ⟨F, ?_, hF_eq⟩
  intro z hz
  simp only [mem_iUnion] at hz
  rcases hz with ⟨i, hi⟩
  have h_nhds : s i ∈ nhds z := (hs i).mem_nhds hi
  rw [← differentiableWithinAt_inter h_nhds]
  have h_sub : (⋃ j, s j) ∩ s i = s i := inter_eq_right.mpr (subset_iUnion s i)
  rw [h_sub]
  have h_diff_i : DifferentiableWithinAt ℂ (F_i i) (s i) z := h_diff i z hi
  exact DifferentiableWithinAt.congr h_diff_i (fun w hw => hF_eq i hw) (hF_eq i hi)

inductive WedgeCoverIdx (U : Set (Fin n → ℝ))
  | plus : WedgeCoverIdx U
  | minus : WedgeCoverIdx U
  | loc (x : U) : WedgeCoverIdx U

def coverSet (V_plus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) : WedgeCoverIdx U → Set (Fin n → ℂ)
  | .plus => TubeDomain V_plus
  | .minus => TubeDomain ((fun v => -v) '' V_plus)
  | .loc ⟨x, _hx⟩ => Metric.ball (fun i => (x i : ℂ)) (r x)

def coverFun (U : Set (Fin n → ℝ)) (f : (Fin n → ℂ) → ℂ)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ) :
    WedgeCoverIdx U → (Fin n → ℂ) → ℂ
  | .plus => f
  | .minus => f
  | .loc ⟨x, _hx⟩ => F_loc x

lemma iUnion_coverSet (V_plus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) :
    (⋃ i, coverSet V_plus U r i) =
    TubeDomain V_plus ∪ TubeDomain ((fun v => -v) '' V_plus) ∪
      ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x) := by
  ext z
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | plus => left; left; exact hi
    | minus => left; right; exact hi
    | loc x => right; exact ⟨x.1, x.2, hi⟩
  · rintro ((h | h) | ⟨x, hx, h⟩)
    · exact ⟨.plus, h⟩
    · exact ⟨.minus, h⟩
    · exact ⟨.loc ⟨x, hx⟩, h⟩

lemma eow_nd_compat (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (r : (Fin n → ℝ) → ℝ)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_eq : ∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
      WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (hF_compat : ∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
      (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩ Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∀ i j : WedgeCoverIdx U, EqOn (coverFun U f F_loc i) (coverFun U f F_loc j)
      (coverSet V_plus U r i ∩ coverSet V_plus U r j) := by
  intro i j z hz
  cases i with
  | plus =>
    cases j with
    | plus => rfl
    | minus => rfl
    | loc x =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.2
      have hz_plus : z ∈ TubeDomain V_plus := hz.1
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; left; exact hz_plus
      have h := hF_eq x hx ⟨hz_loc, hz_wedge⟩
      exact h.symm
  | minus =>
    cases j with
    | plus => rfl
    | minus => rfl
    | loc x =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.2
      have hz_minus : z ∈ TubeDomain ((fun v => -v) '' V_plus) := hz.1
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; right; exact hz_minus
      have h := hF_eq x hx ⟨hz_loc, hz_wedge⟩
      exact h.symm
  | loc x =>
    cases j with
    | plus =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.1
      have hz_plus : z ∈ TubeDomain V_plus := hz.2
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; left; exact hz_plus
      exact hF_eq x hx ⟨hz_loc, hz_wedge⟩
    | minus =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.1
      have hz_minus : z ∈ TubeDomain ((fun v => -v) '' V_plus) := hz.2
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; right; exact hz_minus
      exact hF_eq x hx ⟨hz_loc, hz_wedge⟩
    | loc y =>
      exact hF_compat x y hz

lemma eow_nd_glue (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (_hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (_hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (_h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ U, 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_holo : ∀ x ∈ U, DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_eq : ∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
      WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (hF_compat : ∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
      (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩ Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∃ F : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ F (TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
        ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)) ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  have hs_open : ∀ i : WedgeCoverIdx U, IsOpen (coverSet V_plus U r i) := by
    intro i
    cases i with
    | plus => exact isOpen_TubeDomain hV_plus_open
    | minus => exact isOpen_TubeDomain_minus V_plus hV_plus_open
    | loc x => exact Metric.isOpen_ball
  have h_diff : ∀ i : WedgeCoverIdx U,
      DifferentiableOn ℂ (coverFun U f F_loc i) (coverSet V_plus U r i) := by
    intro i
    cases i with
    | plus => exact h_holo_plus
    | minus => exact h_holo_minus
    | loc x => exact hF_holo x.1 x.2
  have h_compat : ∀ i j : WedgeCoverIdx U, EqOn (coverFun U f F_loc i) (coverFun U f F_loc j)
      (coverSet V_plus U r i ∩ coverSet V_plus U r j) :=
    eow_nd_compat V_plus U f r F_loc hF_eq hF_compat
  rcases differentiableOn_iUnion_of_locally_differentiable (coverSet V_plus U r) hs_open
    (coverFun U f F_loc) h_diff h_compat with ⟨F, hF_diff, hF_eq_i⟩
  rw [iUnion_coverSet] at hF_diff
  refine ⟨F, hF_diff, ?_⟩
  intro z hz
  simp only [WedgeDomain, mem_union, mem_setOf_eq] at hz
  rcases hz with ((h_plus | h_minus) | ⟨hx_re, hx_im⟩)
  · exact hF_eq_i .plus h_plus
  · exact hF_eq_i .minus h_minus
  · let x : Fin n → ℝ := fun i => (z i).re
    have hx_U : x ∈ U := hx_re
    have hx_eq : z = fun i => (x i : ℂ) := by
      ext i
      have h_im : (z i).im = 0 := congr_fun hx_im i
      exact Complex.ext rfl (by simp [x, h_im])
    have hz_ball : z ∈ coverSet V_plus U r (.loc ⟨x, hx_U⟩) := by
      dsimp [coverSet]
      rw [hx_eq]
      exact Metric.mem_ball_self (hr x hx_U)
    have h1 := hF_eq_i (.loc ⟨x, hx_U⟩) hz_ball
    have h2 := hF_eq x hx_U ⟨hz_ball, by
      simp only [WedgeDomain, mem_union, mem_setOf_eq]
      right; exact ⟨hx_re, hx_im⟩⟩
    exact h1.trans h2

lemma eow_nd_continuation {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) ⊆ W ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  rcases eow_nd_local_extension hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
    hU_open f h_cont h_holo_plus h_holo_minus with
    ⟨r, hr, F_loc, hF_holo, hF_eq, hF_compat⟩
  let W : Set (Fin n → ℂ) :=
    TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)
  have hW_open : IsOpen W := isOpen_wedge_neighborhood V_plus U hV_plus_open r
  have hW_sub : WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U ⊆ W :=
    wedge_subset_union_balls V_plus U r hr
  refine ⟨W, hW_open, hW_sub, ?_⟩
  exact eow_nd_glue V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus r hr F_loc hF_holo hF_eq hF_compat

theorem eow_le_one_dim {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) ⊆ W ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  exact eow_nd_continuation hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
    hU_open f h_cont h_holo_plus h_holo_minus

open Analysis

def consFin {k : ℕ} (w' : Fin k → ℂ) (wk : ℂ) : Fin (k + 1) → ℂ :=
  Fin.snoc w' wk

def initFin {k : ℕ} (w : Fin (k + 1) → ℂ) : Fin k → ℂ :=
  fun i => w (Fin.castSucc i)

def lastFin {k : ℕ} (w : Fin (k + 1) → ℂ) : ℂ :=
  w (Fin.last k)

def lastFinR {k : ℕ} (r : Fin (k + 1) → ℝ) : ℝ :=
  r (Fin.last k)

def initFinR {k : ℕ} (r : Fin (k + 1) → ℝ) : Fin k → ℝ :=
  fun i => r (Fin.castSucc i)

lemma consFin_init_last {k : ℕ} (w : Fin (k + 1) → ℂ) :
    consFin (initFin w) (lastFin w) = w := by
  ext i
  dsimp [consFin, initFin, lastFin]
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro j
    rw [Fin.snoc_castSucc]
    rfl

lemma initFin_consFin {k : ℕ} (w' : Fin k → ℂ) (wk : ℂ) :
    initFin (consFin w' wk) = w' := by
  ext i
  dsimp [initFin, consFin]
  rw [Fin.snoc_castSucc]

lemma lastFin_consFin {k : ℕ} (w' : Fin k → ℂ) (wk : ℂ) :
    lastFin (consFin w' wk) = wk := by
  dsimp [lastFin, consFin]
  rw [Fin.snoc_last]

lemma continuous_initFin {k : ℕ} :
    Continuous (initFin (k := k)) := by
  apply continuous_pi
  intro i
  exact continuous_apply (Fin.castSucc i)

lemma continuous_lastFin {k : ℕ} :
    Continuous (lastFin (k := k)) :=
  continuous_apply (Fin.last k)

lemma continuous_consFin {k : ℕ} :
    Continuous (fun (p : (Fin k → ℂ) × ℂ) => consFin p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ ?_ i
  · have h : (fun (p : (Fin k → ℂ) × ℂ) => consFin p.1 p.2 (Fin.last k)) = Prod.snd := by
      ext p; dsimp [consFin]; rw [Fin.snoc_last]
    rw [h]
    exact continuous_snd
  · intro j
    have h : (fun (p : (Fin k → ℂ) × ℂ) => consFin p.1 p.2 (Fin.castSucc j)) =
        (fun p => p.1 j) := by
      ext p; dsimp [consFin]; rw [Fin.snoc_castSucc]
    rw [h]
    exact (continuous_apply j).comp continuous_fst

lemma consFin_mem_pos_orthant_iff {k : ℕ} (w : Fin (k + 1) → ℂ) :
    w ∈ TubeDomain (PosOrthant (k + 1)) ↔
      initFin w ∈ TubeDomain (PosOrthant k) ∧ 0 < (lastFin w).im := by
  constructor
  · intro hw
    refine ⟨fun i => hw (Fin.castSucc i), hw (Fin.last k)⟩
  · intro ⟨hw', hwk⟩ j
    refine Fin.lastCases ?_ ?_ j
    · exact hwk
    · intro i
      exact hw' i

lemma consFin_mem_neg_orthant_iff {k : ℕ} (w : Fin (k + 1) → ℂ) :
    w ∈ TubeDomain (NegOrthant (k + 1)) ↔
      initFin w ∈ TubeDomain (NegOrthant k) ∧ (lastFin w).im < 0 := by
  constructor
  · intro hw
    refine ⟨fun i => hw (Fin.castSucc i), hw (Fin.last k)⟩
  · intro ⟨hw', hwk⟩ j
    refine Fin.lastCases ?_ ?_ j
    · exact hwk
    · intro i
      exact hw' i

lemma consFin_mem_ball {k : ℕ} {r : ℝ} (hr : 0 < r)
    {w' : Fin k → ℂ} (hw' : w' ∈ Metric.ball (0 : Fin k → ℂ) r)
    {wk : ℂ} (hwk : wk ∈ Metric.ball (0 : ℂ) r) :
    consFin w' wk ∈ Metric.ball (0 : Fin (k + 1) → ℂ) r := by
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hr).mpr
  intro i
  refine Fin.lastCases ?_ ?_ i
  · dsimp [consFin]
    rw [Fin.snoc_last]
    exact Metric.mem_ball.mp hwk
  · intro j
    have hj : consFin w' wk (Fin.castSucc j) = w' j := by
      dsimp [consFin]; rw [Fin.snoc_castSucc]
    rw [hj]
    exact (dist_le_pi_dist w' 0 j).trans_lt (Metric.mem_ball.mp hw')

lemma initFin_mem_ball {k : ℕ} {r : ℝ}
    {w : Fin (k + 1) → ℂ} (hw : w ∈ Metric.ball (0 : Fin (k + 1) → ℂ) r) :
    initFin w ∈ Metric.ball (0 : Fin k → ℂ) r := by
  rw [Metric.mem_ball] at hw ⊢
  apply (dist_pi_lt_iff (lt_of_le_of_lt dist_nonneg hw)).mpr
  intro i
  dsimp [initFin]
  exact (dist_le_pi_dist w 0 (Fin.castSucc i)).trans_lt hw

lemma lastFin_mem_ball {k : ℕ} {r : ℝ}
    {w : Fin (k + 1) → ℂ} (hw : w ∈ Metric.ball (0 : Fin (k + 1) → ℂ) r) :
    lastFin w ∈ Metric.ball (0 : ℂ) r := by
  rw [Metric.mem_ball] at hw ⊢
  dsimp [lastFin]
  exact (dist_le_pi_dist w 0 (Fin.last k)).trans_lt hw

def prodOpenSet {k : ℕ} (W' : Set (Fin k → ℂ)) (D : Set ℂ) : Set (Fin (k + 1) → ℂ) :=
  initFin ⁻¹' W' ∩ lastFin ⁻¹' D

lemma isOpen_prodOpenSet {k : ℕ} {W' : Set (Fin k → ℂ)} (hW' : IsOpen W')
    {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (prodOpenSet W' D) :=
  (hW'.preimage continuous_initFin).inter (hD.preimage continuous_lastFin)

lemma nonempty_prodOpenSet {k : ℕ} {W' : Set (Fin k → ℂ)} (hW' : W'.Nonempty)
    {D : Set ℂ} (hD : D.Nonempty) :
    (prodOpenSet W' D).Nonempty := by
  rcases hW' with ⟨w', hw'⟩
  rcases hD with ⟨z, hz⟩
  refine ⟨consFin w' z, ?_⟩
  dsimp [prodOpenSet]
  rw [mem_inter_iff, mem_preimage, mem_preimage, initFin_consFin, lastFin_consFin]
  exact ⟨hw', hz⟩

lemma prodOpenSet_subset_pos_orthant {k : ℕ}
    {W' : Set (Fin k → ℂ)} (hW' : W' ⊆ TubeDomain (PosOrthant k))
    {D : Set ℂ} (hD : D ⊆ {z : ℂ | 0 < z.im}) :
    prodOpenSet W' D ⊆ TubeDomain (PosOrthant (k + 1)) := by
  intro w hw
  dsimp [prodOpenSet] at hw
  rw [mem_inter_iff, mem_preimage, mem_preimage] at hw
  have hw' := hW' hw.1
  have hwk := hD hw.2
  exact (consFin_mem_pos_orthant_iff w).mpr ⟨hw', hwk⟩

lemma prodOpenSet_subset_neg_orthant {k : ℕ}
    {W' : Set (Fin k → ℂ)} (hW' : W' ⊆ TubeDomain (NegOrthant k))
    {D : Set ℂ} (hD : D ⊆ {z : ℂ | z.im < 0}) :
    prodOpenSet W' D ⊆ TubeDomain (NegOrthant (k + 1)) := by
  intro w hw
  dsimp [prodOpenSet] at hw
  rw [mem_inter_iff, mem_preimage, mem_preimage] at hw
  have hw' := hW' hw.1
  have hwk := hD hw.2
  exact (consFin_mem_neg_orthant_iff w).mpr ⟨hw', hwk⟩

lemma prodOpenSet_subset_ball {k : ℕ} {r : ℝ} (hr : 0 < r)
    {W' : Set (Fin k → ℂ)} (hW' : W' ⊆ Metric.ball 0 r)
    {D : Set ℂ} (hD : D ⊆ Metric.ball 0 r) :
    prodOpenSet W' D ⊆ Metric.ball 0 r := by
  intro w hw
  dsimp [prodOpenSet] at hw
  rw [mem_inter_iff, mem_preimage, mem_preimage] at hw
  have hw' := hW' hw.1
  have hwk := hD hw.2
  have heq : w = consFin (initFin w) (lastFin w) := (consFin_init_last w).symm
  rw [heq]
  exact consFin_mem_ball hr hw' hwk

noncomputable def iteratedCauchyIntegral2
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ) (w : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ •
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
      g (fun i => if i = 0 then ζ₀ else ζ₁))

noncomputable def cauchySlice1
    (g : (Fin 2 → ℂ) → ℂ) (c1 : ℂ) (r1 : ℝ) (ζ₀ : ℂ) (w1 : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c1, r1), (ζ₁ - w1)⁻¹ •
    g (fun i => if i = 0 then ζ₀ else ζ₁)

lemma analyticAt_cauchySlice1
    (g : (Fin 2 → ℂ) → ℂ) (c1 : ℂ) (r1 : ℝ) (hr1 : 0 < r1) (ζ₀ : ℂ)
    (h_int : CircleIntegrable (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁)) c1 r1)
    {w1 : ℂ} (hw1 : w1 ∈ Metric.ball c1 r1) :
    AnalyticAt ℂ (fun u => cauchySlice1 g c1 r1 ζ₀ u) w1 := by
  dsimp [cauchySlice1]
  lift r1 to NNReal using hr1.le with R1
  have hw' : w1 ∈ Metric.eball c1 R1 := by
    rw [Metric.eball_coe]
    exact hw1
  have h_series := hasFPowerSeriesOn_cauchy_integral h_int hr1
  exact h_series.analyticAt_of_mem hw'

lemma analyticAt_iteratedCauchyIntegral2_slice0
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ) (hr0 : 0 < r 0)
    (w1 : ℂ)
    (h_int : CircleIntegrable (fun ζ₀ => cauchySlice1 g (c 1) (r 1) ζ₀ w1) (c 0) (r 0))
    {w0 : ℂ} (hw0 : w0 ∈ Metric.ball (c 0) (r 0)) :
    AnalyticAt ℂ (fun u => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ ζ₀ in C(c 0, r 0), (ζ₀ - u)⁻¹ • cauchySlice1 g (c 1) (r 1) ζ₀ w1) w0 := by
  lift (r 0) to NNReal using hr0.le with R0
  have hw' : w0 ∈ Metric.eball (c 0) R0 := by
    rw [Metric.eball_coe]
    exact hw0
  have h_series := hasFPowerSeriesOn_cauchy_integral h_int hr0
  exact h_series.analyticAt_of_mem hw'

lemma iteratedCauchyIntegral2_eq
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ)
    (hr0 : 0 < r 0) (_hr1 : 0 < r 1)
    (w : Fin 2 → ℂ)
    (hw0 : w 0 ∈ Metric.ball (c 0) (r 0))
    (hw1 : w 1 ∈ Metric.ball (c 1) (r 1))
    (h_diff1 : ∀ ζ₀ ∈ Metric.sphere (c 0) (r 0),
      DifferentiableOn ℂ (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁))
        (Metric.closedBall (c 1) (r 1)))
    (h_diff0 : DifferentiableOn ℂ (fun ζ₀ => g (fun i => if i = 0 then ζ₀ else w 1))
        (Metric.closedBall (c 0) (r 0))) :
    iteratedCauchyIntegral2 g c r w = g w := by
  have h_inner_eq : ∀ ζ₀ ∈ Metric.sphere (c 0) (r 0),
      ((2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
        g (fun i => if i = 0 then ζ₀ else ζ₁)) =
      g (fun i => if i = 0 then ζ₀ else w 1) := by
    intro ζ₀ hζ₀
    have h_diff := h_diff1 ζ₀ hζ₀
    have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff hw1
    have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    calc (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
            g (fun i => if i = 0 then ζ₀ else ζ₁)
      _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) •
            (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁)) (w 1)) := by rw [← h_cauchy]
      _ = (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁)) (w 1) := by
        rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
      _ = g (fun i => if i = 0 then ζ₀ else w 1) := rfl
  have h_int_congr : (∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ •
        ((2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
          g (fun i => if i = 0 then ζ₀ else ζ₁))) =
      ∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ • g (fun i => if i = 0 then ζ₀ else w 1) := by
    apply circleIntegral.integral_congr hr0.le
    intro ζ₀ hζ₀
    dsimp only
    rw [h_inner_eq ζ₀ hζ₀]
  have h_cauchy0 := DifferentiableOn.circleIntegral_sub_inv_smul h_diff0 hw0
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  unfold iteratedCauchyIntegral2
  rw [h_int_congr]
  calc (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ •
          g (fun i => if i = 0 then ζ₀ else w 1)
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) •
          (fun ζ₀ => g (fun i => if i = 0 then ζ₀ else w 1)) (w 0)) := by rw [← h_cauchy0]
    _ = (fun ζ₀ => g (fun i => if i = 0 then ζ₀ else w 1)) (w 0) := by
      rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
    _ = g w := by
      have heq : (fun i : Fin 2 => if i = 0 then w 0 else w 1) = w := by
        ext i; fin_cases i <;> rfl
      exact congr_arg g heq

lemma analyticAt_inv_sub {ζ w : ℂ} (h : ζ ≠ w) :
    AnalyticAt ℂ (fun u => (ζ - u)⁻¹) w := by
  have h_sub : AnalyticAt ℂ (fun u => ζ - u) w :=
    analyticAt_const.sub analyticAt_id
  have h_ne : ζ - w ≠ 0 := sub_ne_zero.mpr h
  exact h_sub.inv h_ne

lemma analyticAt_cauchy_kernel_proj0 {ζ₀ : ℂ} {w : Fin 2 → ℂ} (h : ζ₀ ≠ w 0) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹) w := by
  let P : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  have h1 : AnalyticAt ℂ (fun u => (ζ₀ - u)⁻¹) (P w) := analyticAt_inv_sub h
  exact h1.comp hP

lemma analyticAt_cauchy_kernel_proj1 {ζ₁ : ℂ} {w : Fin 2 → ℂ} (h : ζ₁ ≠ w 1) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₁ - u 1)⁻¹) w := by
  let P : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  have h1 : AnalyticAt ℂ (fun u => (ζ₁ - u)⁻¹) (P w) := analyticAt_inv_sub h
  exact h1.comp hP

lemma analyticAt_cauchy_kernel_prod {ζ₀ ζ₁ : ℂ} {w : Fin 2 → ℂ}
    (h0 : ζ₀ ≠ w 0) (h1 : ζ₁ ≠ w 1) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w :=
  (analyticAt_cauchy_kernel_proj0 h0).mul (analyticAt_cauchy_kernel_proj1 h1)

noncomputable def iteratedCauchy (k : ℕ) (g : (Fin k → ℂ) → ℂ)
    (c : Fin k → ℂ) (r : Fin k → ℝ) (w : Fin k → ℂ) : ℂ :=
  match k with
  | 0 => g w
  | m + 1 =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(lastFin c, lastFinR r),
      (ζ - lastFin w)⁻¹ •
        iteratedCauchy m (fun w' => g (consFin w' ζ)) (initFin c) (initFinR r) (initFin w)

lemma iteratedCauchy_zero (g : (Fin 0 → ℂ) → ℂ) (c : Fin 0 → ℂ) (r : Fin 0 → ℝ) (w : Fin 0 → ℂ) :
    iteratedCauchy 0 g c r w = g w := rfl

lemma continuous_deriv_circleMap' (c : ℂ) (R : ℝ) :
    Continuous (deriv (circleMap c R)) := by
  have heq : (deriv (circleMap c R)) = fun θ : ℝ => circleMap 0 R θ * I := by
    ext θ
    exact deriv_circleMap c R θ
  rw [heq]
  exact (continuous_circleMap 0 R).mul continuous_const

lemma tendsto_circleIntegral_cauchy_of_dominated
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F_eps : ι → ℂ → ℂ) (F_lim : ℂ → ℂ)
    (h_cont : ∀ᶠ n in l, ContinuousOn (F_eps n) (Metric.sphere c R))
    (M : ℝ) (hM : ∀ᶠ n in l, ∀ z ∈ Metric.sphere c R, ‖F_eps n z‖ ≤ M)
    (h_pt : ∀ z ∈ Metric.sphere c R, Filter.Tendsto (fun n => F_eps n z) l (nhds (F_lim z)))
    {w : ℂ} (hw : w ∈ Metric.ball c R) :
    Filter.Tendsto
      (fun n => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_eps n ζ) l
      (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_lim ζ)) := by
  have h_2piI : Continuous (fun (I_val : ℂ) => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • I_val) := by
    fun_prop
  apply h_2piI.continuousAt.tendsto.comp
  change Filter.Tendsto
    (fun n => ∫ θ in (0:ℝ)..(2 * Real.pi),
      deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ • F_eps n (circleMap c R θ))) l
    (nhds (∫ θ in (0:ℝ)..(2 * Real.pi),
      deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ • F_lim (circleMap c R θ))))
  have hd_pos : 0 < R - dist w c := sub_pos.mpr (Metric.mem_ball.mp hw)
  let bound : ℝ → ℝ := fun _ => R * (R - dist w c)⁻¹ * max M 0
  have h_bound_int : IntervalIntegrable bound MeasureTheory.volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have h_cm_sphere : ∀ θ : ℝ, circleMap c R θ ∈ Metric.sphere c R := by
    intro θ
    rw [Metric.mem_sphere, circleMap, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h_diff_ne : ∀ θ : ℝ, circleMap c R θ - w ≠ 0 := by
    intro θ h_sub
    have heq : circleMap c R θ = w := sub_eq_zero.mp h_sub
    have h_dist1 : dist (circleMap c R θ) c = R := by
      have := h_cm_sphere θ
      rwa [Metric.mem_sphere] at this
    rw [heq] at h_dist1
    have h_dist2 : dist w c < R := Metric.mem_ball.mp hw
    linarith
  have h_inv_le : ∀ θ : ℝ, ‖(circleMap c R θ - w)⁻¹‖ ≤ (R - dist w c)⁻¹ := by
    intro θ
    rw [norm_inv]
    have h1 : dist (circleMap c R θ) c ≤ dist (circleMap c R θ) w + dist w c := dist_triangle _ _ _
    have h2 : dist (circleMap c R θ) c = R := by
      have := h_cm_sphere θ
      rwa [Metric.mem_sphere] at this
    rw [h2] at h1
    have h_norm : dist (circleMap c R θ) w = ‖circleMap c R θ - w‖ := dist_eq_norm _ _
    rw [h_norm, dist_comm w c] at h1
    have h_le : R - dist c w ≤ ‖circleMap c R θ - w‖ := by linarith
    rw [dist_comm c w] at h_le
    have h_norm_pos : 0 < ‖circleMap c R θ - w‖ := by
      rw [norm_pos_iff]
      exact h_diff_ne θ
    exact (inv_le_inv₀ h_norm_pos hd_pos).mpr h_le
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [h_cont] with n hn
    have h_cont_on : Continuous (fun θ =>
        deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ • F_eps n (circleMap c R θ))) := by
      have h_cm_cont : Continuous (circleMap c R) := continuous_circleMap c R
      have h_der_cont : Continuous (deriv (circleMap c R)) := continuous_deriv_circleMap' c R
      have h_inv_cont : Continuous (fun θ => (circleMap c R θ - w)⁻¹) := by
        exact (h_cm_cont.sub continuous_const).inv₀ h_diff_ne
      have h_F_cont : Continuous (fun θ => F_eps n (circleMap c R θ)) :=
        hn.comp_continuous h_cm_cont h_cm_sphere
      exact h_der_cont.smul (h_inv_cont.smul h_F_cont)
    exact h_cont_on.aestronglyMeasurable
  · filter_upwards [hM] with n hMn
    refine ae_of_all _ ?_
    intro θ _hθ
    dsimp [bound]
    rw [norm_mul, norm_mul]
    have h_deriv_norm : ‖deriv (circleMap c R) θ‖ = R := by
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, circleMap,
        zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hR.le]
    rw [h_deriv_norm]
    have h_fn_le : ‖F_eps n (circleMap c R θ)‖ ≤ max M 0 :=
      (hMn _ (h_cm_sphere θ)).trans (le_max_left _ _)
    have h_mul1 : R * ‖(circleMap c R θ - w)⁻¹‖ ≤ R * (R - dist w c)⁻¹ :=
      mul_le_mul_of_nonneg_left (h_inv_le θ) hR.le
    have h_mul2 : R * ‖(circleMap c R θ - w)⁻¹‖ * ‖F_eps n (circleMap c R θ)‖ ≤
        R * (R - dist w c)⁻¹ * max M 0 :=
      mul_le_mul h_mul1 h_fn_le (norm_nonneg _) (mul_nonneg hR.le (inv_nonneg.mpr hd_pos.le))
    rw [← mul_assoc]
    exact h_mul2
  · exact h_bound_int
  · refine ae_of_all _ ?_
    intro θ _hθ
    refine Tendsto.smul tendsto_const_nhds ?_
    refine Tendsto.smul tendsto_const_nhds ?_
    exact h_pt (circleMap c R θ) (h_cm_sphere θ)

lemma limUnder_circleIntegral_cauchy_of_dominated
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    (F_eps : ι → ℂ → ℂ) (F_lim : ℂ → ℂ)
    (h_cont : ∀ᶠ n in l, ContinuousOn (F_eps n) (Metric.sphere c R))
    (M : ℝ) (hM : ∀ᶠ n in l, ∀ z ∈ Metric.sphere c R, ‖F_eps n z‖ ≤ M)
    (h_pt : ∀ z ∈ Metric.sphere c R, Filter.Tendsto (fun n => F_eps n z) l (nhds (F_lim z)))
    {w : ℂ} (hw : w ∈ Metric.ball c R) :
    limUnder l (fun n => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_eps n ζ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_lim ζ := by
  have h := tendsto_circleIntegral_cauchy_of_dominated hR F_eps F_lim h_cont M hM h_pt hw
  exact h.limUnder_eq

lemma posOrthant_ball_inter_nonempty (n : ℕ) (ρ : ℝ) (hρ_pos : 0 < ρ) :
    (Metric.ball (0 : Fin n → ℂ) ρ ∩ TubeDomain (PosOrthant n)).Nonempty := by
  let z : Fin n → ℂ := fun _ => ((ρ / 2 : ℝ) : ℂ) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball]
    apply (dist_pi_lt_iff hρ_pos).mpr
    intro i
    dsimp [z]
    rw [dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (half_pos hρ_pos).le]
    exact half_lt_self hρ_pos
  · intro i
    dsimp [z]
    simp [Complex.mul_im, half_pos hρ_pos]

lemma negOrthant_ball_inter_nonempty (n : ℕ) (ρ : ℝ) (hρ_pos : 0 < ρ) :
    (Metric.ball (0 : Fin n → ℂ) ρ ∩ TubeDomain (NegOrthant n)).Nonempty := by
  let z : Fin n → ℂ := fun _ => - (((ρ / 2 : ℝ) : ℂ) * Complex.I)
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball]
    apply (dist_pi_lt_iff hρ_pos).mpr
    intro i
    dsimp [z]
    rw [dist_zero_right, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (half_pos hρ_pos).le]
    exact half_lt_self hρ_pos
  · intro i
    dsimp [z]
    simp [Complex.mul_im, half_pos hρ_pos]

lemma analyticAt_circleIntegral_cauchy {K : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hK : CircleIntegrable K c R) {w : ℂ} (hw : w ∈ Metric.ball c R) :
    AnalyticAt ℂ (fun u => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ ζ in C(c, R), (ζ - u)⁻¹ • K ζ) w := by
  lift R to NNReal using hR.le
  have hw' : w ∈ Metric.eball c R := by
    rw [Metric.eball_coe]
    exact hw
  have h_series := hasFPowerSeriesOn_cauchy_integral hK hR
  exact h_series.analyticAt_of_mem hw'

lemma orthant_sum_mem_cone_2d
    (V_plus : Set (Fin 2 → ℝ)) (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    (∑ j, v j) ∈ V_plus := by
  have hk_pos : 0 < (2 : ℕ) := by decide
  have h_ones : ∀ j : Fin 2, 0 < (1 : ℝ) := fun _ => by positivity
  have h_sum := sum_pos_smul_mem_of_convex_cone hk_pos hV_plus_convex hV_plus_cone
    v hv (fun _ => 1) h_ones
  have heq_sum : (∑ j, (1 : ℝ) • v j) = ∑ j, v j := by simp
  rwa [heq_sum] at h_sum

lemma orthant_slice_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    ∃ ρ > 0, AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ) := by
  have hu_mem := orthant_sum_mem_cone_2d V_plus hV_plus_convex hV_plus_cone v hv
  have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (∑ j, v j) hu_mem
  exact Metric.mem_nhds_iff.mp h_slice.eventually_analyticAt

lemma orthant_slice0_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) (v 0)) 0 :=
  slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (v 0) (hv 0)

lemma orthant_slice1_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) (v 1)) 0 :=
  slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (v 1) (hv 1)

lemma orthant_kernel_holo_plus_2d
    (V_plus : Set (Fin 2 → ℝ)) (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin 2 → ℂ) → ℂ) (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    DifferentiableOn ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x)
      (TubeDomain (PosOrthant 2)) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => v j i
  have hn : 0 < (2 : ℕ) := by decide
  exact h_holo_plus.comp (differentiable_cAffine M x).differentiableOn
    (fun w hw => cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hw)

lemma orthant_kernel_holo_minus_2d
    (V_plus : Set (Fin 2 → ℝ)) (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    DifferentiableOn ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x)
      (TubeDomain (NegOrthant 2)) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => v j i
  have hn : 0 < (2 : ℕ) := by decide
  exact h_holo_minus.comp (differentiable_cAffine M x).differentiableOn
    (fun w hw => cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hw)

lemma orthant_kernel_slice0_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 0 then t else 0)) 0 := by
  have heq :
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 0 then t else 0)) =
      slice_fun f (fun i => (x i : ℂ)) (v 0) := by
    ext t
    dsimp [Function.comp, slice_fun]
    congr 1
    ext i
    fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
  rw [heq]
  exact orthant_slice0_analytic_2d V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hv

lemma orthant_kernel_slice1_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 1 then t else 0)) 0 := by
  have heq :
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 1 then t else 0)) =
      slice_fun f (fun i => (x i : ℂ)) (v 1) := by
    ext t
    dsimp [Function.comp, slice_fun]
    congr 1
    ext i
    fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
  rw [heq]
  exact orthant_slice1_analytic_2d V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hv

lemma orthant_kernel_diag_analytic_2d
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t))
      (Metric.ball 0 ρ) := by
  have heq : (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t)) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) := by
    ext t
    dsimp [Function.comp, slice_fun]
    congr 1
    ext i
    fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
  rw [heq]
  exact hg_an

lemma orthant_kernel_diag_analytic_nd (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F w ∧
      F w = (f ∘ cAffine (Matrix.of fun i j => v j i) x) w := by
  have hw0 : w ⟨0, hn⟩ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 ⟨0, hn⟩
    exact lt_of_le_of_lt hle hw
  let P : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ⟨0, hn⟩
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w ⟨0, hn⟩) hw0
  have h_comp : AnalyticAt ℂ (G1 ∘ P) w := hG1.comp hP
  use (G1 ∘ P)
  refine ⟨h_comp, ?_⟩
  dsimp [G1, Function.comp, slice_fun, P]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  have heq : (∑ j : Fin n, (v j i : ℂ) * w j) = (∑ j : Fin n, (v j i : ℂ) * w ⟨0, hn⟩) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hdiag j]
  rw [heq, ← Finset.sum_mul]
  have hsum : ((∑ j : Fin n, v j) i : ℂ) = ∑ j : Fin n, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum]
  ring

lemma orthant_kernel_analytic_1d
    (f : (Fin 1 → ℂ) → ℂ) (x : Fin 1 → ℝ) (v : Fin 1 → (Fin 1 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x) (Metric.ball 0 ρ) := by
  intro w hw
  have hw0 : w 0 ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 0
    exact lt_of_le_of_lt hle hw
  let P : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w 0) hw0
  have h_comp : AnalyticAt ℂ (G1 ∘ P) w := hG1.comp hP
  have heq : (f ∘ cAffine (Matrix.of fun i j => v j i) x) = G1 ∘ P := by
    ext u
    dsimp [G1, Function.comp, slice_fun, P]
    congr 1
    ext i
    fin_cases i
    dsimp [cAffine, Matrix.mulVec, dotProduct]
    simp
    ring
  rw [heq]
  exact h_comp

lemma orthant_kernel_diag_pullback_2d
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin 2 → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    AnalyticAt ℂ
      (fun u : Fin 2 → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u 0)) w := by
  have hw0 : w 0 ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 0
    exact lt_of_le_of_lt hle hw
  let P : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w 0) hw0
  have h_comp : AnalyticAt ℂ (G1 ∘ P) w := hG1.comp hP
  have heq :
      (fun u : Fin 2 → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u 0)) =
      G1 ∘ P := by
    ext u
    dsimp [G1, Function.comp, slice_fun, P]
    congr 1
    ext i; fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
  rw [heq]
  exact h_comp

lemma cAffine_consFin_eq {k : ℕ} (v : Fin (k + 1) → (Fin (k + 1) → ℝ)) (x : Fin (k + 1) → ℝ)
    (w' : Fin k → ℂ) (z : ℂ) (i : Fin (k + 1)) :
    cAffine (Matrix.of fun i j => v j i) x (consFin w' z) i =
      (x i : ℂ) + (∑ j : Fin k, (v (Fin.castSucc j) i : ℂ) * w' j) +
        (v (Fin.last k) i : ℂ) * z := by
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp [consFin]
  ring

lemma orthant_kernel_polydisc_radius_nd (n : ℕ) (w : Fin n → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let r : Fin n → ℝ := fun i => (ρ - dist (w i) 0) / 2
    (∀ i, 0 < r i) ∧ (∀ i, dist (w i) 0 + r i < ρ) ∧
    (∀ i, Metric.closedBall (w i) (r i) ⊆ Metric.ball (0 : ℂ) ρ) := by
  intro r
  have hr_pos : ∀ i, 0 < r i := by
    intro i
    have hwi : dist (w i) 0 < ρ := lt_of_le_of_lt (dist_le_pi_dist w 0 i) (Metric.mem_ball.mp hw)
    dsimp [r]; linarith
  have hr_sum : ∀ i, dist (w i) 0 + r i < ρ := by
    intro i
    have hwi : dist (w i) 0 < ρ := lt_of_le_of_lt (dist_le_pi_dist w 0 i) (Metric.mem_ball.mp hw)
    dsimp [r]; linarith
  have h_sub : ∀ i, Metric.closedBall (w i) (r i) ⊆ Metric.ball (0 : ℂ) ρ := by
    intro i z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have h_tri := dist_triangle z (w i) 0
    have hwi : dist (w i) 0 < ρ := lt_of_le_of_lt (dist_le_pi_dist w 0 i) (Metric.mem_ball.mp hw)
    dsimp [r] at hz ⊢
    linarith
  exact ⟨hr_pos, hr_sum, h_sub⟩

lemma orthant_kernel_torus_analytic_2d
    (w : Fin 2 → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let c : Fin 2 → ℂ := w
    let r : Fin 2 → ℝ := fun i => (ρ - dist (w i) 0) / 2
    ∀ ζ₀ ∈ Metric.sphere (c 0) (r 0), ∀ ζ₁ ∈ Metric.sphere (c 1) (r 1),
      AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w := by
  intro c r ζ₀ h0 ζ₁ h1
  rcases orthant_kernel_polydisc_radius_nd 2 w ρ hw with ⟨hr_pos, _, _⟩
  have h_ne0 : ζ₀ ≠ w 0 := by
    rw [Metric.mem_sphere] at h0
    intro h_eq
    dsimp [c] at h0; subst h_eq; rw [dist_self] at h0
    have hr0 := hr_pos 0; dsimp [r] at h0; linarith
  have h_ne1 : ζ₁ ≠ w 1 := by
    rw [Metric.mem_sphere] at h1
    intro h_eq
    dsimp [c] at h1; subst h_eq; rw [dist_self] at h1
    have hr1 := hr_pos 1; dsimp [r] at h1; linarith
  exact analyticAt_cauchy_kernel_prod h_ne0 h_ne1

lemma analyticAt_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g F : E → ℂ} {w : E} (hF : AnalyticAt ℂ F w) (h_eq : F =ᶠ[nhds w] g) :
    AnalyticAt ℂ g w := hF.congr h_eq

lemma orthant_kernel_diag_proj_analytic (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    AnalyticAt ℂ ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
      ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) w := by
  have hw0 : w ⟨0, hn⟩ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 ⟨0, hn⟩
    exact lt_of_le_of_lt hle hw
  let P : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ⟨0, hn⟩
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w ⟨0, hn⟩) hw0
  exact hG1.comp hP

lemma cAffine_diag_eq (n : ℕ) (_hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) (t : ℂ) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) t := by
  dsimp [slice_fun, Function.comp]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  congr 1
  rw [← Finset.sum_mul]
  have hsum : ((∑ j : Fin n, v j) i : ℂ) = ∑ j : Fin n, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum, mul_comm]

lemma orthant_kernel_analytic_2d_cauchy_rep
    (w : Fin 2 → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let c : Fin 2 → ℂ := w
    let r : Fin 2 → ℝ := fun i => (ρ - dist (w i) 0) / 2
    (∀ i : Fin 2, 0 < r i) ∧
    (∀ i : Fin 2, w i ∈ Metric.ball (c i) (r i)) ∧
    (∀ ζ₀ ∈ Metric.sphere (c 0) (r 0), ∀ ζ₁ ∈ Metric.sphere (c 1) (r 1),
      AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w) := by
  intro c r
  rcases orthant_kernel_polydisc_radius_nd 2 w ρ hw with ⟨hr_pos, _, _⟩
  have hw_in : ∀ i : Fin 2, w i ∈ Metric.ball (c i) (r i) := by
    intro i; dsimp [c]; rw [Metric.mem_ball, dist_self]; exact hr_pos i
  have h_torus := orthant_kernel_torus_analytic_2d w ρ hw
  exact ⟨hr_pos, hw_in, h_torus⟩

lemma orthant_kernel_analytic_nd_cauchy_rep (n : ℕ) (_hn : 0 < n)
    (w : Fin n → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let c : Fin n → ℂ := w
    let r : Fin n → ℝ := fun i => (ρ - dist (w i) 0) / 2
    (∀ i : Fin n, 0 < r i) ∧
    (∀ i : Fin n, w i ∈ Metric.ball (c i) (r i)) ∧
    (∀ i : Fin n, ∀ ζ ∈ Metric.sphere (c i) (r i), ζ ≠ w i) := by
  intro c r
  rcases orthant_kernel_polydisc_radius_nd n w ρ hw with ⟨hr_pos, _, _⟩
  have hw_in : ∀ i : Fin n, w i ∈ Metric.ball (c i) (r i) := by
    intro i; dsimp [c]; rw [Metric.mem_ball, dist_self]; exact hr_pos i
  have h_ne : ∀ i : Fin n, ∀ ζ ∈ Metric.sphere (c i) (r i), ζ ≠ w i := by
    intro i ζ hζ h_eq
    rw [Metric.mem_sphere] at hζ
    dsimp [c] at hζ; subst h_eq; rw [dist_self] at hζ
    have hri := hr_pos i; dsimp [r] at hζ; linarith
  exact ⟨hr_pos, hw_in, h_ne⟩

lemma orthant_kernel_analytic_2d_local
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin 2 → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    ∃ F : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ F w ∧
      F = (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ)) :=
  ⟨_, orthant_kernel_diag_proj_analytic 2 (by decide) f x v ρ hg_an w hw, rfl⟩

lemma orthant_kernel_analytic_nd_local (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F w ∧
      F = (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ)) :=
  ⟨_, orthant_kernel_diag_proj_analytic n hn f x v ρ hg_an w hw, rfl⟩

lemma orthant_kernel_2d_diag_ident
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) (t : ℂ) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) t := by
  dsimp [slice_fun, Function.comp]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  congr 1
  rw [← Finset.sum_mul]
  have hsum : ((∑ j : Fin 2, v j) i : ℂ) = ∑ j : Fin 2, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum, mul_comm]

lemma orthant_kernel_2d_diag_proj_comp
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) :
    (fun u : Fin 2 → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u 0)) =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ))) := by
  ext u
  dsimp [Function.comp]
  exact orthant_kernel_2d_diag_ident f x v (u 0)

lemma orthant_kernel_2d_diag_eval_eq
    (w : Fin 2 → ℂ) (hdiag : w 0 = w 1) :
    (fun _ => w 0) = w := by
  ext i; fin_cases i
  · rfl
  · exact hdiag

lemma orthant_kernel_2d_eval_on_diag
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (w : Fin 2 → ℂ) (hdiag : w 0 = w 1) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ))) w := by
  have heq := orthant_kernel_2d_diag_eval_eq w hdiag
  rw [← heq]
  have hcomp := congr_fun (orthant_kernel_2d_diag_proj_comp f x v) w
  exact hcomp

lemma orthant_kernel_nd_diag_ident (n : ℕ) (_hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) (t : ℂ) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) t := by
  dsimp [slice_fun, Function.comp]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  congr 1
  rw [← Finset.sum_mul]
  have hsum : ((∑ j : Fin n, v j) i : ℂ) = ∑ j : Fin n, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum, mul_comm]

lemma orthant_kernel_nd_diag_proj_comp (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) :
    (fun u : Fin n → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u ⟨0, hn⟩)) =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) := by
  ext u
  dsimp [Function.comp]
  exact orthant_kernel_nd_diag_ident n hn f x v (u ⟨0, hn⟩)

lemma orthant_kernel_nd_diag_eval_eq (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℂ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    (fun _ => w ⟨0, hn⟩) = w := by
  ext i
  exact (hdiag i).symm

lemma orthant_kernel_nd_eval_on_diag (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (w : Fin n → ℂ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) w := by
  have heq := orthant_kernel_nd_diag_eval_eq n hn w hdiag
  rw [← heq]
  have hcomp := congr_fun (orthant_kernel_nd_diag_proj_comp n hn f x v) w
  exact hcomp

lemma orthant_kernel_2d_eq_slice
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (_ρ : ℝ)
    (_hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 _ρ))
    (w : Fin 2 → ℂ) (_hw : w ∈ Metric.ball 0 _ρ) (hdiag : w 0 = w 1) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ))) w :=
  orthant_kernel_2d_eval_on_diag f x v w hdiag

lemma orthant_kernel_nd_eq_slice (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (_ρ : ℝ)
    (_hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 _ρ))
    (w : Fin n → ℂ) (_hw : w ∈ Metric.ball 0 _ρ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) w :=
  orthant_kernel_nd_eval_on_diag n hn f x v w hdiag

lemma orthant_kernel_cauchy_2d_eq
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ)
    (_hr_pos : ∀ i, 0 < r i) (w : Fin 2 → ℂ) (hw : ∀ i, w i ∈ Metric.ball (c i) (r i))
    (h_rep : ∀ u, (∀ i, u i ∈ Metric.ball (c i) (r i)) → iteratedCauchyIntegral2 g c r u = g u) :
    iteratedCauchyIntegral2 g c r =ᶠ[nhds w] g := by
  have heq : {u : Fin 2 → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} =
      Set.pi Set.univ (fun i => Metric.ball (c i) (r i)) := by
    ext u; simp
  have h_open : IsOpen {u : Fin 2 → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := by
    rw [heq]
    exact isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)
  have h_mem : w ∈ {u : Fin 2 → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := hw
  have h_nhds := h_open.mem_nhds h_mem
  exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nhds, fun u hu => h_rep u hu⟩

lemma orthant_kernel_cauchy_nd_eq (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : Fin n → ℝ)
    (_hr_pos : ∀ i, 0 < r i) (w : Fin n → ℂ) (hw : ∀ i, w i ∈ Metric.ball (c i) (r i))
    (h_rep : ∀ u, (∀ i, u i ∈ Metric.ball (c i) (r i)) → iteratedCauchy n g c r u = g u) :
    iteratedCauchy n g c r =ᶠ[nhds w] g := by
  have heq : {u : Fin n → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} =
      Set.pi Set.univ (fun i => Metric.ball (c i) (r i)) := by
    ext u; simp
  have h_open : IsOpen {u : Fin n → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := by
    rw [heq]
    exact isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)
  have h_mem : w ∈ {u : Fin n → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := hw
  have h_nhds := h_open.mem_nhds h_mem
  exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nhds, fun u hu => h_rep u hu⟩

def OrthantEOWData (n : ℕ) (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) : Prop :=
  DifferentiableOn ℂ g (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) ∧
  DifferentiableOn ℂ g (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) ∧
  ContinuousOn g (Metric.ball 0 ρ ∩
    (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
      {w : Fin n → ℂ | ∀ i, (w i).im = 0}))

lemma orthant_eowData_of_wedge (n : ℕ) (hn : 0 < n)
    (V_plus U : Set (Fin n → ℝ))
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    ∃ ρ : ℝ, 0 < ρ ∧
      OrthantEOWData n (f ∘ cAffine (Matrix.of fun i j => v j i) x) ρ := by
  have hcont_aff : Continuous (cAffine (Matrix.of fun i j => v j i) x) :=
    (differentiable_cAffine _ x).continuous
  have hre_cont : Continuous
      (fun w : Fin n → ℂ => fun i => (cAffine (Matrix.of fun i j => v j i) x w i).re) :=
    continuous_pi fun i =>
      Complex.continuous_re.comp ((continuous_apply i).comp hcont_aff)
  have hA_open : IsOpen {w : Fin n → ℂ |
      (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).re) ∈ U} :=
    IsOpen.preimage hre_cont hU_open
  have h0 : (0 : Fin n → ℂ) ∈ {w : Fin n → ℂ |
      (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).re) ∈ U} := by
    change (fun i => (cAffine (Matrix.of fun i j => v j i) x 0 i).re) ∈ U
    rw [cAffine_re]
    have hz : (fun j : Fin n => ((0 : Fin n → ℂ) j).re) = 0 := by
      ext j; simp
    rw [hz, Matrix.mulVec_zero, add_zero]
    exact hx_U
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hA_open 0 h0
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (cAffine (Matrix.of fun i j => v j i) x)
        (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) (TubeDomain V_plus) :=
      fun w hw => cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hw.2
    exact h_holo_plus.comp (differentiable_cAffine _ x).differentiableOn hmaps
  · have hmaps : Set.MapsTo (cAffine (Matrix.of fun i j => v j i) x)
        (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n))
        (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      fun w hw => cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hw.2
    exact h_holo_minus.comp (differentiable_cAffine _ x).differentiableOn hmaps
  · have hmaps : Set.MapsTo (cAffine (Matrix.of fun i j => v j i) x)
        (Metric.ball 0 ρ ∩
          (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
            {w : Fin n → ℂ | ∀ i, (w i).im = 0}))
        (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
      intro w hw
      obtain ⟨hwb, hw'⟩ := hw
      rcases hw' with (hp | hm) | hr
      · exact Or.inl (Or.inl (cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hp))
      · exact Or.inl (Or.inr (cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hm))
      · refine Or.inr ⟨hball hwb, ?_⟩
        rw [cAffine_im]
        have hzero : (fun j => (w j).im) = 0 := by
          ext j; exact hr j
        rw [hzero, Matrix.mulVec_zero]
    exact h_cont.comp hcont_aff.continuousOn hmaps

lemma orthant_eowData_bounded_on_compact (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ)
    (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hK_sub : K ⊆ Metric.ball 0 ρ ∩
      (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
        {w : Fin n → ℂ | ∀ i, (w i).im = 0})) :
    ∃ M : ℝ, ∀ w ∈ K, ‖g w‖ ≤ M := by
  have hcont : ContinuousOn g K := hdata.2.2.mono hK_sub
  have h_img : IsCompact (g '' K) := hK.image_of_continuousOn hcont
  rcases h_img.isBounded.exists_norm_le with ⟨M, hM⟩
  refine ⟨M, fun w hw => ?_⟩
  exact hM (g w) (mem_image_of_mem g hw)

noncomputable def diagCLM (n : ℕ) : ℂ →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ

lemma diagCLM_apply (n : ℕ) (t : ℂ) (i : Fin n) :
    diagCLM n t i = t := rfl

lemma diagCLM_mem_ball (n : ℕ) {ρ : ℝ} {t : ℂ} (ht : t ∈ Metric.ball 0 ρ) :
    diagCLM n t ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · have : ¬ (t ∈ Metric.ball (0 : ℂ) ρ) := by
      rw [Metric.mem_ball]
      intro h
      have := lt_of_le_of_lt dist_nonneg h
      linarith
    contradiction
  · rw [Metric.mem_ball]
    apply (dist_pi_lt_iff hρ).mpr
    intro i
    dsimp [diagCLM]
    exact Metric.mem_ball.mp ht

lemma diagCLM_mem_posOrthant (n : ℕ) {t : ℂ} (ht : 0 < t.im) :
    diagCLM n t ∈ TubeDomain (PosOrthant n) := by
  intro i
  simpa [diagCLM_apply] using ht

lemma diagCLM_mem_negOrthant (n : ℕ) {t : ℂ} (ht : t.im < 0) :
    diagCLM n t ∈ TubeDomain (NegOrthant n) := by
  intro i
  simpa [diagCLM_apply] using ht

lemma diagCLM_im_zero (n : ℕ) {t : ℂ} (ht : t.im = 0) :
    ∀ i, (diagCLM n t i).im = 0 := by
  intro i
  simpa [diagCLM_apply] using ht

lemma orthant_eowData_diag_diff_upper (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    DifferentiableOn ℂ (g ∘ diagCLM n) (Metric.ball 0 ρ ∩ upperHalfPlane) := by
  have hmaps : Set.MapsTo (diagCLM n) (Metric.ball 0 ρ ∩ upperHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) := by
    intro t ht
    exact ⟨diagCLM_mem_ball n ht.1, diagCLM_mem_posOrthant n ht.2⟩
  exact hdata.1.comp (diagCLM n).differentiable.differentiableOn hmaps

lemma orthant_eowData_diag_diff_lower (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    DifferentiableOn ℂ (g ∘ diagCLM n) (Metric.ball 0 ρ ∩ lowerHalfPlane) := by
  have hmaps : Set.MapsTo (diagCLM n) (Metric.ball 0 ρ ∩ lowerHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) := by
    intro t ht
    exact ⟨diagCLM_mem_ball n ht.1, diagCLM_mem_negOrthant n ht.2⟩
  exact hdata.2.1.comp (diagCLM n).differentiable.differentiableOn hmaps

lemma orthant_eowData_diag_continuousOn (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    ContinuousOn (g ∘ diagCLM n)
      (Metric.ball 0 ρ ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0})) := by
  have hmaps : Set.MapsTo (diagCLM n)
      (Metric.ball 0 ρ ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0}))
      (Metric.ball 0 ρ ∩
        (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
          {w : Fin n → ℂ | ∀ i, (w i).im = 0})) := by
    intro t ht
    refine ⟨diagCLM_mem_ball n ht.1, ?_⟩
    rcases ht.2 with (hp | hm) | hr
    · exact Or.inl (Or.inl (diagCLM_mem_posOrthant n hp))
    · exact Or.inl (Or.inr (diagCLM_mem_negOrthant n hm))
    · exact Or.inr (diagCLM_im_zero n hr)
  exact hdata.2.2.comp (diagCLM n).continuous.continuousOn hmaps

lemma bogoliubov_partial_fraction (ζ₀ ζ₁ w₀ w₁ : ℂ)
    (h0 : ζ₀ - w₀ ≠ 0) (h1 : ζ₁ - w₁ ≠ 0)
    (h_diff : (w₀ - w₁) - (ζ₀ - ζ₁) ≠ 0) :
    (ζ₀ - w₀)⁻¹ * (ζ₁ - w₁)⁻¹ =
      ((w₀ - w₁) - (ζ₀ - ζ₁))⁻¹ * ((ζ₀ - w₀)⁻¹ - (ζ₁ - w₁)⁻¹) := by
  have heq : ((w₀ - w₁) - (ζ₀ - ζ₁)) = (ζ₁ - w₁) - (ζ₀ - w₀) := by ring
  rw [heq] at h_diff ⊢
  have h_sub : (ζ₀ - w₀)⁻¹ - (ζ₁ - w₁)⁻¹ =
      ((ζ₁ - w₁) - (ζ₀ - w₀)) * ((ζ₀ - w₀)⁻¹ * (ζ₁ - w₁)⁻¹) := by
    field_simp
  rw [h_sub, ← mul_assoc, inv_mul_cancel₀ h_diff, one_mul]

lemma analyticAt_bogoliubov_kernel (ζ₀ ζ₁ : ℂ) (w : Fin 2 → ℂ)
    (h0 : ζ₀ - w 0 ≠ 0) (h1 : ζ₁ - w 1 ≠ 0)
    (h_diff : (w 0 - w 1) - (ζ₀ - ζ₁) ≠ 0) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ =>
      ((u 0 - u 1) - (ζ₀ - ζ₁))⁻¹ * ((ζ₀ - u 0)⁻¹ - (ζ₁ - u 1)⁻¹)) w := by
  let P0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let P1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
  have hP0 : AnalyticAt ℂ P0 w := P0.analyticAt w
  have hP1 : AnalyticAt ℂ P1 w := P1.analyticAt w
  have han_diff : AnalyticAt ℂ (fun u : Fin 2 → ℂ => ((u 0 - u 1) - (ζ₀ - ζ₁))) w := by
    change AnalyticAt ℂ (fun u => P0 u - P1 u - (ζ₀ - ζ₁)) w
    exact (hP0.sub hP1).sub analyticAt_const
  have han_diff_inv : AnalyticAt ℂ (fun u : Fin 2 → ℂ => ((u 0 - u 1) - (ζ₀ - ζ₁))⁻¹) w :=
    han_diff.inv h_diff
  have han0 : AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹) w := by
    have h : AnalyticAt ℂ (fun u => ζ₀ - P0 u) w := analyticAt_const.sub hP0
    exact h.inv h0
  have han1 : AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₁ - u 1)⁻¹) w := by
    have h : AnalyticAt ℂ (fun u => ζ₁ - P1 u) w := analyticAt_const.sub hP1
    exact h.inv h1
  exact han_diff_inv.mul (han0.sub han1)

lemma analyticAt_cauchy_prod_via_bogoliubov (ζ₀ ζ₁ : ℂ) (w : Fin 2 → ℂ)
    (h0 : ζ₀ - w 0 ≠ 0) (h1 : ζ₁ - w 1 ≠ 0)
    (h_diff : (w 0 - w 1) - (ζ₀ - ζ₁) ≠ 0) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w := by
  have h_bog := analyticAt_bogoliubov_kernel ζ₀ ζ₁ w h0 h1 h_diff
  have h_open : IsOpen
      {u : Fin 2 → ℂ | ζ₀ - u 0 ≠ 0 ∧ ζ₁ - u 1 ≠ 0 ∧ (u 0 - u 1) - (ζ₀ - ζ₁) ≠ 0} := by
    let P0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
    let P1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
    have h1_op : IsOpen {u : Fin 2 → ℂ | ζ₀ - u 0 ≠ 0} :=
      isOpen_ne.preimage (continuous_const.sub P0.continuous)
    have h2_op : IsOpen {u : Fin 2 → ℂ | ζ₁ - u 1 ≠ 0} :=
      isOpen_ne.preimage (continuous_const.sub P1.continuous)
    have h3_op : IsOpen {u : Fin 2 → ℂ | (u 0 - u 1) - (ζ₀ - ζ₁) ≠ 0} :=
      isOpen_ne.preimage ((P0.continuous.sub P1.continuous).sub continuous_const)
    exact h1_op.inter (h2_op.inter h3_op)
  have hw_mem : w ∈ {u : Fin 2 → ℂ | ζ₀ - u 0 ≠ 0 ∧ ζ₁ - u 1 ≠ 0 ∧ (u 0 - u 1) - (ζ₀ - ζ₁) ≠ 0} :=
    ⟨h0, h1, h_diff⟩
  have h_ev : (fun u : Fin 2 → ℂ => ((u 0 - u 1) - (ζ₀ - ζ₁))⁻¹ * ((ζ₀ - u 0)⁻¹ - (ζ₁ - u 1)⁻¹))
      =ᶠ[nhds w] (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨_, h_open.mem_nhds hw_mem, ?_⟩
    intro u hu
    exact (bogoliubov_partial_fraction ζ₀ ζ₁ (u 0) (u 1) hu.1 hu.2.1 hu.2.2).symm
  exact h_bog.congr h_ev

noncomputable def diagMeanCLM2 : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ) +
               (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ))

noncomputable def transverseDiffCLM2 : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ) -
               (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ))

lemma diagMeanCLM2_apply (w : Fin 2 → ℂ) :
    diagMeanCLM2 w = (w 0 + w 1) / 2 := by
  change (1/2 : ℂ) * (w 0 + w 1) = (w 0 + w 1) / 2
  ring

lemma transverseDiffCLM2_apply (w : Fin 2 → ℂ) :
    transverseDiffCLM2 w = (w 0 - w 1) / 2 := by
  change (1/2 : ℂ) * (w 0 - w 1) = (w 0 - w 1) / 2
  ring

lemma coord_reconstruction (w : Fin 2 → ℂ) :
    w 0 = diagMeanCLM2 w + transverseDiffCLM2 w ∧
    w 1 = diagMeanCLM2 w - transverseDiffCLM2 w := by
  simp only [diagMeanCLM2_apply, transverseDiffCLM2_apply]
  constructor <;> ring

lemma norm_half_c : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by
  norm_num

lemma diagMeanCLM2_mem_ball {ρ : ℝ} {w : Fin 2 → ℂ} (hw : w ∈ Metric.ball 0 ρ) :
    diagMeanCLM2 w ∈ Metric.ball (0 : ℂ) ρ := by
  rw [Metric.mem_ball] at hw ⊢
  have h0 : ‖w 0‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 0) hw
  have h1 : ‖w 1‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 1) hw
  rw [diagMeanCLM2_apply, dist_zero_right]
  calc ‖(w 0 + w 1) / 2‖
    _ = ‖(w 0 + w 1) * (1/2 : ℂ)‖ := by ring_nf
    _ = ‖w 0 + w 1‖ * ‖(1/2 : ℂ)‖ := norm_mul _ _
    _ = ‖w 0 + w 1‖ * (1/2) := by rw [norm_half_c]
    _ ≤ (‖w 0‖ + ‖w 1‖) * (1/2) := by gcongr; exact norm_add_le (w 0) (w 1)
    _ < (ρ + ρ) * (1/2) := by gcongr
    _ = ρ := by ring

lemma transverseDiffCLM2_mem_ball {ρ : ℝ} {w : Fin 2 → ℂ} (hw : w ∈ Metric.ball 0 ρ) :
    transverseDiffCLM2 w ∈ Metric.ball (0 : ℂ) ρ := by
  rw [Metric.mem_ball] at hw ⊢
  have h0 : ‖w 0‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 0) hw
  have h1 : ‖w 1‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 1) hw
  rw [transverseDiffCLM2_apply, dist_zero_right]
  calc ‖(w 0 - w 1) / 2‖
    _ = ‖(w 0 - w 1) * (1/2 : ℂ)‖ := by ring_nf
    _ = ‖w 0 - w 1‖ * ‖(1/2 : ℂ)‖ := norm_mul _ _
    _ = ‖w 0 - w 1‖ * (1/2) := by rw [norm_half_c]
    _ ≤ (‖w 0‖ + ‖w 1‖) * (1/2) := by
      gcongr
      exact norm_sub_le (w 0) (w 1)
    _ < (ρ + ρ) * (1/2) := by gcongr
    _ = ρ := by ring

lemma circleIntegrable_of_continuous {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (h_cont : ContinuousOn f (Metric.sphere c |R|)) :
    CircleIntegrable f c R :=
  ContinuousOn.circleIntegrable' h_cont

lemma continuousOn_cauchy_kernel {w c : ℂ} {R : ℝ}
    (hw : w ∉ Metric.sphere c |R|) :
    ContinuousOn (fun ζ => (ζ - w)⁻¹) (Metric.sphere c |R|) := by
  refine ContinuousOn.inv₀ ?_ ?_
  · exact continuous_id.continuousOn.sub continuousOn_const
  · intro ζ hζ h_eq
    have : ζ = w := sub_eq_zero.mp h_eq
    subst this
    exact hw hζ

lemma circleIntegrable_cauchy_kernel {w c : ℂ} {R : ℝ}
    (hw : w ∉ Metric.sphere c |R|) :
    CircleIntegrable (fun ζ => (ζ - w)⁻¹) c R :=
  circleIntegrable_of_continuous (continuousOn_cauchy_kernel hw)

noncomputable def diagTransCLM2 : (ℂ × ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = 0 then
      (ContinuousLinearMap.fst ℂ ℂ ℂ) + (ContinuousLinearMap.snd ℂ ℂ ℂ)
    else
      (ContinuousLinearMap.fst ℂ ℂ ℂ) - (ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma diagTransCLM2_apply (p : ℂ × ℂ) (i : Fin 2) :
    diagTransCLM2 p i = if i = 0 then p.1 + p.2 else p.1 - p.2 := by
  simp only [diagTransCLM2, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

lemma diagTransCLM2_apply_zero (p : ℂ × ℂ) :
    diagTransCLM2 p 0 = p.1 + p.2 := by
  rw [diagTransCLM2_apply]
  simp

lemma diagTransCLM2_apply_one (p : ℂ × ℂ) :
    diagTransCLM2 p 1 = p.1 - p.2 := by
  rw [diagTransCLM2_apply]
  simp

lemma diagTrans_reconstruction (w : Fin 2 → ℂ) :
    diagTransCLM2 (diagMeanCLM2 w, transverseDiffCLM2 w) = w := by
  ext i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [(coord_reconstruction w).1.symm]
  · simp [(coord_reconstruction w).2.symm]

lemma diagMean_diagTrans (u v : ℂ) :
    diagMeanCLM2 (diagTransCLM2 (u, v)) = u := by
  rw [diagMeanCLM2_apply, diagTransCLM2_apply_zero, diagTransCLM2_apply_one]
  ring

lemma transverseDiff_diagTrans (u v : ℂ) :
    transverseDiffCLM2 (diagTransCLM2 (u, v)) = v := by
  rw [transverseDiffCLM2_apply, diagTransCLM2_apply_zero, diagTransCLM2_apply_one]
  ring

lemma diagTrans_im_zero (u v : ℂ) :
    (diagTransCLM2 (u, v) 0).im = u.im + v.im := by
  rw [diagTransCLM2_apply_zero, Complex.add_im]

lemma diagTrans_im_one (u v : ℂ) :
    (diagTransCLM2 (u, v) 1).im = u.im - v.im := by
  rw [diagTransCLM2_apply_one, Complex.sub_im]

lemma diagTrans_mem_posOrthant (u : ℂ) (v : ℂ) (hv : v.im = 0) (hu : 0 < u.im) :
    diagTransCLM2 (u, v) ∈ TubeDomain (PosOrthant 2) := by
  intro i
  dsimp
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [hv, hu]
  · simp [hv, hu]

lemma diagTrans_mem_negOrthant (u : ℂ) (v : ℂ) (hv : v.im = 0) (hu : u.im < 0) :
    diagTransCLM2 (u, v) ∈ TubeDomain (NegOrthant 2) := by
  intro i
  dsimp
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [hv, hu]
  · simp [hv, hu]

lemma diagTrans_im_both_zero (u : ℂ) (v : ℂ) (hu : u.im = 0) (hv : v.im = 0) :
    ∀ i, (diagTransCLM2 (u, v) i).im = 0 := by
  intro i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [hu, hv]
  · simp [hu, hv]

lemma diagTrans_mem_ball {u v : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ‖u‖ < ρ / 2) (hv : ‖v‖ < ρ / 2) :
    diagTransCLM2 (u, v) ∈ Metric.ball (0 : Fin 2 → ℂ) ρ := by
  rw [Metric.mem_ball, dist_zero_right]
  apply (pi_norm_lt_iff hρ).mpr
  intro i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
      _ < ρ / 2 + ρ / 2 := add_lt_add hu hv
      _ = ρ := add_halves ρ
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
      _ < ρ / 2 + ρ / 2 := add_lt_add hu hv
      _ = ρ := add_halves ρ

lemma differentiable_diagTrans_left (v : ℂ) :
    Differentiable ℂ (fun (u : ℂ) => diagTransCLM2 (u, v)) := by
  have hd : Differentiable ℂ (fun (u : ℂ) => (u, v)) :=
    (differentiable_id : Differentiable ℂ (fun u : ℂ => u)).prodMk (differentiable_const v)
  exact diagTransCLM2.differentiable.comp hd

lemma diagTrans_slice_diff_upper (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) (v : ℂ) (hv : v.im = 0) (hv_norm : ‖v‖ < ρ / 2) :
    DifferentiableOn ℂ (fun u => g (diagTransCLM2 (u, v)))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ upperHalfPlane) := by
  have hmaps : Set.MapsTo (fun u => diagTransCLM2 (u, v))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ upperHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant 2)) := by
    intro u hu
    refine ⟨diagTrans_mem_ball hρ (by simpa using hu.1) hv_norm, ?_⟩
    exact diagTrans_mem_posOrthant u v hv hu.2
  exact hdata.1.comp (differentiable_diagTrans_left v).differentiableOn hmaps

lemma diagTrans_slice_diff_lower (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) (v : ℂ) (hv : v.im = 0) (hv_norm : ‖v‖ < ρ / 2) :
    DifferentiableOn ℂ (fun u => g (diagTransCLM2 (u, v)))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ lowerHalfPlane) := by
  have hmaps : Set.MapsTo (fun u => diagTransCLM2 (u, v))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ lowerHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant 2)) := by
    intro u hu
    refine ⟨diagTrans_mem_ball hρ (by simpa using hu.1) hv_norm, ?_⟩
    exact diagTrans_mem_negOrthant u v hv hu.2
  exact hdata.2.1.comp (differentiable_diagTrans_left v).differentiableOn hmaps

lemma diagTrans_slice_continuousOn (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) (v : ℂ) (hv : v.im = 0) (hv_norm : ‖v‖ < ρ / 2) :
    ContinuousOn (fun u => g (diagTransCLM2 (u, v)))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0})) := by
  have hmaps : Set.MapsTo (fun u => diagTransCLM2 (u, v))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0}))
      (Metric.ball 0 ρ ∩
        (TubeDomain (PosOrthant 2) ∪ TubeDomain (NegOrthant 2) ∪
          {w : Fin 2 → ℂ | ∀ i, (w i).im = 0})) := by
    intro u hu
    refine ⟨diagTrans_mem_ball hρ (by simpa using hu.1) hv_norm, ?_⟩
    rcases hu.2 with (h_up | h_low) | h_real
    · exact Or.inl (Or.inl (diagTrans_mem_posOrthant u v hv h_up))
    · exact Or.inl (Or.inr (diagTrans_mem_negOrthant u v hv h_low))
    · exact Or.inr (diagTrans_im_both_zero u v h_real hv)
  exact hdata.2.2.comp (differentiable_diagTrans_left v).continuous.continuousOn hmaps

lemma diagTrans_zero_eq_diag (u : ℂ) :
    diagTransCLM2 (u, 0) = fun _ => u := by
  ext i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp
  · simp

noncomputable def diagCauchy1 (g : (Fin 2 → ℂ) → ℂ) (R : ℝ) (u : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - u)⁻¹ • g (fun _ => ζ)

lemma analyticAt_diagCauchy1 (g : (Fin 2 → ℂ) → ℂ) {R : ℝ} (hR : 0 < R)
    (h_int : CircleIntegrable (fun ζ => g (fun _ => ζ)) 0 R)
    {u : ℂ} (hu : u ∈ Metric.ball 0 R) :
    AnalyticAt ℂ (diagCauchy1 g R) u := by
  lift R to NNReal using hR.le with R_nn
  have hu' : u ∈ Metric.eball 0 R_nn := by
    rw [Metric.eball_coe]
    exact hu
  have h_series := hasFPowerSeriesOn_cauchy_integral h_int hR
  exact h_series.analyticAt_of_mem hu'

lemma circleIntegrable_diagSlice (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (_hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < ρ) :
    CircleIntegrable (fun ζ => g (fun _ => ζ)) 0 R := by
  have hmaps : Set.MapsTo (fun ζ : ℂ => (fun _ : Fin 2 => ζ))
      (Metric.sphere (0 : ℂ) |R|)
      (Metric.ball 0 ρ ∩ (TubeDomain (PosOrthant 2) ∪ TubeDomain (NegOrthant 2) ∪
        {w : Fin 2 → ℂ | ∀ i, (w i).im = 0})) := by
    intro ζ hζ
    rw [Metric.mem_sphere, dist_zero_right] at hζ
    have hζ_ball : (fun _ : Fin 2 => ζ) ∈ Metric.ball (0 : Fin 2 → ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]
      apply (pi_norm_lt_iff (by linarith)).mpr
      intro i
      rw [hζ, abs_of_pos hR_pos]
      exact hR_lt
    refine ⟨hζ_ball, ?_⟩
    rcases lt_trichotomy (0 : ℝ) ζ.im with h_pos | h_zero | h_neg
    · left; left
      intro i; exact h_pos
    · right
      intro i; exact h_zero.symm
    · left; right
      intro i; exact h_neg
  have h_cont_sphere : ContinuousOn (fun ζ => g (fun _ => ζ)) (Metric.sphere 0 |R|) := by
    have hd_cont : Continuous (fun ζ : ℂ => (fun _ : Fin 2 => ζ)) :=
      continuous_pi fun _ => continuous_id
    exact hdata.2.2.comp hd_cont.continuousOn hmaps
  exact circleIntegrable_of_continuous h_cont_sphere

lemma diagCauchy1_eq_of_differentiableOn
    (g : (Fin 2 → ℂ) → ℂ) {R : ℝ} (_hR : 0 < R)
    (h_diff : DifferentiableOn ℂ (fun ζ => g (fun _ => ζ)) (Metric.closedBall 0 R))
    {u : ℂ} (hu : u ∈ Metric.ball 0 R) :
    diagCauchy1 g R u = g (fun _ => u) := by
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff hu
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  change (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - u)⁻¹ • g (fun _ => ζ) = _
  rw [h_cauchy, ← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]

noncomputable def eowAnalyticKernel2 (g : (Fin 2 → ℂ) → ℂ) (R : ℝ) (w : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ ζ in C(0, R), (ζ - diagMeanCLM2 w)⁻¹ • g (diagTransCLM2 (ζ, transverseDiffCLM2 w))

theorem eowAnalyticKernel2_eq_of_differentiableOn
    (g : (Fin 2 → ℂ) → ℂ) {R : ℝ} (_hR : 0 < R)
    (w : Fin 2 → ℂ)
    (h_diff : DifferentiableOn ℂ (fun ζ => g (diagTransCLM2 (ζ, transverseDiffCLM2 w)))
      (Metric.closedBall 0 R))
    (hw_mean : diagMeanCLM2 w ∈ Metric.ball 0 R) :
    eowAnalyticKernel2 g R w = g w := by
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff hw_mean
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  change (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, R),
    (ζ - diagMeanCLM2 w)⁻¹ • g (diagTransCLM2 (ζ, transverseDiffCLM2 w)) = _
  rw [h_cauchy, ← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
  exact congr_arg g (diagTrans_reconstruction w)

lemma analyticOnNhd_diagMean_comp (G1 : ℂ → ℂ) {ρ : ℝ}
    (hG1 : AnalyticOnNhd ℂ G1 (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (G1 ∘ diagMeanCLM2) (Metric.ball (0 : Fin 2 → ℂ) ρ) := by
  intro w hw
  have hw_mean := diagMeanCLM2_mem_ball hw
  exact (hG1 (diagMeanCLM2 w) hw_mean).comp (diagMeanCLM2.analyticAt w)

lemma analyticOnNhd_of_continuousOn_upper_lower {U : Set ℂ} (hU : IsOpen U) (φ : ℂ → ℂ)
    (h_cont : ContinuousOn φ U)
    (h_pos : DifferentiableOn ℂ φ (U ∩ Analysis.upperHalfPlane))
    (h_neg : DifferentiableOn ℂ φ (U ∩ Analysis.lowerHalfPlane)) :
    AnalyticOnNhd ℂ φ U := by
  have h_diff_split : ∀ (x1 x2 y : ℝ),
      Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) ⊆ U →
      DifferentiableOn ℂ φ (Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0)) := by
    intro x1 x2 y hsubU
    rcases lt_trichotomy y 0 with h | h | h
    · have h_min : min y 0 = y := min_eq_left h.le
      have h_max : max y 0 = 0 := max_eq_right h.le
      exact h_neg.mono fun z hz => ⟨hsubU hz, by
        rw [mem_reProdIm, h_min, h_max] at hz
        exact hz.2.2⟩
    · have h_min : min y 0 = 0 := by rw [h]; exact min_self 0
      have h_max : max y 0 = 0 := by rw [h]; exact max_self 0
      have h_empty : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) = ∅ := by
        ext z; simp [mem_reProdIm, h_min, h_max]
      rw [h_empty]
      exact differentiableOn_empty
    · have h_min : min y 0 = 0 := min_eq_right h.le
      have h_max : max y 0 = y := max_eq_left h.le
      exact h_pos.mono fun z hz => ⟨hsubU hz, by
        rw [mem_reProdIm, h_min, h_max] at hz
        exact hz.2.1⟩
  have h_cons : IsConservativeOn φ U := by
    intro z w hzw
    rw [eq_neg_iff_add_eq_zero]
    have h_cont_rect : ContinuousOn φ (z.Rectangle w) := h_cont.mono hzw
    have h_open_rect_sub : ∀ (a1 a2 b1 b2 : ℝ),
        Ioo a1 a2 ⊆ uIcc z.re w.re → Ioo b1 b2 ⊆ uIcc z.im w.im →
        Ioo a1 a2 ×ℂ Ioo b1 b2 ⊆ U := by
      intro a1 a2 b1 b2 ha hb v hv
      rw [mem_reProdIm] at hv
      exact hzw (by rw [Complex.Rectangle, mem_reProdIm]; exact ⟨ha hv.1, hb hv.2⟩)
    have h_min_max_sub : ∀ (p q : ℝ), Ioo (min p q) (max p q) ⊆ uIcc p q := by
      intro p q t ht
      rw [uIcc]
      exact ⟨ht.1.le, ht.2.le⟩
    by_cases h0 : (0 : ℝ) ∈ uIcc z.im w.im
    · have hf_int_w : IntervalIntegrable (fun y => φ (w.re + y * I)) volume z.im 0 ∧
          IntervalIntegrable (fun y => φ (w.re + y * I)) volume 0 w.im :=
        ⟨Analysis.intervalIntegrable_of_continuousOn_rect z w φ w.re right_mem_uIcc z.im 0
            left_mem_uIcc h0 h_cont_rect,
          Analysis.intervalIntegrable_of_continuousOn_rect z w φ w.re right_mem_uIcc 0 w.im
            h0 right_mem_uIcc h_cont_rect⟩
      have hf_int_z : IntervalIntegrable (fun y => φ (z.re + y * I)) volume z.im 0 ∧
          IntervalIntegrable (fun y => φ (z.re + y * I)) volume 0 w.im :=
        ⟨Analysis.intervalIntegrable_of_continuousOn_rect z w φ z.re left_mem_uIcc z.im 0
            left_mem_uIcc h0 h_cont_rect,
          Analysis.intervalIntegrable_of_continuousOn_rect z w φ z.re left_mem_uIcc 0 w.im
            h0 right_mem_uIcc h_cont_rect⟩
      rw [Analysis.wedgeIntegral_split_y z w 0 φ hf_int_w hf_int_z]
      have h1 : wedgeIntegral z (w.re + (0 : ℝ) * I) φ +
          wedgeIntegral (w.re + (0 : ℝ) * I) z φ = 0 := by
        apply Analysis.wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn
        · apply h_cont_rect.mono
          intro v hv
          rw [Complex.Rectangle, mem_reProdIm] at hv ⊢
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
            mul_im, I_im, mul_one, add_zero] at hv
          exact ⟨hv.1, uIcc_subset_uIcc left_mem_uIcc h0 hv.2⟩
        · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
            mul_im, I_im, mul_one, add_zero]
          exact h_diff_split (min z.re w.re) (max z.re w.re) z.im
            (h_open_rect_sub _ _ _ _ (h_min_max_sub z.re w.re)
              ((h_min_max_sub z.im 0).trans (uIcc_subset_uIcc left_mem_uIcc h0)))
      have h2 : wedgeIntegral (z.re + (0 : ℝ) * I) w φ +
          wedgeIntegral w (z.re + (0 : ℝ) * I) φ = 0 := by
        apply Analysis.wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn
        · apply h_cont_rect.mono
          intro v hv
          rw [Complex.Rectangle, mem_reProdIm] at hv ⊢
          simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
            mul_im, I_im, mul_one, add_zero] at hv
          exact ⟨hv.1, uIcc_subset_uIcc h0 right_mem_uIcc hv.2⟩
        · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
            mul_im, I_im, mul_one, add_zero, min_comm 0 w.im, max_comm 0 w.im]
          exact h_diff_split (min z.re w.re) (max z.re w.re) w.im
            (h_open_rect_sub _ _ _ _ (h_min_max_sub z.re w.re)
              (by rw [min_comm w.im 0, max_comm w.im 0]
                  exact (h_min_max_sub 0 w.im).trans (uIcc_subset_uIcc h0 right_mem_uIcc)))
      rw [h1, h2, add_zero]
    · apply Analysis.wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn φ z w h_cont_rect
      have h_in_U := h_open_rect_sub _ _ _ _ (h_min_max_sub z.re w.re) (h_min_max_sub z.im w.im)
      rcases lt_trichotomy 0 z.im with h | h | h
      · have hw_im : 0 < w.im := by
          by_contra h_contra
          push Not at h_contra
          exact h0 (mem_uIcc.mpr (Or.inr ⟨h_contra, h.le⟩))
        exact h_pos.mono fun v hv => ⟨h_in_U hv, lt_trans (lt_min h hw_im) (mem_reProdIm.mp hv).2.1⟩
      · exact False.elim (h0 (h ▸ left_mem_uIcc))
      · have hw_im : w.im < 0 := by
          by_contra h_contra
          push Not at h_contra
          exact h0 (mem_uIcc.mpr (Or.inl ⟨h.le, h_contra⟩))
        exact h_neg.mono fun v hv => ⟨h_in_U hv, lt_trans (mem_reProdIm.mp hv).2.2 (max_lt h hw_im)⟩
  have h_diff : DifferentiableOn ℂ φ U :=
    (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨h_cons, h_cont⟩
  exact h_diff.analyticOnNhd hU

theorem orthant_eowData_diag_analyticOnNhd (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    AnalyticOnNhd ℂ (g ∘ diagCLM n) (Metric.ball 0 ρ) := by
  refine analyticOnNhd_of_continuousOn_upper_lower Metric.isOpen_ball (g ∘ diagCLM n) ?_
    (orthant_eowData_diag_diff_upper n g ρ hdata)
    (orthant_eowData_diag_diff_lower n g ρ hdata)
  refine (orthant_eowData_diag_continuousOn n g ρ hdata).mono fun t ht => ⟨ht, ?_⟩
  rcases lt_trichotomy 0 t.im with hp | hz | hm
  · exact Or.inl (Or.inl hp)
  · exact Or.inr hz.symm
  · exact Or.inl (Or.inr hm)

theorem orthant_eowData_directional_slice_analyticOnNhd (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hdata : OrthantEOWData n g ρ)
    (x y : Fin n → ℝ) (hx : ‖x‖ < ρ / 2) (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ < ρ / 2) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => g (fun i => (x i : ℂ) + ζ * (y i : ℂ)))
      (Metric.ball (0 : ℂ) 1) := by
  let γ : ℂ → (Fin n → ℂ) := fun ζ i => (x i : ℂ) + ζ * (y i : ℂ)
  have hγ_diff : Differentiable ℂ γ :=
    differentiable_pi.mpr fun i =>
      (differentiable_const (x i : ℂ)).add (differentiable_id.mul (differentiable_const (y i : ℂ)))
  have hγ_ball : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, γ ζ ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro ζ hζ
    have hζ_lt : ‖ζ‖ < 1 := by simpa using hζ
    rw [Metric.mem_ball, dist_zero_right]
    apply (pi_norm_lt_iff hρ).mpr
    intro i
    have hxi : |x i| < ρ / 2 := (norm_le_pi_norm x i).trans_lt hx
    have hyi : |y i| < ρ / 2 := (norm_le_pi_norm y i).trans_lt hy
    dsimp [γ]
    calc ‖(x i : ℂ) + ζ * (y i : ℂ)‖
      _ ≤ ‖(x i : ℂ)‖ + ‖ζ * (y i : ℂ)‖ := norm_add_le _ _
      _ = |x i| + ‖ζ‖ * |y i| := by simp [Complex.norm_real]
      _ ≤ |x i| + 1 * |y i| := by nlinarith [abs_nonneg (y i)]
      _ < ρ / 2 + ρ / 2 := by linarith
      _ = ρ := add_halves ρ
  refine analyticOnNhd_of_continuousOn_upper_lower Metric.isOpen_ball (g ∘ γ) ?_ ?_ ?_
  · refine hdata.2.2.comp hγ_diff.continuous.continuousOn fun ζ hζ => ⟨hγ_ball ζ hζ, ?_⟩
    rcases lt_trichotomy 0 ζ.im with hp | hz | hm
    · refine Or.inl (Or.inl fun i => ?_)
      dsimp [γ]
      simp [Complex.mul_im, mul_pos hp (hy_pos i)]
    · refine Or.inr fun i => ?_
      dsimp [γ]
      simp [Complex.mul_im, hz.symm]
    · refine Or.inl (Or.inr fun i => ?_)
      dsimp [γ]
      simp [Complex.mul_im, mul_neg_of_neg_of_pos hm (hy_pos i)]
  · refine hdata.1.comp hγ_diff.differentiableOn fun ζ hζ => ⟨hγ_ball ζ hζ.1, fun i => ?_⟩
    dsimp [γ]
    have hp : 0 < ζ.im := hζ.2
    simp [Complex.mul_im, mul_pos hp (hy_pos i)]
  · refine hdata.2.1.comp hγ_diff.differentiableOn fun ζ hζ => ⟨hγ_ball ζ hζ.1, fun i => ?_⟩
    dsimp [γ]
    have hm : ζ.im < 0 := hζ.2
    simp [Complex.mul_im, mul_neg_of_neg_of_pos hm (hy_pos i)]

theorem orthant_eow_extension_1d
    (g : (Fin 1 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hdata : OrthantEOWData 1 g ρ) :
    OrthantEOWCore 1 g := by
  let P0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let G : (Fin 1 → ℂ) → ℂ := (g ∘ diagCLM 1) ∘ P0
  have h_diag_an := orthant_eowData_diag_analyticOnNhd 1 g ρ hdata
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ) := by
    intro w hw
    have hw0 : P0 w ∈ Metric.ball (0 : ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right] at hw ⊢
      exact (norm_le_pi_norm w 0).trans_lt hw
    exact (h_diag_an (P0 w) hw0).comp (P0.analyticAt w)
  have hG_eq : ∀ w : Fin 1 → ℂ, G w = g w := by
    intro w
    dsimp [G, P0]
    congr 1
    ext i
    fin_cases i
    rfl
  obtain ⟨z₁, hz₁_b, hz₁_pos⟩ := posOrthant_ball_inter_nonempty 1 ρ hρ
  obtain ⟨z₂, hz₂_b, hz₂_neg⟩ := negOrthant_ball_inter_nonempty 1 ρ hρ
  have h_open1 : IsOpen (Metric.ball (0 : Fin 1 → ℂ) ρ ∩ TubeDomain (PosOrthant 1)) :=
    Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant 1))
  have h_open2 : IsOpen (Metric.ball (0 : Fin 1 → ℂ) ρ ∩ TubeDomain (NegOrthant 1)) :=
    Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant 1))
  exact ⟨ρ, hρ, G, hG_an,
    ⟨_, h_open1, ⟨z₁, hz₁_b, hz₁_pos⟩, subset_rfl, fun w _ => hG_eq w⟩,
    ⟨_, h_open2, ⟨z₂, hz₂_b, hz₂_neg⟩, subset_rfl, fun w _ => hG_eq w⟩⟩


lemma alternating_sum_powerset {α : Type*} [DecidableEq α] (B : Finset α) :
    (∑ T ∈ B.powerset, (-1 : ℝ) ^ T.card) = if B = ∅ then 1 else 0 := by
  induction B using Finset.induction_on with
  | empty => simp
  | @insert a s ha _ih =>
    rw [Finset.powerset_insert, Finset.sum_union]
    · simp only [Finset.insert_ne_empty, ↓reduceIte]
      have h_im : (∑ T ∈ Finset.image (insert a) s.powerset, (-1 : ℝ) ^ T.card) =
          - ∑ T ∈ s.powerset, (-1 : ℝ) ^ T.card := by
        rw [Finset.sum_image]
        · rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun T hT => ?_
          have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
          rw [Finset.card_insert_of_notMem haT, pow_succ]
          ring
        · intro T₁ hT₁ T₂ hT₂ h_eq
          have ha₁ : a ∉ T₁ := fun h => ha (Finset.mem_powerset.mp hT₁ h)
          have ha₂ : a ∉ T₂ := fun h => ha (Finset.mem_powerset.mp hT₂ h)
          have h_er := congr_arg (fun U => Finset.erase U a) h_eq
          simpa [Finset.erase_insert ha₁, Finset.erase_insert ha₂] using h_er
      rw [h_im, add_neg_cancel]
    · rw [Finset.disjoint_left]
      intro T hT₁ hT₂
      rcases Finset.mem_image.mp hT₂ with ⟨U, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hT₁ (Finset.mem_insert_self a U))

lemma alternating_sum_superset (m : ℕ) (A : Finset (Fin m)) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => A ⊆ S), (-1 : ℝ) ^ (m - S.card)) =
      if A = Finset.univ then 1 else 0 := by
  have h_bij :
      (∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => A ⊆ S), (-1 : ℝ) ^ (m - S.card)) =
        ∑ T ∈ (Aᶜ).powerset, (-1 : ℝ) ^ T.card := by
    refine Finset.sum_bij (fun S _ => Sᶜ) ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_powerset, Finset.compl_subset_compl]
      exact (Finset.mem_filter.mp hS).2
    · intro S₁ _ S₂ _ h_eq
      exact compl_injective h_eq
    · intro T hT
      refine ⟨Tᶜ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, compl_compl T⟩
      rw [← Finset.compl_subset_compl, compl_compl]
      exact Finset.mem_powerset.mp hT
    · intro S _
      rw [Finset.card_compl, Fintype.card_fin]
  rw [h_bij, alternating_sum_powerset]
  have h_iff : Aᶜ = ∅ ↔ A = Finset.univ := by
    constructor
    · intro hc
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      have hxc : x ∈ Aᶜ := Finset.mem_compl.mpr hx
      rw [hc] at hxc
      exact Finset.notMem_empty x hxc
    · rintro rfl
      simp
  by_cases h : A = Finset.univ
  · rw [if_pos (h_iff.mpr h), if_pos h]
  · have h2 : Aᶜ ≠ ∅ := fun hc => h (h_iff.mp hc)
    rw [if_neg h2, if_neg h]

def optReq {m : ℕ} (f : Fin m → Option (Fin m)) : Finset (Fin m) :=
  Finset.univ.biUnion fun i => match f i with | none => ∅ | some k => {k}

lemma optReq_eq_univ_iff {m : ℕ} (f : Fin m → Option (Fin m)) :
    optReq f = Finset.univ ↔ ∃ σ : Equiv.Perm (Fin m), f = fun i => some (σ i) := by
  constructor
  · intro h_univ
    have h_surj : ∀ k : Fin m, ∃ i : Fin m, f i = some k := by
      intro k
      have hk : k ∈ optReq f := by rw [h_univ]; exact Finset.mem_univ k
      rcases Finset.mem_biUnion.mp hk with ⟨i, _, hi⟩
      cases hfi : f i with
      | none => simp [hfi] at hi
      | some j =>
        rw [hfi, Finset.mem_singleton] at hi
        exact ⟨i, by rw [hfi, hi]⟩
    choose g hg using h_surj
    have hg_inj : Function.Injective g := by
      intro k₁ k₂ h_eq
      have h1 := hg k₁
      rw [h_eq, hg k₂] at h1
      exact Option.some.inj h1.symm
    let σ_inv : Equiv.Perm (Fin m) :=
      Equiv.ofBijective g ⟨hg_inj, Finite.injective_iff_surjective.mp hg_inj⟩
    refine ⟨σ_inv.symm, ?_⟩
    ext i
    obtain ⟨k, hk⟩ := σ_inv.surjective i
    have hgk : g k = i := hk
    have h_app : σ_inv.symm i = k := by
      rw [← hk]
      exact σ_inv.symm_apply_apply k
    rw [h_app, ← hgk, hg k]
  · rintro ⟨σ, rfl⟩
    ext k
    simp only [optReq, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton, true_and,
      iff_true]
    exact ⟨σ.symm k, (Equiv.apply_symm_apply σ k).symm⟩

lemma multilinear_polarization {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) ℝ)
    (y₀ : E) (w : Fin m → E) :
    (∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) * p (fun _ => y₀ + ∑ k ∈ S, w k)) =
      ∑ σ : Equiv.Perm (Fin m), p (fun i => w (σ i)) := by
  let term : Finset (Fin m) → Option (Fin m) → E := fun S o =>
    match o with
    | none => y₀
    | some k => if k ∈ S then w k else 0
  have h_sum_term :
      ∀ S : Finset (Fin m), y₀ + (∑ k ∈ S, w k) = ∑ o : Option (Fin m), term S o := by
    intro S
    rw [Fintype.sum_option]
    dsimp [term]
    congr 1
    rw [← Finset.sum_filter]
    congr 1
    ext k
    simp
  have h_expand : ∀ S : Finset (Fin m),
      p (fun _ => y₀ + ∑ k ∈ S, w k) =
        ∑ f : Fin m → Option (Fin m), p (fun i => term S (f i)) := by
    intro S
    rw [h_sum_term S]
    have h := p.toMultilinearMap.map_sum_finset (fun _ o => term S o) (fun _ => Finset.univ)
    simpa [Fintype.piFinset_univ] using h
  have h_term_eq : ∀ (S : Finset (Fin m)) (f : Fin m → Option (Fin m)),
      p (fun i => term S (f i)) =
        if optReq f ⊆ S then p (fun i => term Finset.univ (f i)) else 0 := by
    intro S f
    by_cases hsub : optReq f ⊆ S
    · rw [if_pos hsub]
      congr 1
      ext i
      cases hfi : f i with
      | none => rfl
      | some k =>
        have hk : k ∈ optReq f := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hfi]⟩
        simp [term, hsub hk]
    · rw [if_neg hsub]
      rcases Finset.not_subset.mp hsub with ⟨k, hk_req, hk_not⟩
      rcases Finset.mem_biUnion.mp hk_req with ⟨i, _, hi⟩
      have hfi : f i = some k := by
        cases h : f i with
        | none => simp [h] at hi
        | some j =>
          rw [h, Finset.mem_singleton] at hi
          exact congr_arg some hi.symm
      exact p.map_coord_zero i (by rw [hfi]; dsimp [term]; rw [if_neg hk_not])
  simp_rw [h_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h_inner : ∀ f : Fin m → Option (Fin m),
      (∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) * p (fun i => term S (f i))) =
        if optReq f = Finset.univ then p (fun i => term Finset.univ (f i)) else 0 := by
    intro f
    have h_congr_S :
        (∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) * p (fun i => term S (f i))) =
        ∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) *
          (if optReq f ⊆ S then p (fun i => term Finset.univ (f i)) else 0) :=
      Finset.sum_congr rfl fun S _ => by rw [h_term_eq S f]
    rw [h_congr_S]
    have h_fil : (∑ S : Finset (Fin m),
        (-1 : ℝ) ^ (m - S.card) *
          (if optReq f ⊆ S then p (fun i => term Finset.univ (f i)) else 0)) =
        (∑ S ∈ Finset.univ.filter (fun S => optReq f ⊆ S), (-1 : ℝ) ^ (m - S.card)) *
          p (fun i => term Finset.univ (f i)) := by
      rw [Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> ring
    rw [h_fil, alternating_sum_superset]
    split_ifs <;> ring
  simp_rw [h_inner, ← Finset.sum_filter]
  have h_perm_sum :
      (∑ f ∈ Finset.univ.filter (fun f : Fin m → Option (Fin m) => optReq f = Finset.univ),
        p (fun i => term Finset.univ (f i))) =
      ∑ σ : Equiv.Perm (Fin m), p (fun i => w (σ i)) := by
    refine Finset.sum_bij
      (fun f hf => Classical.choose ((optReq_eq_univ_iff f).mp (Finset.mem_filter.mp hf).2))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro f₁ hf₁ f₂ hf₂ h_eq
      have h1 := Classical.choose_spec ((optReq_eq_univ_iff f₁).mp (Finset.mem_filter.mp hf₁).2)
      have h2 := Classical.choose_spec ((optReq_eq_univ_iff f₂).mp (Finset.mem_filter.mp hf₂).2)
      rw [h1, h2, h_eq]
    · intro σ _
      let f : Fin m → Option (Fin m) := fun i => some (σ i)
      have hf : f ∈ Finset.univ.filter (fun f => optReq f = Finset.univ) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (optReq_eq_univ_iff f).mpr ⟨σ, rfl⟩⟩
      refine ⟨f, hf, ?_⟩
      have hspec := Classical.choose_spec ((optReq_eq_univ_iff f).mp (Finset.mem_filter.mp hf).2)
      apply Equiv.ext
      intro i
      have hi : some (σ i) = some ((Classical.choose
          ((optReq_eq_univ_iff f).mp (Finset.mem_filter.mp hf).2)) i) := congr_fun hspec i
      exact (Option.some.inj hi).symm
    · intro f hf
      have hspec := Classical.choose_spec ((optReq_eq_univ_iff f).mp (Finset.mem_filter.mp hf).2)
      conv_lhs => rw [hspec]
      congr 1
      ext i
      simp [term]
  exact h_perm_sum

lemma sum_perm_multilinear_basis (n k : ℕ)
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ℝ) (y : Fin n → ℝ) :
    (∑ α : Fin k → Fin n, (∏ j : Fin k, y (α j)) *
        ∑ σ : Equiv.Perm (Fin k), p (fun j => Pi.single (α (σ j)) (1 : ℝ))) =
      (k.factorial : ℝ) * p (fun _ => y) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hy_basis : y = ∑ i : Fin n, y i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne (Ne.symm hji)]
    · intro hi; exact False.elim (hi (Finset.mem_univ i))
  have h_diag : (∑ β : Fin k → Fin n, (∏ j : Fin k, y (β j)) *
      p (fun j => Pi.single (β j) (1 : ℝ))) = p (fun _ => y) := by
    have h_map := p.toMultilinearMap.map_sum_finset
      (fun _ i => y i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) (fun _ => Finset.univ)
    simp only [Fintype.piFinset_univ] at h_map
    have h_lhs : p (fun _ => y) =
        p.toMultilinearMap (fun _ => ∑ i : Fin n, y i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) := by
      rw [← hy_basis]; rfl
    rw [h_lhs, h_map]
    refine Finset.sum_congr rfl fun β _ => ?_
    change (∏ j : Fin k, y (β j)) * p (fun j => Pi.single (β j) (1 : ℝ)) =
      p (fun j => y (β j) • (Pi.single (β j) (1 : ℝ) : Fin n → ℝ))
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]
  have h_each_σ : ∀ σ : Equiv.Perm (Fin k),
      (∑ α : Fin k → Fin n, (∏ j : Fin k, y (α j)) *
          p (fun j => Pi.single (α (σ j)) (1 : ℝ))) = p (fun _ => y) := by
    intro σ
    rw [← h_diag]
    refine Finset.sum_bij (fun α _ => α ∘ σ) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro α₁ _ α₂ _ h_eq
      funext j
      have := congr_fun h_eq (σ.symm j)
      simpa using this
    · intro β _
      refine ⟨β ∘ σ.symm, Finset.mem_univ _, ?_⟩
      ext j
      simp
    · intro α _
      dsimp only [Function.comp_apply]
      congr 1
      exact (Equiv.prod_comp σ (fun j => y (α j))).symm
  simp_rw [h_each_σ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

def orthantSlice {n : ℕ} (g : (Fin n → ℂ) → ℂ) (x y : Fin n → ℝ) (ζ : ℂ) : ℂ :=
  g (fun i => (x i : ℂ) + ζ * (y i : ℂ))

noncomputable def orthantSliceCoeff {n : ℕ} (g : (Fin n → ℂ) → ℂ) (x y : Fin n → ℝ)
    (m : ℕ) : ℂ :=
  (cauchyPowerSeries (orthantSlice g x y) 0 (5 / 4) m) (fun _ => 1)

def orthantBox (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {y | ∀ i, ρ / 8 ≤ y i ∧ y i ≤ 3 * ρ / 8}

lemma isCompact_orthantBox (n : ℕ) (ρ : ℝ) : IsCompact (orthantBox n ρ) := by
  have heq : orthantBox n ρ = Set.pi Set.univ (fun _ => Set.Icc (ρ / 8) (3 * ρ / 8)) := by
    ext y
    simp only [orthantBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
  rw [heq]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

lemma orthantBox_subset_posOrthant (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    orthantBox n ρ ⊆ PosOrthant n := by
  intro y hy i
  linarith [(hy i).1]

lemma orthantBox_norm_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {y : Fin n → ℝ} (hy : y ∈ orthantBox n ρ) :
    ‖y‖ ≤ 3 * ρ / 8 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [(hy i).1], (hy i).2⟩

lemma orthantSlice_mem_wedge {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x y : Fin n → ℝ} (hx : ‖x‖ ≤ ρ / 8) (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8)
    {ζ : ℂ} (hζ : ‖ζ‖ < 3 / 2) :
    (fun i => (x i : ℂ) + ζ * (y i : ℂ)) ∈
      Metric.ball (0 : Fin n → ℂ) ρ ∩
        (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
          {w : Fin n → ℂ | ∀ i, (w i).im = 0}) := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    refine (pi_norm_lt_iff hρ).mpr fun i => ?_
    have hxi : |x i| ≤ ρ / 8 := (norm_le_pi_norm x i).trans hx
    have hyi : |y i| ≤ 3 * ρ / 8 := (norm_le_pi_norm y i).trans hy
    calc ‖(x i : ℂ) + ζ * (y i : ℂ)‖
        ≤ ‖(x i : ℂ)‖ + ‖ζ * (y i : ℂ)‖ := norm_add_le _ _
      _ = |x i| + ‖ζ‖ * |y i| := by simp [Complex.norm_real]
      _ ≤ ρ / 8 + (3 / 2) * (3 * ρ / 8) := by nlinarith [abs_nonneg (y i)]
      _ < ρ := by linarith
  · rcases lt_trichotomy 0 ζ.im with hp | hz | hm
    · exact Or.inl (Or.inl fun i => by simp [Complex.mul_im, mul_pos hp (hy_pos i)])
    · exact Or.inr fun i => by simp [Complex.mul_im, hz.symm]
    · exact Or.inl (Or.inr fun i => by simp [Complex.mul_im, mul_neg_of_neg_of_pos hm (hy_pos i)])

lemma orthantSlice_analyticOnNhd (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) {x y : Fin n → ℝ}
    (hx : ‖x‖ ≤ ρ / 8) (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8) :
    AnalyticOnNhd ℂ (orthantSlice g x y) (Metric.ball (0 : ℂ) (3 / 2)) := by
  let γ : ℂ → (Fin n → ℂ) := fun ζ i => (x i : ℂ) + ζ * (y i : ℂ)
  have hγ_diff : Differentiable ℂ γ :=
    differentiable_pi.mpr fun i =>
      (differentiable_const (x i : ℂ)).add (differentiable_id.mul (differentiable_const (y i : ℂ)))
  refine analyticOnNhd_of_continuousOn_upper_lower Metric.isOpen_ball (g ∘ γ) ?_ ?_ ?_
  · refine hdata.2.2.comp hγ_diff.continuous.continuousOn fun ζ hζ => ?_
    exact orthantSlice_mem_wedge hρ hx hy_pos hy (by simpa using hζ)
  · refine hdata.1.comp hγ_diff.differentiableOn fun ζ hζ => ⟨?_, fun i => ?_⟩
    · exact (orthantSlice_mem_wedge hρ hx hy_pos hy (by simpa using hζ.1)).1
    · have hp : 0 < ζ.im := hζ.2
      simp [γ, Complex.mul_im, mul_pos hp (hy_pos i)]
  · refine hdata.2.1.comp hγ_diff.differentiableOn fun ζ hζ => ⟨?_, fun i => ?_⟩
    · exact (orthantSlice_mem_wedge hρ hx hy_pos hy (by simpa using hζ.1)).1
    · have hm : ζ.im < 0 := hζ.2
      simp [γ, Complex.mul_im, mul_neg_of_neg_of_pos hm (hy_pos i)]

lemma orthantSlice_hasFPowerSeriesOnBall (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) {x y : Fin n → ℝ}
    (hx : ‖x‖ ≤ ρ / 8) (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8) :
    HasFPowerSeriesOnBall (orthantSlice g x y)
      (cauchyPowerSeries (orthantSlice g x y) 0 (5 / 4)) 0 (5 / 4 : NNReal) := by
  have han := orthantSlice_analyticOnNhd n g hρ hdata hx hy_pos hy
  have h_coe : ((5 / 4 : NNReal) : ℝ) = 5 / 4 := by norm_num
  have hdiff : DifferentiableOn ℂ (orthantSlice g x y)
      (Metric.closedBall 0 ((5 / 4 : NNReal) : ℝ)) := by
    refine han.differentiableOn.mono fun ζ hζ => ?_
    rw [Metric.mem_closedBall, dist_zero_right, h_coe] at hζ
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hζ (by norm_num)
  have hP := hdiff.hasFPowerSeriesOnBall (by norm_num : (0 : NNReal) < 5 / 4)
  rwa [h_coe] at hP

lemma orthant_eowData_uniform_box_bound (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) (ρ / 8),
      ∀ y ∈ orthantBox n ρ,
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) (5 / 4),
        ‖orthantSlice g x y ζ‖ ≤ M := by
  let S : Set ((Fin n → ℝ) × (Fin n → ℝ) × ℂ) :=
    Metric.closedBall 0 (ρ / 8) ×ˢ (orthantBox n ρ ×ˢ Metric.closedBall 0 (5 / 4))
  have hS_comp : IsCompact S :=
    (isCompact_closedBall _ _).prod ((isCompact_orthantBox n ρ).prod (isCompact_closedBall _ _))
  let Φ : (Fin n → ℝ) × (Fin n → ℝ) × ℂ → (Fin n → ℂ) :=
    fun p i => (p.1 i : ℂ) + p.2.2 * (p.2.1 i : ℂ)
  have hΦ_cont : Continuous Φ := by
    refine continuous_pi fun i => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst)).add
      ((continuous_snd.comp continuous_snd).mul
        (Complex.continuous_ofReal.comp
          ((continuous_apply i).comp (continuous_fst.comp continuous_snd))))
  have h_sub : Φ '' S ⊆ Metric.ball 0 ρ ∩
      (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
        {w : Fin n → ℂ | ∀ i, (w i).im = 0}) := by
    rintro _ ⟨⟨x, y, ζ⟩, ⟨hx, hy, hζ⟩, rfl⟩
    have hx' : ‖x‖ ≤ ρ / 8 := by simpa [Metric.mem_closedBall] using hx
    have hζ' : ‖ζ‖ < 3 / 2 :=
      lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hζ) (by norm_num)
    exact orthantSlice_mem_wedge hρ hx' (orthantBox_subset_posOrthant n hρ hy)
      (orthantBox_norm_le hρ hy) hζ'
  rcases orthant_eowData_bounded_on_compact n g ρ hdata (Φ '' S) (hS_comp.image hΦ_cont) h_sub with
    ⟨M₀, hM₀⟩
  refine ⟨max M₀ 0, le_max_right _ _, fun x hx y hy ζ hζ => ?_⟩
  exact (hM₀ (Φ (x, y, ζ)) ⟨(x, y, ζ), ⟨hx, hy, hζ⟩, rfl⟩).trans (le_max_left _ _)

lemma orthant_eowData_fixed_y_bound (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) {y : Fin n → ℝ}
    (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) (ρ / 8),
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) (5 / 4),
        ‖orthantSlice g x y ζ‖ ≤ M := by
  let S : Set ((Fin n → ℝ) × ℂ) :=
    Metric.closedBall 0 (ρ / 8) ×ˢ Metric.closedBall 0 (5 / 4)
  have hS_comp : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  let Φ : (Fin n → ℝ) × ℂ → (Fin n → ℂ) := fun p i => (p.1 i : ℂ) + p.2 * (y i : ℂ)
  have hΦ_cont : Continuous Φ := by
    refine continuous_pi fun i => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst)).add
      (continuous_snd.mul continuous_const)
  have h_sub : Φ '' S ⊆ Metric.ball 0 ρ ∩
      (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
        {w : Fin n → ℂ | ∀ i, (w i).im = 0}) := by
    rintro _ ⟨⟨x, ζ⟩, ⟨hx, hζ⟩, rfl⟩
    have hx' : ‖x‖ ≤ ρ / 8 := by simpa [Metric.mem_closedBall] using hx
    have hζ' : ‖ζ‖ < 3 / 2 :=
      lt_of_le_of_lt (by simpa [Metric.mem_closedBall] using hζ) (by norm_num)
    exact orthantSlice_mem_wedge hρ hx' hy_pos hy hζ'
  rcases orthant_eowData_bounded_on_compact n g ρ hdata (Φ '' S) (hS_comp.image hΦ_cont) h_sub with
    ⟨M₀, hM₀⟩
  refine ⟨max M₀ 0, le_max_right _ _, fun x hx ζ hζ => ?_⟩
  exact (hM₀ (Φ (x, ζ)) ⟨(x, ζ), ⟨hx, hζ⟩, rfl⟩).trans (le_max_left _ _)

lemma norm_orthantSliceCoeff_le {n : ℕ} {g : (Fin n → ℂ) → ℂ} {x y : Fin n → ℝ} {M : ℝ}
    (_hM_nn : 0 ≤ M)
    (h_bd : ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ‖orthantSlice g x y ζ‖ ≤ M) (m : ℕ) :
    ‖orthantSliceCoeff g x y m‖ ≤ M := by
  dsimp [orthantSliceCoeff]
  rw [cauchyPowerSeries_apply]
  simp only [sub_zero, smul_eq_mul]
  rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h_int : ‖∮ z in C(0, 5 / 4), (1 / z) ^ m * (z⁻¹ * orthantSlice g x y z)‖ ≤
      2 * Real.pi * (5 / 4) * ((4 / 5) * M) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) fun z hz => ?_
    have hz_norm : ‖z‖ = 5 / 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_mul, one_div, norm_pow, norm_inv, hz_norm]
    have h_inv : (5 / 4 : ℝ)⁻¹ = 4 / 5 := by norm_num
    rw [h_inv]
    have h_pow : (4 / 5 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (4 / 5 : ℝ) ^ m * ((4 / 5) * ‖orthantSlice g x y z‖)
        ≤ 1 * ((4 / 5) * M) := by
          refine mul_le_mul h_pow (mul_le_mul_of_nonneg_left (h_bd z hz) (by norm_num))
            (by positivity) zero_le_one
      _ = (4 / 5) * M := one_mul _
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∮ z in C(0, 5 / 4), (1 / z) ^ m * (z⁻¹ * orthantSlice g x y z)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (5 / 4) * ((4 / 5) * M)) :=
        mul_le_mul_of_nonneg_left h_int (inv_nonneg.mpr h2pi_pos.le)
    _ = M := by field_simp [h2pi_pos.ne']

lemma continuousOn_orthantSliceCoeff (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) {y : Fin n → ℝ}
    (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8) (m : ℕ) :
    ContinuousOn (fun x => orthantSliceCoeff g x y m)
      (Metric.closedBall (0 : Fin n → ℝ) (ρ / 8)) := by
  obtain ⟨M, _hM_nn, hM_bd⟩ := orthant_eowData_fixed_y_bound n g hρ hdata hy_pos hy
  have h_eq : (fun x => orthantSliceCoeff g x y m) = fun x =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap 0 (5 / 4)) θ *
            ((1 / circleMap 0 (5 / 4) θ) ^ m *
              ((circleMap 0 (5 / 4) θ)⁻¹ * orthantSlice g x y (circleMap 0 (5 / 4) θ))) := by
    ext x
    dsimp [orthantSliceCoeff]
    rw [cauchyPowerSeries_apply, circleIntegral]
    simp only [sub_zero, smul_eq_mul]
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [h_eq]
  refine continuousOn_const.mul ?_
  let F : (Fin n → ℝ) → ℝ → ℂ := fun x θ =>
    deriv (circleMap 0 (5 / 4)) θ *
      ((1 / circleMap 0 (5 / 4) θ) ^ m *
        ((circleMap 0 (5 / 4) θ)⁻¹ * orthantSlice g x y (circleMap 0 (5 / 4) θ)))
  have hF_cont_θ : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) (ρ / 8), Continuous (F x) := by
    intro x hx
    have hx' : ‖x‖ ≤ ρ / 8 := by simpa [Metric.mem_closedBall] using hx
    have h_cm : Continuous (circleMap (0 : ℂ) (5 / 4)) := continuous_circleMap 0 (5 / 4)
    have h_dcm : Continuous (deriv (circleMap (0 : ℂ) (5 / 4))) := by
      have hd : deriv (circleMap (0 : ℂ) (5 / 4)) = fun θ => circleMap 0 (5 / 4) θ * Complex.I := by
        ext θ; exact deriv_circleMap 0 (5 / 4) θ
      rw [hd]
      exact h_cm.mul continuous_const
    have h_ne : ∀ θ : ℝ, circleMap (0 : ℂ) (5 / 4) θ ≠ 0 := fun θ =>
      norm_ne_zero_iff.mp (by rw [norm_circleMap_zero]; norm_num)
    have h_sl : Continuous (fun θ : ℝ => orthantSlice g x y (circleMap 0 (5 / 4) θ)) := by
      have han := orthantSlice_analyticOnNhd n g hρ hdata hx' hy_pos hy
      refine han.continuousOn.comp_continuous h_cm fun θ => ?_
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero]
      norm_num
    exact h_dcm.mul (((continuous_const.div h_cm h_ne).pow m).mul ((h_cm.inv₀ h_ne).mul h_sl))
  have h_fin_ioc : volume (Set.Ioc (0 : ℝ) (2 * Real.pi)) < ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  refine MeasureTheory.continuousOn_of_dominated
    (bound := fun _ => M)
    (fun x hx => (hF_cont_θ x hx).aestronglyMeasurable)
    (fun x hx => Filter.Eventually.of_forall fun θ => ?_)
    (integrableOn_const (hs := h_fin_ioc.ne))
    (Filter.Eventually.of_forall fun θ => ?_)
  · change ‖deriv (circleMap 0 (5 / 4)) θ *
      ((1 / circleMap 0 (5 / 4) θ) ^ m *
        ((circleMap 0 (5 / 4) θ)⁻¹ * orthantSlice g x y (circleMap 0 (5 / 4) θ)))‖ ≤ M
    rw [deriv_circleMap, norm_mul, norm_mul, norm_I, mul_one, norm_circleMap_zero,
      abs_of_pos (by norm_num), norm_mul, norm_mul, one_div, norm_pow, norm_inv,
      norm_circleMap_zero, abs_of_pos (by norm_num)]
    have h_inv : (5 / 4 : ℝ)⁻¹ = 4 / 5 := by norm_num
    rw [h_inv]
    have h_pow : (4 / 5 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h_cm_mem : circleMap (0 : ℂ) (5 / 4) θ ∈ Metric.closedBall (0 : ℂ) (5 / 4) := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero]
      norm_num
    have hg_le := hM_bd x hx _ h_cm_mem
    calc (5 / 4 : ℝ) * ((4 / 5 : ℝ) ^ m * ((4 / 5) * ‖orthantSlice g x y (circleMap 0 (5 / 4) θ)‖))
        ≤ (5 / 4) * (1 * ((4 / 5) * M)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul h_pow (mul_le_mul_of_nonneg_left hg_le (by norm_num))
            (by positivity) zero_le_one
      _ = M := by ring
  · refine continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul ?_))
    let γ : (Fin n → ℝ) → (Fin n → ℂ) := fun x i => (x i : ℂ) + circleMap 0 (5 / 4) θ * (y i : ℂ)
    have hγ_cont : Continuous γ :=
      continuous_pi fun i =>
        (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const
    refine hdata.2.2.comp hγ_cont.continuousOn fun x hx => ?_
    have hx' : ‖x‖ ≤ ρ / 8 := by simpa [Metric.mem_closedBall] using hx
    have hθ : ‖circleMap (0 : ℂ) (5 / 4) θ‖ < 3 / 2 := by
      rw [norm_circleMap_zero]; norm_num
    exact orthantSlice_mem_wedge hρ hx' hy_pos hy hθ

lemma iteratedDeriv_comp_ofReal {U : Set ℂ} (hU : IsOpen U) :
    ∀ (m : ℕ) {F : ℂ → ℂ} (_hF : AnalyticOnNhd ℂ F U) {t : ℝ} (_ht : (t : ℂ) ∈ U),
      iteratedDeriv m (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv m F (t : ℂ)
  | 0, _, _, _, _ => rfl
  | m + 1, F, hF, t, ht => by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have h_ev : deriv (fun s : ℝ => F (s : ℂ)) =ᶠ[nhds t] fun s : ℝ => deriv F (s : ℂ) := by
      have h_pre : (fun s : ℝ => (s : ℂ)) ⁻¹' U ∈ nhds t :=
        (hU.preimage Complex.continuous_ofReal).mem_nhds ht
      filter_upwards [h_pre] with s hs
      exact ((hF (s : ℂ) hs).differentiableAt.hasDerivAt.comp_ofReal).deriv
    rw [h_ev.iteratedDeriv_eq]
    exact iteratedDeriv_comp_ofReal hU m hF.deriv ht

lemma hasDerivAt_iteratedFDeriv_shift {n : ℕ} {h : (Fin n → ℝ) → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (u y : Fin n → ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ k h (u - s • y) (fun _ => -y))
      (iteratedFDeriv ℝ (k + 1) h (u - t • y) (fun _ => -y)) t := by
  let γ : ℝ → (Fin n → ℝ) := fun s => u - s • y
  have hγ : HasDerivAt γ (-y) t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_sub u
  have hk_lt : ((k : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k)
  have hM : DifferentiableAt ℝ (iteratedFDeriv ℝ k h) (γ t) :=
    (hh.contDiffAt).differentiableAt_iteratedFDeriv hk_lt
  have h_comp : HasDerivAt (fun s => iteratedFDeriv ℝ k h (γ s))
      (fderiv ℝ (iteratedFDeriv ℝ k h) (γ t) (-y)) t :=
    hM.hasFDerivAt.comp_hasDerivAt t hγ
  let ev : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin n → ℝ) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin n → ℝ) ℝ (fun _ => -y)
  have h_ev := ev.hasFDerivAt.comp_hasDerivAt t h_comp
  have h_eq : ev (fderiv ℝ (iteratedFDeriv ℝ k h) (γ t) (-y)) =
      iteratedFDeriv ℝ (k + 1) h (γ t) (fun _ => -y) := by
    rw [iteratedFDeriv_succ_apply_left]
    rfl
  rwa [h_eq] at h_ev

noncomputable def gRealCut {n : ℕ} (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (u : Fin n → ℝ) : ℂ :=
  open Classical in
  if u ∈ Metric.closedBall 0 (ρ / 4) then g (fun i => (u i : ℂ)) else 0

lemma gRealCut_aestronglyMeasurable_and_bound (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) :
    AEStronglyMeasurable (gRealCut g ρ) volume ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Fin n → ℝ, ‖gRealCut g ρ u‖ ≤ M := by
  classical
  let emb : (Fin n → ℝ) → (Fin n → ℂ) := fun u i => (u i : ℂ)
  have hemb_cont : Continuous emb :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  have h_sub : emb '' Metric.closedBall 0 (ρ / 4) ⊆ Metric.ball 0 ρ ∩
      (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
        {w : Fin n → ℂ | ∀ i, (w i).im = 0}) := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, Or.inr fun i => Complex.ofReal_im (u i)⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    rw [Metric.mem_ball, dist_zero_right]
    refine (pi_norm_lt_iff hρ).mpr fun i => ?_
    have hui : |u i| ≤ ρ / 4 := (norm_le_pi_norm u i).trans hu
    simpa [emb, Complex.norm_real] using lt_of_le_of_lt hui (by linarith)
  have h_cont : ContinuousOn (g ∘ emb) (Metric.closedBall 0 (ρ / 4)) :=
    hdata.2.2.comp hemb_cont.continuousOn (Set.mapsTo_image emb _ |>.mono subset_rfl h_sub)
  have h_meas_set : MeasurableSet (Metric.closedBall (0 : Fin n → ℝ) (ρ / 4)) :=
    Metric.isClosed_closedBall.measurableSet
  have h_meas : AEStronglyMeasurable (gRealCut g ρ) volume := by
    have heq : gRealCut g ρ = Set.piecewise (Metric.closedBall 0 (ρ / 4)) (g ∘ emb) 0 := by
      ext u
      by_cases hu : u ∈ Metric.closedBall 0 (ρ / 4)
      · rw [Set.piecewise_eq_of_mem _ _ _ hu]
        simp [gRealCut, hu, emb]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hu]
        simp [gRealCut, hu]
    rw [heq]
    exact AEStronglyMeasurable.piecewise h_meas_set
      (h_cont.aestronglyMeasurable h_meas_set) aestronglyMeasurable_zero
  rcases orthant_eowData_bounded_on_compact n g ρ hdata _
      ((isCompact_closedBall 0 (ρ / 4)).image hemb_cont) h_sub with ⟨M₀, hM₀⟩
  refine ⟨h_meas, max M₀ 0, le_max_right _ _, fun u => ?_⟩
  by_cases hu : u ∈ Metric.closedBall 0 (ρ / 4)
  · simp only [gRealCut, if_pos hu]
    exact (hM₀ (emb u) ⟨u, hu, rfl⟩).trans (le_max_left _ _)
  · simp only [gRealCut, if_neg hu, norm_zero]
    exact le_max_right _ _

lemma iteratedDeriv_integral_gRealCut_shift (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) (y : Fin n → ℝ) (b : ContDiffBump (0 : Fin n → ℝ)) :
    ∀ (m : ℕ) {t : ℝ} (_ht : t ∈ Set.Ioo (-1 / 8 : ℝ) (1 / 8)),
      iteratedDeriv m (fun s : ℝ => ∫ u, gRealCut g ρ u * ((b (u - s • y) : ℝ) : ℂ)) t =
        ∫ u, gRealCut g ρ u * ((iteratedFDeriv ℝ m b (u - t • y) (fun _ => -y) : ℝ) : ℂ) := by
  obtain ⟨hg_meas, M, hM_nn, hM_bd⟩ := gRealCut_aestronglyMeasurable_and_bound n g hρ hdata
  have hb_cd : ContDiff ℝ (⊤ : ℕ∞) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  have hK_meas : MeasurableSet (Metric.closedBall (0 : Fin n → ℝ) (ρ / 4)) :=
    Metric.isClosed_closedBall.measurableSet
  have hK_fin : volume (Metric.closedBall (0 : Fin n → ℝ) (ρ / 4)) < ⊤ := measure_closedBall_lt_top
  have h_step : ∀ (k : ℕ) {t : ℝ}, t ∈ Set.Ioo (-1 / 8 : ℝ) (1 / 8) →
      HasDerivAt
        (fun s : ℝ =>
          ∫ u, gRealCut g ρ u * ((iteratedFDeriv ℝ k b (u - s • y) (fun _ => -y) : ℝ) : ℂ))
        (∫ u, gRealCut g ρ u *
          ((iteratedFDeriv ℝ (k + 1) b (u - t • y) (fun _ => -y) : ℝ) : ℂ)) t := by
    intro k t ht
    let F : ℝ → (Fin n → ℝ) → ℂ := fun s u =>
      gRealCut g ρ u * ((iteratedFDeriv ℝ k b (u - s • y) (fun _ => -y) : ℝ) : ℂ)
    let F' : ℝ → (Fin n → ℝ) → ℂ := fun s u =>
      gRealCut g ρ u * ((iteratedFDeriv ℝ (k + 1) b (u - s • y) (fun _ => -y) : ℝ) : ℂ)
    let K_u : Set (Fin n → ℝ) := Metric.closedBall 0 (ρ / 4)
    have hK_comp : IsCompact (Set.Icc (-1 / 8 : ℝ) (1 / 8) ×ˢ K_u) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    let d_norm : ℝ × (Fin n → ℝ) → ℝ :=
      fun p => ‖iteratedFDeriv ℝ (k + 1) b (p.2 - p.1 • y) (fun _ => -y)‖
    have hd_cont : Continuous d_norm := by
      have h1 : Continuous (fun p : ℝ × (Fin n → ℝ) => p.2 - p.1 • y) :=
        continuous_snd.sub (continuous_fst.smul continuous_const)
      have h2 : Continuous (iteratedFDeriv ℝ (k + 1) (b : (Fin n → ℝ) → ℝ)) :=
        hb_cd.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : ((k + 1 : ℕ) : ℕ∞) ≤ ⊤))
      let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin (k + 1) => Fin n → ℝ) ℝ (fun _ => -y)
      exact continuous_norm.comp (ev.continuous.comp (h2.comp h1))
    rcases (hK_comp.image hd_cont).isBounded.exists_norm_le with ⟨C_k, hC_k⟩
    let C : ℝ := max C_k 0
    let bound : (Fin n → ℝ) → ℝ := Set.indicator K_u (fun _ => M * C)
    have h_bound_int : Integrable bound volume :=
      (integrableOn_const (hs := hK_fin.ne) (hC := ENNReal.coe_ne_top)).integrable_indicator hK_meas
    have h_meas_all : ∀ (j : ℕ) (s : ℝ), AEStronglyMeasurable
        (fun u => gRealCut g ρ u * ((iteratedFDeriv ℝ j b (u - s • y) (fun _ => -y) : ℝ) : ℂ))
        volume := by
      intro j s
      have h_cont_j : Continuous
          (fun u : Fin n → ℝ => ((iteratedFDeriv ℝ j b (u - s • y) (fun _ => -y) : ℝ) : ℂ)) := by
        let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Fin n → ℝ) ℝ (fun _ => -y)
        exact Complex.continuous_ofReal.comp
          (ev.continuous.comp
            ((hb_cd.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))).comp
              (continuous_id.sub continuous_const)))
      exact hg_meas.mul h_cont_j.aestronglyMeasurable
    have hF_int : Integrable (F t) volume := by
      let d0 : (Fin n → ℝ) → ℝ := fun u => ‖iteratedFDeriv ℝ k b (u - t • y) (fun _ => -y)‖
      have hd0_cont : Continuous d0 := by
        let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin n → ℝ) ℝ (fun _ => -y)
        exact continuous_norm.comp (ev.continuous.comp
          ((hb_cd.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤))).comp
            (continuous_id.sub continuous_const)))
      rcases ((isCompact_closedBall (0 : Fin n → ℝ) (ρ / 4)).image
        hd0_cont).isBounded.exists_norm_le with ⟨C₀, hC₀⟩
      let b0 : (Fin n → ℝ) → ℝ := Set.indicator K_u (fun _ => M * max C₀ 0)
      have hb0_int : Integrable b0 volume :=
        (integrableOn_const (hs := hK_fin.ne)
          (hC := ENNReal.coe_ne_top)).integrable_indicator hK_meas
      refine Integrable.mono' hb0_int (h_meas_all k t) (Filter.Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ K_u
      · simp only [F, b0, Set.indicator_of_mem hu, norm_mul, Complex.norm_real]
        exact mul_le_mul (hM_bd u)
          ((le_abs_self _).trans ((hC₀ _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)))
          (norm_nonneg _) hM_nn
      · have hgu : gRealCut g ρ u = 0 := by simp [gRealCut, K_u, hu]
        simp [F, b0, hu, hgu]
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := F') (bound := bound)
      (s := Set.Ioo (-1 / 8 : ℝ) (1 / 8))
      (isOpen_Ioo.mem_nhds ht)
      (Filter.Eventually.of_forall fun s => h_meas_all k s)
      hF_int
      (h_meas_all (k + 1) t)
      (Filter.Eventually.of_forall fun u s hs => by
        by_cases hu : u ∈ K_u
        · change ‖F' s u‖ ≤ bound u
          simp only [F', bound, Set.indicator_of_mem hu, norm_mul, Complex.norm_real]
          have hs_cc : s ∈ Set.Icc (-1 / 8 : ℝ) (1 / 8) := ⟨hs.1.le, hs.2.le⟩
          have hd_le : ‖iteratedFDeriv ℝ (k + 1) b (u - s • y) (fun _ => -y)‖ ≤ C :=
            (le_abs_self _).trans ((hC_k _ ⟨(s, u), ⟨hs_cc, hu⟩, rfl⟩).trans (le_max_left _ _))
          exact mul_le_mul (hM_bd u) hd_le (norm_nonneg _) hM_nn
        · change ‖F' s u‖ ≤ bound u
          have hgu : gRealCut g ρ u = 0 := by simp [gRealCut, K_u, hu]
          simp [F', bound, hu, hgu])
      h_bound_int
      (Filter.Eventually.of_forall fun u s _ => by
        have hd1 := hasDerivAt_iteratedFDeriv_shift hb_cd u y k s
        exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hd1).const_mul (gRealCut g ρ u))).2
  intro m
  induction m with
  | zero =>
    intro t _
    simp [iteratedDeriv_zero]
  | succ m ih =>
    intro t ht
    rw [iteratedDeriv_succ]
    have h_ev : (iteratedDeriv m fun s : ℝ => ∫ u, gRealCut g ρ u * ((b (u - s • y) : ℝ) : ℂ))
        =ᶠ[nhds t]
        fun s : ℝ => ∫ u, gRealCut g ρ u *
          ((iteratedFDeriv ℝ m b (u - s • y) (fun _ => -y) : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact ih hs
    rw [Filter.EventuallyEq.deriv_eq h_ev]
    exact (h_step m ht).deriv

lemma orthantSliceCoeff_shift_identity (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) {y : Fin n → ℝ}
    (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8)
    (b : ContDiffBump (0 : Fin n → ℝ)) (hb : b.rOut ≤ ρ / 16) (m : ℕ) :
    (m.factorial : ℂ) * ∫ x, orthantSliceCoeff g x y m * ((b x : ℝ) : ℂ) =
      (-1 : ℂ) ^ m * ∫ u, gRealCut g ρ u * ((iteratedFDeriv ℝ m b u (fun _ => y) : ℝ) : ℂ) := by
  classical
  obtain ⟨M_y, hMy_nn, hMy_bd⟩ := orthant_eowData_fixed_y_bound n g hρ hdata hy_pos hy
  have hb_cd : ContDiff ℝ (⊤ : ℕ∞) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  have hb_int : Integrable (fun x : Fin n → ℝ => ((b x : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hb_cd.continuous).integrable_of_hasCompactSupport
      (b.hasCompactSupport.comp_left Complex.ofReal_zero)
  have hb_supp : ∀ x : Fin n → ℝ, b x ≠ 0 → x ∈ Metric.closedBall 0 (ρ / 8) := by
    intro x hx
    have hx_ball : x ∈ Metric.ball 0 b.rOut := by
      have : x ∈ Function.support b := hx
      rwa [b.support_eq] at this
    rw [Metric.mem_ball, dist_zero_right] at hx_ball
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hK8_meas : MeasurableSet (Metric.closedBall (0 : Fin n → ℝ) (ρ / 8)) :=
    Metric.isClosed_closedBall.measurableSet
  have h_coeff_meas : ∀ k : ℕ,
      AEStronglyMeasurable (fun x => orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ)) volume := by
    intro k
    have h_eq : (fun x => orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ)) =
        Set.piecewise (Metric.closedBall 0 (ρ / 8))
          (fun x => orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ)) 0 := by
      ext x
      by_cases hx : x ∈ Metric.closedBall 0 (ρ / 8)
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        have hbx : b x = 0 := by
          by_contra hne
          exact hx (hb_supp x hne)
        simp [hbx]
    rw [h_eq]
    refine AEStronglyMeasurable.piecewise hK8_meas ?_ aestronglyMeasurable_zero
    exact ((continuousOn_orthantSliceCoeff n g hρ hdata hy_pos hy k).mul
      (Complex.continuous_ofReal.comp hb_cd.continuous).continuousOn).aestronglyMeasurable hK8_meas
  have h_coeff_bd : ∀ (k : ℕ) (x : Fin n → ℝ),
      ‖orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ)‖ ≤ M_y * ‖((b x : ℝ) : ℂ)‖ := by
    intro k x
    by_cases hbx : b x = 0
    · simp [hbx]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact norm_orthantSliceCoeff_le hMy_nn
        (fun ζ hζ => hMy_bd x (hb_supp x hbx) ζ (Metric.sphere_subset_closedBall hζ)) k
  let B : ℕ → ℂ := fun k => ∫ x, orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ)
  let Q : FormalMultilinearSeries ℂ ℂ ℂ :=
    fun k => B k • ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ
  have hQ_rad : ((1 / 2 : NNReal) : ENNReal) ≤ Q.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound Q (M_y * ∫ x, ‖((b x : ℝ) : ℂ)‖) fun k => ?_
    have hBk : ‖B k‖ ≤ M_y * ∫ x, ‖((b x : ℝ) : ℂ)‖ := by
      refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
      rw [← MeasureTheory.integral_const_mul]
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (hb_int.norm.const_mul M_y) (Filter.Eventually.of_forall (h_coeff_bd k))
    have hmk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ ≤ 1 := by
      cases k with
      | zero => rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero]; exact norm_one.le
      | succ _ => exact ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le
    have h_normQ : ‖Q k‖ ≤ M_y * ∫ x, ‖((b x : ℝ) : ℂ)‖ := by
      dsimp [Q]
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hmk).trans hBk
    have h_pow : ((1 / 2 : NNReal) : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (mul_le_of_le_one_right (norm_nonneg _) h_pow).trans h_normQ
  let L : ℂ → ℂ := fun w => ∫ x, orthantSlice g x y w * ((b x : ℝ) : ℂ)
  have hL_series : HasFPowerSeriesOnBall L Q 0 (1 / 2 : NNReal) := by
    refine ⟨hQ_rad, by norm_num, fun {w} hw => ?_⟩
    rw [zero_add]
    have hw_lt : ‖w‖ < 1 / 2 := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe] at hw
      change ‖w‖ < ((1 / 2 : NNReal) : ℝ) at hw
      have hc : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
      rwa [hc] at hw
    have hQ_eq : (fun k => Q k (fun _ => w)) =
        fun k => ∫ x, (orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ)) * w ^ k := by
      ext k
      dsimp [Q, B]
      rw [_root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
        List.prod_ofFn, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        ← MeasureTheory.integral_mul_const]
    rw [hQ_eq]
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun k x => M_y * ‖((b x : ℝ) : ℂ)‖ * (1 / 2 : ℝ) ^ k)
      (fun k => (h_coeff_meas k).mul_const (w ^ k))
      (fun k => Filter.Eventually.of_forall fun x => ?_)
      ?_ ?_
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [norm_mul, norm_pow]
      exact mul_le_mul (h_coeff_bd k x) (pow_le_pow_left₀ (norm_nonneg _) hw_lt.le k)
        (by positivity) (by positivity)
    · refine Filter.Eventually.of_forall fun x => ?_
      exact ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _).hasSum.summable
    · have h_tsum : (fun x : Fin n → ℝ => ∑' k : ℕ, M_y * ‖((b x : ℝ) : ℂ)‖ * (1 / 2 : ℝ) ^ k) =
          fun x => (M_y * 2) * ‖((b x : ℝ) : ℂ)‖ := by
        ext x
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        ring
      rw [h_tsum]
      exact hb_int.norm.const_mul (M_y * 2)
    · by_cases hbx : b x = 0
      · simp [hbx, hasSum_zero]
      · have hx_b : ‖x‖ ≤ ρ / 8 := by simpa [Metric.mem_closedBall] using hb_supp x hbx
        have hP := orthantSlice_hasFPowerSeriesOnBall n g hρ hdata hx_b hy_pos hy
        have hw54 : w ∈ Metric.eball (0 : ℂ) (5 / 4 : NNReal) := by
          rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
          change ‖w‖ < ((5 / 4 : NNReal) : ℝ)
          have hc : ((5 / 4 : NNReal) : ℝ) = 5 / 4 := by norm_num
          rw [hc]
          exact lt_trans hw_lt (by norm_num)
        have h_sum_x := hP.hasSum hw54
        rw [zero_add] at h_sum_x
        have h_term : (fun k => (cauchyPowerSeries (orthantSlice g x y) 0 (5 / 4) k) (fun _ => w)) =
            fun k => orthantSliceCoeff g x y k * w ^ k := by
          ext k
          have hw' : (fun _ : Fin k => w) = fun _ => w • (1 : ℂ) := by ext; simp
          rw [hw', ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul, mul_comm]
          rfl
        rw [h_term] at h_sum_x
        have h_mul := h_sum_x.mul_right ((b x : ℝ) : ℂ)
        simpa [mul_right_comm] using h_mul
  have h_fact := hL_series.factorial_smul (1 : ℂ) m
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul,
    ← Nat.cast_smul_eq_nsmul ℂ] at h_fact
  have hQ1 : Q m (fun _ => 1) = B m := by
    dsimp [Q]
    rw [_root_.smul_apply, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.prod_ofFn, Finset.prod_const_one, smul_eq_mul, mul_one]
  rw [hQ1, smul_eq_mul] at h_fact
  have hL_an : AnalyticOnNhd ℂ L (Metric.ball 0 (1 / 2)) := by
    intro z hz
    have hz_eb : z ∈ Metric.eball (0 : ℂ) (1 / 2 : NNReal) := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      change ‖z‖ < ((1 / 2 : NNReal) : ℝ)
      have hc : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
      rw [hc]
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hL_series.analyticAt_of_mem hz_eb
  have h_real_der := iteratedDeriv_comp_ofReal (U := Metric.ball (0 : ℂ) (1 / 2))
    Metric.isOpen_ball m hL_an (t := 0) (by simp)
  simp only [Complex.ofReal_zero] at h_real_der
  have h_ev_shift : (fun s : ℝ => L (s : ℂ)) =ᶠ[nhds 0]
      fun s : ℝ => ∫ u, gRealCut g ρ u * ((b (u - s • y) : ℝ) : ℂ) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 / 8) (1 / 8) by norm_num)]
      with s hs
    dsimp [L]
    have h_congr : (fun x : Fin n → ℝ => orthantSlice g x y (s : ℂ) * ((b x : ℝ) : ℂ)) =
        fun x => gRealCut g ρ (x + s • y) * ((b ((x + s • y) - s • y) : ℝ) : ℂ) := by
      ext x
      rw [add_sub_cancel_right]
      by_cases hbx : b x = 0
      · simp [hbx]
      · have hx_b : x ∈ Metric.ball 0 b.rOut := by
          have : x ∈ Function.support b := hbx
          rwa [b.support_eq] at this
        rw [Metric.mem_ball, dist_zero_right] at hx_b
        have h_in : x + s • y ∈ Metric.closedBall 0 (ρ / 4) := by
          rw [Metric.mem_closedBall, dist_zero_right]
          have hs_abs : |s| < 1 / 8 := abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩
          calc ‖x + s • y‖ ≤ ‖x‖ + |s| * ‖y‖ := by
                rw [← Real.norm_eq_abs, ← norm_smul]
                exact norm_add_le _ _
            _ ≤ ρ / 16 + (1 / 8) * (3 * ρ / 8) := by
                nlinarith [norm_nonneg y]
            _ ≤ ρ / 4 := by linarith
        simp only [gRealCut, if_pos h_in, orthantSlice]
        congr 2
        ext i
        simp [Pi.add_apply, Pi.smul_apply]
    rw [h_congr]
    exact MeasureTheory.integral_add_right_eq_self
      (fun u => gRealCut g ρ u * ((b (u - s • y) : ℝ) : ℂ)) (s • y)
  have h_der_eq : iteratedDeriv m L 0 =
      iteratedDeriv m (fun s : ℝ => ∫ u, gRealCut g ρ u * ((b (u - s • y) : ℝ) : ℂ)) 0 := by
    rw [← h_real_der, h_ev_shift.iteratedDeriv_eq]
  rw [h_fact, h_der_eq, iteratedDeriv_integral_gRealCut_shift n g hρ hdata y b m (by norm_num)]
  simp only [zero_smul, sub_zero]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  have h_neg : (fun _ : Fin m => -y) = fun _ : Fin m => (-1 : ℝ) • y := by ext; simp
  rw [h_neg, ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

lemma continuousAt_zero_eq_zero_of_bump_integral_zero {n : ℕ} {H : (Fin n → ℝ) → ℂ}
    {r_max : ℝ} (hr_max : 0 < r_max) (hH_cont : ContinuousOn H (Metric.closedBall 0 r_max))
    (h_int : ∀ (b : ContDiffBump (0 : Fin n → ℝ)), b.rOut ≤ r_max →
      ∫ x, H x * ((b x : ℝ) : ℂ) = 0) :
    H 0 = 0 := by
  classical
  by_contra hne
  have h_pos : 0 < ‖H 0‖ := norm_pos_iff.mpr hne
  have h_c0 : ContinuousWithinAt H (Metric.closedBall 0 r_max) 0 :=
    hH_cont 0 (Metric.mem_closedBall_self hr_max.le)
  rcases Metric.continuousWithinAt_iff.mp h_c0 (‖H 0‖ / 2) (half_pos h_pos) with ⟨δ₁, hδ₁, h_close⟩
  let δ : ℝ := min (r_max / 2) (δ₁ / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos hr_max) (half_pos hδ₁)
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ_pos, half_lt_self hδ_pos⟩
  have hb_le : b.rOut ≤ r_max := (min_le_left _ _).trans (half_le_self hr_max.le)
  have hb_cd : ContDiff ℝ (⊤ : ℕ∞) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  have hb_int_real : Integrable (b : (Fin n → ℝ) → ℝ) volume :=
    hb_cd.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hK_meas : MeasurableSet (Metric.closedBall (0 : Fin n → ℝ) r_max) :=
    Metric.isClosed_closedBall.measurableSet
  have hH_b_int : Integrable (fun x => H x * ((b x : ℝ) : ℂ)) volume := by
    have heq : (fun x => H x * ((b x : ℝ) : ℂ)) =
        Set.piecewise (Metric.closedBall 0 r_max) (fun x => H x * ((b x : ℝ) : ℂ)) 0 := by
      ext x
      by_cases hx : x ∈ Metric.closedBall 0 r_max
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        have hbx : b x = 0 := by
          by_contra hbn
          have hxb : x ∈ Metric.ball 0 b.rOut := by
            have : x ∈ Function.support b := hbn
            rwa [b.support_eq] at this
          exact hx (Metric.ball_subset_closedBall (Metric.ball_subset_ball hb_le hxb))
        simp [hbx]
    rw [heq]
    have hcomp : IsCompact (Metric.closedBall (0 : Fin n → ℝ) r_max) := isCompact_closedBall _ _
    rcases (hcomp.image_of_continuousOn hH_cont).isBounded.exists_norm_le with ⟨M, hM⟩
    refine Integrable.mono' (hb_int_real.const_mul (max M 0))
      (AEStronglyMeasurable.piecewise hK_meas
        ((hH_cont.mul
          (Complex.continuous_ofReal.comp hb_cd.continuous).continuousOn).aestronglyMeasurable
          hK_meas) aestronglyMeasurable_zero)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Metric.closedBall 0 r_max
    · rw [Set.piecewise_eq_of_mem _ _ _ hx, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg b.nonneg]
      exact mul_le_mul_of_nonneg_right ((hM _ ⟨x, hx, rfl⟩).trans (le_max_left _ _)) b.nonneg
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      simp only [Pi.zero_apply, norm_zero]
      exact mul_nonneg (le_max_right _ _) b.nonneg
  have hI_pos : 0 < ∫ x, (b x : ℝ) := by
    have h_ball_sub : Metric.ball (0 : Fin n → ℝ) (δ / 2) ⊆ Metric.closedBall 0 b.rIn :=
      Metric.ball_subset_closedBall
    have h_set_le : ∫ x in Metric.ball (0 : Fin n → ℝ) (δ / 2), (b x : ℝ) ≤ ∫ x, (b x : ℝ) :=
      setIntegral_le_integral hb_int_real (Filter.Eventually.of_forall fun _ => b.nonneg)
    have h_one : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) (δ / 2), (b x : ℝ) = 1 :=
      fun x hx => b.one_of_mem_closedBall (h_ball_sub hx)
    have h_eq_vol : ∫ x in Metric.ball (0 : Fin n → ℝ) (δ / 2), (b x : ℝ) =
        (volume (Metric.ball (0 : Fin n → ℝ) (δ / 2))).toReal := by
      rw [setIntegral_congr_fun measurableSet_ball h_one, setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have h_vol_pos : 0 < (volume (Metric.ball (0 : Fin n → ℝ) (δ / 2))).toReal :=
      ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (half_pos hδ_pos)).ne'
        measure_ball_lt_top.ne
    linarith
  have h_zero := h_int b hb_le
  have h_split : H 0 * Complex.ofReal (∫ x, (b x : ℝ)) =
      - ∫ x, (H x - H 0) * ((b x : ℝ) : ℂ) := by
    have h1 : (fun x => (H x - H 0) * ((b x : ℝ) : ℂ)) =
        fun x => H x * ((b x : ℝ) : ℂ) - H 0 * ((b x : ℝ) : ℂ) := by ext x; ring
    have hb_int_c : Integrable (fun x : Fin n → ℝ => ((b x : ℝ) : ℂ)) volume :=
      hb_int_real.ofReal
    have h2 : ∫ x, (H x * ((b x : ℝ) : ℂ) - H 0 * ((b x : ℝ) : ℂ)) =
        (∫ x, H x * ((b x : ℝ) : ℂ)) - ∫ x, H 0 * ((b x : ℝ) : ℂ) :=
      MeasureTheory.integral_sub hH_b_int (hb_int_c.const_mul (H 0))
    have h3 : (∫ x : Fin n → ℝ, ((b x : ℝ) : ℂ)) = Complex.ofReal (∫ x, (b x : ℝ)) :=
      integral_ofReal
    calc H 0 * Complex.ofReal (∫ x, (b x : ℝ))
        = H 0 * ∫ x : Fin n → ℝ, ((b x : ℝ) : ℂ) := by rw [← h3]
      _ = ∫ x, H 0 * ((b x : ℝ) : ℂ) := (MeasureTheory.integral_const_mul _ _).symm
      _ = -((∫ x, H x * ((b x : ℝ) : ℂ)) - ∫ x, H 0 * ((b x : ℝ) : ℂ)) := by
            rw [h_zero, zero_sub, neg_neg]
      _ = - ∫ x, (H x - H 0) * ((b x : ℝ) : ℂ) := by rw [← h2, ← h1]
  have h_lhs_norm : ‖H 0 * Complex.ofReal (∫ x, (b x : ℝ))‖ = ‖H 0‖ * ∫ x, (b x : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hI_pos.le]
  have h_rhs_le : ‖- ∫ x, (H x - H 0) * ((b x : ℝ) : ℂ)‖ ≤ (‖H 0‖ / 2) * ∫ x, (b x : ℝ) := by
    rw [norm_neg]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hb_int_real.const_mul (‖H 0‖ / 2)) (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    by_cases hbx : b x = 0
    · simp [hbx]
    · have hxb : x ∈ Metric.ball 0 δ := by
        have : x ∈ Function.support b := hbx
        rwa [b.support_eq] at this
      have hx_rmax : x ∈ Metric.closedBall 0 r_max :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball hb_le hxb)
      have hx_δ₁ : dist x 0 < δ₁ :=
        (Metric.mem_ball.mp hxb).trans (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ₁))
      have h_le := (h_close hx_rmax hx_δ₁).le
      rw [dist_eq_norm] at h_le
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg b.nonneg]
      exact mul_le_mul_of_nonneg_right h_le b.nonneg
  rw [h_split] at h_lhs_norm
  nlinarith

noncomputable def orthantMonomial (n k : ℕ) (α : Fin k → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin n → ℂ)) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
    (fun m => ContinuousLinearMap.proj (R := ℂ) (α m))

lemma orthantMonomial_diag (n k : ℕ) (α : Fin k → Fin n) (w : Fin n → ℂ) :
    orthantMonomial n k α (fun _ => w) = ∏ m : Fin k, w (α m) := by
  dsimp [orthantMonomial]
  rw [List.prod_ofFn]

lemma orthantMonomial_norm_le (n k : ℕ) (α : Fin k → Fin n) :
    ‖orthantMonomial n k α‖ ≤ 1 := by
  dsimp [orthantMonomial]
  have h_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ)
    (fun m => ContinuousLinearMap.proj (R := ℂ) (ι := Fin n) (φ := fun _ => ℂ) (α m))
  have h_mk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ ≤ 1 := by
    cases k with
    | zero => rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero]; exact norm_one.le
    | succ _ => exact ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le
  have h_prod : ∏ m : Fin k,
      ‖ContinuousLinearMap.proj (R := ℂ) (ι := Fin n) (φ := fun _ => ℂ) (α m)‖ ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun m _ => ?_
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      simpa using norm_le_pi_norm w (α m)
  calc ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap _‖
      ≤ ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ * ∏ m : Fin k, ‖_‖ := h_le
    _ ≤ 1 * 1 := mul_le_mul h_mk h_prod (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

noncomputable def orthantYStep (n : ℕ) (ρ : ℝ) (m : ℕ) (α : Fin m → Fin n)
    (S : Finset (Fin m)) : Fin n → ℝ :=
  (fun _ => ρ / 4) + ∑ k ∈ S, (ρ / (8 * (m : ℝ))) • Pi.single (α k) (1 : ℝ)

lemma orthantYStep_mem_box {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {m : ℕ} (hm : 0 < m)
    (α : Fin m → Fin n) (S : Finset (Fin m)) :
    orthantYStep n ρ m α S ∈ orthantBox n ρ := by
  intro i
  change ρ / 8 ≤ ρ / 4 + (∑ k ∈ S, (ρ / (8 * (m : ℝ))) •
    (Pi.single (α k) (1 : ℝ) : Fin n → ℝ)) i ∧
    ρ / 4 + (∑ k ∈ S, (ρ / (8 * (m : ℝ))) •
      (Pi.single (α k) (1 : ℝ) : Fin n → ℝ)) i ≤ 3 * ρ / 8
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h_single_01 : ∀ k : Fin m,
      0 ≤ (Pi.single (α k) (1 : ℝ) : Fin n → ℝ) i ∧
        (Pi.single (α k) (1 : ℝ) : Fin n → ℝ) i ≤ 1 := by
    intro k
    by_cases h : i = α k
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have h_nonneg : 0 ≤ ∑ k ∈ S, (ρ / (8 * (m : ℝ))) *
      (Pi.single (α k) (1 : ℝ) : Fin n → ℝ) i :=
    Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (h_single_01 k).1
  have h_upper : (∑ k ∈ S, (ρ / (8 * (m : ℝ))) *
      (Pi.single (α k) (1 : ℝ) : Fin n → ℝ) i) ≤ ρ / 8 := by
    calc (∑ k ∈ S, (ρ / (8 * (m : ℝ))) * (Pi.single (α k) (1 : ℝ) : Fin n → ℝ) i)
        ≤ ∑ _k : Fin m, (ρ / (8 * (m : ℝ))) := by
          refine (Finset.sum_le_univ_sum_of_nonneg fun k =>
            mul_nonneg (by positivity) (h_single_01 k).1).trans ?_
          refine Finset.sum_le_sum fun k _ =>
            mul_le_of_le_one_right (by positivity) (h_single_01 k).2
      _ = (m : ℝ) * (ρ / (8 * (m : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ρ / 8 := by field_simp [hm_pos.ne']
  exact ⟨by linarith, by linarith⟩

noncomputable def orthantBasisCoeff (n : ℕ) (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (x : Fin n → ℝ) :
    ∀ m : ℕ, (Fin m → Fin n) → ℂ
  | 0, _ => orthantSliceCoeff g x (fun _ => ρ / 4) 0
  | m + 1, α =>
    (((m + 1).factorial : ℂ) * ((ρ / (8 * ((m + 1 : ℕ) : ℝ)) : ℝ) : ℂ) ^ (m + 1))⁻¹ *
      ∑ S : Finset (Fin (m + 1)),
        (-1 : ℂ) ^ ((m + 1) - S.card) *
          orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1)

lemma orthantSliceCoeff_zero_eq {n : ℕ} (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) {x y : Fin n → ℝ}
    (hx : ‖x‖ ≤ ρ / 8) (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8) :
    orthantSliceCoeff g x y 0 = g (fun i => (x i : ℂ)) := by
  have hP := orthantSlice_hasFPowerSeriesOnBall n g hρ hdata hx hy_pos hy
  have h_fact := hP.factorial_smul (1 : ℂ) 0
  simp only [Nat.factorial_zero, one_smul, iteratedFDeriv_zero_apply] at h_fact
  exact h_fact.trans (by simp [orthantSlice])

lemma gRealCut_ifd_integrable (n k : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) (b : ContDiffBump (0 : Fin n → ℝ))
    (v : Fin k → (Fin n → ℝ)) :
    Integrable (fun u => gRealCut g ρ u * ((iteratedFDeriv ℝ k b u v : ℝ) : ℂ)) volume := by
  have hb_cd : ContDiff ℝ (⊤ : ℕ∞) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  have hK4_meas : MeasurableSet (Metric.closedBall (0 : Fin n → ℝ) (ρ / 4)) :=
    Metric.isClosed_closedBall.measurableSet
  have hK4_fin : volume (Metric.closedBall (0 : Fin n → ℝ) (ρ / 4)) < ⊤ :=
    measure_closedBall_lt_top
  obtain ⟨hg_meas, M_cut, hMc_nn, hM_cut⟩ := gRealCut_aestronglyMeasurable_and_bound n g hρ hdata
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin n → ℝ) ℝ v
  have hc : Continuous (fun u : Fin n → ℝ => iteratedFDeriv ℝ k b u v) :=
    ev.continuous.comp
      (hb_cd.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : (k : ℕ∞) ≤ ⊤)))
  rcases ((isCompact_closedBall (0 : Fin n → ℝ) (ρ / 4)).image
    (continuous_norm.comp hc)).isBounded.exists_norm_le with ⟨C_v, hC_v⟩
  let bv : (Fin n → ℝ) → ℝ :=
    Set.indicator (Metric.closedBall 0 (ρ / 4)) (fun _ => M_cut * max C_v 0)
  have hbv_int : Integrable bv volume :=
    (integrableOn_const (hs := hK4_fin.ne) (hC := ENNReal.coe_ne_top)).integrable_indicator hK4_meas
  refine Integrable.mono' hbv_int
    (hg_meas.mul (Complex.continuous_ofReal.comp hc).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ Metric.closedBall (0 : Fin n → ℝ) (ρ / 4)
  · simp only [bv, Set.indicator_of_mem hu, norm_mul, Complex.norm_real]
    exact mul_le_mul (hM_cut u)
      ((le_abs_self _).trans ((hC_v _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)))
      (norm_nonneg _) hMc_nn
  · have hgu : gRealCut g ρ u = 0 := by simp [gRealCut, hu]
    simp [bv, hu, hgu]

lemma orthantSliceCoeff_bump_integrable (n k : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) (b : ContDiffBump (0 : Fin n → ℝ)) (hb : b.rOut ≤ ρ / 16)
    {z : Fin n → ℝ} (hz_pos : z ∈ PosOrthant n) (hz_n : ‖z‖ ≤ 3 * ρ / 8) :
    Integrable (fun x => orthantSliceCoeff g x z k * ((b x : ℝ) : ℂ)) volume := by
  classical
  have hb_cd : ContDiff ℝ (⊤ : ℕ∞) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  have hK8_meas : MeasurableSet (Metric.closedBall (0 : Fin n → ℝ) (ρ / 8)) :=
    Metric.isClosed_closedBall.measurableSet
  obtain ⟨M_z, hMz_nn, hMz⟩ := orthant_eowData_fixed_y_bound n g hρ hdata hz_pos hz_n
  have hb_i : Integrable (fun x : Fin n → ℝ => ((b x : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp hb_cd.continuous).integrable_of_hasCompactSupport
      (b.hasCompactSupport.comp_left Complex.ofReal_zero)
  have h_meas :
      AEStronglyMeasurable (fun x => orthantSliceCoeff g x z k * ((b x : ℝ) : ℂ)) volume := by
    have heq : (fun x => orthantSliceCoeff g x z k * ((b x : ℝ) : ℂ)) =
        Set.piecewise (Metric.closedBall 0 (ρ / 8))
          (fun x => orthantSliceCoeff g x z k * ((b x : ℝ) : ℂ)) 0 := by
      ext x
      by_cases hx : x ∈ Metric.closedBall 0 (ρ / 8)
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
        have hbx : b x = 0 := by
          by_contra hbn
          have hxb : x ∈ Metric.ball 0 b.rOut := by
            have : x ∈ Function.support b := hbn
            rwa [b.support_eq] at this
          exact hx (Metric.ball_subset_closedBall
            (Metric.ball_subset_ball (hb.trans (by linarith)) hxb))
        simp [hbx]
    rw [heq]
    exact AEStronglyMeasurable.piecewise hK8_meas
      (((continuousOn_orthantSliceCoeff n g hρ hdata hz_pos hz_n k).mul
        (Complex.continuous_ofReal.comp hb_cd.continuous).continuousOn).aestronglyMeasurable
        hK8_meas) aestronglyMeasurable_zero
  refine Integrable.mono' (hb_i.norm.const_mul M_z) h_meas (Filter.Eventually.of_forall fun x => ?_)
  by_cases hbx : b x = 0
  · simp [hbx]
  · have hxb : x ∈ Metric.closedBall 0 (ρ / 8) := by
      have : x ∈ Function.support b := hbx
      rw [b.support_eq] at this
      exact Metric.ball_subset_closedBall
        (Metric.ball_subset_ball (hb.trans (by linarith)) this)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_orthantSliceCoeff_le hMz_nn
        (fun ζ hζ => hMz x hxb ζ (Metric.sphere_subset_closedBall hζ)) k) (norm_nonneg _)

lemma orthantBasisCoeff_bump_integrable (n m : ℕ)
    (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) (b : ContDiffBump (0 : Fin n → ℝ)) (hb : b.rOut ≤ ρ / 16)
    (α : Fin (m + 1) → Fin n) :
    Integrable (fun x => orthantBasisCoeff n g ρ x (m + 1) α * ((b x : ℝ) : ℂ)) volume := by
  have hk : 0 < m + 1 := Nat.succ_pos m
  let η : ℝ := ρ / (8 * ((m + 1 : ℕ) : ℝ))
  have h_expand : ∀ x : Fin n → ℝ,
      orthantBasisCoeff n g ρ x (m + 1) α * ((b x : ℝ) : ℂ) =
        (((m + 1).factorial : ℂ) * (η : ℂ) ^ (m + 1))⁻¹ *
          ∑ S : Finset (Fin (m + 1)), (-1 : ℂ) ^ ((m + 1) - S.card) *
            (orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1) *
              ((b x : ℝ) : ℂ)) := by
    intro x
    change ((((m + 1).factorial : ℂ) * (η : ℂ) ^ (m + 1))⁻¹ *
        ∑ S : Finset (Fin (m + 1)), (-1 : ℂ) ^ ((m + 1) - S.card) *
          orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1)) * ((b x : ℝ) : ℂ) = _
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun S _ => mul_assoc _ _ _
  rw [show (fun x => orthantBasisCoeff n g ρ x (m + 1) α * ((b x : ℝ) : ℂ)) = _ from
    funext h_expand]
  refine Integrable.const_mul (MeasureTheory.integrable_finsetSum _ fun S _ => ?_) _
  have hbox := orthantYStep_mem_box hρ hk α S
  exact (orthantSliceCoeff_bump_integrable n (m + 1) g hρ hdata b hb
    (orthantBox_subset_posOrthant n hρ hbox) (orthantBox_norm_le hρ hbox)).const_mul _

lemma integral_orthantBasisCoeff_mul_bump (n m : ℕ)
    (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) (b : ContDiffBump (0 : Fin n → ℝ)) (hb : b.rOut ≤ ρ / 16)
    (α : Fin (m + 1) → Fin n) :
    (((m + 1).factorial : ℂ) ^ 2) *
        ∫ x, orthantBasisCoeff n g ρ x (m + 1) α * ((b x : ℝ) : ℂ) =
      (-1 : ℂ) ^ (m + 1) *
        ∫ u, gRealCut g ρ u *
          ((∑ σ : Equiv.Perm (Fin (m + 1)),
            iteratedFDeriv ℝ (m + 1) b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ) := by
  have hk : 0 < m + 1 := Nat.succ_pos m
  let η : ℝ := ρ / (8 * ((m + 1 : ℕ) : ℝ))
  have hη_pos : 0 < η := by dsimp [η]; positivity
  have h_fac_ne : ((m + 1).factorial : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1))
  have hη_ne : ((η : ℂ) ^ (m + 1)) ≠ 0 :=
    pow_ne_zero (m + 1) (Complex.ofReal_ne_zero.mpr hη_pos.ne')
  have h_expand : ∀ x : Fin n → ℝ,
      orthantBasisCoeff n g ρ x (m + 1) α * ((b x : ℝ) : ℂ) =
        (((m + 1).factorial : ℂ) * (η : ℂ) ^ (m + 1))⁻¹ *
          ∑ S : Finset (Fin (m + 1)), (-1 : ℂ) ^ ((m + 1) - S.card) *
            (orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1) *
              ((b x : ℝ) : ℂ)) := by
    intro x
    change ((((m + 1).factorial : ℂ) * (η : ℂ) ^ (m + 1))⁻¹ *
        ∑ S : Finset (Fin (m + 1)), (-1 : ℂ) ^ ((m + 1) - S.card) *
          orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1)) * ((b x : ℝ) : ℂ) = _
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun S _ => mul_assoc _ _ _
  have h_int_congr :
      (∫ x, orthantBasisCoeff n g ρ x (m + 1) α * ((b x : ℝ) : ℂ)) =
        ∫ x, (((m + 1).factorial : ℂ) * (η : ℂ) ^ (m + 1))⁻¹ *
          ∑ S : Finset (Fin (m + 1)), (-1 : ℂ) ^ ((m + 1) - S.card) *
            (orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1) *
              ((b x : ℝ) : ℂ)) :=
    integral_congr_ae (Filter.Eventually.of_forall h_expand)
  rw [h_int_congr, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_finsetSum _ fun S _ => ?_]
  · have h_each : ∀ S : Finset (Fin (m + 1)),
        ∫ x, (-1 : ℂ) ^ ((m + 1) - S.card) *
            (orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1) *
              ((b x : ℝ) : ℂ)) =
        (((m + 1).factorial : ℂ)⁻¹ * (-1 : ℂ) ^ (m + 1)) *
          ∫ u, (-1 : ℂ) ^ ((m + 1) - S.card) *
            (gRealCut g ρ u *
              ((iteratedFDeriv ℝ (m + 1) b u
                (fun _ => orthantYStep n ρ (m + 1) α S) : ℝ) : ℂ)) := by
      intro S
      have hbox := orthantYStep_mem_box hρ hk α S
      have hs := orthantSliceCoeff_shift_identity n g hρ hdata
        (orthantBox_subset_posOrthant n hρ hbox) (orthantBox_norm_le hρ hbox) b hb (m + 1)
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      apply mul_left_cancel₀ h_fac_ne
      calc ((m + 1).factorial : ℂ) *
            ((-1 : ℂ) ^ ((m + 1) - S.card) * ∫ x, orthantSliceCoeff g x _ (m + 1) * _)
          = (-1 : ℂ) ^ ((m + 1) - S.card) *
              (((m + 1).factorial : ℂ) * ∫ x, orthantSliceCoeff g x _ (m + 1) * _) := by ring
        _ = (-1 : ℂ) ^ ((m + 1) - S.card) *
              ((-1 : ℂ) ^ (m + 1) * ∫ u, gRealCut g ρ u * _) := by rw [hs]
        _ = ((m + 1).factorial : ℂ) * ((((m + 1).factorial : ℂ)⁻¹ * (-1 : ℂ) ^ (m + 1)) *
              ((-1 : ℂ) ^ ((m + 1) - S.card) * ∫ u, gRealCut g ρ u * _)) := by
              field_simp [h_fac_ne]
    have h_sum_shift :
        (∑ S : Finset (Fin (m + 1)), ∫ x, (-1 : ℂ) ^ ((m + 1) - S.card) *
            (orthantSliceCoeff g x (orthantYStep n ρ (m + 1) α S) (m + 1) *
              ((b x : ℝ) : ℂ))) =
        (((m + 1).factorial : ℂ)⁻¹ * (-1 : ℂ) ^ (m + 1)) *
          ∫ u, gRealCut g ρ u *
            ((∑ S : Finset (Fin (m + 1)), (-1 : ℝ) ^ ((m + 1) - S.card) *
              iteratedFDeriv ℝ (m + 1) b u
                (fun _ => orthantYStep n ρ (m + 1) α S) : ℝ) : ℂ) := by
      simp_rw [h_each, ← Finset.mul_sum]
      congr 1
      rw [← MeasureTheory.integral_finsetSum _ fun S _ =>
        (gRealCut_ifd_integrable n (m + 1) g hρ hdata b _).const_mul _]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => by ring
    rw [h_sum_shift]
    have h_pol : ∀ u : Fin n → ℝ,
        (∑ S : Finset (Fin (m + 1)), (-1 : ℝ) ^ ((m + 1) - S.card) *
            iteratedFDeriv ℝ (m + 1) b u (fun _ => orthantYStep n ρ (m + 1) α S)) =
        η ^ (m + 1) * ∑ σ : Equiv.Perm (Fin (m + 1)),
          iteratedFDeriv ℝ (m + 1) b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) := by
      intro u
      have hp := multilinear_polarization (m + 1) (iteratedFDeriv ℝ (m + 1) b u)
        (fun _ => ρ / 4) (fun j => η • Pi.single (α j) (1 : ℝ))
      have h_smul : ∀ σ : Equiv.Perm (Fin (m + 1)),
          iteratedFDeriv ℝ (m + 1) b u (fun j => η • Pi.single (α (σ j)) (1 : ℝ)) =
            η ^ (m + 1) *
              iteratedFDeriv ℝ (m + 1) b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) := by
        intro σ
        rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul]
      have h_step_eq : ∀ S : Finset (Fin (m + 1)),
          orthantYStep n ρ (m + 1) α S =
            (fun _ => ρ / 4) + ∑ j ∈ S, η • Pi.single (α j) (1 : ℝ) :=
        fun _ => rfl
      simp_rw [h_step_eq]
      rw [hp]
      simp_rw [h_smul, ← Finset.mul_sum]
    have h_congr_u :
        (∫ u, gRealCut g ρ u *
            ((∑ S : Finset (Fin (m + 1)), (-1 : ℝ) ^ ((m + 1) - S.card) *
              iteratedFDeriv ℝ (m + 1) b u
                (fun _ => orthantYStep n ρ (m + 1) α S) : ℝ) : ℂ)) =
        ((η : ℂ) ^ (m + 1)) *
          ∫ u, gRealCut g ρ u *
            ((∑ σ : Equiv.Perm (Fin (m + 1)),
              iteratedFDeriv ℝ (m + 1) b u
                (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ) := by
      simp_rw [h_pol]
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      dsimp only
      push_cast
      ring
    rw [h_congr_u]
    field_simp [h_fac_ne, hη_ne]
  · have hbox := orthantYStep_mem_box hρ hk α S
    exact (orthantSliceCoeff_bump_integrable n (m + 1) g hρ hdata b hb
      (orthantBox_subset_posOrthant n hρ hbox) (orthantBox_norm_le hρ hbox)).const_mul _

lemma orthantSliceCoeff_eq_sum_orthantBasisCoeff {n : ℕ} (_hn : 0 < n) (g : (Fin n → ℂ) → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hdata : OrthantEOWData n g ρ) {y : Fin n → ℝ}
    (hy_pos : y ∈ PosOrthant n) (hy : ‖y‖ ≤ 3 * ρ / 8) (m : ℕ) :
    orthantSliceCoeff g 0 y m =
      ∑ α : Fin m → Fin n, orthantBasisCoeff n g ρ 0 m α * ∏ k : Fin m, (y (α k) : ℂ) := by
  classical
  cases m with
  | zero =>
    have hy0_pos : (fun _ : Fin n => ρ / 4) ∈ PosOrthant n := fun _ => by positivity
    have hy0_norm : ‖(fun _ : Fin n => ρ / 4)‖ ≤ 3 * ρ / 8 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun _ => ?_
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have h0_le : ‖(0 : Fin n → ℝ)‖ ≤ ρ / 8 := by rw [norm_zero]; positivity
    rw [orthantSliceCoeff_zero_eq g hρ hdata h0_le hy_pos hy]
    simp only [Finset.univ_unique, Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty,
      mul_one, orthantBasisCoeff]
    exact (orthantSliceCoeff_zero_eq g hρ hdata h0_le hy0_pos hy0_norm).symm
  | succ m =>
    let k := m + 1
    have hk : 0 < k := Nat.succ_pos m
    have h_fac_ne : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have h_fac2_ne : ((k.factorial : ℂ) ^ 2) ≠ 0 := pow_ne_zero 2 h_fac_ne
    let H : (Fin n → ℝ) → ℂ := fun x =>
      orthantSliceCoeff g x y k -
        ∑ α : Fin k → Fin n, orthantBasisCoeff n g ρ x k α * ∏ j : Fin k, (y (α j) : ℂ)
    have hH_cont : ContinuousOn H (Metric.closedBall 0 (ρ / 8)) := by
      refine (continuousOn_orthantSliceCoeff n g hρ hdata hy_pos hy k).sub ?_
      refine continuousOn_finsetSum _ fun α _ => ContinuousOn.mul ?_ continuousOn_const
      dsimp [orthantBasisCoeff]
      refine continuousOn_const.mul (continuousOn_finsetSum _ fun S _ => continuousOn_const.mul ?_)
      have hbox := orthantYStep_mem_box hρ hk α S
      exact continuousOn_orthantSliceCoeff n g hρ hdata
        (orthantBox_subset_posOrthant n hρ hbox) (orthantBox_norm_le hρ hbox) k
    have hH_zero := continuousAt_zero_eq_zero_of_bump_integral_zero
      (r_max := ρ / 16) (by positivity)
      (hH_cont.mono (Metric.closedBall_subset_closedBall (by linarith)))
      fun b hb => by
        have h_sum_int : Integrable
            (fun x => (∑ α : Fin k → Fin n,
              orthantBasisCoeff n g ρ x k α * ∏ j : Fin k, (y (α j) : ℂ)) *
                ((b x : ℝ) : ℂ)) volume := by
          have heq : (fun x => (∑ α : Fin k → Fin n,
              orthantBasisCoeff n g ρ x k α * ∏ j : Fin k, (y (α j) : ℂ)) *
                ((b x : ℝ) : ℂ)) =
              fun x => ∑ α : Fin k → Fin n, (∏ j : Fin k, (y (α j) : ℂ)) *
                (orthantBasisCoeff n g ρ x k α * ((b x : ℝ) : ℂ)) := by
            ext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun α _ => by ring
          rw [heq]
          exact MeasureTheory.integrable_finsetSum _ fun α _ =>
            (orthantBasisCoeff_bump_integrable n m g hρ hdata b hb α).const_mul _
        apply mul_left_cancel₀ h_fac2_ne
        rw [mul_zero]
        have h_sub_eq : (fun x => H x * ((b x : ℝ) : ℂ)) =
            fun x => orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ) -
              (∑ α : Fin k → Fin n, orthantBasisCoeff n g ρ x k α * ∏ j : Fin k, (y (α j) : ℂ)) *
                ((b x : ℝ) : ℂ) := by ext x; dsimp [H]; ring
        rw [h_sub_eq, MeasureTheory.integral_sub
          (orthantSliceCoeff_bump_integrable n k g hρ hdata b hb hy_pos hy) h_sum_int,
          mul_sub, sub_eq_zero]
        have h_lhs : ((k.factorial : ℂ) ^ 2) * ∫ x, orthantSliceCoeff g x y k * ((b x : ℝ) : ℂ) =
            (k.factorial : ℂ) * ((-1 : ℂ) ^ k * ∫ u, gRealCut g ρ u *
              ((iteratedFDeriv ℝ k b u (fun _ => y) : ℝ) : ℂ)) := by
          rw [sq, mul_assoc, orthantSliceCoeff_shift_identity n g hρ hdata hy_pos hy b hb k]
        rw [h_lhs]
        have h_rhs_sum :
            ((k.factorial : ℂ) ^ 2) * ∫ x, (∑ α : Fin k → Fin n,
                orthantBasisCoeff n g ρ x k α * ∏ j : Fin k, (y (α j) : ℂ)) * ((b x : ℝ) : ℂ) =
            ∑ α : Fin k → Fin n, (∏ j : Fin k, (y (α j) : ℂ)) *
              (((k.factorial : ℂ) ^ 2) * ∫ x, orthantBasisCoeff n g ρ x k α * ((b x : ℝ) : ℂ)) := by
          have heq : (fun x => (∑ α : Fin k → Fin n,
              orthantBasisCoeff n g ρ x k α * ∏ j : Fin k, (y (α j) : ℂ)) *
                ((b x : ℝ) : ℂ)) =
              fun x => ∑ α : Fin k → Fin n, (∏ j : Fin k, (y (α j) : ℂ)) *
                (orthantBasisCoeff n g ρ x k α * ((b x : ℝ) : ℂ)) := by
            ext x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun α _ => by ring
          rw [heq, MeasureTheory.integral_finsetSum _ fun α _ =>
            (orthantBasisCoeff_bump_integrable n m g hρ hdata b hb α).const_mul _,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [MeasureTheory.integral_const_mul]
          ring
        rw [h_rhs_sum]
        have h_ib : ∀ α : Fin k → Fin n,
            ((k.factorial : ℂ) ^ 2) * ∫ x, orthantBasisCoeff n g ρ x k α * ((b x : ℝ) : ℂ) =
              (-1 : ℂ) ^ k * ∫ u, gRealCut g ρ u *
                ((∑ σ : Equiv.Perm (Fin k),
                  iteratedFDeriv ℝ k b u
                    (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ) :=
          integral_orthantBasisCoeff_mul_bump n m g hρ hdata b hb
        simp_rw [h_ib]
        have h_ifd_perm_int : ∀ α : Fin k → Fin n,
            Integrable (fun u => gRealCut g ρ u *
              ((∑ σ : Equiv.Perm (Fin k),
                iteratedFDeriv ℝ k b u
                  (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ)) volume := by
          intro α
          have heq : (fun u => gRealCut g ρ u *
              ((∑ σ : Equiv.Perm (Fin k),
                iteratedFDeriv ℝ k b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ)) =
              fun u => ∑ σ : Equiv.Perm (Fin k),
                gRealCut g ρ u *
                  ((iteratedFDeriv ℝ k b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ) := by
            ext u; push_cast; rw [Finset.mul_sum]
          rw [heq]
          exact MeasureTheory.integrable_finsetSum _ fun σ _ =>
            gRealCut_ifd_integrable n k g hρ hdata b _
        have h_comb :
            (∑ α : Fin k → Fin n, (∏ j : Fin k, (y (α j) : ℂ)) *
              ((-1 : ℂ) ^ k * ∫ u, gRealCut g ρ u *
                ((∑ σ : Equiv.Perm (Fin k),
                  iteratedFDeriv ℝ k b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ))) =
            (-1 : ℂ) ^ k * ∫ u, gRealCut g ρ u *
              ((∑ α : Fin k → Fin n, (∏ j : Fin k, y (α j)) *
                ∑ σ : Equiv.Perm (Fin k),
                  iteratedFDeriv ℝ k b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ) := by
          have h1 : ∀ α : Fin k → Fin n,
              (∏ j : Fin k, (y (α j) : ℂ)) * ((-1 : ℂ) ^ k * ∫ u, gRealCut g ρ u *
                ((∑ σ : Equiv.Perm (Fin k),
                  iteratedFDeriv ℝ k b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ)) =
              (-1 : ℂ) ^ k * ∫ u, (∏ j : Fin k, (y (α j) : ℂ)) *
                (gRealCut g ρ u * ((∑ σ : Equiv.Perm (Fin k),
                  iteratedFDeriv ℝ k b u (fun j => Pi.single (α (σ j)) (1 : ℝ)) : ℝ) : ℂ)) := by
            intro α; rw [MeasureTheory.integral_const_mul]; ring
          simp_rw [h1, ← Finset.mul_sum]
          congr 1
          rw [← MeasureTheory.integral_finsetSum _ fun α _ => (h_ifd_perm_int α).const_mul _]
          refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun α _ => by ring
        rw [h_comb]
        simp_rw [sum_perm_multilinear_basis n k _ y]
        rw [show (k.factorial : ℂ) * ((-1 : ℂ) ^ k * ∫ u, gRealCut g ρ u *
            ((iteratedFDeriv ℝ k b u (fun _ => y) : ℝ) : ℂ)) =
          (-1 : ℂ) ^ k * ((k.factorial : ℂ) * ∫ u, gRealCut g ρ u *
            ((iteratedFDeriv ℝ k b u (fun _ => y) : ℝ) : ℂ)) by ring]
        congr 1
        rw [← MeasureTheory.integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        dsimp only
        push_cast
        ring
    exact sub_eq_zero.mp hH_zero

noncomputable def orthantPowerSeries (n : ℕ) (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) :
    FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ :=
  fun m => ∑ α : Fin m → Fin n, orthantBasisCoeff n g ρ 0 m α • orthantMonomial n m α

lemma norm_orthantPowerSeries_le {n : ℕ} (_hn : 0 < n) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    {M : ℝ} (hM_nn : 0 ≤ M)
    (hM_bd : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) (ρ / 8),
      ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.closedBall (0 : ℂ) (5 / 4),
        ‖orthantSlice g x y ζ‖ ≤ M) (m : ℕ) :
    ‖orthantPowerSeries n g ρ m‖ ≤ M * (16 * Real.exp 1 * (n : ℝ) / ρ) ^ m := by
  dsimp [orthantPowerSeries]
  refine (norm_sum_le Finset.univ _).trans ?_
  cases m with
  | zero =>
    simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, mul_one,
      norm_smul, orthantBasisCoeff]
    have hy0_box : (fun _ : Fin n => ρ / 4) ∈ orthantBox n ρ := fun _ => ⟨by linarith, by linarith⟩
    have hc : ‖orthantSliceCoeff g 0 (fun _ => ρ / 4) 0‖ ≤ M :=
      norm_orthantSliceCoeff_le hM_nn
        (fun ζ hζ => hM_bd 0 (Metric.mem_closedBall_self (by positivity)) _ hy0_box ζ
          (Metric.sphere_subset_closedBall hζ)) 0
    exact (mul_le_of_le_one_right (norm_nonneg _) (orthantMonomial_norm_le n 0 _)).trans hc
  | succ m =>
    let k := m + 1
    have hk : 0 < k := Nat.succ_pos m
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have h_fac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    have h_each : ∀ α : Fin k → Fin n,
        ‖orthantBasisCoeff n g ρ 0 k α • orthantMonomial n k α‖ ≤
          M * (16 * Real.exp 1 / ρ) ^ k := by
      intro α
      rw [norm_smul]
      refine (mul_le_of_le_one_right (norm_nonneg _) (orthantMonomial_norm_le n k α)).trans ?_
      dsimp [orthantBasisCoeff]
      change ‖(((k.factorial : ℂ) * ((ρ / (8 * (k : ℝ)) : ℝ) : ℂ) ^ k)⁻¹ *
          ∑ S : Finset (Fin k), (-1 : ℂ) ^ (k - S.card) *
            orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k)‖ ≤ _
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have h_sum_le :
          ‖∑ S : Finset (Fin k), (-1 : ℂ) ^ (k - S.card) *
              orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k‖ ≤ (2 : ℝ) ^ k * M := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ S : Finset (Fin k), ‖(-1 : ℂ) ^ (k - S.card) *
                orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k‖
            ≤ ∑ _S : Finset (Fin k), M := by
              refine Finset.sum_le_sum fun S _ => ?_
              rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
              exact norm_orthantSliceCoeff_le hM_nn
                (fun ζ hζ => hM_bd 0 (Metric.mem_closedBall_self (by positivity)) _
                  (orthantYStep_mem_box hρ hk α S) ζ (Metric.sphere_subset_closedBall hζ)) k
          _ = (2 : ℝ) ^ k * M := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
                nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      have h_exp : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) :=
        Real.pow_div_factorial_le_exp (k : ℝ) hk_pos.le k
      have h_exp_pow : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
        rw [← Real.exp_nat_mul, mul_one]
      rw [h_exp_pow] at h_exp
      have h_alg : ((k.factorial : ℝ) * (ρ / (8 * (k : ℝ))) ^ k)⁻¹ * ((2 : ℝ) ^ k * M) =
          M * (16 / ρ) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by
        have h16 : (16 / ρ) ^ k = (2 : ℝ) ^ k * (8 / ρ) ^ k := by
          rw [← mul_pow]; congr 1; ring
        have h8 : (ρ / (8 * (k : ℝ))) ^ k = ((8 / ρ) ^ k)⁻¹ * ((k : ℝ) ^ k)⁻¹ := by
          rw [← inv_pow, ← inv_pow, ← mul_pow]
          congr 1
          field_simp [hρ.ne', hk_pos.ne']
        have h8_ne : (8 / ρ) ^ k ≠ 0 := pow_ne_zero k (by positivity)
        have hk_ne : (k : ℝ) ^ k ≠ 0 := pow_ne_zero k hk_pos.ne'
        rw [h16, h8]
        field_simp [h_fac_pos.ne', h8_ne, hk_ne]
      calc ((k.factorial : ℝ) * (ρ / (8 * (k : ℝ))) ^ k)⁻¹ *
            ‖∑ S : Finset (Fin k), (-1 : ℂ) ^ (k - S.card) *
              orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k‖
          ≤ ((k.factorial : ℝ) * (ρ / (8 * (k : ℝ))) ^ k)⁻¹ * ((2 : ℝ) ^ k * M) :=
            mul_le_mul_of_nonneg_left h_sum_le (by positivity)
        _ = M * (16 / ρ) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := h_alg
        _ ≤ M * (16 / ρ) ^ k * (Real.exp 1) ^ k :=
            mul_le_mul_of_nonneg_left h_exp (by positivity)
        _ = M * (16 * Real.exp 1 / ρ) ^ k := by
            rw [mul_assoc, ← mul_pow]
            congr 2
            ring
    calc ∑ α : Fin k → Fin n, ‖orthantBasisCoeff n g ρ 0 k α • orthantMonomial n k α‖
        ≤ ∑ _α : Fin k → Fin n, (M * (16 * Real.exp 1 / ρ) ^ k) :=
          Finset.sum_le_sum fun α _ => h_each α
      _ = ((n : ℝ) ^ k) * (M * (16 * Real.exp 1 / ρ) ^ k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      _ = M * ((16 * Real.exp 1 / ρ) ^ k * (n : ℝ) ^ k) := by ring
      _ = M * (16 * Real.exp 1 * (n : ℝ) / ρ) ^ k := by
          rw [← mul_pow]
          congr 2
          ring

theorem orthant_eow_extension (n : ℕ) (g : (Fin n → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData n g ρ) :
    OrthantEOWCore n g := by
  by_cases hn0 : n = 0
  · subst hn0
    let G : (Fin 0 → ℂ) → ℂ := fun _ => g 0
    have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ) := fun _ _ => analyticAt_const
    have hG_eq : ∀ w : Fin 0 → ℂ, G w = g w := by
      intro w
      dsimp [G]
      congr 1
      ext i
      exact Fin.elim0 i
    refine ⟨ρ, hρ, G, hG_an,
      ⟨Metric.ball 0 ρ, Metric.isOpen_ball, Metric.nonempty_ball.mpr hρ,
        fun w hw => ⟨hw, fun i => Fin.elim0 i⟩, fun w _ => hG_eq w⟩,
      ⟨Metric.ball 0 ρ, Metric.isOpen_ball, Metric.nonempty_ball.mpr hρ,
        fun w hw => ⟨hw, fun i => Fin.elim0 i⟩, fun w _ => hG_eq w⟩⟩
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
    obtain ⟨M, hM_nn, hM_bd⟩ := orthant_eowData_uniform_box_bound n g hρ hdata
    let P := orthantPowerSeries n g ρ
    let r₀ : ℝ := min (ρ / 8) (ρ / (32 * Real.exp 1 * (n : ℝ)))
    have hr₀_pos : 0 < r₀ := lt_min (by positivity) (by positivity)
    let r₀_nn : NNReal := ⟨r₀, hr₀_pos.le⟩
    have hr₀_rad : (r₀_nn : ENNReal) ≤ P.radius := by
      refine FormalMultilinearSeries.le_radius_of_bound P M fun m => ?_
      have hPm := norm_orthantPowerSeries_le hn g hρ hM_nn hM_bd m
      have hr_le : (r₀_nn : ℝ) ≤ ρ / (32 * Real.exp 1 * (n : ℝ)) := min_le_right _ _
      have h_prod : (16 * Real.exp 1 * (n : ℝ) / ρ) ^ m * (r₀_nn : ℝ) ^ m ≤ 1 := by
        rw [← mul_pow]
        refine pow_le_one₀ (by positivity) ?_
        have h1 : (16 * Real.exp 1 * (n : ℝ) / ρ) * (r₀_nn : ℝ) ≤
            (16 * Real.exp 1 * (n : ℝ) / ρ) * (ρ / (32 * Real.exp 1 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hr_le (by positivity)
        have h2 : (16 * Real.exp 1 * (n : ℝ) / ρ) * (ρ / (32 * Real.exp 1 * (n : ℝ))) = 1 / 2 := by
          have he : (Real.exp 1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
          field_simp [hρ.ne', hn_pos.ne', he]
          ring
        linarith
      calc ‖P m‖ * (r₀_nn : ℝ) ^ m
          ≤ (M * (16 * Real.exp 1 * (n : ℝ) / ρ) ^ m) * (r₀_nn : ℝ) ^ m :=
            mul_le_mul_of_nonneg_right hPm (pow_nonneg hr₀_pos.le m)
        _ = M * ((16 * Real.exp 1 * (n : ℝ) / ρ) ^ m * (r₀_nn : ℝ) ^ m) := by ring
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left h_prod hM_nn
        _ = M := mul_one M
    let G : (Fin n → ℂ) → ℂ := P.sum
    have hr₀_enn_pos : (0 : ENNReal) < (r₀_nn : ENNReal) :=
      ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hr₀_pos)
    have hP_rad_pos : 0 < P.radius := lt_of_lt_of_le hr₀_enn_pos hr₀_rad
    have hG_series : HasFPowerSeriesOnBall G P 0 r₀_nn := by
      have h_full := P.hasFPowerSeriesOnBall hP_rad_pos
      exact h_full.mono hr₀_enn_pos hr₀_rad
    have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 r₀) := by
      intro z hz
      have hze : z ∈ Metric.eball (0 : Fin n → ℂ) r₀_nn := by
        rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
        change ‖z‖ < r₀
        simpa [Metric.mem_ball, dist_zero_right] using hz
      exact hG_series.analyticAt_of_mem hze
    have hG_real_pos : ∀ y : Fin n → ℝ, y ∈ PosOrthant n → ‖y‖ < r₀ →
        G (fun i => (y i : ℂ)) = g (fun i => (y i : ℂ)) := by
      intro y hy_pos hy_lt
      have hy_38 : ‖y‖ ≤ 3 * ρ / 8 := by
        have h1 : r₀ ≤ ρ / 8 := min_le_left _ _
        linarith
      have hye : (fun i => (y i : ℂ)) ∈ Metric.eball (0 : Fin n → ℂ) r₀_nn := by
        rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
        change ‖fun i => (y i : ℂ)‖ < r₀
        refine (pi_norm_lt_iff hr₀_pos).mpr fun i => ?_
        simpa [Complex.norm_real] using (norm_le_pi_norm y i).trans_lt hy_lt
      have h_sumG := hG_series.hasSum hye
      rw [zero_add] at h_sumG
      have h0_le : ‖(0 : Fin n → ℝ)‖ ≤ ρ / 8 := by rw [norm_zero]; positivity
      have hP_y := orthantSlice_hasFPowerSeriesOnBall n g hρ hdata h0_le hy_pos hy_38
      have h1e : (1 : ℂ) ∈ Metric.eball (0 : ℂ) (5 / 4 : NNReal) := by
        rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
        change ‖(1 : ℂ)‖ < ((5 / 4 : NNReal) : ℝ)
        have hc : ((5 / 4 : NNReal) : ℝ) = 5 / 4 := by norm_num
        rw [hc, norm_one]
        norm_num
      have h_sumg := hP_y.hasSum h1e
      rw [zero_add] at h_sumg
      have hg1 : orthantSlice g 0 y 1 = g (fun i => (y i : ℂ)) := by
        dsimp [orthantSlice]
        congr 1
        ext i
        simp
      rw [hg1] at h_sumg
      have h_terms : (fun m => P m (fun _ => fun i => (y i : ℂ))) =
          fun m => (cauchyPowerSeries (orthantSlice g 0 y) 0 (5 / 4) m) (fun _ => 1) := by
        ext m
        dsimp [P, orthantPowerSeries]
        rw [_root_.sum_apply]
        simp only [_root_.smul_apply, orthantMonomial_diag, smul_eq_mul]
        exact (orthantSliceCoeff_eq_sum_orthantBasisCoeff hn g hρ hdata hy_pos hy_38 m).symm
      rw [h_terms] at h_sumG
      exact h_sumG.unique h_sumg
    let a : ℝ := r₀ / 4
    have ha_pos : 0 < a := by dsimp [a]; positivity
    let c_a : Fin n → ℝ := fun _ => a
    have h_slice_eq : ∀ x y : Fin n → ℝ,
        x ∈ Metric.ball c_a (a / 2) → y ∈ Metric.ball c_a (a / 2) →
        ∀ ζ ∈ Metric.ball (0 : ℂ) (6 / 5),
          G (fun i => (x i : ℂ) + ζ * (y i : ℂ)) = g (fun i => (x i : ℂ) + ζ * (y i : ℂ)) := by
      intro x y hx_b hy_b
      have hx_bounds : ∀ i : Fin n, a / 2 < x i ∧ |x i| < 3 * a / 2 := by
        intro i
        have hdi : |x i - a| < a / 2 := by
          simpa [Real.dist_eq, c_a] using
            (dist_le_pi_dist x c_a i).trans_lt (Metric.mem_ball.mp hx_b)
        rw [abs_lt] at hdi ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
      have hy_bounds : ∀ i : Fin n, a / 2 < y i ∧ |y i| < 3 * a / 2 := by
        intro i
        have hdi : |y i - a| < a / 2 := by
          simpa [Real.dist_eq, c_a] using
            (dist_le_pi_dist y c_a i).trans_lt (Metric.mem_ball.mp hy_b)
        rw [abs_lt] at hdi ⊢
        exact ⟨by linarith, by linarith, by linarith⟩
      have hx_norm : ‖x‖ ≤ ρ / 8 := by
        have hr8 : r₀ ≤ ρ / 8 := min_le_left _ _
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        have := (hx_bounds i).2
        dsimp [a] at this
        linarith
      have hy_pos : y ∈ PosOrthant n := fun i => lt_trans (half_pos ha_pos) (hy_bounds i).1
      have hy_norm : ‖y‖ ≤ 3 * ρ / 8 := by
        have hr8 : r₀ ≤ ρ / 8 := min_le_left _ _
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        have := (hy_bounds i).2
        dsimp [a] at this
        linarith
      let γ : ℂ → (Fin n → ℂ) := fun ζ i => (x i : ℂ) + ζ * (y i : ℂ)
      have hγ_an : ∀ ζ : ℂ, AnalyticAt ℂ γ ζ := by
        let L : ℂ →L[ℂ] (Fin n → ℂ) :=
          ContinuousLinearMap.pi fun i =>
            (ContinuousLinearMap.id ℂ ℂ).smulRight (y i : ℂ)
        intro ζ
        have heq : γ = fun w => (fun i => (x i : ℂ)) + L w := by
          ext w i; simp [γ, L]
        rw [heq]
        exact analyticAt_const.add (L.analyticAt ζ)
      have hγ_r0 : ∀ ζ ∈ Metric.ball (0 : ℂ) (6 / 5), γ ζ ∈ Metric.ball (0 : Fin n → ℂ) r₀ := by
        intro ζ hζ
        have hζ_lt : ‖ζ‖ < 6 / 5 := by simpa using hζ
        rw [Metric.mem_ball, dist_zero_right]
        refine (pi_norm_lt_iff hr₀_pos).mpr fun i => ?_
        calc ‖(x i : ℂ) + ζ * (y i : ℂ)‖
            ≤ |x i| + ‖ζ‖ * |y i| := by
              simpa [Complex.norm_real] using norm_add_le (x i : ℂ) (ζ * (y i : ℂ))
          _ < 3 * a / 2 + (6 / 5) * (3 * a / 2) := by
              nlinarith [(hx_bounds i).2, (hy_bounds i).2, abs_nonneg (y i), norm_nonneg ζ]
          _ < r₀ := by dsimp [a]; linarith
      have hGγ_an : AnalyticOnNhd ℂ (G ∘ γ) (Metric.ball 0 (6 / 5)) :=
        fun ζ hζ => (hG_an (γ ζ) (hγ_r0 ζ hζ)).comp (hγ_an ζ)
      have hgγ_an : AnalyticOnNhd ℂ (g ∘ γ) (Metric.ball 0 (6 / 5)) := by
        refine (orthantSlice_analyticOnNhd n g hρ hdata hx_norm hy_pos hy_norm).mono ?_
        exact Metric.ball_subset_ball (by norm_num)
      have h_real_ev : ∀ᶠ t : ℝ in nhds 0, (G ∘ γ) (t : ℂ) = (g ∘ γ) (t : ℂ) := by
        filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 / 4) (1 / 4) by norm_num)]
          with t ht
        have h_pos_t : (fun i => x i + t * y i) ∈ PosOrthant n := by
          intro i
          have hxi := (hx_bounds i).1
          have hyi := (hy_bounds i).2
          rw [abs_lt] at hyi
          nlinarith [ht.1, ht.2]
        have h_norm_t : ‖fun i => x i + t * y i‖ < r₀ := by
          refine (pi_norm_lt_iff hr₀_pos).mpr fun i => ?_
          rw [Real.norm_eq_abs]
          have hxi := (hx_bounds i).2
          have hyi := (hy_bounds i).2
          have ht_abs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
          calc |x i + t * y i| ≤ |x i| + |t| * |y i| := by
                simpa [abs_mul] using abs_add_le (x i) (t * y i)
            _ < 3 * a / 2 + (1 / 4) * (3 * a / 2) := by nlinarith [abs_nonneg (y i)]
            _ < r₀ := by dsimp [a]; linarith
        have hγ_t : γ (t : ℂ) = fun i => ((x i + t * y i : ℝ) : ℂ) := by
          ext i; simp [γ]
        dsimp [Function.comp]
        rw [hγ_t]
        exact hG_real_pos _ h_pos_t h_norm_t
      have h_ev0 := Analysis.analytic_nhds_eq_of_real_eq_1D (G ∘ γ) (g ∘ γ) 0
        (hGγ_an 0 (by simp)) (hgγ_an 0 (by simp)) h_real_ev
      exact hGγ_an.eqOn_of_preconnected_of_eventuallyEq hgγ_an
        (convex_ball (0 : ℂ) (6 / 5)).isPreconnected (by simp) h_ev0
    let reMap : (Fin n → ℂ) → (Fin n → ℝ) := fun z i => (z i).re
    let imMap : (Fin n → ℂ) → (Fin n → ℝ) := fun z i => (z i).im
    have hre_cont : Continuous reMap :=
      continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)
    have him_cont : Continuous imMap :=
      continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i)
    refine ⟨r₀, hr₀_pos, G, hG_an, ?_, ?_⟩
    · let W₁ : Set (Fin n → ℂ) :=
        reMap ⁻¹' Metric.ball c_a (a / 2) ∩ imMap ⁻¹' Metric.ball c_a (a / 2)
      have hW₁_open : IsOpen W₁ :=
        (Metric.isOpen_ball.preimage hre_cont).inter (Metric.isOpen_ball.preimage him_cont)
      have hW₁_ne : W₁.Nonempty := by
        refine ⟨fun _ => (a : ℂ) + Complex.I * (a : ℂ), ?_, ?_⟩
        · rw [Set.mem_preimage]
          convert Metric.mem_ball_self (half_pos ha_pos) using 1
          ext i; simp [reMap, c_a]
        · rw [Set.mem_preimage]
          convert Metric.mem_ball_self (half_pos ha_pos) using 1
          ext i; simp [imMap, c_a]
      have hW₁_sub : W₁ ⊆ Metric.ball 0 r₀ ∩ TubeDomain (PosOrthant n) := by
        rintro z ⟨hz_re, hz_im⟩
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right]
          refine (pi_norm_lt_iff hr₀_pos).mpr fun i => ?_
          have hri : |(z i).re - a| < a / 2 := by
            simpa [Real.dist_eq, reMap, c_a] using
              (dist_le_pi_dist (reMap z) c_a i).trans_lt (Metric.mem_ball.mp hz_re)
          have hii : |(z i).im - a| < a / 2 := by
            simpa [Real.dist_eq, imMap, c_a] using
              (dist_le_pi_dist (imMap z) c_a i).trans_lt (Metric.mem_ball.mp hz_im)
          rw [abs_lt] at hri hii
          calc ‖z i‖ ≤ |(z i).re| + |(z i).im| := Complex.norm_le_abs_re_add_abs_im (z i)
            _ < 3 * a / 2 + 3 * a / 2 := by
                refine add_lt_add (abs_lt.mpr ⟨by linarith, by linarith⟩)
                  (abs_lt.mpr ⟨by linarith, by linarith⟩)
            _ < r₀ := by dsimp [a]; linarith
        · intro i
          have hii : |(z i).im - a| < a / 2 := by
            simpa [Real.dist_eq, imMap, c_a] using
              (dist_le_pi_dist (imMap z) c_a i).trans_lt (Metric.mem_ball.mp hz_im)
          rw [abs_lt] at hii
          linarith
      refine ⟨W₁, hW₁_open, hW₁_ne, hW₁_sub, fun z ⟨hz_re, hz_im⟩ => ?_⟩
      have hz_eq : z = fun i => ((reMap z i : ℝ) : ℂ) + Complex.I * ((imMap z i : ℝ) : ℂ) := by
        ext i; exact (Complex.re_add_im (z i)).symm.trans (by ring)
      rw [hz_eq]
      exact h_slice_eq (reMap z) (imMap z) hz_re hz_im Complex.I
        (by rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num)
    · let negImMap : (Fin n → ℂ) → (Fin n → ℝ) := fun z i => -(z i).im
      have hnim_cont : Continuous negImMap :=
        continuous_pi fun i => continuous_neg.comp (Complex.continuous_im.comp (continuous_apply i))
      let W₂ : Set (Fin n → ℂ) :=
        reMap ⁻¹' Metric.ball c_a (a / 2) ∩ negImMap ⁻¹' Metric.ball c_a (a / 2)
      have hW₂_open : IsOpen W₂ :=
        (Metric.isOpen_ball.preimage hre_cont).inter (Metric.isOpen_ball.preimage hnim_cont)
      have hW₂_ne : W₂.Nonempty := by
        refine ⟨fun _ => (a : ℂ) - Complex.I * (a : ℂ), ?_, ?_⟩
        · rw [Set.mem_preimage]
          convert Metric.mem_ball_self (half_pos ha_pos) using 1
          ext i; simp [reMap, c_a]
        · rw [Set.mem_preimage]
          convert Metric.mem_ball_self (half_pos ha_pos) using 1
          ext i; simp [negImMap, c_a]
      have hW₂_sub : W₂ ⊆ Metric.ball 0 r₀ ∩ TubeDomain (NegOrthant n) := by
        rintro z ⟨hz_re, hz_im⟩
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, dist_zero_right]
          refine (pi_norm_lt_iff hr₀_pos).mpr fun i => ?_
          have hri : |(z i).re - a| < a / 2 := by
            simpa [Real.dist_eq, reMap, c_a] using
              (dist_le_pi_dist (reMap z) c_a i).trans_lt (Metric.mem_ball.mp hz_re)
          have hii : |-(z i).im - a| < a / 2 := by
            simpa [Real.dist_eq, negImMap, c_a] using
              (dist_le_pi_dist (negImMap z) c_a i).trans_lt (Metric.mem_ball.mp hz_im)
          rw [abs_lt] at hri hii
          calc ‖z i‖ ≤ |(z i).re| + |(z i).im| := Complex.norm_le_abs_re_add_abs_im (z i)
            _ < 3 * a / 2 + 3 * a / 2 := by
                refine add_lt_add (abs_lt.mpr ⟨by linarith, by linarith⟩)
                  (abs_lt.mpr ⟨by linarith, by linarith⟩)
            _ < r₀ := by dsimp [a]; linarith
        · intro i
          have hii : |-(z i).im - a| < a / 2 := by
            simpa [Real.dist_eq, negImMap, c_a] using
              (dist_le_pi_dist (negImMap z) c_a i).trans_lt (Metric.mem_ball.mp hz_im)
          rw [abs_lt] at hii
          linarith
      refine ⟨W₂, hW₂_open, hW₂_ne, hW₂_sub, fun z ⟨hz_re, hz_im⟩ => ?_⟩
      have hz_eq :
          z = fun i => ((reMap z i : ℝ) : ℂ) + (-Complex.I) * ((negImMap z i : ℝ) : ℂ) := by
        ext i
        dsimp [reMap, negImMap]
        push_cast
        exact (Complex.re_add_im (z i)).symm.trans (by ring)
      rw [hz_eq]
      exact h_slice_eq (reMap z) (negImMap z) hz_re hz_im (-Complex.I)
        (by rw [Metric.mem_ball, dist_zero_right, norm_neg, Complex.norm_I]; norm_num)

lemma eow_local_core_all_dim {n : ℕ} (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    LocalEOWCore V_plus f x := by
  by_cases h0 : n = 0
  · subst h0
    exact eow_local_core_0d V_plus U hV_plus_ne f x
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    obtain ⟨v, hli, hv⟩ := exists_linearIndependent_mem_open hV_plus_open hV_plus_ne
    obtain ⟨ρ, hρ, hdata⟩ := orthant_eowData_of_wedge n hn V_plus U hV_plus_convex hV_plus_cone
      hU_open f h_cont h_holo_plus h_holo_minus x hx_U v hv
    have h_orth := orthant_eow_extension n _ hρ hdata
    exact eow_local_core_of_orthant hn V_plus hV_plus_open hV_plus_convex hV_plus_cone f
      h_holo_plus h_holo_minus x v hli hv h_orth

lemma eow_local_exists_all_dim {n : ℕ} (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  have h_core := eow_local_core_all_dim V_plus U hV_plus_open hV_plus_convex hV_plus_cone
    hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U
  obtain ⟨F_x, hF_ana, hF_eq⟩ := exists_local_analytic_extension_of_core V_plus U hV_plus_open
    hV_plus_convex hV_plus_cone f h_cont h_holo_plus h_holo_minus x h_core
  obtain ⟨r_x, hr_x_pos, h_sub, h_ana_nhd⟩ :=
    exists_ball_subset_and_analyticOnNhd hU_open hx_U hF_ana
  exact ⟨r_x, hr_x_pos, h_sub, F_x, h_ana_nhd, hF_eq.mono Set.inter_subset_right⟩

theorem eow_all_dim {n : ℕ} (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) ⊆ W ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  have h_exists : ∀ x ∈ U, ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) :=
    fun x hx => eow_local_exists_all_dim V_plus U hV_plus_open hV_plus_convex hV_plus_cone
      hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx
  rcases local_extension_assembly V_plus U f h_exists (eow_local_compat V_plus U f) with
    ⟨r, hr, F_loc, hF_holo, hF_eq, hF_compat⟩
  let W : Set (Fin n → ℂ) :=
    TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)
  refine ⟨W, isOpen_wedge_neighborhood V_plus U hV_plus_open r,
    wedge_subset_union_balls V_plus U r hr, ?_⟩
  exact eow_nd_glue V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus r hr F_loc hF_holo hF_eq hF_compat

lemma partial_deriv_pi_eq_intervalIntegral {N : ℕ}
    (f : (Fin N → ℂ) → ℂ) (z : Fin N → ℂ) (m : Fin N) (R : ℝ) (hR : 0 < R)
    (h_diff : DifferentiableOn ℂ (fun w => f (Function.update z m w))
      (Metric.closedBall (z m) R)) :
    deriv (fun w => f (Function.update z m w)) (z m) =
      (2 * ↑Real.pi * I)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (I / (↑R * exp (↑θ * I))) * f (Function.update z m (z m + ↑R * exp (↑θ * I))) := by
  let g : ℂ × ℂ → ℂ := fun p => f (Function.update z m p.1)
  exact Analysis.partial_deriv_eq_intervalIntegral g (z m) 0 R hR h_diff

lemma continuousAt_partial_deriv_pi {N : ℕ} {U : Set (Fin N → ℂ)} (hU : IsOpen U)
    (f : (Fin N → ℂ) → ℂ) (h_cont : ContinuousOn f U) (m : Fin N)
    (h_holo : ∀ z ∈ U, DifferentiableAt ℂ (fun w => f (Function.update z m w)) (z m))
    {z₀ : Fin N → ℂ} (hz₀ : z₀ ∈ U) :
    ContinuousAt (fun z => deriv (fun w => f (Function.update z m w)) (z m)) z₀ := by
  rcases Metric.isOpen_iff.mp hU z₀ hz₀ with ⟨ε, hε, h_ball⟩
  let R : ℝ := ε / 2
  have hR : 0 < R := half_pos hε
  have h_upd_mem : ∀ z ∈ Metric.ball z₀ R, ∀ w ∈ Metric.closedBall (z m) R,
      Function.update z m w ∈ U := by
    intro z hz w hw
    apply h_ball
    rw [Metric.mem_ball] at hz ⊢
    refine (dist_pi_lt_iff hε).mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm
      rw [Function.update_self]
      have hw' : dist w (z j) ≤ R := Metric.mem_closedBall.mp hw
      have hz' : dist (z j) (z₀ j) < R := (dist_le_pi_dist z z₀ j).trans_lt hz
      calc dist w (z₀ j) ≤ dist w (z j) + dist (z j) (z₀ j) := dist_triangle _ _ _
        _ < R + R := by linarith
        _ = ε := add_halves ε
    · rw [Function.update_of_ne hjm]
      exact ((dist_le_pi_dist z z₀ j).trans_lt hz).trans (half_lt_self hε)
  have h_circ_mem : ∀ z ∈ Metric.ball z₀ R, ∀ θ : ℝ,
      z m + ↑R * exp (↑θ * I) ∈ Metric.closedBall (z m) R := by
    intro z _ θ
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hR.le, Complex.norm_exp_ofReal_mul_I, mul_one]
  let f_int : Metric.ball z₀ R → ℝ → ℂ := fun p θ =>
    (I / (↑R * exp (↑θ * I))) * f (Function.update p.val m (p.val m + ↑R * exp (↑θ * I)))
  have h_cont_int : Continuous (Function.uncurry f_int) := by
    have h_left : Continuous (fun X : Metric.ball z₀ R × ℝ => I / (↑R * exp (↑X.2 * I))) := by
      refine Continuous.div continuous_const ?_ ?_
      · exact continuous_const.mul
          (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
      · intro X
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
    have h_inner : Continuous (fun X : Metric.ball z₀ R × ℝ =>
        Function.update X.1.val m (X.1.val m + ↑R * exp (↑X.2 * I))) := by
      refine continuous_pi fun j => ?_
      by_cases hjm : j = m
      · subst hjm
        simp only [Function.update_self]
        exact ((continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)).add
          (continuous_const.mul
            (Complex.continuous_exp.comp
              ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
      · simp only [Function.update_of_ne hjm]
        exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    have h_right : Continuous (fun X : Metric.ball z₀ R × ℝ =>
        f (Function.update X.1.val m (X.1.val m + ↑R * exp (↑X.2 * I)))) :=
      h_cont.comp_continuous h_inner (fun X =>
        h_upd_mem X.1.val X.1.property _ (h_circ_mem X.1.val X.1.property X.2))
    exact h_left.mul h_right
  let F_int : (Fin N → ℂ) → ℂ := fun z =>
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (I / (↑R * exp (↑θ * I))) * f (Function.update z m (z m + ↑R * exp (↑θ * I)))
  have h_int_cont : Continuous (fun p : Metric.ball z₀ R => F_int p.val) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      h_cont_int 0 (2 * Real.pi)
  have h_int_contAt : ContinuousAt F_int z₀ :=
    (continuousOn_iff_continuous_restrict.mpr h_int_cont).continuousAt
      (Metric.ball_mem_nhds z₀ hR)
  have h_mul : ContinuousAt (fun z => (2 * ↑Real.pi * I)⁻¹ * F_int z) z₀ :=
    continuousAt_const.mul h_int_contAt
  refine h_mul.congr ?_
  filter_upwards [Metric.ball_mem_nhds z₀ hR] with z hz
  have h_diff_z : DifferentiableOn ℂ (fun w => f (Function.update z m w))
      (Metric.closedBall (z m) R) := by
    intro w hw
    have hd := h_holo (Function.update z m w) (h_upd_mem z hz w hw)
    have h_fn : (fun w₁ => f (Function.update (Function.update z m w) m w₁)) =
        fun w₁ => f (Function.update z m w₁) := by
      ext w₁
      rw [Function.update_idem]
    rw [h_fn, Function.update_self] at hd
    exact hd.differentiableWithinAt
  exact (partial_deriv_pi_eq_intervalIntegral f z m R hR h_diff_z).symm

lemma hasDerivAt_update_pi {N : ℕ} (y : Fin N → ℂ) (j : Fin N) (u₀ : ℂ) :
    HasDerivAt (fun u : ℂ => Function.update y j u) (Pi.single j (1 : ℂ)) u₀ := by
  classical
  rw [hasDerivAt_pi]
  intro k
  by_cases hkj : k = j
  · subst hkj
    simp only [Function.update_self, Pi.single_eq_same]
    exact hasDerivAt_id u₀
  · simp only [Function.update_of_ne hkj, Pi.single_eq_of_ne hkj]
    exact hasDerivAt_const u₀ (y k)

lemma fderiv_pi_eq_sum_partial {N : ℕ} {g : (Fin N → ℂ) → ℂ} {y : Fin N → ℂ}
    (hg : DifferentiableAt ℂ g y) :
    fderiv ℂ g y = ∑ j : Fin N,
      (ContinuousLinearMap.proj j).smulRight
        (deriv (fun u => g (Function.update y j u)) (y j)) := by
  classical
  ext v
  have hv_sum : v = ∑ j : Fin N, v j • Pi.single j (1 : ℂ) := by
    ext k
    simp [Pi.single_apply]
  have h_lhs : (fderiv ℂ g y) v = ∑ j : Fin N, v j * (fderiv ℂ g y) (Pi.single j (1 : ℂ)) := by
    conv_lhs => rw [hv_sum]
    rw [_root_.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [h_lhs, sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  have hg' : HasFDerivAt g (fderiv ℂ g y) (Function.update y j (y j)) := by
    rw [Function.update_eq_self]
    exact hg.hasFDerivAt
  exact (hg'.comp_hasDerivAt (y j) (hasDerivAt_update_pi y j (y j))).deriv.symm

noncomputable def osgoodSplitToCLM (N : ℕ) : (Fin (N + 1) → ℂ) →L[ℂ] ℂ × (Fin N → ℂ) :=
  ContinuousLinearMap.prod (ContinuousLinearMap.proj 0)
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.succ)

noncomputable def osgoodSplitFromCLM (N : ℕ) : ℂ × (Fin N → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  ContinuousLinearMap.pi (Fin.cases (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ))
    (fun j => (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))))

lemma osgoodSplit_from_to {N : ℕ} (z : Fin (N + 1) → ℂ) :
    osgoodSplitFromCLM N (osgoodSplitToCLM N z) = z := by
  ext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

lemma osgoodSplit_to_from {N : ℕ} (p : ℂ × (Fin N → ℂ)) :
    osgoodSplitToCLM N (osgoodSplitFromCLM N p) = p := by
  ext
  · rfl
  · rename_i j
    change osgoodSplitFromCLM N p j.succ = p.2 j
    simp [osgoodSplitFromCLM]

lemma osgoodSplitFrom_update_zero {N : ℕ} (p : ℂ × (Fin N → ℂ)) (w : ℂ) :
    osgoodSplitFromCLM N (w, p.2) = Function.update (osgoodSplitFromCLM N p) 0 w := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [osgoodSplitFromCLM]
  · intro j
    simp [osgoodSplitFromCLM]

lemma osgoodSplitFrom_update_succ {N : ℕ} (p : ℂ × (Fin N → ℂ)) (j : Fin N) (u : ℂ) :
    osgoodSplitFromCLM N (p.1, Function.update p.2 j u) =
      Function.update (osgoodSplitFromCLM N p) j.succ u := by
  ext i
  refine Fin.cases ?_ ?_ i
  · rw [Function.update_of_ne (Fin.succ_ne_zero j).symm]
    rfl
  · intro k
    by_cases hkj : k = j
    · subst hkj
      simp [osgoodSplitFromCLM]
    · have h_succ : k.succ ≠ j.succ := fun h => hkj (Fin.succ_inj.mp h)
      simp [osgoodSplitFromCLM, hkj, h_succ]

theorem osgood_nd : ∀ (N : ℕ) {U : Set (Fin N → ℂ)}, IsOpen U →
    ∀ (f : (Fin N → ℂ) → ℂ), ContinuousOn f U →
    (∀ z ∈ U, ∀ m : Fin N, DifferentiableAt ℂ (fun w => f (Function.update z m w)) (z m)) →
    DifferentiableOn ℂ f U
  | 0, U, _hU, f, _h_cont, _h_holo => by
    have hf_const : f = fun _ => f 0 := by
      ext z
      congr 1
      ext i
      exact Fin.elim0 i
    rw [hf_const]
    exact differentiableOn_const (f 0)
  | N + 1, U, hU, f, h_cont, h_holo => by
    intro z₀ hz₀
    let toL := osgoodSplitToCLM N
    let frL := osgoodSplitFromCLM N
    let U' : Set (ℂ × (Fin N → ℂ)) := frL ⁻¹' U
    have hU' : IsOpen U' := hU.preimage frL.continuous
    let f' : ℂ × (Fin N → ℂ) → ℂ := f ∘ frL
    have h_cont' : ContinuousOn f' U' := h_cont.comp frL.continuous.continuousOn (fun _ hp => hp)
    let p₀ := toL z₀
    have hp₀ : p₀ ∈ U' := by
      change frL (toL z₀) ∈ U
      rwa [osgoodSplit_from_to]
    have h_holo_y : ∀ x : ℂ, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'} := by
      intro x
      have hUx : IsOpen {y : Fin N → ℂ | (x, y) ∈ U'} :=
        hU'.preimage (Continuous.prodMk continuous_const continuous_id)
      have hc_x : ContinuousOn (fun y => f' (x, y)) {y | (x, y) ∈ U'} :=
        h_cont'.comp (Continuous.prodMk continuous_const continuous_id).continuousOn
          (fun _ hy => hy)
      refine osgood_nd N hUx (fun y => f' (x, y)) hc_x ?_
      intro y hy j
      have h_eq_fn : (fun u => f' (x, Function.update y j u)) =
          fun u => f (Function.update (frL (x, y)) j.succ u) := by
        ext u
        dsimp [f']
        rw [osgoodSplitFrom_update_succ (x, y) j u]
      rw [h_eq_fn]
      have h_val : y j = frL (x, y) j.succ := by simp [frL, osgoodSplitFromCLM]
      rw [h_val]
      exact h_holo (frL (x, y)) hy j.succ
    let f₁ : ℂ → (Fin N → ℂ) → ℂ →L[ℂ] ℂ := fun x y =>
      (1 : ℂ →L[ℂ] ℂ).smulRight
        (deriv (fun w => f (Function.update (frL (x, y)) 0 w)) (frL (x, y) 0))
    let f₂ : ℂ → (Fin N → ℂ) → (Fin N → ℂ) →L[ℂ] ℂ := fun x y =>
      ∑ j : Fin N, (ContinuousLinearMap.proj j).smulRight
        (deriv (fun u => f (Function.update (frL (x, y)) j.succ u)) (frL (x, y) j.succ))
    have df₁ : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fun x => f' (x, p.2)) (f₁ p.1 p.2) p.1 := by
      filter_upwards [hU'.mem_nhds hp₀] with p hp
      have h_eq_fn : (fun x => f' (x, p.2)) =
          fun w => f (Function.update (frL p) 0 w) := by
        ext w
        dsimp [f']
        rw [osgoodSplitFrom_update_zero p w]
      have h_val : p.1 = frL p 0 := by simp [frL, osgoodSplitFromCLM]
      rw [h_eq_fn]
      dsimp [f₁]
      rw [Prod.mk.eta, h_val]
      exact (h_holo (frL p) hp 0).hasDerivAt.hasFDerivAt
    have df₂ : ∀ᶠ p in 𝓝 p₀, HasFDerivAt (fun y => f' (p.1, y)) (f₂ p.1 p.2) p.2 := by
      filter_upwards [hU'.mem_nhds hp₀] with p hp
      have hUx : IsOpen {y : Fin N → ℂ | (p.1, y) ∈ U'} :=
        hU'.preimage (Continuous.prodMk continuous_const continuous_id)
      have hd_at : DifferentiableAt ℂ (fun y => f' (p.1, y)) p.2 :=
        ((h_holo_y p.1) p.2 hp).differentiableAt (hUx.mem_nhds hp)
      have hf_eq := fderiv_pi_eq_sum_partial hd_at
      have h_sum_eq : (∑ j : Fin N, (ContinuousLinearMap.proj j).smulRight
          (deriv (fun u => f' (p.1, Function.update p.2 j u)) (p.2 j))) = f₂ p.1 p.2 := by
        dsimp [f₂]
        rw [Prod.mk.eta]
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        have h_eq_fn : (fun u => f' (p.1, Function.update p.2 j u)) =
            fun u => f (Function.update (frL p) j.succ u) := by
          ext u
          dsimp [f']
          rw [osgoodSplitFrom_update_succ p j u]
        have h_val : p.2 j = frL p j.succ := by simp [frL, osgoodSplitFromCLM]
        rw [h_eq_fn, h_val]
      rw [← h_sum_eq, ← hf_eq]
      exact hd_at.hasFDerivAt
    have cf₁ : ContinuousAt ↿f₁ p₀ := by
      have hc0 := continuousAt_partial_deriv_pi hU f h_cont 0
        (fun z hz => h_holo z hz 0) (z₀ := frL p₀) hp₀
      have hc_comp : ContinuousAt
          (fun p : ℂ × (Fin N → ℂ) =>
            deriv (fun w => f (Function.update (frL p) 0 w)) (frL p 0)) p₀ :=
        hc0.comp frL.continuous.continuousAt
      have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
        (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
      exact h_smul.continuousAt.comp hc_comp
    have cf₂ : ContinuousAt ↿f₂ p₀ := by
      have h_eq_fn : (↿f₂ : ℂ × (Fin N → ℂ) → (Fin N → ℂ) →L[ℂ] ℂ) =
          fun p : ℂ × (Fin N → ℂ) =>
            ∑ j : Fin N, (ContinuousLinearMap.proj j).smulRight
              (deriv (fun u => f (Function.update (frL p) j.succ u)) (frL p j.succ)) := by
        ext p v
        rfl
      rw [h_eq_fn, ContinuousAt]
      refine tendsto_finsetSum Finset.univ fun j _ => ?_
      have hcj := continuousAt_partial_deriv_pi hU f h_cont j.succ
        (fun z hz => h_holo z hz j.succ) (z₀ := frL p₀) hp₀
      have hc_comp : ContinuousAt
          (fun p : ℂ × (Fin N → ℂ) =>
            deriv (fun u => f (Function.update (frL p) j.succ u)) (frL p j.succ)) p₀ :=
        hcj.comp frL.continuous.continuousAt
      have h_smul : Continuous
          (fun c : ℂ => (ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).smulRight c) :=
        (ContinuousLinearMap.smulRightL ℂ (Fin N → ℂ) ℂ
          (ContinuousLinearMap.proj j)).continuous
      exact (h_smul.continuousAt.comp hc_comp).tendsto
    have h_strict := hasStrictFDerivAt_uncurry_coprod (f := fun x y => f' (x, y)) df₁ df₂ cf₁ cf₂
    have hf'_diff : DifferentiableAt ℂ f' p₀ := h_strict.hasFDerivAt.differentiableAt
    have hf_eq : f = f' ∘ toL := by
      ext z
      dsimp [f', toL, frL]
      rw [osgoodSplit_from_to]
    rw [hf_eq]
    exact (hf'_diff.comp z₀ toL.differentiableAt).differentiableWithinAt

def FlatStrip (N : ℕ) (α : ℝ) (m : Fin N) : Set (Fin N → ℂ) :=
  { z | |(z m).im| < α ∧ ∀ j : Fin N, j ≠ m → (z j).im = 0 }

def Octahedron (N : ℕ) (α : ℝ) : Set (Fin N → ℝ) :=
  { y | ∑ m : Fin N, |y m| < α }

lemma isOpen_Octahedron (N : ℕ) (α : ℝ) : IsOpen (Octahedron N α) := by
  have h_cont : Continuous (fun y : Fin N → ℝ => ∑ m : Fin N, |y m|) :=
    continuous_finsetSum Finset.univ fun m _ => (continuous_apply m).abs
  exact isOpen_Iio.preimage h_cont

lemma convex_Octahedron (N : ℕ) (α : ℝ) : Convex ℝ (Octahedron N α) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  change ∑ m : Fin N, |a * y₁ m + b * y₂ m| < α
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_add] at hab
    subst hab
    simpa [Octahedron] using hy₂
  · calc ∑ m : Fin N, |a * y₁ m + b * y₂ m|
        ≤ ∑ m : Fin N, (a * |y₁ m| + b * |y₂ m|) := by
          refine Finset.sum_le_sum fun m _ => ?_
          calc |a * y₁ m + b * y₂ m|
              ≤ |a * y₁ m| + |b * y₂ m| := abs_add_le _ _
            _ = a * |y₁ m| + b * |y₂ m| := by
                rw [abs_mul, abs_mul, abs_of_pos ha_pos, abs_of_nonneg hb]
      _ = a * (∑ m : Fin N, |y₁ m|) + b * (∑ m : Fin N, |y₂ m|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ < a * α + b * α := by
          have h1 : a * (∑ m : Fin N, |y₁ m|) < a * α := mul_lt_mul_of_pos_left hy₁ ha_pos
          have h2 : b * (∑ m : Fin N, |y₂ m|) ≤ b * α := mul_le_mul_of_nonneg_left hy₂.le hb
          linarith
      _ = α := by linear_combination α * hab

noncomputable def fourierTransformND {N : ℕ} (φ : (Fin N → ℝ) → ℂ) (ξ : Fin N → ℝ) : ℂ :=
  ∫ x : Fin N → ℝ, φ x * Complex.exp (-I * ∑ j : Fin N, (x j : ℂ) * (ξ j : ℂ))

open Real FiniteDimensional VectorFourier in
lemma fourier_inversion_nd {N : ℕ} (φ : (Fin N → ℝ) → ℂ) (x₀ : Fin N → ℝ)
    (hφ_cont : Continuous φ) (hφ_int : Integrable φ volume)
    (hφ_hat_int : Integrable (fourierTransformND φ) volume) :
    ((2 * Real.pi)⁻¹ : ℂ) ^ N *
      (∫ ξ : Fin N → ℝ, fourierTransformND φ ξ *
        Complex.exp (I * ∑ j : Fin N, (x₀ j : ℂ) * (ξ j : ℂ))) = φ x₀ := by
  let f : EuclideanSpace ℝ (Fin N) → ℂ := fun v => φ v
  have h_euc_int_iff : ∀ g : (Fin N → ℝ) → ℂ,
      Integrable (fun v : EuclideanSpace ℝ (Fin N) => g v) volume ↔ Integrable g volume :=
    fun g =>
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin N)).integrable_comp_emb
        (MeasurableEquiv.measurableEmbedding _)
  have h_euc_int_eq : ∀ g : (Fin N → ℝ) → ℂ,
      ∫ v : EuclideanSpace ℝ (Fin N), g v = ∫ x : Fin N → ℝ, g x :=
    fun g => (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin N)).integral_comp' g
  have h_F_eq : ∀ w : EuclideanSpace ℝ (Fin N),
      𝓕 f w = fourierTransformND φ (((2 * Real.pi) • w : EuclideanSpace ℝ (Fin N))) := by
    intro w
    rw [fourier_eq']
    dsimp [fourierTransformND, f]
    rw [← h_euc_int_eq]
    congr 1
    ext v
    rw [mul_comm]
    congr 1
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    have h_arg : (↑(-2 * Real.pi * ∑ x : Fin N, w.ofLp x * v.ofLp x) : ℂ) * I =
        -I * ∑ j : Fin N, (v.ofLp j : ℂ) *
          (((2 * Real.pi) • w : EuclideanSpace ℝ (Fin N)).ofLp j : ℂ) := by
      change (↑(-2 * Real.pi * ∑ x : Fin N, w.ofLp x * v.ofLp x) : ℂ) * I =
        -I * ∑ j : Fin N, (v.ofLp j : ℂ) * (((2 * Real.pi) * w.ofLp j : ℝ) : ℂ)
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
        Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    exact h_arg
  have hf_cont : Continuous f := hφ_cont.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ => ℝ))
  have hf_int : Integrable f volume := (h_euc_int_iff φ).2 hφ_int
  have h_2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h_F_int : Integrable (𝓕 f) volume := by
    have h1 : Integrable
        (fun ξ : EuclideanSpace ℝ (Fin N) => fourierTransformND φ ξ) volume :=
      (h_euc_int_iff (fourierTransformND φ)).2 hφ_hat_int
    have h2 : Integrable (fun w : EuclideanSpace ℝ (Fin N) =>
        fourierTransformND φ (((2 * Real.pi) • w : EuclideanSpace ℝ (Fin N)))) volume :=
      h1.comp_smul h_2pi_ne
    have h_fn : 𝓕 f = fun w : EuclideanSpace ℝ (Fin N) =>
        fourierTransformND φ (((2 * Real.pi) • w : EuclideanSpace ℝ (Fin N))) :=
      funext h_F_eq
    rwa [h_fn]
  have h_inv_at := congr_fun (Continuous.fourierInv_fourier_eq hf_cont hf_int h_F_int)
    (WithLp.toLp 2 x₀)
  change _ = f (WithLp.toLp 2 x₀)
  rw [← h_inv_at, fourierInv_eq]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  let H_fin : (Fin N → ℝ) → ℂ := fun ξ =>
    fourierTransformND φ ξ * Complex.exp (I * ∑ j : Fin N, (x₀ j : ℂ) * (ξ j : ℂ))
  let H : EuclideanSpace ℝ (Fin N) → ℂ := fun ξ => H_fin ξ
  have h_int_H : (∫ w : EuclideanSpace ℝ (Fin N),
      Complex.exp (↑(2 * Real.pi * ⟪w, WithLp.toLp 2 x₀⟫) * I) * 𝓕 f w) =
      ∫ w : EuclideanSpace ℝ (Fin N), H ((2 * Real.pi) • w) := by
    congr 1
    ext w
    rw [h_F_eq w]
    dsimp [H, H_fin]
    rw [mul_comm]
    congr 1
    congr 1
    change (↑(2 * Real.pi * ⟪w, WithLp.toLp 2 x₀⟫) : ℂ) * I =
      I * ∑ j : Fin N, (x₀ j : ℂ) * (((2 * Real.pi) * w.ofLp j : ℝ) : ℂ)
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Complex.ofReal_mul,
      Complex.ofReal_ofNat, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h_int_H]
  have hR : 0 ≤ 2 * Real.pi := by positivity
  have h_smul := Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))) H (2 * Real.pi) (hR := hR)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := by simp
  rw [hdim] at h_smul
  rw [h_smul, h_euc_int_eq H_fin]
  simp only [Complex.real_smul, inv_pow, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rfl

noncomputable def mzGaussianDamped {N : ℕ} (f₀ : (Fin N → ℝ) → ℂ) (ε : ℝ)
    (x : Fin N → ℝ) : ℂ :=
  f₀ x * Complex.exp (-↑ε * ∑ j : Fin N, (x j : ℂ) ^ 2)

lemma norm_mzGaussianKernel {N : ℕ} (ε : ℝ) (z : Fin N → ℂ) :
    ‖Complex.exp (-↑ε * ∑ j : Fin N, (z j) ^ 2)‖ =
      Real.exp (-ε * ∑ j : Fin N, (z j).re ^ 2) *
        Real.exp (ε * ∑ j : Fin N, (z j).im ^ 2) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  congr 1
  have h_re : (-↑ε * ∑ j : Fin N, (z j) ^ 2).re =
      -ε * ∑ j : Fin N, ((z j) ^ 2).re := by
    rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, neg_mul, Complex.re_sum]
  rw [h_re]
  have h_sq : ∀ j : Fin N, ((z j) ^ 2).re = (z j).re ^ 2 - (z j).im ^ 2 := by
    intro j
    rw [sq, Complex.mul_re, sq, sq]
  simp_rw [h_sq, Finset.sum_sub_distrib]
  ring

lemma integrable_mzGaussian_real (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : Fin N → ℝ => ∏ j : Fin N, Real.exp (-ε * (x j) ^ 2)) volume :=
  Integrable.fintype_prod (f := fun _ : Fin N => fun t : ℝ => Real.exp (-ε * t ^ 2))
    (fun _ => integrable_exp_neg_mul_sq hε)

lemma integrable_exp_neg_abs_sum (N : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : Fin N → ℝ => Real.exp (-c * ∑ j : Fin N, |ξ j|)) volume := by
  have h_eq : (fun ξ : Fin N → ℝ => Real.exp (-c * ∑ j : Fin N, |ξ j|)) =
      fun ξ => ∏ j : Fin N, Real.exp (-c * |ξ j|) := by
    ext ξ
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [h_eq]
  exact Integrable.fintype_prod (f := fun _ : Fin N => fun t : ℝ => Real.exp (-c * |t|))
    (fun _ => Bochner.integrable_exp_neg_abs hc)

lemma integrable_exp_neg_abs_sum_mul_abs (N : ℕ) (m : Fin N) {c : ℝ} (hc : 0 < c) :
    Integrable (fun ξ : Fin N → ℝ => Real.exp (-c * ∑ j : Fin N, |ξ j|) * |ξ m|) volume := by
  have hc2 : 0 < c / 2 := half_pos hc
  have h_dom : Integrable
      (fun ξ : Fin N → ℝ => (2 / c + 1) * Real.exp (-(c / 2) * ∑ j : Fin N, |ξ j|)) volume :=
    (integrable_exp_neg_abs_sum N hc2).const_mul (2 / c + 1)
  have h_cont : Continuous
      (fun ξ : Fin N → ℝ => Real.exp (-c * ∑ j : Fin N, |ξ j|) * |ξ m|) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_finsetSum Finset.univ fun j _ =>
        (continuous_apply j).abs))).mul (continuous_apply m).abs
  refine h_dom.mono' h_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have h_nn : 0 ≤ Real.exp (-c * ∑ j : Fin N, |ξ j|) * |ξ m| := by positivity
  rw [Real.norm_of_nonneg h_nn]
  have h_poly : |ξ m| ≤ (2 / c + 1) * Real.exp (c / 2 * |ξ m|) := by
    have hp := Bochner.poly_le_exp_half c hc (ξ m)
    linarith
  have h_le_sum : |ξ m| ≤ ∑ j : Fin N, |ξ j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (ξ j)) (Finset.mem_univ m)
  have h_exp_le : Real.exp (c / 2 * |ξ m|) ≤ Real.exp (c / 2 * ∑ j : Fin N, |ξ j|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_le_sum hc2.le)
  calc Real.exp (-c * ∑ j : Fin N, |ξ j|) * |ξ m|
      ≤ Real.exp (-c * ∑ j : Fin N, |ξ j|) *
          ((2 / c + 1) * Real.exp (c / 2 * ∑ j : Fin N, |ξ j|)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact h_poly.trans (mul_le_mul_of_nonneg_left h_exp_le (by positivity))
    _ = (2 / c + 1) *
          (Real.exp (-c * ∑ j : Fin N, |ξ j|) * Real.exp (c / 2 * ∑ j : Fin N, |ξ j|)) := by ring
    _ = (2 / c + 1) * Real.exp (-(c / 2) * ∑ j : Fin N, |ξ j|) := by
        rw [← Real.exp_add]
        congr 2
        ring

lemma integrable_mzGaussianDamped {N : ℕ} {f₀ : (Fin N → ℝ) → ℂ} {M ε : ℝ}
    (_hM : 0 ≤ M) (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M) (hε : 0 < ε) :
    Integrable (mzGaussianDamped f₀ ε) volume := by
  have h_dom : Integrable
      (fun x : Fin N → ℝ => M * ∏ j : Fin N, Real.exp (-ε * (x j) ^ 2)) volume :=
    (integrable_mzGaussian_real N hε).const_mul M
  have h_cont : Continuous (mzGaussianDamped f₀ ε) := by
    refine hf₀_cont.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
    exact continuous_finsetSum Finset.univ fun j _ =>
      (Complex.continuous_ofReal.comp (continuous_apply j)).pow 2
  refine h_dom.mono' h_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  dsimp [mzGaussianDamped]
  rw [norm_mul, norm_mzGaussianKernel]
  have h_im0 : (∑ j : Fin N, ((x j : ℂ)).im ^ 2) = 0 := by simp
  have h_re_eq : (∑ j : Fin N, ((x j : ℂ)).re ^ 2) = ∑ j : Fin N, (x j) ^ 2 := by simp
  rw [h_im0, mul_zero, Real.exp_zero, mul_one, h_re_eq]
  have h_prod : Real.exp (-ε * ∑ j : Fin N, (x j) ^ 2) =
      ∏ j : Fin N, Real.exp (-ε * (x j) ^ 2) := by
    rw [← Real.exp_sum, Finset.mul_sum]
  rw [h_prod]
  exact mul_le_mul_of_nonneg_right (hf₀_bdd x)
    (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

lemma mz_fourier_bound_coord {n : ℕ} {α M : ℝ} (_hα : 0 < α) (hM : 0 ≤ M)
    {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (_hf₀_cont : Continuous f₀) (_hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m))
    (h_bdd_br : ∀ (m : Fin (n + 1)), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ),
      DifferentiableOn ℂ (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w))
        { w : ℂ | |w.im| < α })
    {ε β : ℝ} (hε : 0 < ε) (hβ_pos : 0 < β) (hβ_lt : β < α)
    (m : Fin (n + 1)) (ξ : Fin (n + 1) → ℝ) :
    ‖fourierTransformND (mzGaussianDamped f₀ ε) ξ‖ ≤
      (M * Real.exp (ε * β ^ 2) *
        ∫ x : Fin (n + 1) → ℝ, ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2)) *
        Real.exp (-β * |ξ m|) := by
  classical
  let b : ℝ := if 0 ≤ ξ m then -β else β
  have hb_abs : |b| = β := by
    dsimp [b]
    split_ifs <;> simp [abs_of_pos hβ_pos]
  have hb_lt : |b| < α := by rwa [hb_abs]
  have hb_xi : b * ξ m = -β * |ξ m| := by
    dsimp [b]
    split_ifs with hxi
    · rw [abs_of_nonneg hxi]
    · push Not at hxi
      rw [abs_of_neg hxi]; ring
  let z_sh : (Fin (n + 1) → ℝ) → ℝ → (Fin (n + 1) → ℂ) := fun x y =>
    Function.update (fun j => (x j : ℂ)) m ((x m : ℂ) + I * (y : ℂ))
  let G_y : ℝ → (Fin (n + 1) → ℝ) → ℂ := fun y x =>
    f_br m (z_sh x y) *
      Complex.exp (-↑ε * ∑ j : Fin (n + 1), (z_sh x y j) ^ 2) *
      Complex.exp (-I * ∑ j : Fin (n + 1), (z_sh x y j) * (ξ j : ℂ))
  have hz_sh_mem : ∀ (x : Fin (n + 1) → ℝ) {y : ℝ}, |y| < α →
      z_sh x y ∈ FlatStrip (n + 1) α m := by
    intro x y hy
    refine ⟨?_, fun j hj => ?_⟩
    · simp [z_sh, hy]
    · simp [z_sh, hj]
  have hG_norm_le : ∀ {y : ℝ}, |y| ≤ β → ∀ x : Fin (n + 1) → ℝ,
      ‖G_y y x‖ ≤ (M * Real.exp (ε * β ^ 2) * Real.exp (y * ξ m)) *
        ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2) := by
    intro y hy x
    have hy_lt : |y| < α := lt_of_le_of_lt hy hβ_lt
    dsimp [G_y]
    rw [norm_mul, norm_mul, norm_mzGaussianKernel, Complex.norm_exp]
    have hf_le : ‖f_br m (z_sh x y)‖ ≤ M := h_bdd_br m _ (hz_sh_mem x hy_lt)
    have h_re_sum : (∑ j : Fin (n + 1), (z_sh x y j).re ^ 2) = ∑ j : Fin (n + 1), (x j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjm : j = m
      · subst hjm; simp [z_sh]
      · simp [z_sh, hjm]
    have h_im_sum : (∑ j : Fin (n + 1), (z_sh x y j).im ^ 2) = y ^ 2 := by
      rw [Finset.sum_eq_single m]
      · simp [z_sh]
      · intro j _ hjm; simp [z_sh, hjm]
      · intro hm; exact (hm (Finset.mem_univ m)).elim
    have h_phase_re : (-I * ∑ j : Fin (n + 1), z_sh x y j * (ξ j : ℂ)).re = y * ξ m := by
      rw [Finset.mul_sum, Complex.re_sum, Finset.sum_eq_single m]
      · simp [z_sh]
      · intro j _ hjm
        simp [z_sh, hjm]
      · intro hm; exact (hm (Finset.mem_univ m)).elim
    rw [h_re_sum, h_im_sum, h_phase_re]
    have h_prod : Real.exp (-ε * ∑ j : Fin (n + 1), (x j) ^ 2) =
        ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    rw [h_prod]
    have hy_sq : y ^ 2 ≤ β ^ 2 := by
      have := mul_le_mul hy hy (abs_nonneg y) hβ_pos.le
      rwa [← sq, ← sq, sq_abs] at this
    have hexp_im : Real.exp (ε * y ^ 2) ≤ Real.exp (ε * β ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy_sq hε.le)
    calc ‖f_br m (z_sh x y)‖ *
          ((∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2)) * Real.exp (ε * y ^ 2)) *
          Real.exp (y * ξ m)
        = (‖f_br m (z_sh x y)‖ * Real.exp (ε * y ^ 2) * Real.exp (y * ξ m)) *
            ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2) := by ring
      _ ≤ (M * Real.exp (ε * β ^ 2) * Real.exp (y * ξ m)) *
            ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_
            (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul hf_le hexp_im (Real.exp_pos _).le hM
  have hG_int : ∀ {y : ℝ}, |y| ≤ β → Integrable (G_y y) volume := by
    intro y hy
    have hy_lt : |y| < α := lt_of_le_of_lt hy hβ_lt
    have hz_cont : Continuous (fun x : Fin (n + 1) → ℝ => z_sh x y) := by
      refine continuous_pi fun j => ?_
      by_cases hjm : j = m
      · subst hjm
        simp only [z_sh, Function.update_self]
        exact (Complex.continuous_ofReal.comp (continuous_apply j)).add continuous_const
      · simp only [z_sh, Function.update_of_ne hjm]
        exact Complex.continuous_ofReal.comp (continuous_apply j)
    have h_cont : Continuous (G_y y) := by
      refine Continuous.mul
        (Continuous.mul ((h_cont_br m).comp_continuous hz_cont (fun x => hz_sh_mem x hy_lt)) ?_) ?_
      · refine Complex.continuous_exp.comp (continuous_const.mul ?_)
        exact continuous_finsetSum Finset.univ fun j _ =>
          ((continuous_apply j).comp hz_cont).pow 2
      · refine Complex.continuous_exp.comp (continuous_const.mul ?_)
        exact continuous_finsetSum Finset.univ fun j _ =>
          ((continuous_apply j).comp hz_cont).mul continuous_const
    refine ((integrable_mzGaussian_real (n + 1) hε).const_mul
      (M * Real.exp (ε * β ^ 2) * Real.exp (y * ξ m))).mono'
      h_cont.aestronglyMeasurable (Filter.Eventually.of_forall (hG_norm_le hy))
  have hG0_eq : fourierTransformND (mzGaussianDamped f₀ ε) ξ = ∫ x, G_y 0 x := by
    dsimp [fourierTransformND, mzGaussianDamped, G_y]
    congr 1
    ext x
    have hz0 : z_sh x 0 = fun j => (x j : ℂ) := by
      ext j
      by_cases hjm : j = m
      · subst hjm; simp [z_sh]
      · simp [z_sh, hjm]
    rw [hz0, h_real m x, mul_assoc]
  let mp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) m).symm
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) m).symm
  have he_upd : ∀ (s : ℝ) (x' : Fin n → ℝ), e (s, x') = Function.update (e (0, x')) m s := by
    intro s x'
    ext j
    by_cases hjm : j = m
    · subst hjm
      simp [e, MeasurableEquiv.piFinSuccAbove]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hjm
      simp [e, MeasurableEquiv.piFinSuccAbove, Fin.succAbove_ne]
  have h_shift_eq : ∫ x, G_y 0 x = ∫ x, G_y b x := by
    have h0_int : Integrable (fun p : ℝ × (Fin n → ℝ) => G_y 0 (e p)) (volume.prod volume) :=
      (mp.integrable_comp_emb e.measurableEmbedding).mpr (hG_int (by simp [hβ_pos.le]))
    have hb_int : Integrable (fun p : ℝ × (Fin n → ℝ) => G_y b (e p)) (volume.prod volume) :=
      (mp.integrable_comp_emb e.measurableEmbedding).mpr (hG_int (by rw [hb_abs]))
    rw [← mp.integral_comp' (G_y 0), ← mp.integral_comp' (G_y b)]
    change (∫ p : ℝ × (Fin n → ℝ), G_y 0 (e p) ∂(volume.prod volume)) =
      ∫ p : ℝ × (Fin n → ℝ), G_y b (e p) ∂(volume.prod volume)
    rw [MeasureTheory.integral_prod _ h0_int, MeasureTheory.integral_prod _ hb_int,
      MeasureTheory.integral_integral_swap (f := fun s x' => G_y 0 (e (s, x'))) h0_int,
      MeasureTheory.integral_integral_swap (f := fun s x' => G_y b (e (s, x'))) hb_int]
    congr 1
    ext x'
    let x₀ : Fin (n + 1) → ℝ := e (0, x')
    let g_sl : ℂ → ℂ := fun w =>
      f_br m (Function.update (fun j => (x₀ j : ℂ)) m w) *
        Complex.exp (-↑ε * ∑ j : Fin (n + 1),
          (Function.update (fun j => (x₀ j : ℂ)) m w j) ^ 2) *
        Complex.exp (-I * ∑ j : Fin (n + 1),
          (Function.update (fun j => (x₀ j : ℂ)) m w j) * (ξ j : ℂ))
    have h_sl_eq : ∀ y : ℝ, ∀ s : ℝ, G_y y (e (s, x')) = g_sl (↑s + I * ↑y) := by
      intro y s
      dsimp [G_y, g_sl, z_sh]
      have h_u : Function.update (fun j => (e (s, x') j : ℂ)) m (↑(e (s, x') m) + I * ↑y) =
          Function.update (fun j => (x₀ j : ℂ)) m (↑s + I * ↑y) := by
        rw [he_upd s x']
        ext j
        by_cases hjm : j = m
        · subst hjm; simp
        · simp [hjm, x₀]
      rw [h_u]
    simp_rw [h_sl_eq 0, h_sl_eq b]
    have huIcc_sub : ∀ w : ℂ, w.im ∈ uIcc 0 b → |w.im| ≤ β := by
      intro w hw
      rw [uIcc] at hw
      rw [abs_le]
      have hb_le : -β ≤ b ∧ b ≤ β := abs_le.mp (le_of_eq hb_abs)
      exact ⟨(le_min (by linarith) hb_le.1).trans hw.1, hw.2.trans (max_le hβ_pos.le hb_le.2)⟩
    have hg_holo : DifferentiableOn ℂ g_sl {w : ℂ | w.im ∈ uIcc 0 b} := by
      have h_sub : {w : ℂ | w.im ∈ uIcc 0 b} ⊆ {w : ℂ | |w.im| < α} :=
        fun w hw => lt_of_le_of_lt (huIcc_sub w hw) hβ_lt
      have h_upd_diff : Differentiable ℂ
          (fun w : ℂ => Function.update (fun j => (x₀ j : ℂ)) m w) := by
        refine differentiable_pi.mpr fun j => ?_
        by_cases hjm : j = m
        · subst hjm; simp only [Function.update_self]; exact differentiable_id
        · simp only [Function.update_of_ne hjm]; exact differentiable_const _
      refine (((h_holo_br m x₀).mono h_sub).mul ?_).mul ?_
      · refine (Complex.differentiable_exp.comp (differentiable_const _ |>.mul ?_)).differentiableOn
        exact Differentiable.fun_sum fun j _ => ((differentiable_apply j).comp h_upd_diff).pow 2
      · refine (Complex.differentiable_exp.comp (differentiable_const _ |>.mul ?_)).differentiableOn
        exact Differentiable.fun_sum fun j _ =>
          ((differentiable_apply j).comp h_upd_diff).mul (differentiable_const _)
    have hg_bd : ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc 0 b → ‖g_sl w‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
      let K_xi := Real.exp (β * |ξ m|)
      refine ⟨M * Real.exp (ε * β ^ 2) * K_xi, fun w hw => ?_⟩
      have hw_le : |w.im| ≤ β := huIcc_sub w hw
      have hw_eq : w = ↑w.re + I * ↑w.im := by rw [mul_comm I, Complex.re_add_im]
      have hg_eq : g_sl w = G_y w.im (Function.update x₀ m w.re) := by
        dsimp [G_y, g_sl, z_sh]
        have h_u : Function.update (fun j => (Function.update x₀ m w.re j : ℂ)) m
            (↑(Function.update x₀ m w.re m) + I * ↑w.im) =
            Function.update (fun j => (x₀ j : ℂ)) m w := by
          ext j
          by_cases hjm : j = m
          · subst hjm; simp [← hw_eq]
          · simp [hjm]
        rw [h_u]
      rw [hg_eq]
      have h1 := hG_norm_le hw_le (Function.update x₀ m w.re)
      have h_prod_le : (∏ j : Fin (n + 1), Real.exp (-ε * (Function.update x₀ m w.re j) ^ 2)) ≤
          Real.exp (-ε * w.re ^ 2) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m)]
        simp only [Function.update_self]
        refine mul_le_of_le_one_right (Real.exp_pos _).le ?_
        refine Finset.prod_le_one (fun j _ => (Real.exp_pos _).le) fun j _ => ?_
        rw [Real.exp_le_one_iff]
        have : 0 ≤ (Function.update x₀ m w.re j) ^ 2 := sq_nonneg _
        nlinarith
      have h_xi_le : Real.exp (w.im * ξ m) ≤ K_xi := by
        apply Real.exp_le_exp.mpr
        calc w.im * ξ m ≤ |w.im * ξ m| := le_abs_self _
          _ = |w.im| * |ξ m| := abs_mul _ _
          _ ≤ β * |ξ m| := mul_le_mul_of_nonneg_right hw_le (abs_nonneg _)
      calc ‖G_y w.im (Function.update x₀ m w.re)‖
          ≤ (M * Real.exp (ε * β ^ 2) * Real.exp (w.im * ξ m)) *
              ∏ j : Fin (n + 1), Real.exp (-ε * (Function.update x₀ m w.re j) ^ 2) := h1
        _ ≤ (M * Real.exp (ε * β ^ 2) * K_xi) * Real.exp (-ε * w.re ^ 2) := by
            refine mul_le_mul ?_ h_prod_le
              (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le) (by positivity)
            exact mul_le_mul_of_nonneg_left h_xi_le (by positivity)
    exact Bochner.fourier_shift_1d_eps_uIcc 0 b ε hε g_sl hg_holo hg_bd
  rw [hG0_eq, h_shift_eq]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  have h_int_bd : ∫ x, ‖G_y b x‖ ≤
      ∫ x : Fin (n + 1) → ℝ,
        (M * Real.exp (ε * β ^ 2) * Real.exp (b * ξ m)) *
          ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      ((integrable_mzGaussian_real (n + 1) hε).const_mul _)
      (Filter.Eventually.of_forall (hG_norm_le (le_of_eq hb_abs)))
  refine h_int_bd.trans ?_
  rw [MeasureTheory.integral_const_mul, hb_xi]
  exact le_of_eq (by ring)

lemma mz_fourier_phase_domination {n : ℕ} {α : ℝ}
    {C_β β δ : ℝ} (hC_nn : 0 ≤ C_β) (hδ_pos : 0 < δ)
    {g_hat : (Fin (n + 1) → ℝ) → ℂ}
    (h_coord : ∀ (m : Fin (n + 1)) (ξ : Fin (n + 1) → ℝ),
      ‖g_hat ξ‖ ≤ C_β * Real.exp (-β * |ξ m|))
    {w : Fin (n + 1) → ℂ}
    (hw_sum : ∑ m : Fin (n + 1), |(w m).im| ≤ β - ((n + 1 : ℕ) : ℝ) * δ)
    (_hα : 0 < α) (ξ : Fin (n + 1) → ℝ) :
    ‖g_hat ξ * Complex.exp (I * ∑ m : Fin (n + 1), w m * (ξ m : ℂ))‖ ≤
      C_β * Real.exp (-δ * ∑ m : Fin (n + 1), |ξ m|) := by
  obtain ⟨m₀, _, hm₀_max⟩ :=
    Finset.exists_max_image Finset.univ (fun m : Fin (n + 1) => |ξ m|) Finset.univ_nonempty
  rw [norm_mul, Complex.norm_exp]
  have h_re : (I * ∑ m : Fin (n + 1), w m * (ξ m : ℂ)).re =
      -∑ m : Fin (n + 1), (w m).im * ξ m := by
    rw [Finset.mul_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [Complex.mul_re]
  rw [h_re]
  have h_phase_le : -∑ m : Fin (n + 1), (w m).im * ξ m ≤
      (β - ((n + 1 : ℕ) : ℝ) * δ) * |ξ m₀| := by
    calc -∑ m : Fin (n + 1), (w m).im * ξ m
        = ∑ m : Fin (n + 1), (-(w m).im * ξ m) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun m _ => by ring
      _ ≤ ∑ m : Fin (n + 1), |(w m).im| * |ξ m| := by
          refine Finset.sum_le_sum fun m _ => ?_
          calc -(w m).im * ξ m ≤ |-(w m).im * ξ m| := le_abs_self _
            _ = |(w m).im| * |ξ m| := by rw [abs_mul, abs_neg]
      _ ≤ ∑ m : Fin (n + 1), |(w m).im| * |ξ m₀| :=
          Finset.sum_le_sum fun m _ =>
            mul_le_mul_of_nonneg_left (hm₀_max m (Finset.mem_univ m)) (abs_nonneg _)
      _ = (∑ m : Fin (n + 1), |(w m).im|) * |ξ m₀| := (Finset.sum_mul _ _ _).symm
      _ ≤ (β - ((n + 1 : ℕ) : ℝ) * δ) * |ξ m₀| :=
          mul_le_mul_of_nonneg_right hw_sum (abs_nonneg _)
  have h_sum_xi : ∑ m : Fin (n + 1), |ξ m| ≤ ((n + 1 : ℕ) : ℝ) * |ξ m₀| := by
    calc ∑ m : Fin (n + 1), |ξ m|
        ≤ ∑ _m : Fin (n + 1), |ξ m₀| :=
          Finset.sum_le_sum fun m _ => hm₀_max m (Finset.mem_univ m)
      _ = ((n + 1 : ℕ) : ℝ) * |ξ m₀| := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_exp_le : Real.exp (-β * |ξ m₀|) * Real.exp (-∑ m : Fin (n + 1), (w m).im * ξ m) ≤
      Real.exp (-δ * ∑ m : Fin (n + 1), |ξ m|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -β * |ξ m₀| + (-∑ m : Fin (n + 1), (w m).im * ξ m) ≤
        -(((n + 1 : ℕ) : ℝ) * δ * |ξ m₀|) := by linarith
    have h2 : δ * ∑ m : Fin (n + 1), |ξ m| ≤ δ * (((n + 1 : ℕ) : ℝ) * |ξ m₀|) :=
      mul_le_mul_of_nonneg_left h_sum_xi hδ_pos.le
    linarith
  calc ‖g_hat ξ‖ * Real.exp (-∑ m : Fin (n + 1), (w m).im * ξ m)
      ≤ (C_β * Real.exp (-β * |ξ m₀|)) * Real.exp (-∑ m : Fin (n + 1), (w m).im * ξ m) :=
        mul_le_mul_of_nonneg_right (h_coord m₀ ξ) (Real.exp_pos _).le
    _ = C_β * (Real.exp (-β * |ξ m₀|) * Real.exp (-∑ m : Fin (n + 1), (w m).im * ξ m)) := by ring
    _ ≤ C_β * Real.exp (-δ * ∑ m : Fin (n + 1), |ξ m|) :=
        mul_le_mul_of_nonneg_left h_exp_le hC_nn

noncomputable def mzFEps {N : ℕ} (f₀ : (Fin N → ℝ) → ℂ) (ε : ℝ) (z : Fin N → ℂ) : ℂ :=
  ((2 * Real.pi)⁻¹ : ℂ) ^ N *
    ∫ ξ : Fin N → ℝ, fourierTransformND (mzGaussianDamped f₀ ε) ξ *
      Complex.exp (I * ∑ j : Fin N, z j * (ξ j : ℂ))

lemma continuous_fourierTransformND_of_integrable {N : ℕ} {φ : (Fin N → ℝ) → ℂ}
    (hφ : Integrable φ volume) :
    Continuous (fourierTransformND φ) := by
  unfold fourierTransformND
  refine MeasureTheory.continuous_of_dominated
    (bound := fun x => ‖φ x‖)
    (fun ξ => ?_) (fun ξ => Filter.Eventually.of_forall fun x => ?_) hφ.norm
    (Filter.Eventually.of_forall fun x => ?_)
  · refine hφ.aestronglyMeasurable.mul ?_
    refine (Complex.continuous_exp.comp (continuous_const.mul ?_)).aestronglyMeasurable
    exact continuous_finsetSum Finset.univ fun j _ =>
      (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const
  · rw [norm_mul, Complex.norm_exp]
    have h_re : (-I * ∑ j : Fin N, (x j : ℂ) * (ξ j : ℂ)).re = 0 := by
      rw [Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_eq_zero fun j _ => by simp
    rw [h_re, Real.exp_zero, mul_one]
  · refine continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
    exact continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))

lemma mzFEps_holomorphic {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m))
    (h_bdd_br : ∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
      (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α})
    {ε : ℝ} (hε : 0 < ε) :
    DifferentiableOn ℂ (mzFEps f₀ ε) (TubeDomain (Octahedron (n + 1) α)) := by
  let g_hat := fourierTransformND (mzGaussianDamped f₀ ε)
  have hg_cont : Continuous g_hat :=
    continuous_fourierTransformND_of_integrable
      (integrable_mzGaussianDamped hM hf₀_cont hf₀_bdd hε)
  have hU_open : IsOpen (TubeDomain (Octahedron (n + 1) α)) :=
    isOpen_TubeDomain (isOpen_Octahedron (n + 1) α)
  have h_loc_setup : ∀ z₀ ∈ TubeDomain (Octahedron (n + 1) α),
      ∃ (C_β δ η : ℝ), 0 ≤ C_β ∧ 0 < δ ∧ 0 < η ∧
        Metric.ball z₀ η ⊆ TubeDomain (Octahedron (n + 1) α) ∧
        ∀ w ∈ Metric.ball z₀ η, ∀ ξ : Fin (n + 1) → ℝ,
          ‖g_hat ξ * Complex.exp (I * ∑ j : Fin (n + 1), w j * (ξ j : ℂ))‖ ≤
            C_β * Real.exp (-δ * ∑ j : Fin (n + 1), |ξ j|) := by
    intro z₀ hz₀
    let S_y : ℝ := ∑ m : Fin (n + 1), |(z₀ m).im|
    have hSy_lt : S_y < α := hz₀
    have hSy_nn : 0 ≤ S_y := Finset.sum_nonneg fun m _ => abs_nonneg _
    let β : ℝ := (S_y + α) / 2
    have hβ_pos : 0 < β := by dsimp [β]; linarith
    have hβ_lt : β < α := by dsimp [β]; linarith
    have hSy_lt_β : S_y < β := by dsimp [β]; linarith
    have hN_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    let δ : ℝ := (β - S_y) / (2 * ((n + 1 : ℕ) : ℝ))
    have hδ_pos : 0 < δ := div_pos (sub_pos.mpr hSy_lt_β) (mul_pos two_pos hN_pos)
    let C_β : ℝ := M * Real.exp (ε * β ^ 2) *
      ∫ x : Fin (n + 1) → ℝ, ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2)
    have hC_nn : 0 ≤ C_β :=
      mul_nonneg (mul_nonneg hM (Real.exp_pos _).le)
        (integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
    have h_coord : ∀ m ξ, ‖g_hat ξ‖ ≤ C_β * Real.exp (-β * |ξ m|) :=
      fun m ξ => mz_fourier_bound_coord hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
        h_holo_br hε hβ_pos hβ_lt m ξ
    have hw_sum_of_ball : ∀ w ∈ Metric.ball z₀ δ,
        ∑ m : Fin (n + 1), |(w m).im| ≤ β - ((n + 1 : ℕ) : ℝ) * δ := by
      intro w hw
      have hw_dist : ‖w - z₀‖ < δ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      have h_each : ∀ m : Fin (n + 1), |(w m).im| ≤ |(z₀ m).im| + δ := by
        intro m
        have hdm : |(w m).im - (z₀ m).im| ≤ δ := by
          calc |(w m).im - (z₀ m).im| = |(w m - z₀ m).im| := by simp
            _ ≤ ‖w m - z₀ m‖ := Complex.abs_im_le_norm _
            _ ≤ ‖w - z₀‖ := norm_le_pi_norm (w - z₀) m
            _ ≤ δ := hw_dist.le
        linarith [abs_sub_abs_le_abs_sub (w m).im (z₀ m).im]
      calc ∑ m : Fin (n + 1), |(w m).im|
          ≤ ∑ m : Fin (n + 1), (|(z₀ m).im| + δ) := Finset.sum_le_sum fun m _ => h_each m
        _ = S_y + ((n + 1 : ℕ) : ℝ) * δ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
        _ = β - ((n + 1 : ℕ) : ℝ) * δ := by
            dsimp [δ]
            field_simp [hN_pos.ne']
            ring
    have h_sub_tube : Metric.ball z₀ δ ⊆ TubeDomain (Octahedron (n + 1) α) := by
      intro w hw
      change ∑ m : Fin (n + 1), |(w m).im| < α
      have h1 := hw_sum_of_ball w hw
      have h2 : 0 < ((n + 1 : ℕ) : ℝ) * δ := mul_pos hN_pos hδ_pos
      linarith
    refine ⟨C_β, δ, δ, hC_nn, hδ_pos, hδ_pos, h_sub_tube, fun w hw ξ => ?_⟩
    exact mz_fourier_phase_domination hC_nn hδ_pos h_coord (hw_sum_of_ball w hw) hα ξ
  have h_meas_integrand : ∀ w : Fin (n + 1) → ℂ,
      AEStronglyMeasurable
        (fun ξ : Fin (n + 1) → ℝ =>
          g_hat ξ * Complex.exp (I * ∑ j : Fin (n + 1), w j * (ξ j : ℂ))) volume := by
    intro w
    refine (hg_cont.mul
      (Complex.continuous_exp.comp (continuous_const.mul ?_))).aestronglyMeasurable
    exact continuous_finsetSum Finset.univ fun j _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))
  have h_cont : ContinuousOn (mzFEps f₀ ε) (TubeDomain (Octahedron (n + 1) α)) := by
    intro z₀ hz₀
    rcases h_loc_setup z₀ hz₀ with ⟨C_β, δ, η, _hC_nn, hδ_pos, hη_pos, _h_sub, h_bd⟩
    have h_cont_ball : ContinuousOn (mzFEps f₀ ε) (Metric.ball z₀ η) := by
      refine continuousOn_const.mul ?_
      refine MeasureTheory.continuousOn_of_dominated
        (bound := fun ξ => C_β * Real.exp (-δ * ∑ j : Fin (n + 1), |ξ j|))
        (fun w _ => h_meas_integrand w)
        (fun w hw => Filter.Eventually.of_forall (h_bd w hw))
        ((integrable_exp_neg_abs_sum (n + 1) hδ_pos).const_mul C_β)
        (Filter.Eventually.of_forall fun ξ => ?_)
      refine continuousOn_const.mul
        ((Complex.continuous_exp.comp (continuous_const.mul ?_)).continuousOn)
      exact continuous_finsetSum Finset.univ fun j _ =>
        (continuous_apply j).mul continuous_const
    exact (h_cont_ball.continuousAt (Metric.ball_mem_nhds z₀ hη_pos)).continuousWithinAt
  refine osgood_nd (n + 1) hU_open (mzFEps f₀ ε) h_cont ?_
  intro z₀ hz₀ m
  rcases h_loc_setup z₀ hz₀ with ⟨C_β, δ, η, _hC_nn, hδ_pos, hη_pos, _h_sub, h_bd⟩
  let F_sl : ℂ → (Fin (n + 1) → ℝ) → ℂ := fun u ξ =>
    g_hat ξ * Complex.exp (I * ∑ j : Fin (n + 1), Function.update z₀ m u j * (ξ j : ℂ))
  let F_sl' : ℂ → (Fin (n + 1) → ℝ) → ℂ := fun u ξ =>
    g_hat ξ * (Complex.exp (I * ∑ j : Fin (n + 1), Function.update z₀ m u j * (ξ j : ℂ)) *
      (I * (ξ m : ℂ)))
  have h_upd_ball : ∀ u ∈ Metric.ball (z₀ m) η, Function.update z₀ m u ∈ Metric.ball z₀ η := by
    intro u hu
    rw [Metric.mem_ball] at hu ⊢
    refine (dist_pi_lt_iff hη_pos).mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm; simpa using hu
    · simp [hjm, hη_pos]
  have h_hasDeriv : ∀ (ξ : Fin (n + 1) → ℝ) (u : ℂ),
      HasDerivAt (fun u' => F_sl u' ξ) (F_sl' u ξ) u := by
    intro ξ u
    dsimp [F_sl, F_sl']
    have h_sum_der : HasDerivAt
        (fun u' : ℂ => I * ∑ j : Fin (n + 1), Function.update z₀ m u' j * (ξ j : ℂ))
        (I * (ξ m : ℂ)) u := by
      have h_s : (fun u' : ℂ => ∑ j : Fin (n + 1), Function.update z₀ m u' j * (ξ j : ℂ)) =
          fun u' => u' * (ξ m : ℂ) +
            ∑ j ∈ Finset.univ.erase m, z₀ j * (ξ j : ℂ) := by
        ext u'
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m)]
        simp only [Function.update_self]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have h_s2 :
          (fun u' : ℂ => I * ∑ j : Fin (n + 1), Function.update z₀ m u' j * (ξ j : ℂ)) =
          fun u' => I * (u' * (ξ m : ℂ) + ∑ j ∈ Finset.univ.erase m, z₀ j * (ξ j : ℂ)) := by
        ext u'
        rw [congr_fun h_s u']
      rw [h_s2]
      have h1 : HasDerivAt
          (fun u' : ℂ => u' * (ξ m : ℂ) + ∑ j ∈ Finset.univ.erase m, z₀ j * (ξ j : ℂ))
          (1 * (ξ m : ℂ) + 0) u :=
        ((hasDerivAt_id u).mul_const (ξ m : ℂ)).add (hasDerivAt_const u _)
      simpa using h1.const_mul I
    exact h_sum_der.cexp.const_mul (g_hat ξ)
  have hF_int0 : Integrable (F_sl (z₀ m)) volume := by
    have hz_self : Function.update z₀ m (z₀ m) = z₀ := Function.update_eq_self m z₀
    refine ((integrable_exp_neg_abs_sum (n + 1) hδ_pos).const_mul C_β).mono'
      (by simpa [F_sl, hz_self] using h_meas_integrand z₀)
      (Filter.Eventually.of_forall fun ξ => ?_)
    simpa [F_sl, hz_self] using h_bd z₀ (Metric.mem_ball_self hη_pos) ξ
  have hF'_meas0 : AEStronglyMeasurable (F_sl' (z₀ m)) volume := by
    have hc_F' : Continuous (F_sl' (z₀ m)) := by
      refine hg_cont.mul ((Complex.continuous_exp.comp (continuous_const.mul ?_)).mul ?_)
      · exact continuous_finsetSum Finset.univ fun j _ =>
          continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))
      · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply m))
    exact hc_F'.aestronglyMeasurable
  have h_int_der := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F_sl) (F' := F_sl')
    (bound := fun ξ => C_β * (Real.exp (-δ * ∑ j : Fin (n + 1), |ξ j|) * |ξ m|))
    (s := Metric.ball (z₀ m) η)
    (Metric.ball_mem_nhds (z₀ m) hη_pos)
    (Filter.Eventually.of_forall fun u => h_meas_integrand (Function.update z₀ m u))
    hF_int0 hF'_meas0
    (Filter.Eventually.of_forall fun ξ u hu => by
      dsimp [F_sl']
      rw [← mul_assoc, norm_mul, norm_mul (I : ℂ), Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (h_bd _ (h_upd_ball u hu) ξ) (abs_nonneg _))
    ((integrable_exp_neg_abs_sum_mul_abs (n + 1) m hδ_pos).const_mul C_β)
    (Filter.Eventually.of_forall fun ξ u _ => h_hasDeriv ξ u)).2
  exact (h_int_der.const_mul (((2 * Real.pi)⁻¹ : ℂ) ^ (n + 1))).differentiableAt

lemma mzFEps_eq_on_flatStrip {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m))
    (h_bdd_br : ∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
      (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α})
    {ε : ℝ} (hε : 0 < ε) (m : Fin (n + 1)) {z : Fin (n + 1) → ℂ}
    (hz : z ∈ FlatStrip (n + 1) α m) :
    mzFEps f₀ ε z = f_br m z * Complex.exp (-↑ε * ∑ j : Fin (n + 1), (z j) ^ 2) := by
  have hg_cont : Continuous (mzGaussianDamped f₀ ε) := by
    refine hf₀_cont.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
    exact continuous_finsetSum Finset.univ fun j _ =>
      (Complex.continuous_ofReal.comp (continuous_apply j)).pow 2
  have hg_int : Integrable (mzGaussianDamped f₀ ε) volume :=
    integrable_mzGaussianDamped hM hf₀_cont hf₀_bdd hε
  have hg_hat_int : Integrable (fourierTransformND (mzGaussianDamped f₀ ε)) volume := by
    let β := α / 2
    have hβ_pos : 0 < β := half_pos hα
    have hβ_lt : β < α := half_lt_self hα
    have hN_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    let δ := β / ((n + 1 : ℕ) : ℝ)
    have hδ_pos : 0 < δ := div_pos hβ_pos hN_pos
    let C_β : ℝ := M * Real.exp (ε * β ^ 2) *
      ∫ x : Fin (n + 1) → ℝ, ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2)
    have hC_nn : 0 ≤ C_β :=
      mul_nonneg (mul_nonneg hM (Real.exp_pos _).le)
        (integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
    have h_coord : ∀ k ξ,
        ‖fourierTransformND (mzGaussianDamped f₀ ε) ξ‖ ≤ C_β * Real.exp (-β * |ξ k|) :=
      fun k ξ => mz_fourier_bound_coord hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
        h_holo_br hε hβ_pos hβ_lt k ξ
    refine ((integrable_exp_neg_abs_sum (n + 1) hδ_pos).const_mul C_β).mono'
      (continuous_fourierTransformND_of_integrable hg_int).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h_rhs0 : β - ((n + 1 : ℕ) : ℝ) * δ = 0 := by
      dsimp [δ]
      field_simp [hN_pos.ne']
      ring
    have h_zero := mz_fourier_phase_domination (w := 0) hC_nn hδ_pos h_coord
      (by rw [h_rhs0]; simp) hα ξ
    simpa using h_zero
  have h_real_eq : ∀ x : Fin (n + 1) → ℝ,
      mzFEps f₀ ε (fun j => (x j : ℂ)) = mzGaussianDamped f₀ ε x :=
    fun x => fourier_inversion_nd (mzGaussianDamped f₀ ε) x hg_cont hg_int hg_hat_int
  let x_re : Fin (n + 1) → ℝ := fun j => (z j).re
  let S_strip : Set ℂ := {w : ℂ | |w.im| < α}
  have hS_open : IsOpen S_strip :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hS_conv : Convex ℝ S_strip := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    simp only [S_strip, Set.mem_setOf_eq, Complex.add_im, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hw₁ hw₂ ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_add] at hab; subst hab; simpa using hw₂
    · calc |a * w₁.im + b * w₂.im|
          ≤ |a * w₁.im| + |b * w₂.im| := abs_add_le _ _
        _ = a * |w₁.im| + b * |w₂.im| := by
            rw [abs_mul, abs_mul, abs_of_pos ha_pos, abs_of_nonneg hb]
        _ < a * α + b * α := by
            have h1 := mul_lt_mul_of_pos_left hw₁ ha_pos
            have h2 := mul_le_mul_of_nonneg_left hw₂.le hb
            linarith
        _ = α := by linear_combination α * hab
  let γ : ℂ → (Fin (n + 1) → ℂ) := fun w => Function.update (fun j => (x_re j : ℂ)) m w
  have hγ_diff : Differentiable ℂ γ := by
    refine differentiable_pi.mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm; simp only [γ, Function.update_self]; exact differentiable_id
    · simp only [γ, Function.update_of_ne hjm]; exact differentiable_const _
  have hγ_maps : Set.MapsTo γ S_strip (TubeDomain (Octahedron (n + 1) α)) := by
    intro w hw
    change |w.im| < α at hw
    change ∑ j : Fin (n + 1), |(γ w j).im| < α
    rw [Finset.sum_eq_single m]
    · simpa [γ] using hw
    · intro j _ hjm; simp [γ, hjm]
    · intro hm; exact (hm (Finset.mem_univ m)).elim
  let L₁ : ℂ → ℂ := fun w => mzFEps f₀ ε (γ w)
  let L₂ : ℂ → ℂ := fun w =>
    f_br m (γ w) * Complex.exp (-↑ε * ∑ j : Fin (n + 1), (γ w j) ^ 2)
  have hL₁_diff : DifferentiableOn ℂ L₁ S_strip :=
    (mzFEps_holomorphic hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
      h_holo_br hε).comp hγ_diff.differentiableOn hγ_maps
  have hL₂_diff : DifferentiableOn ℂ L₂ S_strip := by
    refine (h_holo_br m x_re).mul ?_
    refine (Complex.differentiable_exp.comp (differentiable_const _ |>.mul ?_)).differentiableOn
    have h_sum_fn : (fun w : ℂ => ∑ j : Fin (n + 1), (γ w j) ^ 2) =
        ∑ j : Fin (n + 1), fun w => (γ w j) ^ 2 := by
      ext w; simp
    rw [h_sum_fn]
    exact Differentiable.sum fun j _ => ((differentiable_apply j).comp hγ_diff).pow 2
  have hL₁_an : AnalyticOnNhd ℂ L₁ S_strip :=
    hS_open.analyticOn_iff_analyticOnNhd.mp (hL₁_diff.analyticOn hS_open)
  have hL₂_an : AnalyticOnNhd ℂ L₂ S_strip :=
    hS_open.analyticOn_iff_analyticOnNhd.mp (hL₂_diff.analyticOn hS_open)
  have h0_S : (0 : ℂ) ∈ S_strip := by simp [S_strip, hα]
  have h_real_1d : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), L₁ (t : ℂ) = L₂ (t : ℂ) := by
    refine Filter.Eventually.of_forall fun t => ?_
    dsimp [L₁, L₂]
    have hγ_real : γ (t : ℂ) = fun j => (Function.update x_re m t j : ℂ) := by
      ext j
      by_cases hjm : j = m
      · subst hjm; simp [γ]
      · simp [γ, hjm]
    rw [hγ_real, h_real_eq (Function.update x_re m t), h_real m (Function.update x_re m t)]
    rfl
  have h_nhds := Analysis.analytic_nhds_eq_of_real_eq_1D L₁ L₂ 0
    (hL₁_an 0 h0_S) (hL₂_an 0 h0_S) h_real_1d
  have h_ne_bot : (𝓝[≠] (0 : ℂ)).NeBot := PerfectSpace.not_isolated 0
  have h_ev_ne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), L₁ w = L₂ w := nhdsWithin_le_nhds h_nhds
  have h_freq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), L₁ w = L₂ w := h_ev_ne.frequently
  have h_eqOn := hL₁_an.eqOn_of_preconnected_of_frequently_eq hL₂_an
    hS_conv.isPreconnected h0_S h_freq
  have hzm_S : z m ∈ S_strip := hz.1
  have hγ_zm : γ (z m) = z := by
    ext j
    by_cases hjm : j = m
    · subst hjm; simp [γ]
    · simp only [γ, Function.update_of_ne hjm, x_re]
      have hj_eq := Complex.re_add_im (z j)
      rw [hz.2 j hjm] at hj_eq
      simpa using hj_eq
  have h_at := h_eqOn hzm_S
  dsimp [L₁, L₂] at h_at
  rwa [hγ_zm] at h_at

def OctaSubTube (N : ℕ) (α : ℝ) (A : Finset (Fin N)) : Set (Fin N → ℂ) :=
  { z | (∑ m : Fin N, |(z m).im| < α) ∧ ∀ j : Fin N, j ∉ A → (z j).im = 0 }

noncomputable def mzSweepLine {N : ℕ} (z : Fin N → ℂ) (m₁ m₂ : Fin N)
    (s₁ s₂ : ℝ) (w : ℂ) : Fin N → ℂ :=
  fun j =>
    if j = m₁ then z m₁ + (s₁ : ℂ) * w
    else if j = m₂ then z m₂ - (s₂ : ℂ) * w
    else z j

lemma differentiable_mzSweepLine {N : ℕ} (z : Fin N → ℂ) (m₁ m₂ : Fin N) (s₁ s₂ : ℝ) :
    Differentiable ℂ (mzSweepLine z m₁ m₂ s₁ s₂) := by
  refine differentiable_pi.mpr fun j => ?_
  dsimp [mzSweepLine]
  split_ifs
  · exact (differentiable_const _).add ((differentiable_const _).mul differentiable_id)
  · exact (differentiable_const _).sub ((differentiable_const _).mul differentiable_id)
  · exact differentiable_const _

lemma mzSweepLine_zero {N : ℕ} (z : Fin N → ℂ) (m₁ m₂ : Fin N) (s₁ s₂ : ℝ) :
    mzSweepLine z m₁ m₂ s₁ s₂ 0 = z := by
  ext j
  dsimp [mzSweepLine]
  split_ifs with h1 h2
  · subst h1; simp
  · subst h2; simp
  · rfl

lemma mzSweepLine_im_sum {N : ℕ} {z : Fin N → ℂ} {m₁ m₂ : Fin N} (hne : m₁ ≠ m₂)
    (hy₁ : (z m₁).im ≠ 0) (hy₂ : (z m₂).im ≠ 0) :
    let s₁ : ℝ := if 0 < (z m₁).im then 1 else -1
    let s₂ : ℝ := if 0 < (z m₂).im then 1 else -1
    let t₁ : ℝ := -|(z m₁).im|
    let t₂ : ℝ := |(z m₂).im|
    (∀ w : ℂ, w.im ∈ Set.Icc t₁ t₂ →
      ∑ j : Fin N, |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im| = ∑ j : Fin N, |(z j).im|) ∧
    (∀ (σ : ℝ), 0 < σ → ∀ w : ℂ, w.im ∈ Set.Ioo (t₁ - σ) (t₂ + σ) →
      ∑ j : Fin N, |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im| <
        (∑ j : Fin N, |(z j).im|) + 2 * σ) ∧
    (∀ w : ℂ, w.im = t₁ → (mzSweepLine z m₁ m₂ s₁ s₂ w m₁).im = 0) ∧
    (∀ w : ℂ, w.im = t₂ → (mzSweepLine z m₁ m₂ s₁ s₂ w m₂).im = 0) := by
  intro s₁ s₂ t₁ t₂
  have hs₁_sq : s₁ * s₁ = 1 := by dsimp [s₁]; split_ifs <;> ring
  have hs₂_sq : s₂ * s₂ = 1 := by dsimp [s₂]; split_ifs <;> ring
  have hs₁_abs : |s₁| = 1 := by dsimp [s₁]; split_ifs <;> norm_num
  have hs₂_abs : |s₂| = 1 := by dsimp [s₂]; split_ifs <;> norm_num
  have hs₁_val : (z m₁).im = s₁ * |(z m₁).im| := by
    dsimp [s₁]
    split_ifs with h1
    · rw [abs_of_pos h1, one_mul]
    · have h1' : (z m₁).im < 0 := lt_of_le_of_ne (le_of_not_gt h1) hy₁
      rw [abs_of_neg h1']; ring
  have hs₂_val : (z m₂).im = s₂ * |(z m₂).im| := by
    dsimp [s₂]
    split_ifs with h2
    · rw [abs_of_pos h2, one_mul]
    · have h2' : (z m₂).im < 0 := lt_of_le_of_ne (le_of_not_gt h2) hy₂
      rw [abs_of_neg h2']; ring
  have h_im_m1 : ∀ w : ℂ, (mzSweepLine z m₁ m₂ s₁ s₂ w m₁).im = (z m₁).im + s₁ * w.im := by
    intro w; simp [mzSweepLine]
  have h_im_m2 : ∀ w : ℂ, (mzSweepLine z m₁ m₂ s₁ s₂ w m₂).im = (z m₂).im - s₂ * w.im := by
    intro w; simp [mzSweepLine, hne.symm]
  have h_im_other : ∀ (j : Fin N), j ≠ m₁ → j ≠ m₂ →
      ∀ w : ℂ, (mzSweepLine z m₁ m₂ s₁ s₂ w j).im = (z j).im := by
    intro j hj1 hj2 w; simp [mzSweepLine, hj1, hj2]
  have h_pair_icc : ∀ t ∈ Set.Icc t₁ t₂,
      |(z m₁).im + s₁ * t| + |(z m₂).im - s₂ * t| = |(z m₁).im| + |(z m₂).im| := by
    intro t ht
    have h1_eq : (z m₁).im + s₁ * t = s₁ * (|(z m₁).im| + t) := by
      conv_lhs => rw [hs₁_val]
      ring
    have h2_eq : (z m₂).im - s₂ * t = s₂ * (|(z m₂).im| - t) := by
      conv_lhs => rw [hs₂_val]
      ring
    rw [h1_eq, h2_eq, abs_mul, abs_mul, hs₁_abs, hs₂_abs, one_mul, one_mul]
    have ht1 : 0 ≤ |(z m₁).im| + t := by dsimp [t₁] at ht; linarith [ht.1]
    have ht2 : 0 ≤ |(z m₂).im| - t := by dsimp [t₂] at ht; linarith [ht.2]
    rw [abs_of_nonneg ht1, abs_of_nonneg ht2]
    ring
  have h_split_sum : ∀ f : Fin N → ℝ,
      ∑ j : Fin N, f j = f m₁ + f m₂ + ∑ j ∈ (Finset.univ.erase m₁).erase m₂, f j := by
    intro f
    have hm1 : m₁ ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ m₁
    have hm2 : m₂ ∈ Finset.univ.erase m₁ := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ m₂⟩
    rw [← Finset.add_sum_erase Finset.univ f hm1,
      ← Finset.add_sum_erase (Finset.univ.erase m₁) f hm2, add_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [h_split_sum (fun j => |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im|),
      h_split_sum (fun j => |(z j).im|), h_im_m1, h_im_m2, h_pair_icc w.im hw]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj2 : j ≠ m₂ := (Finset.mem_erase.mp hj).1
    have hj1 : j ≠ m₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    rw [h_im_other j hj1 hj2]
  · intro σ hσ w hw
    let t' : ℝ := max t₁ (min w.im t₂)
    have ht₁_le_t₂ : t₁ ≤ t₂ := by
      dsimp [t₁, t₂]
      linarith [abs_nonneg (z m₁).im, abs_nonneg (z m₂).im]
    have ht'_mem : t' ∈ Set.Icc t₁ t₂ :=
      ⟨le_max_left _ _, max_le ht₁_le_t₂ (min_le_right _ _)⟩
    have h_diff_lt : |w.im - t'| < σ := by
      dsimp [t']
      rcases lt_or_ge w.im t₁ with hlt1 | hge1
      · have hmin : min w.im t₂ = w.im := min_eq_left (hlt1.le.trans ht₁_le_t₂)
        rw [hmin, max_eq_left hlt1.le, abs_of_neg (by linarith)]
        linarith [hw.1]
      · rcases le_or_gt w.im t₂ with hle2 | hgt2
        · rw [min_eq_left hle2, max_eq_right hge1, sub_self, abs_zero]
          exact hσ
        · rw [min_eq_right hgt2.le, max_eq_right ht₁_le_t₂, abs_of_pos (by linarith)]
          linarith [hw.2]
    have hp1 : |(z m₁).im + s₁ * w.im| ≤ |(z m₁).im + s₁ * t'| + |w.im - t'| := by
      have heq : (z m₁).im + s₁ * w.im = ((z m₁).im + s₁ * t') + s₁ * (w.im - t') := by ring
      rw [heq]
      calc |((z m₁).im + s₁ * t') + s₁ * (w.im - t')|
          ≤ |(z m₁).im + s₁ * t'| + |s₁ * (w.im - t')| := abs_add_le _ _
        _ = |(z m₁).im + s₁ * t'| + |w.im - t'| := by rw [abs_mul, hs₁_abs, one_mul]
    have hp2 : |(z m₂).im - s₂ * w.im| ≤ |(z m₂).im - s₂ * t'| + |w.im - t'| := by
      have heq : (z m₂).im - s₂ * w.im = ((z m₂).im - s₂ * t') + (-s₂) * (w.im - t') := by ring
      rw [heq]
      calc |((z m₂).im - s₂ * t') + (-s₂) * (w.im - t')|
          ≤ |(z m₂).im - s₂ * t'| + |(-s₂) * (w.im - t')| := abs_add_le _ _
        _ = |(z m₂).im - s₂ * t'| + |w.im - t'| := by rw [abs_mul, abs_neg, hs₂_abs, one_mul]
    rw [h_split_sum (fun j => |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im|),
      h_split_sum (fun j => |(z j).im|), h_im_m1, h_im_m2]
    have h_rest : (∑ j ∈ (Finset.univ.erase m₁).erase m₂,
        |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im|) =
        ∑ j ∈ (Finset.univ.erase m₁).erase m₂, |(z j).im| := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj2 : j ≠ m₂ := (Finset.mem_erase.mp hj).1
      have hj1 : j ≠ m₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      rw [h_im_other j hj1 hj2]
    rw [h_rest]
    linarith [h_pair_icc t' ht'_mem]
  · intro w hw
    rw [h_im_m1, hw, hs₁_val]
    dsimp [t₁]
    ring
  · intro w hw
    rw [h_im_m2, hw, hs₂_val]
    dsimp [t₂]
    ring

lemma mzFEps_strip_uniform_bdd_fixed_eps {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m))
    (h_bdd_br : ∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
      (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α})
    {ε S₀ : ℝ} (hε : 0 < ε) (hS₀ : S₀ < α) (hS₀_nn : 0 ≤ S₀) :
    ∃ K : ℝ, ∀ z : Fin (n + 1) → ℂ, (∑ m : Fin (n + 1), |(z m).im| ≤ S₀) →
      ‖mzFEps f₀ ε z‖ ≤ K := by
  let β : ℝ := (S₀ + α) / 2
  have hβ_pos : 0 < β := by dsimp [β]; linarith
  have hβ_lt : β < α := by dsimp [β]; linarith
  have hS₀_lt_β : S₀ < β := by dsimp [β]; linarith
  have hN_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  let δ : ℝ := (β - S₀) / ((n + 1 : ℕ) : ℝ)
  have hδ_pos : 0 < δ := div_pos (sub_pos.mpr hS₀_lt_β) hN_pos
  let C_β : ℝ := M * Real.exp (ε * β ^ 2) *
    ∫ x : Fin (n + 1) → ℝ, ∏ j : Fin (n + 1), Real.exp (-ε * (x j) ^ 2)
  have hC_nn : 0 ≤ C_β :=
    mul_nonneg (mul_nonneg hM (Real.exp_pos _).le)
      (integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  have h_coord : ∀ m ξ,
      ‖fourierTransformND (mzGaussianDamped f₀ ε) ξ‖ ≤ C_β * Real.exp (-β * |ξ m|) :=
    fun m ξ => mz_fourier_bound_coord hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
      h_holo_br hε hβ_pos hβ_lt m ξ
  refine ⟨((2 * Real.pi)⁻¹) ^ (n + 1) *
    ∫ ξ : Fin (n + 1) → ℝ, C_β * Real.exp (-δ * ∑ j : Fin (n + 1), |ξ j|), ?_⟩
  intro z hz
  dsimp [mzFEps]
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by positivity) _)
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    ((integrable_exp_neg_abs_sum (n + 1) hδ_pos).const_mul C_β)
    (Filter.Eventually.of_forall fun ξ => ?_)
  have hw_sum : ∑ m : Fin (n + 1), |(z m).im| ≤ β - ((n + 1 : ℕ) : ℝ) * δ := by
    have h_eq : β - ((n + 1 : ℕ) : ℝ) * δ = S₀ := by
      dsimp [δ]; field_simp [hN_pos.ne']; ring
    rwa [h_eq]
  exact mz_fourier_phase_domination hC_nn hδ_pos h_coord hw_sum hα ξ

lemma octaSubTube_subset_flatStrip_of_card_le_one {n : ℕ} {α : ℝ}
    {A : Finset (Fin (n + 1))} (hA : A.card ≤ 1) {z : Fin (n + 1) → ℂ}
    (hz : z ∈ OctaSubTube (n + 1) α A) :
    ∃ m₀ : Fin (n + 1), z ∈ FlatStrip (n + 1) α m₀ := by
  rcases Finset.card_le_one_iff_subset_singleton.mp hA with ⟨m₀, hm₀⟩
  refine ⟨m₀, ?_, fun j hj => hz.2 j (fun hjA => hj (Finset.mem_singleton.mp (hm₀ hjA)))⟩
  calc |(z m₀).im| ≤ ∑ m : Fin (n + 1), |(z m).im| :=
        Finset.single_le_sum (f := fun m : Fin (n + 1) => |(z m).im|)
          (fun m _ => abs_nonneg _) (Finset.mem_univ m₀)
    _ < α := hz.1

lemma mzFEps_norm_le_all {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m))
    (h_bdd_br : ∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
      (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α})
    {ε : ℝ} (hε : 0 < ε) :
    ∀ {z : Fin (n + 1) → ℂ}, z ∈ TubeDomain (Octahedron (n + 1) α) →
      ‖mzFEps f₀ ε z‖ ≤ M * Real.exp (ε * α ^ 2) := by
  have h_holo := mzFEps_holomorphic hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
    h_holo_br hε
  have h_base : ∀ (A : Finset (Fin (n + 1))), A.card ≤ 1 →
      ∀ z ∈ OctaSubTube (n + 1) α A, ‖mzFEps f₀ ε z‖ ≤ M * Real.exp (ε * α ^ 2) := by
    intro A hA z hz
    obtain ⟨m₀, hm₀⟩ := octaSubTube_subset_flatStrip_of_card_le_one hA hz
    rw [mzFEps_eq_on_flatStrip hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
      h_holo_br hε m₀ hm₀, norm_mul, norm_mzGaussianKernel]
    have h_re_le : Real.exp (-ε * ∑ j : Fin (n + 1), (z j).re ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ∑ j : Fin (n + 1), (z j).re ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith
    have h_im_sq : ∑ j : Fin (n + 1), (z j).im ^ 2 ≤ α ^ 2 := by
      rw [Finset.sum_eq_single m₀]
      · have hm0_le : |(z m₀).im| ≤ α := hm₀.1.le
        have := mul_le_mul hm0_le hm0_le (abs_nonneg _) hα.le
        rwa [← sq, ← sq, sq_abs] at this
      · intro j _ hj; simp [hm₀.2 j hj]
      · intro hm; exact (hm (Finset.mem_univ m₀)).elim
    have h_im_le : Real.exp (ε * ∑ j : Fin (n + 1), (z j).im ^ 2) ≤ Real.exp (ε * α ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_im_sq hε.le)
    calc ‖f_br m₀ z‖ * (Real.exp (-ε * ∑ j : Fin (n + 1), (z j).re ^ 2) *
          Real.exp (ε * ∑ j : Fin (n + 1), (z j).im ^ 2))
        ≤ M * (1 * Real.exp (ε * α ^ 2)) :=
          mul_le_mul (h_bdd_br m₀ z hm₀)
            (mul_le_mul h_re_le h_im_le (Real.exp_pos _).le zero_le_one)
            (by positivity) hM
      _ = M * Real.exp (ε * α ^ 2) := by ring
  have h_ind : ∀ (k : ℕ) (A : Finset (Fin (n + 1))), A.card ≤ k →
      ∀ z ∈ OctaSubTube (n + 1) α A, ‖mzFEps f₀ ε z‖ ≤ M * Real.exp (ε * α ^ 2) := by
    intro k
    induction k with
    | zero =>
      intro A hA z hz
      exact h_base A (hA.trans zero_le_one) z hz
    | succ k ih =>
      intro A hA z hz
      by_cases hA1 : A.card ≤ 1
      · exact h_base A hA1 z hz
      · push Not at hA1
        obtain ⟨m₁, hm₁, m₂, hm₂, hne⟩ := Finset.one_lt_card.mp hA1
        by_cases hy₁ : (z m₁).im = 0
        · refine ih (A.erase m₁) (by rw [Finset.card_erase_of_mem hm₁]; omega) z ⟨hz.1, ?_⟩
          intro j hj
          by_cases hjm : j = m₁
          · subst hjm; exact hy₁
          · exact hz.2 j (fun hjA => hj (Finset.mem_erase.mpr ⟨hjm, hjA⟩))
        · by_cases hy₂ : (z m₂).im = 0
          · refine ih (A.erase m₂) (by rw [Finset.card_erase_of_mem hm₂]; omega) z ⟨hz.1, ?_⟩
            intro j hj
            by_cases hjm : j = m₂
            · subst hjm; exact hy₂
            · exact hz.2 j (fun hjA => hj (Finset.mem_erase.mpr ⟨hjm, hjA⟩))
          · let s₁ : ℝ := if 0 < (z m₁).im then 1 else -1
            let s₂ : ℝ := if 0 < (z m₂).im then 1 else -1
            let t₁ : ℝ := -|(z m₁).im|
            let t₂ : ℝ := |(z m₂).im|
            have ht₁_neg : t₁ < 0 := neg_lt_zero.mpr (abs_pos.mpr hy₁)
            have ht₂_pos : 0 < t₂ := abs_pos.mpr hy₂
            have ht₁_lt_t₂ : t₁ < t₂ := ht₁_neg.trans ht₂_pos
            obtain ⟨h_icc, h_ioo, h_end1, h_end2⟩ := mzSweepLine_im_sum hne hy₁ hy₂
            let S₀ : ℝ := ∑ j : Fin (n + 1), |(z j).im|
            have hS₀_lt : S₀ < α := hz.1
            have hS₀_nn : 0 ≤ S₀ := Finset.sum_nonneg fun _ _ => abs_nonneg _
            let σ : ℝ := (α - S₀) / 4
            have hσ_pos : 0 < σ := by dsimp [σ]; linarith
            let g_w : ℂ → ℂ := fun w => mzFEps f₀ ε (mzSweepLine z m₁ m₂ s₁ s₂ w)
            have hg_wide : DifferentiableOn ℂ g_w (Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ)) := by
              refine h_holo.comp (differentiable_mzSweepLine z m₁ m₂ s₁ s₂).differentiableOn ?_
              intro w hw
              change ∑ j : Fin (n + 1), |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im| < α
              have hlt := h_ioo σ hσ_pos w hw
              dsimp [S₀, σ] at hlt ⊢
              linarith
            obtain ⟨K, hK⟩ := mzFEps_strip_uniform_bdd_fixed_eps hα hM hf₀_cont hf₀_bdd
              h_real h_cont_br h_bdd_br h_holo_br hε hS₀_lt hS₀_nn
            have h_sub_ioo : Complex.im ⁻¹' Set.Ioo t₁ t₂ ⊆
                Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
              fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
            have h_sub_icc : Complex.im ⁻¹' Set.Icc t₁ t₂ ⊆
                Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
              fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
            have h0 : ‖g_w 0‖ ≤ M * Real.exp (ε * α ^ 2) := by
              refine Bochner.norm_le_on_horizontal_strip_of_bdd ht₁_lt_t₂
                (hg_wide.mono h_sub_ioo) (hg_wide.continuousOn.mono h_sub_icc)
                (fun u hu => hK _ (le_of_eq (h_icc u ⟨hu.1.le, hu.2.le⟩)))
                (fun u hu => ?_) (fun u hu => ?_)
                (z := 0) (by simpa using ht₁_neg.le) (by simpa using ht₂_pos.le)
              · have hu_icc : u.im ∈ Set.Icc (-|(z m₁).im|) |(z m₂).im| :=
                  ⟨by dsimp [t₁] at hu; linarith, by dsimp [t₁, t₂] at hu ht₁_lt_t₂; linarith⟩
                refine ih (A.erase m₁) (by rw [Finset.card_erase_of_mem hm₁]; omega) _ ⟨?_, ?_⟩
                · rw [h_icc u hu_icc]; exact hz.1
                · intro j hj
                  by_cases hjm1 : j = m₁
                  · subst hjm1; exact h_end1 u hu
                  · have hj_notA : j ∉ A := fun hjA => hj (Finset.mem_erase.mpr ⟨hjm1, hjA⟩)
                    have hjm2 : j ≠ m₂ := fun h => hj_notA (h ▸ hm₂)
                    simp only [mzSweepLine, if_neg hjm1, if_neg hjm2, hz.2 j hj_notA]
              · have hu_icc : u.im ∈ Set.Icc (-|(z m₁).im|) |(z m₂).im| :=
                  ⟨by dsimp [t₁, t₂] at hu ht₁_lt_t₂; linarith, by dsimp [t₂] at hu; linarith⟩
                refine ih (A.erase m₂) (by rw [Finset.card_erase_of_mem hm₂]; omega) _ ⟨?_, ?_⟩
                · rw [h_icc u hu_icc]; exact hz.1
                · intro j hj
                  by_cases hjm2 : j = m₂
                  · subst hjm2; exact h_end2 u hu
                  · have hj_notA : j ∉ A := fun hjA => hj (Finset.mem_erase.mpr ⟨hjm2, hjA⟩)
                    have hjm1 : j ≠ m₁ := fun h => hj_notA (h ▸ hm₁)
                    simp only [mzSweepLine, if_neg hjm1, if_neg hjm2, hz.2 j hj_notA]
            simpa [g_w, mzSweepLine_zero] using h0
  intro z hz
  exact h_ind (n + 1) Finset.univ (by simp) z ⟨hz, fun j hj => (hj (Finset.mem_univ j)).elim⟩

lemma mzFEps_bounded_cauchy_uniform {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    ∀ (k : ℕ) {B γ : ℝ}, 0 < B → 0 < γ →
      ∃ ε₀ > 0, ∀ {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ},
        Continuous f₀ → (∀ x, ‖f₀ x‖ ≤ M) →
        (∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x) →
        (∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m)) →
        (∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M) →
        (∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
          (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α}) →
        ∀ ε₁ ∈ Set.Ioo 0 ε₀, ∀ ε₂ ∈ Set.Ioo 0 ε₀,
          ∀ (A : Finset (Fin (n + 1))), A.card ≤ k →
            ∀ z ∈ OctaSubTube (n + 1) α A, ‖z‖ ≤ B →
              ‖mzFEps f₀ ε₁ z - mzFEps f₀ ε₂ z‖ ≤ γ := by
  have h_base : ∀ {B γ : ℝ}, 0 < B → 0 < γ →
      ∃ ε₀ > 0, ∀ {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ},
        Continuous f₀ → (∀ x, ‖f₀ x‖ ≤ M) →
        (∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x) →
        (∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m)) →
        (∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M) →
        (∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
          (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α}) →
        ∀ ε₁ ∈ Set.Ioo 0 ε₀, ∀ ε₂ ∈ Set.Ioo 0 ε₀,
          ∀ (A : Finset (Fin (n + 1))), A.card ≤ 1 →
            ∀ z ∈ OctaSubTube (n + 1) α A, ‖z‖ ≤ B →
              ‖mzFEps f₀ ε₁ z - mzFEps f₀ ε₂ z‖ ≤ γ := by
    intro B γ hB hγ
    let S : ℝ := ((n + 1 : ℕ) : ℝ) * B ^ 2 + 1
    have hS_pos : 0 < S := by dsimp [S]; positivity
    let ε₀ : ℝ := min 1 (min (1 / S) (γ / (4 * (M + 1) * S)))
    have hε₀_pos : 0 < ε₀ := by dsimp [ε₀]; positivity
    refine ⟨ε₀, hε₀_pos, fun {f₀ f_br} hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
      ε₁ hε₁ ε₂ hε₂ A hA z hz hzB => ?_⟩
    obtain ⟨m₀, hm₀⟩ := octaSubTube_subset_flatStrip_of_card_le_one hA hz
    rw [mzFEps_eq_on_flatStrip hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
      h_holo_br hε₁.1 m₀ hm₀,
      mzFEps_eq_on_flatStrip hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
      h_holo_br hε₂.1 m₀ hm₀]
    let s : ℂ := ∑ j : Fin (n + 1), (z j) ^ 2
    have hs_norm : ‖s‖ ≤ S := by
      calc ‖s‖ ≤ ∑ j : Fin (n + 1), ‖(z j) ^ 2‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin (n + 1), B ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm z j).trans hzB) 2
        _ = ((n + 1 : ℕ) : ℝ) * B ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ S := by dsimp [S]; linarith
    have hε₁_S : ε₁ * S ≤ 1 := by
      have hle : ε₁ ≤ 1 / S := hε₁.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      exact (mul_le_mul_of_nonneg_right hle hS_pos.le).trans
        (by rw [one_div, inv_mul_cancel₀ hS_pos.ne'])
    have hε₂_S : ε₂ * S ≤ 1 := by
      have hle : ε₂ ≤ 1 / S := hε₂.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      exact (mul_le_mul_of_nonneg_right hle hS_pos.le).trans
        (by rw [one_div, inv_mul_cancel₀ hS_pos.ne'])
    have hn1 : ‖-↑ε₁ * s‖ ≤ ε₁ * S := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε₁.1.le]
      exact mul_le_mul_of_nonneg_left hs_norm hε₁.1.le
    have hn2 : ‖-↑ε₂ * s‖ ≤ ε₂ * S := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hε₂.1.le]
      exact mul_le_mul_of_nonneg_left hs_norm hε₂.1.le
    have he1 : ‖Complex.exp (-↑ε₁ * s) - 1‖ ≤ 2 * (ε₁ * S) :=
      (Complex.norm_exp_sub_one_le (hn1.trans hε₁_S)).trans (by linarith)
    have he2 : ‖Complex.exp (-↑ε₂ * s) - 1‖ ≤ 2 * (ε₂ * S) :=
      (Complex.norm_exp_sub_one_le (hn2.trans hε₂_S)).trans (by linarith)
    have h_alg : f_br m₀ z * Complex.exp (-↑ε₁ * s) - f_br m₀ z * Complex.exp (-↑ε₂ * s) =
        f_br m₀ z * ((Complex.exp (-↑ε₁ * s) - 1) - (Complex.exp (-↑ε₂ * s) - 1)) := by ring
    change ‖f_br m₀ z * Complex.exp (-↑ε₁ * s) - f_br m₀ z * Complex.exp (-↑ε₂ * s)‖ ≤ γ
    rw [h_alg, norm_mul]
    have h_sub : ‖(Complex.exp (-↑ε₁ * s) - 1) - (Complex.exp (-↑ε₂ * s) - 1)‖ ≤
        4 * (ε₀ * S) := by
      have h1 : ε₁ * S ≤ ε₀ * S := mul_le_mul_of_nonneg_right hε₁.2.le hS_pos.le
      have h2 : ε₂ * S ≤ ε₀ * S := mul_le_mul_of_nonneg_right hε₂.2.le hS_pos.le
      exact (norm_sub_le _ _).trans (by linarith)
    have h_cap_div : ε₀ ≤ γ / (4 * (M + 1) * S) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have h_denom_pos : 0 < 4 * (M + 1) * S := by positivity
    have h_cap : 4 * (M + 1) * S * ε₀ ≤ γ := by
      have := (le_div_iff₀ h_denom_pos).mp h_cap_div
      linarith
    calc ‖f_br m₀ z‖ * ‖(Complex.exp (-↑ε₁ * s) - 1) - (Complex.exp (-↑ε₂ * s) - 1)‖
        ≤ (M + 1) * (4 * (ε₀ * S)) :=
          mul_le_mul ((h_bdd_br m₀ z hm₀).trans (by linarith)) h_sub (norm_nonneg _) (by positivity)
      _ = 4 * (M + 1) * S * ε₀ := by ring
      _ ≤ γ := h_cap
  intro k
  induction k with
  | zero =>
    intro B γ hB hγ
    obtain ⟨ε₀, hε₀, hbd⟩ := h_base hB hγ
    exact ⟨ε₀, hε₀, fun hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
      ε₁ hε₁ ε₂ hε₂ A hA z hz hzB =>
      hbd hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
        ε₁ hε₁ ε₂ hε₂ A (hA.trans zero_le_one) z hz hzB⟩
  | succ k ih =>
    intro B γ hB hγ
    let M₀ : ℝ := M * Real.exp (α ^ 2)
    have hM₀_nn : 0 ≤ M₀ := by dsimp [M₀]; positivity
    let E_α : ℝ := Real.exp (α ^ 2)
    have hE_pos : 0 < E_α := Real.exp_pos _
    have hE_ge1 : 1 ≤ E_α := Real.one_le_exp (sq_nonneg α)
    let L : ℝ := max 1 ((2 * M₀ * E_α + 1) / γ)
    have hL_ge1 : 1 ≤ L := le_max_left _ _
    have hL_pos : 0 < L := zero_lt_one.trans_le hL_ge1
    let B' : ℝ := B + L + α
    have hB'_pos : 0 < B' := by dsimp [B']; positivity
    let γ' : ℝ := γ / E_α
    have hγ'_pos : 0 < γ' := div_pos hγ hE_pos
    obtain ⟨ε_ih, hε_ih, hbd_ih⟩ := ih hB'_pos hγ'_pos
    obtain ⟨ε_b, hε_b, hbd_b⟩ := h_base hB hγ
    let ε₀ : ℝ := min 1 (min ε_ih ε_b)
    have hε₀_pos : 0 < ε₀ := lt_min zero_lt_one (lt_min hε_ih hε_b)
    refine ⟨ε₀, hε₀_pos, fun {f₀ f_br} hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
      ε₁ hε₁ ε₂ hε₂ A hA z hz hzB => ?_⟩
    have hε₁_le1 : ε₁ ≤ 1 := hε₁.2.le.trans (min_le_left _ _)
    have hε₂_le1 : ε₂ ≤ 1 := hε₂.2.le.trans (min_le_left _ _)
    have hε₁_ih : ε₁ ∈ Set.Ioo 0 ε_ih :=
      ⟨hε₁.1, hε₁.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hε₂_ih : ε₂ ∈ Set.Ioo 0 ε_ih :=
      ⟨hε₂.1, hε₂.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
    have hε₁_b : ε₁ ∈ Set.Ioo 0 ε_b :=
      ⟨hε₁.1, hε₁.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hε₂_b : ε₂ ∈ Set.Ioo 0 ε_b :=
      ⟨hε₂.1, hε₂.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
    have hγ'_le : γ' ≤ γ := div_le_self hγ.le hE_ge1
    have hB_le : B ≤ B' := by dsimp [B']; linarith
    by_cases hA1 : A.card ≤ 1
    · exact hbd_b hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
        ε₁ hε₁_b ε₂ hε₂_b A hA1 z hz hzB
    · push Not at hA1
      obtain ⟨m₁, hm₁, m₂, hm₂, hne⟩ := Finset.one_lt_card.mp hA1
      by_cases hy₁ : (z m₁).im = 0
      · refine (hbd_ih hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
          ε₁ hε₁_ih ε₂ hε₂_ih (A.erase m₁)
          (by rw [Finset.card_erase_of_mem hm₁]; omega) z ⟨hz.1, ?_⟩ (hzB.trans hB_le)).trans hγ'_le
        intro j hj
        by_cases hjm : j = m₁
        · subst hjm; exact hy₁
        · exact hz.2 j (fun hjA => hj (Finset.mem_erase.mpr ⟨hjm, hjA⟩))
      · by_cases hy₂ : (z m₂).im = 0
        · refine (hbd_ih hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
            ε₁ hε₁_ih ε₂ hε₂_ih (A.erase m₂)
            (by rw [Finset.card_erase_of_mem hm₂]; omega) z ⟨hz.1, ?_⟩
              (hzB.trans hB_le)).trans hγ'_le
          intro j hj
          by_cases hjm : j = m₂
          · subst hjm; exact hy₂
          · exact hz.2 j (fun hjA => hj (Finset.mem_erase.mpr ⟨hjm, hjA⟩))
        · let s₁ : ℝ := if 0 < (z m₁).im then 1 else -1
          let s₂ : ℝ := if 0 < (z m₂).im then 1 else -1
          let t₁ : ℝ := -|(z m₁).im|
          let t₂ : ℝ := |(z m₂).im|
          have ht₁_neg : t₁ < 0 := neg_lt_zero.mpr (abs_pos.mpr hy₁)
          have ht₂_pos : 0 < t₂ := abs_pos.mpr hy₂
          have ht₁_lt_t₂ : t₁ < t₂ := ht₁_neg.trans ht₂_pos
          have ht₁_gt : -α < t₁ := by
            have h1 : |(z m₁).im| < α :=
              (Finset.single_le_sum (f := fun m : Fin (n + 1) => |(z m).im|)
                (fun m _ => abs_nonneg _) (Finset.mem_univ m₁)).trans_lt hz.1
            dsimp [t₁]
            linarith
          have ht₂_lt : t₂ < α :=
            (Finset.single_le_sum (f := fun m : Fin (n + 1) => |(z m).im|)
              (fun m _ => abs_nonneg _) (Finset.mem_univ m₂)).trans_lt hz.1
          obtain ⟨h_icc, h_ioo, h_end1, h_end2⟩ := mzSweepLine_im_sum hne hy₁ hy₂
          let S₀ : ℝ := ∑ j : Fin (n + 1), |(z j).im|
          let σ : ℝ := (α - S₀) / 4
          have hσ_pos : 0 < σ := by dsimp [σ, S₀]; linarith [hz.1]
          let d : ℂ → ℂ := fun w =>
            (mzFEps f₀ ε₁ (mzSweepLine z m₁ m₂ s₁ s₂ w) -
              mzFEps f₀ ε₂ (mzSweepLine z m₁ m₂ s₁ s₂ w)) * Complex.exp (-w ^ 2)
          have hd_wide : DifferentiableOn ℂ d (Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ)) := by
            have h_maps : Set.MapsTo (mzSweepLine z m₁ m₂ s₁ s₂)
                (Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ))
                (TubeDomain (Octahedron (n + 1) α)) := by
              intro w hw
              change ∑ j : Fin (n + 1), |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im| < α
              have hlt := h_ioo σ hσ_pos w hw
              dsimp [S₀, σ] at hlt ⊢; linarith [hz.1]
            have hd1 := (mzFEps_holomorphic hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
              h_holo_br hε₁.1).comp (differentiable_mzSweepLine z m₁ m₂ s₁ s₂).differentiableOn
                h_maps
            have hd2 := (mzFEps_holomorphic hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
              h_holo_br hε₂.1).comp (differentiable_mzSweepLine z m₁ m₂ s₁ s₂).differentiableOn
                h_maps
            exact (hd1.sub hd2).mul
              (Complex.differentiable_exp.comp ((differentiable_id.pow 2).neg)).differentiableOn
          have hexp_norm : ∀ w : ℂ,
              ‖Complex.exp (-w ^ 2)‖ = Real.exp (-w.re ^ 2 + w.im ^ 2) := by
            intro w
            rw [Complex.norm_exp]
            congr 1
            rw [neg_re, sq, Complex.mul_re]
            ring
          have h_im_sq_le : ∀ w : ℂ, w.im ∈ Set.Icc t₁ t₂ → w.im ^ 2 ≤ α ^ 2 := by
            intro w hw
            have habs : |w.im| ≤ α :=
              abs_le.mpr ⟨by linarith [ht₁_gt, hw.1], by linarith [ht₂_lt, hw.2]⟩
            have := mul_le_mul habs habs (abs_nonneg _) hα.le
            rwa [← sq, ← sq, sq_abs] at this
          have h_diff_M0 : ∀ w : ℂ, w.im ∈ Set.Icc t₁ t₂ →
              ‖mzFEps f₀ ε₁ (mzSweepLine z m₁ m₂ s₁ s₂ w) -
                mzFEps f₀ ε₂ (mzSweepLine z m₁ m₂ s₁ s₂ w)‖ ≤ 2 * M₀ := by
            intro w hw
            have hw_tube : mzSweepLine z m₁ m₂ s₁ s₂ w ∈ TubeDomain (Octahedron (n + 1) α) := by
              change ∑ j : Fin (n + 1), |(mzSweepLine z m₁ m₂ s₁ s₂ w j).im| < α
              rw [h_icc w hw]; exact hz.1
            have hb1 := (mzFEps_norm_le_all hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
              h_holo_br hε₁.1 hw_tube).trans
              (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (mul_le_of_le_one_left (sq_nonneg α) hε₁_le1)) hM)
            have hb2 := (mzFEps_norm_le_all hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br
              h_holo_br hε₂.1 hw_tube).trans
              (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (mul_le_of_le_one_left (sq_nonneg α) hε₂_le1)) hM)
            exact (norm_sub_le _ _).trans (by dsimp [M₀]; linarith)
          have hd_edge : ∀ (u : ℂ) (A' : Finset (Fin (n + 1))),
              u.im ∈ Set.Icc t₁ t₂ → A'.card ≤ k →
              mzSweepLine z m₁ m₂ s₁ s₂ u ∈ OctaSubTube (n + 1) α A' →
              ‖d u‖ ≤ γ := by
            intro u A' hu_icc hA'_card hu_sub
            by_cases hu_re : L ≤ |u.re|
            · have hre_sq : L ^ 2 ≤ u.re ^ 2 := by
                have := mul_le_mul hu_re hu_re hL_pos.le (abs_nonneg _)
                rwa [← sq, ← sq, sq_abs] at this
              have hexp_le : ‖Complex.exp (-u ^ 2)‖ ≤ E_α * Real.exp (-L ^ 2) := by
                rw [hexp_norm, ← Real.exp_add]
                exact Real.exp_le_exp.mpr (by linarith [h_im_sq_le u hu_icc])
              have hL_exp : L ≤ Real.exp (L ^ 2) := by
                have h1 : L ≤ L ^ 2 := by nlinarith
                linarith [Real.add_one_le_exp (L ^ 2)]
              have hL_cap : 2 * M₀ * E_α ≤ γ * L := by
                have hdiv : (2 * M₀ * E_α + 1) / γ ≤ L := le_max_right _ _
                have := (div_le_iff₀ hγ).mp hdiv
                linarith
              dsimp [d]
              rw [norm_mul]
              calc ‖mzFEps f₀ ε₁ (mzSweepLine z m₁ m₂ s₁ s₂ u) -
                    mzFEps f₀ ε₂ (mzSweepLine z m₁ m₂ s₁ s₂ u)‖ * ‖Complex.exp (-u ^ 2)‖
                  ≤ (2 * M₀) * (E_α * Real.exp (-L ^ 2)) :=
                    mul_le_mul (h_diff_M0 u hu_icc) hexp_le (norm_nonneg _) (by positivity)
                _ = (2 * M₀ * E_α) * Real.exp (-L ^ 2) := by ring
                _ ≤ (γ * Real.exp (L ^ 2)) * Real.exp (-L ^ 2) :=
                    mul_le_mul_of_nonneg_right
                      (hL_cap.trans (mul_le_mul_of_nonneg_left hL_exp hγ.le)) (Real.exp_pos _).le
                _ = γ := by rw [mul_assoc, ← Real.exp_add]; simp
            · push Not at hu_re
              have hu_im_abs : |u.im| ≤ α :=
                abs_le.mpr ⟨by linarith [ht₁_gt, hu_icc.1], by linarith [ht₂_lt, hu_icc.2]⟩
              have hu_norm : ‖u‖ ≤ L + α := by
                have hu_eq : u = ↑u.re + I * ↑u.im := by rw [mul_comm I, Complex.re_add_im]
                calc ‖u‖ = ‖(u.re : ℂ) + I * (u.im : ℂ)‖ := by conv_lhs => rw [hu_eq]
                  _ ≤ ‖(u.re : ℂ)‖ + ‖I * (u.im : ℂ)‖ := norm_add_le _ _
                  _ = |u.re| + |u.im| := by simp [Complex.norm_real]
                  _ ≤ L + α := by linarith
              have hs1_norm : ‖(s₁ : ℂ)‖ = 1 := by dsimp [s₁]; split_ifs <;> norm_num
              have hs2_norm : ‖(s₂ : ℂ)‖ = 1 := by dsimp [s₂]; split_ifs <;> norm_num
              have h_sw_norm : ‖mzSweepLine z m₁ m₂ s₁ s₂ u‖ ≤ B' := by
                refine (pi_norm_le_iff_of_nonneg hB'_pos.le).mpr fun j => ?_
                dsimp [mzSweepLine]
                split_ifs with hj1 hj2
                · calc ‖z m₁ + (s₁ : ℂ) * u‖ ≤ ‖z m₁‖ + ‖(s₁ : ℂ) * u‖ := norm_add_le _ _
                    _ = ‖z m₁‖ + ‖u‖ := by rw [norm_mul, hs1_norm, one_mul]
                    _ ≤ B + (L + α) := add_le_add ((norm_le_pi_norm z m₁).trans hzB) hu_norm
                    _ = B' := by dsimp [B']; ring
                · calc ‖z m₂ - (s₂ : ℂ) * u‖ ≤ ‖z m₂‖ + ‖(s₂ : ℂ) * u‖ := norm_sub_le _ _
                    _ = ‖z m₂‖ + ‖u‖ := by rw [norm_mul, hs2_norm, one_mul]
                    _ ≤ B + (L + α) := add_le_add ((norm_le_pi_norm z m₂).trans hzB) hu_norm
                    _ = B' := by dsimp [B']; ring
                · exact ((norm_le_pi_norm z j).trans hzB).trans hB_le
              have h_ih_u := hbd_ih hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br
                ε₁ hε₁_ih ε₂ hε₂_ih A' hA'_card _ hu_sub h_sw_norm
              have hexp_le : ‖Complex.exp (-u ^ 2)‖ ≤ E_α := by
                rw [hexp_norm]
                exact Real.exp_le_exp.mpr
                  (by linarith [sq_nonneg u.re, h_im_sq_le u hu_icc])
              dsimp [d]
              rw [norm_mul]
              calc ‖mzFEps f₀ ε₁ (mzSweepLine z m₁ m₂ s₁ s₂ u) -
                    mzFEps f₀ ε₂ (mzSweepLine z m₁ m₂ s₁ s₂ u)‖ * ‖Complex.exp (-u ^ 2)‖
                  ≤ γ' * E_α := mul_le_mul h_ih_u hexp_le (norm_nonneg _) hγ'_pos.le
                _ = γ := div_mul_cancel₀ γ hE_pos.ne'
          have h_sub_ioo : Complex.im ⁻¹' Set.Ioo t₁ t₂ ⊆
              Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
            fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
          have h_sub_icc : Complex.im ⁻¹' Set.Icc t₁ t₂ ⊆
              Complex.im ⁻¹' Set.Ioo (t₁ - σ) (t₂ + σ) :=
            fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
          have hd0 := Bochner.norm_le_on_horizontal_strip_of_bdd ht₁_lt_t₂
            (hd_wide.mono h_sub_ioo) (hd_wide.continuousOn.mono h_sub_icc)
            (fun u hu => by
              dsimp [d]; rw [norm_mul]
              have hexp : ‖Complex.exp (-u ^ 2)‖ ≤ E_α := by
                rw [hexp_norm]
                exact Real.exp_le_exp.mpr
                  (by linarith [sq_nonneg u.re, h_im_sq_le u ⟨hu.1.le, hu.2.le⟩])
              calc ‖mzFEps f₀ ε₁ (mzSweepLine z m₁ m₂ s₁ s₂ u) -
                    mzFEps f₀ ε₂ (mzSweepLine z m₁ m₂ s₁ s₂ u)‖ * ‖Complex.exp (-u ^ 2)‖
                  ≤ (2 * M₀) * E_α :=
                    mul_le_mul (h_diff_M0 u ⟨hu.1.le, hu.2.le⟩) hexp (norm_nonneg _)
                      (by positivity)
                _ = 2 * M₀ * E_α := by ring)
            (fun u hu => hd_edge u (A.erase m₁) ⟨by rw [hu], by rw [hu]; exact ht₁_lt_t₂.le⟩
              (by rw [Finset.card_erase_of_mem hm₁]; omega) ⟨by
                rw [h_icc u ⟨by rw [hu], by rw [hu]; exact ht₁_lt_t₂.le⟩]; exact hz.1,
                fun j hj => by
                  by_cases hjm1 : j = m₁
                  · subst hjm1; exact h_end1 u hu
                  · have hj_notA : j ∉ A := fun hjA => hj (Finset.mem_erase.mpr ⟨hjm1, hjA⟩)
                    have hjm2 : j ≠ m₂ := fun h => hj_notA (h ▸ hm₂)
                    simp [mzSweepLine, hjm1, hjm2, hz.2 j hj_notA]⟩)
            (fun u hu => hd_edge u (A.erase m₂) ⟨by rw [hu]; exact ht₁_lt_t₂.le, by rw [hu]⟩
              (by rw [Finset.card_erase_of_mem hm₂]; omega) ⟨by
                rw [h_icc u ⟨by rw [hu]; exact ht₁_lt_t₂.le, by rw [hu]⟩]; exact hz.1,
                fun j hj => by
                  by_cases hjm2 : j = m₂
                  · subst hjm2; exact h_end2 u hu
                  · have hj_notA : j ∉ A := fun hjA => hj (Finset.mem_erase.mpr ⟨hjm2, hjA⟩)
                    have hjm1 : j ≠ m₁ := fun h => hj_notA (h ▸ hm₁)
                    simp [mzSweepLine, hjm1, hjm2, hz.2 j hj_notA]⟩)
            (z := 0) (by simpa using ht₁_neg.le) (by simpa using ht₂_pos.le)
          simpa [d, mzSweepLine_zero] using hd0

lemma mzFEps_bounded_cauchy {n : ℕ} {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    {f₀ : (Fin (n + 1) → ℝ) → ℂ} {f_br : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin (n + 1), ContinuousOn (f_br m) (FlatStrip (n + 1) α m))
    (h_bdd_br : ∀ m : Fin (n + 1), ∀ z ∈ FlatStrip (n + 1) α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin (n + 1)) (x : Fin (n + 1) → ℝ), DifferentiableOn ℂ
      (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w)) {w : ℂ | |w.im| < α}) :
    ∀ (k : ℕ) {B γ : ℝ}, 0 < B → 0 < γ →
      ∃ ε₀ > 0, ∀ ε₁ ∈ Set.Ioo 0 ε₀, ∀ ε₂ ∈ Set.Ioo 0 ε₀,
        ∀ (A : Finset (Fin (n + 1))), A.card ≤ k →
          ∀ z ∈ OctaSubTube (n + 1) α A, ‖z‖ ≤ B →
            ‖mzFEps f₀ ε₁ z - mzFEps f₀ ε₂ z‖ ≤ γ := by
  intro k B γ hB hγ
  obtain ⟨ε₀, hε₀, hbd⟩ := mzFEps_bounded_cauchy_uniform hα hM k hB hγ
  exact ⟨ε₀, hε₀, hbd hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br⟩

theorem malgrange_zerner_flat_tube (N : ℕ) {α M : ℝ} (hα : 0 < α) (hM : 0 ≤ M)
    (f₀ : (Fin N → ℝ) → ℂ) (f_br : Fin N → (Fin N → ℂ) → ℂ)
    (hf₀_cont : Continuous f₀) (hf₀_bdd : ∀ x : Fin N → ℝ, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin N) (x : Fin N → ℝ), f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin N, ContinuousOn (f_br m) (FlatStrip N α m))
    (h_bdd_br : ∀ (m : Fin N), ∀ z ∈ FlatStrip N α m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin N) (x : Fin N → ℝ),
      DifferentiableOn ℂ (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w))
        { w : ℂ | |w.im| < α }) :
    ∃ F : (Fin N → ℂ) → ℂ,
      DifferentiableOn ℂ F (TubeDomain (Octahedron N α)) ∧
      (∀ z ∈ TubeDomain (Octahedron N α), ‖F z‖ ≤ M) ∧
      (∀ x : Fin N → ℝ, F (fun j => (x j : ℂ)) = f₀ x) ∧
      (∀ (m : Fin N), ∀ z ∈ FlatStrip N α m, F z = f_br m z) := by
  cases N with
  | zero =>
    refine ⟨fun _ => f₀ 0, differentiableOn_const _, fun _ _ => hf₀_bdd 0, fun x => ?_,
      fun m => Fin.elim0 m⟩
    dsimp only
    congr 1
    ext i
    exact Fin.elim0 i
  | succ n =>
    let F : (Fin (n + 1) → ℂ) → ℂ :=
      fun z => limUnder (𝓝[>] (0 : ℝ)) (fun ε => mzFEps f₀ ε z)
    have hU_open : IsOpen (TubeDomain (Octahedron (n + 1) α)) :=
      isOpen_TubeDomain (isOpen_Octahedron (n + 1) α)
    have h_ev_holo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        DifferentiableOn ℂ (mzFEps f₀ ε) (TubeDomain (Octahedron (n + 1) α)) :=
      eventually_nhdsWithin_of_forall fun ε hε =>
        mzFEps_holomorphic hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br hε
    have h_unif_ball : ∀ z₀ ∈ TubeDomain (Octahedron (n + 1) α),
        ∃ η > 0, Metric.ball z₀ η ⊆ TubeDomain (Octahedron (n + 1) α) ∧
          TendstoUniformlyOn (fun ε z => mzFEps f₀ ε z) F (𝓝[>] (0 : ℝ))
            (Metric.ball z₀ η) := by
      intro z₀ hz₀
      rcases Metric.isOpen_iff.mp hU_open z₀ hz₀ with ⟨η, hη, h_sub⟩
      refine ⟨η, hη, h_sub, Bochner.tendstoUniformlyOn_limUnder_of_uniform_cauchy _ ?_⟩
      intro γ hγ
      let B : ℝ := ‖z₀‖ + η + 1
      have hB_pos : 0 < B := by dsimp [B]; positivity
      obtain ⟨ε₀, hε₀, hbd⟩ := mzFEps_bounded_cauchy hα hM hf₀_cont hf₀_bdd h_real h_cont_br
        h_bdd_br h_holo_br (n + 1) hB_pos hγ
      refine ⟨ε₀, hε₀, fun ε₁ hε₁ ε₂ hε₂ z hz => ?_⟩
      have hz_norm : ‖z‖ ≤ B := by
        have hd : ‖z - z₀‖ < η := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ B := by dsimp [B]; linarith
      exact hbd ε₁ hε₁ ε₂ hε₂ Finset.univ (by simp) z
        ⟨h_sub hz, fun j hj => (hj (Finset.mem_univ j)).elim⟩ hz_norm
    have h_loc : TendstoLocallyUniformlyOn (fun ε z => mzFEps f₀ ε z) F (𝓝[>] (0 : ℝ))
        (TubeDomain (Octahedron (n + 1) α)) := by
      refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z₀ hz₀ => ?_
      obtain ⟨η, hη, _, hunif⟩ := h_unif_ball z₀ hz₀
      exact ⟨Metric.ball z₀ η, nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ hη), hunif⟩
    have hF_cont : ContinuousOn F (TubeDomain (Octahedron (n + 1) α)) := by
      intro z₀ hz₀
      obtain ⟨η, hη, h_sub, hunif⟩ := h_unif_ball z₀ hz₀
      have h_ev_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          ContinuousOn (mzFEps f₀ ε) (Metric.ball z₀ η) :=
        h_ev_holo.mono fun ε hε => hε.continuousOn.mono h_sub
      exact (hunif.continuousOn h_ev_cont.frequently |>.continuousAt
        (Metric.ball_mem_nhds z₀ hη)).continuousWithinAt
    have hF_holo : DifferentiableOn ℂ F (TubeDomain (Octahedron (n + 1) α)) := by
      refine osgood_nd (n + 1) hU_open F hF_cont ?_
      intro z₀ hz₀ m
      let φ : ℂ → (Fin (n + 1) → ℂ) := fun w => Function.update z₀ m w
      have hφ_diff : Differentiable ℂ φ := by
        refine differentiable_pi.mpr fun j => ?_
        by_cases hjm : j = m
        · subst hjm; simp only [φ, Function.update_self]; exact differentiable_id
        · simp only [φ, Function.update_of_ne hjm]; exact differentiable_const _
      let S_m : Set ℂ := φ ⁻¹' TubeDomain (Octahedron (n + 1) α)
      have hSm_open : IsOpen S_m := hU_open.preimage hφ_diff.continuous
      have h_loc_sl : TendstoLocallyUniformlyOn (fun ε w => mzFEps f₀ ε (φ w))
          (fun w => F (φ w)) (𝓝[>] (0 : ℝ)) S_m :=
        h_loc.comp φ (fun _ hw => hw) hφ_diff.continuous.continuousOn
      have h_ev_sl : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          DifferentiableOn ℂ (fun w => mzFEps f₀ ε (φ w)) S_m :=
        h_ev_holo.mono fun ε hε => hε.comp hφ_diff.differentiableOn (fun _ hw => hw)
      have h_diffOn := h_loc_sl.differentiableOn h_ev_sl hSm_open
      have hzm_Sm : z₀ m ∈ S_m := by
        change Function.update z₀ m (z₀ m) ∈ TubeDomain (Octahedron (n + 1) α)
        rwa [Function.update_eq_self]
      exact (h_diffOn (z₀ m) hzm_Sm).differentiableAt (hSm_open.mem_nhds hzm_Sm)
    have hF_bdd : ∀ z ∈ TubeDomain (Octahedron (n + 1) α), ‖F z‖ ≤ M := by
      intro z hz
      obtain ⟨η, hη, _, hunif⟩ := h_unif_ball z hz
      have h_tendsto : Tendsto (fun ε => mzFEps f₀ ε z) (𝓝[>] (0 : ℝ)) (𝓝 (F z)) :=
        hunif.tendsto_at (Metric.mem_ball_self hη)
      have h_rhs : Tendsto (fun ε : ℝ => M * Real.exp (ε * α ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 M) := by
        have hc : Continuous (fun ε : ℝ => M * Real.exp (ε * α ^ 2)) :=
          continuous_const.mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))
        have h_lim := tendsto_nhdsWithin_of_tendsto_nhds
          (s := Set.Ioi (0 : ℝ)) (hc.continuousAt (x := 0)).tendsto
        simpa using h_lim
      refine le_of_tendsto_of_tendsto h_tendsto.norm h_rhs ?_
      exact eventually_nhdsWithin_of_forall fun ε hε =>
        mzFEps_norm_le_all hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br hε hz
    have hF_strip : ∀ (m : Fin (n + 1)), ∀ z ∈ FlatStrip (n + 1) α m, F z = f_br m z := by
      intro m z hz
      have hz_tube : z ∈ TubeDomain (Octahedron (n + 1) α) := by
        change ∑ j : Fin (n + 1), |(z j).im| < α
        rw [Finset.sum_eq_single m]
        · exact hz.1
        · intro j _ hjm; simp [hz.2 j hjm]
        · intro hm; exact (hm (Finset.mem_univ m)).elim
      obtain ⟨η, hη, _, hunif⟩ := h_unif_ball z hz_tube
      have h_t1 : Tendsto (fun ε => mzFEps f₀ ε z) (𝓝[>] (0 : ℝ)) (𝓝 (F z)) :=
        hunif.tendsto_at (Metric.mem_ball_self hη)
      let s : ℂ := ∑ j : Fin (n + 1), (z j) ^ 2
      have h_t2 : Tendsto (fun ε : ℝ => f_br m z * Complex.exp (-↑ε * s))
          (𝓝[>] (0 : ℝ)) (𝓝 (f_br m z)) := by
        have hc : Continuous (fun ε : ℝ => f_br m z * Complex.exp (-↑ε * s)) :=
          continuous_const.mul
            (Complex.continuous_exp.comp
              ((Complex.continuous_ofReal.neg).mul continuous_const))
        have h_lim := tendsto_nhdsWithin_of_tendsto_nhds
          (s := Set.Ioi (0 : ℝ)) (hc.continuousAt (x := 0)).tendsto
        simpa using h_lim
      have h_ev_eq : (fun ε => mzFEps f₀ ε z) =ᶠ[𝓝[>] (0 : ℝ)]
          fun ε => f_br m z * Complex.exp (-↑ε * s) :=
        eventually_nhdsWithin_of_forall fun ε hε =>
          mzFEps_eq_on_flatStrip hα hM hf₀_cont hf₀_bdd h_real h_cont_br h_bdd_br h_holo_br hε m hz
      exact tendsto_nhds_unique h_t1 (h_t2.congr' h_ev_eq.symm)
    refine ⟨F, hF_holo, hF_bdd, fun x => ?_, hF_strip⟩
    have hx_strip : (fun j : Fin (n + 1) => (x j : ℂ)) ∈ FlatStrip (n + 1) α 0 :=
      ⟨by simp [hα], fun j _ => by simp⟩
    rw [hF_strip 0 _ hx_strip, h_real 0 x]

def RealCube (N : ℕ) (x₀ : Fin N → ℝ) (r : ℝ) : Set (Fin N → ℝ) :=
  { x | ∀ m : Fin N, |x m - x₀ m| < r }

def LocalCrossBranch (N : ℕ) (x₀ : Fin N → ℝ) (r R : ℝ) (m : Fin N) : Set (Fin N → ℂ) :=
  { z | |(z m).re - x₀ m| < r ∧ |(z m).im| < R ∧
    ∀ j : Fin N, j ≠ m → (z j).im = 0 ∧ |(z j).re - x₀ j| < r }

noncomputable def mzCrossRadius (N : ℕ) (r R : ℝ) : ℝ :=
  r * min (1 / 4) (min (Real.pi / 8) (R / (2 * r)) / (2 * ((N : ℝ) + 1)))

lemma mzCrossRadius_pos (N : ℕ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    0 < mzCrossRadius N r R := by
  dsimp [mzCrossRadius]
  refine mul_pos hr (lt_min (by norm_num) (div_pos (lt_min ?_ ?_) (by positivity)))
  · positivity
  · positivity

noncomputable def mzTanhC (w : ℂ) : ℂ :=
  (Complex.exp (2 * w) - 1) / (Complex.exp (2 * w) + 1)

noncomputable def mzArtanhC (ζ : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * Complex.log ((1 + ζ) * (1 - ζ)⁻¹)

lemma mzTanhC_strip_props {w : ℂ} (hw : |w.im| ≤ Real.pi / 8) :
    Complex.exp (2 * w) + 1 ≠ 0 ∧ |(mzTanhC w).re| < 1 ∧ |(mzTanhC w).im| ≤ 2 * |w.im| := by
  let u : ℝ := w.re
  let v : ℝ := w.im
  let E : ℝ := Real.exp (2 * u)
  have hE_pos : 0 < E := Real.exp_pos _
  have hv_le := abs_le.mp hw
  have hcos_pos : 0 < Real.cos (2 * v) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hexp_re_im : Complex.exp (2 * w) =
      (E * Real.cos (2 * v) : ℝ) + (E * Real.sin (2 * v) : ℝ) * I := by
    have h2w : 2 * w = ↑(2 * u) + ↑(2 * v) * I := by
      conv_lhs => rw [← Complex.re_add_im w]
      dsimp [u, v]
      push_cast
      ring
    rw [h2w, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    dsimp [E]
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  have hexp_re : (Complex.exp (2 * w)).re = E * Real.cos (2 * v) := by
    rw [hexp_re_im]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have hexp_im : (Complex.exp (2 * w)).im = E * Real.sin (2 * v) := by
    rw [hexp_re_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  let z_den : ℂ := Complex.exp (2 * w) + 1
  have hden_re : z_den.re = E * Real.cos (2 * v) + 1 := by simp [z_den, hexp_re]
  have hden_im : z_den.im = E * Real.sin (2 * v) := by simp [z_den, hexp_im]
  have hden_normSq : Complex.normSq z_den = E ^ 2 + 2 * E * Real.cos (2 * v) + 1 := by
    rw [Complex.normSq_apply, hden_re, hden_im]
    have hcs := Real.cos_sq_add_sin_sq (2 * v)
    calc (E * Real.cos (2 * v) + 1) * (E * Real.cos (2 * v) + 1) +
          (E * Real.sin (2 * v)) * (E * Real.sin (2 * v))
        = E ^ 2 * (Real.cos (2 * v) ^ 2 + Real.sin (2 * v) ^ 2) +
            2 * E * Real.cos (2 * v) + 1 := by ring
      _ = E ^ 2 + 2 * E * Real.cos (2 * v) + 1 := by rw [hcs]; ring
  have hden_gt_sq : E ^ 2 + 1 < Complex.normSq z_den := by
    rw [hden_normSq]
    nlinarith [mul_pos hE_pos hcos_pos]
  have hden_ge_2E : 2 * E ≤ Complex.normSq z_den := by
    have hsq : 2 * E ≤ E ^ 2 + 1 := by nlinarith [sq_nonneg (E - 1)]
    exact hsq.trans hden_gt_sq.le
  have hden_pos : 0 < Complex.normSq z_den := by linarith [sq_nonneg E]
  have hden_ne : z_den ≠ 0 := Complex.normSq_pos.mp hden_pos
  have hnum_re : (Complex.exp (2 * w) - 1).re = E * Real.cos (2 * v) - 1 := by
    simp [hexp_re]
  have hnum_im : (Complex.exp (2 * w) - 1).im = E * Real.sin (2 * v) := by
    simp [hexp_im]
  have htanh_re : (mzTanhC w).re = (E ^ 2 - 1) / Complex.normSq z_den := by
    dsimp [mzTanhC]
    rw [Complex.div_re, ← add_div]
    change ((Complex.exp (2 * w) - 1).re * z_den.re +
        (Complex.exp (2 * w) - 1).im * z_den.im) / Complex.normSq z_den = _
    rw [hnum_re, hnum_im, hden_re, hden_im]
    congr 1
    have hcs := Real.cos_sq_add_sin_sq (2 * v)
    calc (E * Real.cos (2 * v) - 1) * (E * Real.cos (2 * v) + 1) +
          E * Real.sin (2 * v) * (E * Real.sin (2 * v))
        = E ^ 2 * (Real.cos (2 * v) ^ 2 + Real.sin (2 * v) ^ 2) - 1 := by ring
      _ = E ^ 2 - 1 := by rw [hcs]; ring
  have htanh_im : (mzTanhC w).im = (2 * E * Real.sin (2 * v)) / Complex.normSq z_den := by
    dsimp [mzTanhC]
    rw [Complex.div_im, ← sub_div]
    change ((Complex.exp (2 * w) - 1).im * z_den.re -
        (Complex.exp (2 * w) - 1).re * z_den.im) / Complex.normSq z_den = _
    rw [hnum_re, hnum_im, hden_re, hden_im]
    congr 1
    ring
  refine ⟨hden_ne, ?_, ?_⟩
  · rw [htanh_re, abs_div, abs_of_pos hden_pos, div_lt_one hden_pos]
    have habs : |E ^ 2 - 1| ≤ E ^ 2 + 1 :=
      abs_le.mpr ⟨by nlinarith [sq_nonneg E], by linarith⟩
    exact habs.trans_lt hden_gt_sq
  · rw [htanh_im, abs_div, abs_of_pos hden_pos, abs_mul, abs_of_pos (mul_pos two_pos hE_pos)]
    have hsin_le : |Real.sin (2 * v)| ≤ 2 * |v| := by
      calc |Real.sin (2 * v)| ≤ |2 * v| := Real.abs_sin_le_abs
        _ = 2 * |v| := by rw [abs_mul, abs_of_pos two_pos]
    have h_div_le : (2 * E * |Real.sin (2 * v)|) / Complex.normSq z_den ≤
        (2 * E * (2 * |v|)) / (2 * E) := by
      refine div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hsin_le (by positivity))
        (mul_pos two_pos hE_pos) hden_ge_2E
    have h2E_ne : (2 * E : ℝ) ≠ 0 := (mul_pos two_pos hE_pos).ne'
    have h_simp : (2 * E * (2 * |v|)) / (2 * E) = 2 * |v| := by
      field_simp [h2E_ne]
    exact h_div_le.trans_eq h_simp

lemma mzTanhC_ofReal_im (t : ℝ) : (mzTanhC (t : ℂ)).im = 0 := by
  have hp := (mzTanhC_strip_props (w := (t : ℂ))
    (by simp only [Complex.ofReal_im, abs_zero]; positivity)).2.2
  have h0 : |(mzTanhC (t : ℂ)).im| ≤ 0 := by simpa using hp
  exact abs_nonpos_iff.mp h0

lemma differentiableOn_mzTanhC :
    DifferentiableOn ℂ mzTanhC {w : ℂ | |w.im| < Real.pi / 8} := by
  have h_exp : Differentiable ℂ (fun w : ℂ => Complex.exp (2 * w)) :=
    Complex.differentiable_exp.comp ((differentiable_const 2).mul differentiable_id)
  exact ((h_exp.sub (differentiable_const 1)).differentiableOn).div
    ((h_exp.add (differentiable_const 1)).differentiableOn)
    (fun w hw => (mzTanhC_strip_props (le_of_lt hw)).1)

lemma mzArtanhC_slit_and_deriv {ζ : ℂ} (hζ : ‖ζ‖ < 1 / 2) :
    1 - ζ ≠ 0 ∧ (1 + ζ) * (1 - ζ)⁻¹ ∈ Complex.slitPlane ∧
      HasDerivAt mzArtanhC ((1 - ζ ^ 2)⁻¹) ζ ∧ mzTanhC (mzArtanhC ζ) = ζ := by
  have h1_norm : 1 / 2 < ‖1 - ζ‖ := by
    have htri : ‖(1 : ℂ)‖ ≤ ‖1 - ζ‖ + ‖ζ‖ := by
      simpa using norm_add_le (1 - ζ) ζ
    rw [norm_one] at htri
    linarith
  have h1_ne : 1 - ζ ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hden_pos : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr h1_ne
  have hq_re : ((1 + ζ) * (1 - ζ)⁻¹).re =
      (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
    rw [← div_eq_mul_inv, Complex.div_re, ← add_div]
    congr 1
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.sub_re]
    ring
  have hζ_nsq : Complex.normSq ζ < 1 / 4 := by
    rw [Complex.normSq_eq_norm_sq]
    have := mul_lt_mul' hζ.le hζ (norm_nonneg ζ) (by norm_num)
    nlinarith
  have hq_pos : 0 < ((1 + ζ) * (1 - ζ)⁻¹).re := by
    rw [hq_re]
    exact div_pos (by linarith) hden_pos
  have hq_slit : (1 + ζ) * (1 - ζ)⁻¹ ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hq_pos)
  have hq_ne : (1 + ζ) * (1 - ζ)⁻¹ ≠ 0 := Complex.slitPlane_ne_zero hq_slit
  have h1_plus_ne : 1 + ζ ≠ 0 := left_ne_zero_of_mul hq_ne
  have h_sub_der : HasDerivAt (fun u : ℂ => 1 - u) (-1) ζ :=
    (hasDerivAt_id ζ).const_sub (1 : ℂ)
  have h_inv_der : HasDerivAt (fun u : ℂ => (1 - u)⁻¹) (-(-1) / (1 - ζ) ^ 2) ζ :=
    h_sub_der.inv h1_ne
  have h_q_der : HasDerivAt (fun u : ℂ => (1 + u) * (1 - u)⁻¹)
      (1 * (1 - ζ)⁻¹ + (1 + ζ) * (-(-1) / (1 - ζ) ^ 2)) ζ :=
    ((hasDerivAt_id ζ).const_add (1 : ℂ)).mul h_inv_der
  have h_log_der := (Complex.hasDerivAt_log hq_slit).comp ζ h_q_der
  have h_art_der0 := h_log_der.const_mul (2 : ℂ)⁻¹
  have h_der_simp : (2 : ℂ)⁻¹ *
      (((1 + ζ) * (1 - ζ)⁻¹)⁻¹ * (1 * (1 - ζ)⁻¹ + (1 + ζ) * (-(-1) / (1 - ζ) ^ 2))) =
      (1 - ζ ^ 2)⁻¹ := by
    have hsq_ne : 1 - ζ ^ 2 ≠ 0 := by
      have hf : 1 - ζ ^ 2 = (1 + ζ) * (1 - ζ) := by ring
      rw [hf]
      exact mul_ne_zero h1_plus_ne h1_ne
    field_simp [h1_ne, h1_plus_ne, hsq_ne]
    ring
  rw [h_der_simp] at h_art_der0
  have h_inv_eq : mzTanhC (mzArtanhC ζ) = ζ := by
    dsimp [mzTanhC, mzArtanhC]
    have h2 : 2 * ((2 : ℂ)⁻¹ * Complex.log ((1 + ζ) * (1 - ζ)⁻¹)) =
        Complex.log ((1 + ζ) * (1 - ζ)⁻¹) := by ring
    rw [h2, Complex.exp_log hq_ne]
    have hq_plus1 : (1 + ζ) * (1 - ζ)⁻¹ + 1 ≠ 0 := by
      have hf : (1 + ζ) * (1 - ζ)⁻¹ + 1 = 2 * (1 - ζ)⁻¹ := by
        field_simp [h1_ne]; ring
      rw [hf]
      exact mul_ne_zero two_ne_zero (inv_ne_zero h1_ne)
    field_simp [h1_ne, hq_plus1]
    ring
  exact ⟨h1_ne, hq_slit, h_art_der0, h_inv_eq⟩

lemma norm_mzArtanhC_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1 / 3) :
    ‖mzArtanhC ζ‖ ≤ 2 * ‖ζ‖ := by
  have h0 : mzArtanhC 0 = 0 := by simp [mzArtanhC]
  let g : ℝ → ℂ := fun t => mzArtanhC ((t : ℂ) * ζ)
  have hg_dw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g (ζ * (1 - ((t : ℂ) * ζ) ^ 2)⁻¹) (Set.Icc 0 1) t := by
    intro t ht
    have ht_lt : ‖(t : ℂ) * ζ‖ < 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      calc t * ‖ζ‖ ≤ 1 * (1 / 3) := mul_le_mul ht.2 hζ (norm_nonneg _) zero_le_one
        _ < 1 / 2 := by norm_num
    have hd_art := (mzArtanhC_slit_and_deriv ht_lt).2.2.1
    have hd_lin : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ) ζ t := by
      simpa using (Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := t)).mul_const ζ
    have hd_comp := hd_art.comp t hd_lin
    rw [mul_comm] at hd_comp
    exact hd_comp.hasDerivWithinAt
  have hg_nb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖ζ * (1 - ((t : ℂ) * ζ) ^ 2)⁻¹‖ ≤ 2 * ‖ζ‖ := by
    intro t ht
    rw [norm_mul, norm_inv, mul_comm]
    have ht_sq : ‖((t : ℂ) * ζ) ^ 2‖ ≤ 1 / 9 := by
      rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      have h1 : t * ‖ζ‖ ≤ 1 / 3 := by
        calc t * ‖ζ‖ ≤ 1 * (1 / 3) := mul_le_mul ht.2 hζ (norm_nonneg _) zero_le_one
          _ = 1 / 3 := one_mul _
      nlinarith [mul_nonneg ht.1 (norm_nonneg ζ)]
    have h_den_ge : 1 / 2 ≤ ‖1 - ((t : ℂ) * ζ) ^ 2‖ := by
      have htri := norm_add_le (1 - ((t : ℂ) * ζ) ^ 2) (((t : ℂ) * ζ) ^ 2)
      have hsum1 : (1 - ((t : ℂ) * ζ) ^ 2) + ((t : ℂ) * ζ) ^ 2 = 1 := by ring
      rw [hsum1, norm_one] at htri
      linarith
    have h_inv_le : ‖1 - ((t : ℂ) * ζ) ^ 2‖⁻¹ ≤ 2 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) h_den_ge
      norm_num at this
      exact this
    exact mul_le_mul_of_nonneg_right h_inv_le (norm_nonneg ζ)
  have h_mvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hg_dw hg_nb ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  simpa [g, h0] using h_mvt

lemma mzArtanhC_ofReal_im {u : ℝ} (hu : |u| < 1 / 2) :
    (mzArtanhC (u : ℂ)).im = 0 := by
  have hu' := abs_lt.mp hu
  have h_pos : 0 < (1 + u) / (1 - u) := div_pos (by linarith) (by linarith)
  have hq : (1 + (u : ℂ)) * (1 - (u : ℂ))⁻¹ = (((1 + u) / (1 - u) : ℝ) : ℂ) := by
    rw [← div_eq_mul_inv]
    push_cast
    rfl
  dsimp [mzArtanhC]
  rw [hq, ← Complex.ofReal_log h_pos.le]
  have h2 : (2 : ℂ)⁻¹ * ↑(Real.log ((1 + u) / (1 - u))) =
      (((2 : ℝ)⁻¹ * Real.log ((1 + u) / (1 - u)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, Complex.ofReal_im]

theorem malgrange_zerner_local_cross (N : ℕ) {r R M : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hM : 0 ≤ M) (x₀ : Fin N → ℝ)
    (f₀ : (Fin N → ℝ) → ℂ) (f_br : Fin N → (Fin N → ℂ) → ℂ)
    (hf₀_cont : ContinuousOn f₀ (RealCube N x₀ r))
    (hf₀_bdd : ∀ x ∈ RealCube N x₀ r, ‖f₀ x‖ ≤ M)
    (h_real : ∀ (m : Fin N), ∀ x ∈ RealCube N x₀ r, f_br m (fun j => (x j : ℂ)) = f₀ x)
    (h_cont_br : ∀ m : Fin N, ContinuousOn (f_br m) (LocalCrossBranch N x₀ r R m))
    (h_bdd_br : ∀ (m : Fin N), ∀ z ∈ LocalCrossBranch N x₀ r R m, ‖f_br m z‖ ≤ M)
    (h_holo_br : ∀ (m : Fin N), ∀ x ∈ RealCube N x₀ r,
      DifferentiableOn ℂ (fun w => f_br m (Function.update (fun j => (x j : ℂ)) m w))
        { w : ℂ | |w.re - x₀ m| < r ∧ |w.im| < R }) :
    let ρ := mzCrossRadius N r R
    ∃ H : (Fin N → ℂ) → ℂ,
      DifferentiableOn ℂ H (Metric.ball (fun m => (x₀ m : ℂ)) ρ) ∧
      (∀ z ∈ Metric.ball (fun m => (x₀ m : ℂ)) ρ, ‖H z‖ ≤ M) ∧
      (∀ x : Fin N → ℝ, (fun m => (x m : ℂ)) ∈ Metric.ball (fun m => (x₀ m : ℂ)) ρ →
        H (fun m => (x m : ℂ)) = f₀ x) ∧
      (∀ (m : Fin N), ∀ z ∈ Metric.ball (fun m => (x₀ m : ℂ)) ρ ∩ LocalCrossBranch N x₀ r R m,
        H z = f_br m z) ∧
      (∀ m : Fin N,
        ‖deriv (fun ζ => H (Function.update (fun j => (x₀ j : ℂ)) m ζ)) (x₀ m)‖ ≤
          2 * M / ρ) := by
  intro ρ
  have hρ_pos : 0 < ρ := mzCrossRadius_pos N hr hR
  let α : ℝ := min (Real.pi / 8) (R / (2 * r))
  have hα_pos : 0 < α := lt_min (by positivity) (by positivity)
  have hα_pi : α ≤ Real.pi / 8 := min_le_left _ _
  have hα_R : 2 * r * α ≤ R := by
    have h1 : α ≤ R / (2 * r) := min_le_right _ _
    have h2r : 0 < 2 * r := by positivity
    have := (le_div_iff₀ h2r).mp h1
    linarith
  let ψC : Fin N → ℂ → ℂ := fun m w => (x₀ m : ℂ) + (r : ℂ) * mzTanhC w
  let ψR : (Fin N → ℝ) → (Fin N → ℝ) := fun u m => x₀ m + r * (mzTanhC (u m : ℂ)).re
  have hψC_real : ∀ (u : Fin N → ℝ) (m : Fin N), ψC m (u m : ℂ) = (ψR u m : ℂ) := by
    intro u m
    dsimp [ψC, ψR]
    have him := mzTanhC_ofReal_im (u m)
    have h_eq := (Complex.re_add_im (mzTanhC (u m : ℂ))).symm
    rw [him] at h_eq
    have h_re : mzTanhC (u m : ℂ) = ((mzTanhC (u m : ℂ)).re : ℂ) := by simpa using h_eq
    rw [h_re]
    push_cast
    rfl
  have hψC_strip : ∀ (m : Fin N) {w : ℂ}, |w.im| < α →
      |(ψC m w).re - x₀ m| < r ∧ |(ψC m w).im| < R := by
    intro m w hw
    have hw_pi : |w.im| ≤ Real.pi / 8 := hw.le.trans hα_pi
    obtain ⟨_, hre_lt, him_le⟩ := mzTanhC_strip_props hw_pi
    have h_re : (ψC m w).re - x₀ m = r * (mzTanhC w).re := by
      dsimp [ψC]
      simp
    have h_im : (ψC m w).im = r * (mzTanhC w).im := by
      dsimp [ψC]
      simp
    refine ⟨?_, ?_⟩
    · rw [h_re, abs_mul, abs_of_pos hr]
      calc r * |(mzTanhC w).re| < r * 1 := mul_lt_mul_of_pos_left hre_lt hr
        _ = r := mul_one r
    · rw [h_im, abs_mul, abs_of_pos hr]
      calc r * |(mzTanhC w).im| ≤ r * (2 * |w.im|) :=
            mul_le_mul_of_nonneg_left him_le hr.le
        _ < r * (2 * α) := mul_lt_mul_of_pos_left (by linarith) hr
        _ = 2 * r * α := by ring
        _ ≤ R := hα_R
  have hψR_cube : ∀ u : Fin N → ℝ, ψR u ∈ RealCube N x₀ r := by
    intro u m
    have h := (hψC_strip m (w := (u m : ℂ)) (by simp [hα_pos])).1
    rwa [hψC_real u m, Complex.ofReal_re] at h
  have hψC_diff : ∀ m : Fin N, DifferentiableOn ℂ (ψC m) {w : ℂ | |w.im| < α} := by
    intro m
    have h_sub : {w : ℂ | |w.im| < α} ⊆ {w : ℂ | |w.im| < Real.pi / 8} :=
      fun w hw => lt_of_lt_of_le hw hα_pi
    exact (differentiableOn_const (x₀ m : ℂ)).add
      ((differentiableOn_const (r : ℂ)).mul (differentiableOn_mzTanhC.mono h_sub))
  have hψR_cont : Continuous ψR := by
    refine continuous_pi fun m => continuous_const.add (continuous_const.mul ?_)
    have h_emb : Continuous (fun u : Fin N → ℝ => (u m : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_apply m)
    exact Complex.continuous_re.comp
      (differentiableOn_mzTanhC.continuousOn.comp_continuous h_emb
        (fun u => by simp [Real.pi_pos]))
  let g₀ : (Fin N → ℝ) → ℂ := fun u => f₀ (ψR u)
  let g_br : Fin N → (Fin N → ℂ) → ℂ := fun m w => f_br m (fun j => ψC j (w j))
  have h_maps_br : ∀ m : Fin N,
      Set.MapsTo (fun w : Fin N → ℂ => fun j => ψC j (w j))
        (FlatStrip N α m) (LocalCrossBranch N x₀ r R m) := by
    intro m w hw
    obtain ⟨h1, h2⟩ := hψC_strip m hw.1
    refine ⟨h1, h2, fun j hj => ?_⟩
    have hj_im : (w j).im = 0 := hw.2 j hj
    have hj_real : w j = ((w j).re : ℂ) :=
      (Complex.re_add_im (w j)).symm.trans (by simp [hj_im])
    dsimp only
    rw [hj_real, hψC_real (fun k => (w k).re) j]
    exact ⟨Complex.ofReal_im _, hψR_cube (fun k => (w k).re) j⟩
  have hg₀_cont : Continuous g₀ :=
    hf₀_cont.comp_continuous hψR_cont hψR_cube
  have hg₀_bdd : ∀ u : Fin N → ℝ, ‖g₀ u‖ ≤ M := fun u => hf₀_bdd _ (hψR_cube u)
  have hg_real : ∀ (m : Fin N) (u : Fin N → ℝ), g_br m (fun j => (u j : ℂ)) = g₀ u := by
    intro m u
    dsimp [g_br, g₀]
    have h_eq : (fun j : Fin N => ψC j (u j : ℂ)) = fun j => (ψR u j : ℂ) :=
      funext (hψC_real u)
    rw [h_eq, h_real m (ψR u) (hψR_cube u)]
  have hg_cont_br : ∀ m : Fin N, ContinuousOn (g_br m) (FlatStrip N α m) := by
    intro m
    have h_map_cont : ContinuousOn (fun w : Fin N → ℂ => fun j => ψC j (w j))
        (FlatStrip N α m) := by
      refine continuousOn_pi.mpr fun j => ?_
      refine (hψC_diff j).continuousOn.comp (continuous_apply j).continuousOn ?_
      intro w hw
      by_cases hjm : j = m
      · subst hjm; exact hw.1
      · change |(w j).im| < α; rw [hw.2 j hjm, abs_zero]; exact hα_pos
    exact (h_cont_br m).comp h_map_cont (h_maps_br m)
  have hg_bdd_br : ∀ (m : Fin N), ∀ w ∈ FlatStrip N α m, ‖g_br m w‖ ≤ M :=
    fun m w hw => h_bdd_br m _ (h_maps_br m hw)
  have hg_holo_br : ∀ (m : Fin N) (u : Fin N → ℝ),
      DifferentiableOn ℂ (fun ζ => g_br m (Function.update (fun j => (u j : ℂ)) m ζ))
        {ζ : ℂ | |ζ.im| < α} := by
    intro m u
    have h_fn : (fun ζ : ℂ => g_br m (Function.update (fun j => (u j : ℂ)) m ζ)) =
        (fun ω => f_br m (Function.update (fun j => (ψR u j : ℂ)) m ω)) ∘ (ψC m) := by
      ext ζ
      dsimp [g_br]
      congr 1
      ext j
      by_cases hjm : j = m
      · subst hjm; simp
      · simp [hjm, hψC_real u j]
    rw [h_fn]
    exact (h_holo_br m (ψR u) (hψR_cube u)).comp (hψC_diff m)
      (fun ζ hζ => hψC_strip m hζ)
  obtain ⟨F, hF_holo, hF_bdd, hF_real, hF_strip⟩ :=
    malgrange_zerner_flat_tube N hα_pos hM g₀ g_br hg₀_cont hg₀_bdd hg_real
      hg_cont_br hg_bdd_br hg_holo_br
  let x₀_c : Fin N → ℂ := fun m => (x₀ m : ℂ)
  let φInv : (Fin N → ℂ) → (Fin N → ℂ) :=
    fun z m => mzArtanhC ((z m - x₀ m) * (r : ℂ)⁻¹)
  have hρ_div_le_quarter : ρ / r ≤ 1 / 4 := by
    dsimp [ρ, mzCrossRadius]
    rw [mul_div_cancel_left₀ _ hr.ne']
    exact min_le_left _ _
  have hρ_div_le_α : ρ / r ≤ α / (2 * ((N : ℝ) + 1)) := by
    dsimp [ρ, mzCrossRadius, α]
    rw [mul_div_cancel_left₀ _ hr.ne']
    exact min_le_right _ _
  have h_arg_lt : ∀ {z : Fin N → ℂ}, z ∈ Metric.ball x₀_c ρ →
      ∀ m : Fin N, ‖(z m - x₀ m) * (r : ℂ)⁻¹‖ < ρ / r := by
    intro z hz m
    have hzm : ‖z m - x₀ m‖ < ρ := by
      have hd := (dist_le_pi_dist z x₀_c m).trans_lt (Metric.mem_ball.mp hz)
      simpa [dist_eq_norm, x₀_c] using hd
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, ← div_eq_mul_inv]
    exact div_lt_div_of_pos_right hzm hr
  have hφInv_maps : Set.MapsTo φInv (Metric.ball x₀_c ρ) (TubeDomain (Octahedron N α)) := by
    intro z hz
    change ∑ m : Fin N, |(φInv z m).im| < α
    have h_each : ∀ m : Fin N, |(φInv z m).im| ≤ α / ((N : ℝ) + 1) := by
      intro m
      have hlt := h_arg_lt hz m
      have hle_third : ‖(z m - x₀ m) * (r : ℂ)⁻¹‖ ≤ 1 / 3 :=
        hlt.le.trans (hρ_div_le_quarter.trans (by norm_num))
      calc |(φInv z m).im| ≤ ‖φInv z m‖ := Complex.abs_im_le_norm _
        _ ≤ 2 * ‖(z m - x₀ m) * (r : ℂ)⁻¹‖ := norm_mzArtanhC_le hle_third
        _ ≤ 2 * (ρ / r) := mul_le_mul_of_nonneg_left hlt.le two_pos.le
        _ ≤ 2 * (α / (2 * ((N : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hρ_div_le_α two_pos.le
        _ = α / ((N : ℝ) + 1) := by
            have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
            field_simp [hN1]
    calc ∑ m : Fin N, |(φInv z m).im|
        ≤ ∑ _m : Fin N, α / ((N : ℝ) + 1) := Finset.sum_le_sum fun m _ => h_each m
      _ = (N : ℝ) * (α / ((N : ℝ) + 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ < α := by
          have hN1_pos : 0 < (N : ℝ) + 1 := by positivity
          rw [mul_div_assoc', div_lt_iff₀ hN1_pos]
          linarith
  have hφInv_diff : DifferentiableOn ℂ φInv (Metric.ball x₀_c ρ) := by
    refine differentiableOn_pi.mpr fun m z hz => ?_
    have hlt : ‖(z m - x₀ m) * (r : ℂ)⁻¹‖ < 1 / 2 :=
      (h_arg_lt hz m).trans_le (hρ_div_le_quarter.trans (by norm_num))
    have hd_art := (mzArtanhC_slit_and_deriv hlt).2.2.1
    have hd_aff : DifferentiableAt ℂ
        (fun w : Fin N → ℂ => (w m - x₀ m) * (r : ℂ)⁻¹) z :=
      (((differentiable_apply m).differentiableAt.sub
        (differentiableAt_const _)).mul (differentiableAt_const _))
    exact (hd_art.differentiableAt.comp z hd_aff).differentiableWithinAt
  have hψ_φInv : ∀ {z : Fin N → ℂ}, z ∈ Metric.ball x₀_c ρ →
      ∀ m : Fin N, ψC m (φInv z m) = z m := by
    intro z hz m
    have hlt : ‖(z m - x₀ m) * (r : ℂ)⁻¹‖ < 1 / 2 :=
      (h_arg_lt hz m).trans_le (hρ_div_le_quarter.trans (by norm_num))
    dsimp [ψC, φInv]
    rw [(mzArtanhC_slit_and_deriv hlt).2.2.2]
    have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    field_simp [hr_c]
    ring
  let H : (Fin N → ℂ) → ℂ := fun z => F (φInv z)
  have hH_holo : DifferentiableOn ℂ H (Metric.ball x₀_c ρ) :=
    hF_holo.comp hφInv_diff hφInv_maps
  have hH_bdd : ∀ z ∈ Metric.ball x₀_c ρ, ‖H z‖ ≤ M :=
    fun z hz => hF_bdd (φInv z) (hφInv_maps hz)
  have hH_real : ∀ x : Fin N → ℝ, (fun m => (x m : ℂ)) ∈ Metric.ball x₀_c ρ →
      H (fun m => (x m : ℂ)) = f₀ x := by
    intro x hx
    let u : Fin N → ℝ := fun m => (φInv (fun k => (x k : ℂ)) m).re
    have hφ_real : φInv (fun k => (x k : ℂ)) = fun m => (u m : ℂ) := by
      ext m
      have hlt := h_arg_lt hx m
      have hu_abs : |(x m - x₀ m) * r⁻¹| < 1 / 2 := by
        have h_eq : (((x m - x₀ m) * r⁻¹ : ℝ) : ℂ) = ((x m : ℂ) - x₀ m) * (r : ℂ)⁻¹ := by
          push_cast; rfl
        have hn : ‖(((x m - x₀ m) * r⁻¹ : ℝ) : ℂ)‖ < 1 / 2 := by
          rw [h_eq]
          exact hlt.trans_le (hρ_div_le_quarter.trans (by norm_num))
        rwa [Complex.norm_real, Real.norm_eq_abs] at hn
      have him : (φInv (fun k => (x k : ℂ)) m).im = 0 := by
        dsimp [φInv]
        have h_eq : ((x m : ℂ) - x₀ m) * (r : ℂ)⁻¹ = (((x m - x₀ m) * r⁻¹ : ℝ) : ℂ) := by
          push_cast; rfl
        rw [h_eq]
        exact mzArtanhC_ofReal_im hu_abs
      exact (Complex.re_add_im _).symm.trans (by simp [u, him])
    dsimp [H]
    rw [hφ_real, hF_real u]
    dsimp [g₀]
    congr 1
    ext m
    have h_inv_m := hψ_φInv hx m
    rw [hφ_real, hψC_real u m] at h_inv_m
    exact Complex.ofReal_inj.mp h_inv_m
  have hH_branch : ∀ (m : Fin N),
      ∀ z ∈ Metric.ball x₀_c ρ ∩ LocalCrossBranch N x₀ r R m, H z = f_br m z := by
    intro m z ⟨hz_ball, hz_br⟩
    have hφ_strip : φInv z ∈ FlatStrip N α m := by
      refine ⟨?_, fun j hj => ?_⟩
      · have hsum : ∑ k : Fin N, |(φInv z k).im| < α := hφInv_maps hz_ball
        exact (Finset.single_le_sum (f := fun k : Fin N => |(φInv z k).im|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ m)).trans_lt hsum
      · have hj_im : (z j).im = 0 := (hz_br.2.2 j hj).1
        have hj_eq : z j = ((z j).re : ℂ) :=
          (Complex.re_add_im (z j)).symm.trans (by simp [hj_im])
        have hlt := h_arg_lt hz_ball j
        rw [hj_eq] at hlt
        have hu_abs : |((z j).re - x₀ j) * r⁻¹| < 1 / 2 := by
          have h_eq : ((((z j).re - x₀ j) * r⁻¹ : ℝ) : ℂ) =
              (((z j).re : ℂ) - x₀ j) * (r : ℂ)⁻¹ := by push_cast; rfl
          have hn : ‖((((z j).re - x₀ j) * r⁻¹ : ℝ) : ℂ)‖ < 1 / 2 := by
            rw [h_eq]
            exact hlt.trans_le (hρ_div_le_quarter.trans (by norm_num))
          rwa [Complex.norm_real, Real.norm_eq_abs] at hn
        dsimp [φInv]
        rw [hj_eq]
        have h_eq : (((z j).re : ℂ) - x₀ j) * (r : ℂ)⁻¹ =
            ((((z j).re - x₀ j) * r⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [h_eq]
        exact mzArtanhC_ofReal_im hu_abs
    dsimp [H]
    rw [hF_strip m (φInv z) hφ_strip]
    dsimp [g_br]
    congr 1
    ext j
    exact hψ_φInv hz_ball j
  refine ⟨H, hH_holo, hH_bdd, hH_real, hH_branch, fun m => ?_⟩
  let sl : ℂ → (Fin N → ℂ) := fun ζ => Function.update x₀_c m ζ
  have hsl_diff : Differentiable ℂ sl := by
    refine differentiable_pi.mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm; simp only [sl, Function.update_self]; exact differentiable_id
    · simp only [sl, Function.update_of_ne hjm]; exact differentiable_const _
  have hsl_maps : Set.MapsTo sl (Metric.ball (x₀ m : ℂ) ρ) (Metric.ball x₀_c ρ) := by
    intro ζ hζ
    rw [Metric.mem_ball] at hζ ⊢
    refine (dist_pi_lt_iff hρ_pos).mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm; simpa [sl, x₀_c] using hζ
    · simp [sl, hjm, hρ_pos]
  have hsl_holo : DifferentiableOn ℂ (fun ζ => H (Function.update x₀_c m ζ))
      (Metric.ball (x₀ m : ℂ) ρ) :=
    hH_holo.comp hsl_diff.differentiableOn hsl_maps
  have hρ2_pos : 0 < ρ / 2 := half_pos hρ_pos
  have hsl_cb : DifferentiableOn ℂ (fun ζ => H (Function.update x₀_c m ζ))
      (Metric.closedBall (x₀_c m) (ρ / 2)) :=
    hsl_holo.mono (Metric.closedBall_subset_ball (half_lt_self hρ_pos))
  rw [partial_deriv_pi_eq_intervalIntegral H x₀_c m (ρ / 2) hρ2_pos hsl_cb,
    norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h_int_bd :
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
        (I / (↑(ρ / 2) * exp (↑θ * I))) *
          H (Function.update x₀_c m (x₀_c m + ↑(ρ / 2) * exp (↑θ * I)))‖ ≤
        ((ρ / 2)⁻¹ * M) * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_mul, norm_div, Complex.norm_I, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ2_pos.le, Complex.norm_exp_ofReal_mul_I, mul_one, one_div]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hρ2_pos.le)
    refine hH_bdd _ (hsl_maps ?_)
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hρ2_pos.le, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact half_lt_self hρ_pos
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ *
        ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
          (I / (↑(ρ / 2) * exp (↑θ * I))) *
            H (Function.update x₀_c m (x₀_c m + ↑(ρ / 2) * exp (↑θ * I)))‖
      ≤ (2 * Real.pi)⁻¹ * (((ρ / 2)⁻¹ * M) * |2 * Real.pi - 0|) :=
        mul_le_mul_of_nonneg_left h_int_bd (inv_nonneg.mpr h2pi_pos.le)
    _ = 2 * M / ρ := by
        rw [sub_zero, abs_of_pos h2pi_pos]
        field_simp [h2pi_pos.ne', hρ_pos.ne']

section Phase1LogTime

def SectorCone (θ : ℝ) : Set ℂ :=
  { τ : ℂ | 0 < τ.re ∧ |τ.im| < τ.re * Real.tan θ }

lemma mem_sectorCone_iff_exists_exp {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (τ : ℂ) :
    τ ∈ SectorCone θ ↔ ∃ w : ℂ, |w.im| < θ ∧ Complex.exp w = τ := by
  constructor
  · intro ⟨hre, him⟩
    have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hre
    refine ⟨Complex.log τ, ?_, Complex.exp_log hτ_ne⟩
    rw [Complex.log_im]
    have harg_lt : |τ.arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    have htan_arg : Real.tan τ.arg = τ.im / τ.re := Complex.tan_arg τ
    have htan_abs : Real.tan |τ.arg| < Real.tan θ := by
      have h1 : |Real.tan τ.arg| < Real.tan θ := by
        rw [htan_arg, abs_div, abs_of_pos hre, div_lt_iff₀ hre, mul_comm]
        exact him
      have h_eq : Real.tan |τ.arg| = |Real.tan τ.arg| := by
        rcases le_or_gt 0 τ.arg with ha | ha
        · rw [abs_of_nonneg ha, abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha
            (abs_lt.mp harg_lt).2.le)]
        · rw [abs_of_neg ha, Real.tan_neg, abs_of_nonpos]
          have hpos := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (neg_nonneg.mpr ha.le)
            (by linarith [(abs_lt.mp harg_lt).1])
          rw [Real.tan_neg] at hpos
          linarith
      rwa [h_eq]
    by_contra hge
    have hle : θ ≤ |τ.arg| := not_lt.mp hge
    have hmono := Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith, hθpi⟩ ⟨by linarith [abs_nonneg τ.arg], harg_lt⟩ hle
    linarith
  · rintro ⟨w, hw, rfl⟩
    have hcos : 0 < Real.cos w.im :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_lt.mp hw], by linarith [abs_lt.mp hw]⟩
    have hre : 0 < (Complex.exp w).re := by
      rw [Complex.exp_re]
      exact mul_pos (Real.exp_pos _) hcos
    refine ⟨hre, ?_⟩
    rw [Complex.exp_im, Complex.exp_re, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
    refine mul_lt_mul_of_pos_left ?_ (Real.exp_pos _)
    have h_tan : |Real.sin w.im| / Real.cos w.im < Real.tan θ := by
      have h_eq : |Real.sin w.im| / Real.cos w.im = Real.tan |w.im| := by
        rw [← abs_of_pos hcos, ← abs_div, ← Real.tan_eq_sin_div_cos]
        rcases le_or_gt 0 w.im with ha | ha
        · rw [abs_of_nonneg ha, abs_of_nonneg (Real.tan_nonneg_of_nonneg_of_le_pi_div_two ha
            (by linarith [abs_lt.mp hw]))]
        · rw [abs_of_neg ha, Real.tan_neg, abs_of_nonpos]
          have hpos := Real.tan_nonneg_of_nonneg_of_le_pi_div_two (neg_nonneg.mpr ha.le)
            (by linarith [(abs_lt.mp hw).1])
          rw [Real.tan_neg] at hpos
          linarith
      rw [h_eq]
      exact Real.strictMonoOn_tan
        ⟨by linarith [abs_nonneg w.im], by linarith⟩
        ⟨by linarith, hθpi⟩ hw
    rwa [div_lt_iff₀ hcos, mul_comm] at h_tan

lemma re_pos_iff_exists_exp (τ : ℂ) :
    0 < τ.re ↔ ∃ w : ℂ, |w.im| < Real.pi / 2 ∧ Complex.exp w = τ := by
  constructor
  · intro hre
    have hτ_ne : τ ≠ 0 := fun h => by simp [h] at hre
    refine ⟨Complex.log τ, ?_, Complex.exp_log hτ_ne⟩
    rw [Complex.log_im]
    exact Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  · rintro ⟨w, hw, rfl⟩
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp hw).1, (abs_lt.mp hw).2⟩)

noncomputable def logTimeDamp (w : ℂ) : ℂ :=
  Complex.exp w / (1 + Complex.exp w) ^ 2

lemma re_one_add_exp_pos_of_abs_im_lt_pi_div_two {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    1 < (1 + Complex.exp w).re := by
  have hre : 0 < (Complex.exp w).re := by
    rw [Complex.exp_re]
    exact mul_pos (Real.exp_pos _)
      (Real.cos_pos_of_mem_Ioo ⟨(abs_lt.mp hw).1, (abs_lt.mp hw).2⟩)
  simp [hre]

lemma one_add_exp_ne_zero_of_abs_im_lt_pi_div_two {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    1 + Complex.exp w ≠ 0 := by
  intro h
  have hre := re_one_add_exp_pos_of_abs_im_lt_pi_div_two hw
  rw [h, Complex.zero_re] at hre
  linarith

lemma differentiableOn_logTimeDamp :
    DifferentiableOn ℂ logTimeDamp { w : ℂ | |w.im| < Real.pi / 2 } := by
  intro w hw
  have hne : (1 + Complex.exp w) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (one_add_exp_ne_zero_of_abs_im_lt_pi_div_two hw)
  exact ((Complex.differentiable_exp.differentiableAt).div
    (((differentiableAt_const (1 : ℂ)).add Complex.differentiable_exp.differentiableAt).pow 2)
    hne).differentiableWithinAt

lemma norm_sq_one_add_of_re_pos {τ : ℂ} (hτ : 0 < τ.re) :
    1 + ‖τ‖ ^ 2 < ‖1 + τ‖ ^ 2 := by
  have h1 : ‖1 + τ‖ ^ 2 = (1 + τ.re) ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [sq]
  have h2 : ‖τ‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [sq]
  nlinarith

lemma norm_logTimeDamp_mul_le {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    ‖logTimeDamp w‖ * (1 + ‖Complex.exp w‖ + ‖Complex.exp w‖⁻¹) ≤ 3 / 2 := by
  have hre : 0 < (Complex.exp w).re := (re_pos_iff_exists_exp _).mpr ⟨w, hw, rfl⟩
  have hnorm_pos : 0 < ‖Complex.exp w‖ := norm_pos_iff.mpr (Complex.exp_ne_zero w)
  have hsq : 1 + ‖Complex.exp w‖ ^ 2 < ‖1 + Complex.exp w‖ ^ 2 :=
    norm_sq_one_add_of_re_pos hre
  have h_amgm : 2 * ‖Complex.exp w‖ ≤ 1 + ‖Complex.exp w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖Complex.exp w‖ - 1)]
  have h_num : ‖Complex.exp w‖ * (1 + ‖Complex.exp w‖ + ‖Complex.exp w‖⁻¹) =
      1 + ‖Complex.exp w‖ + ‖Complex.exp w‖ ^ 2 := by
    field_simp [hnorm_pos.ne']
    ring
  have h_le : 1 + ‖Complex.exp w‖ + ‖Complex.exp w‖ ^ 2 ≤
      (3 / 2 : ℝ) * (1 + ‖Complex.exp w‖ ^ 2) := by
    linarith
  have h_den_pos : 0 < ‖1 + Complex.exp w‖ ^ 2 := by nlinarith [sq_nonneg ‖Complex.exp w‖]
  unfold logTimeDamp
  rw [norm_div, norm_pow, div_mul_eq_mul_div, h_num, div_le_iff₀ h_den_pos]
  nlinarith

lemma norm_logTimeDamp_le_half {w : ℂ} (hw : |w.im| < Real.pi / 2) :
    ‖logTimeDamp w‖ ≤ 1 / 2 := by
  have hre : 0 < (Complex.exp w).re := (re_pos_iff_exists_exp _).mpr ⟨w, hw, rfl⟩
  have hsq : 1 + ‖Complex.exp w‖ ^ 2 < ‖1 + Complex.exp w‖ ^ 2 :=
    norm_sq_one_add_of_re_pos hre
  have h_amgm : 2 * ‖Complex.exp w‖ ≤ 1 + ‖Complex.exp w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖Complex.exp w‖ - 1)]
  have h_den_pos : 0 < ‖1 + Complex.exp w‖ ^ 2 := by nlinarith [sq_nonneg ‖Complex.exp w‖]
  unfold logTimeDamp
  rw [norm_div, norm_pow, div_le_iff₀ h_den_pos]
  linarith

lemma one_add_exp_re_inv_mul_logTimeDamp_le {w : ℂ} {α : ℝ}
    (hα_lt : α < Real.pi / 2) (hw : |w.im| ≤ α) :
    ‖logTimeDamp w‖ * (1 + ((Complex.exp w).re)⁻¹) ≤ 2 / Real.cos α := by
  have hw_lt : |w.im| < Real.pi / 2 := lt_of_le_of_lt hw hα_lt
  have hcos_α_pos : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg w.im], hα_lt⟩
  have hcos_le : Real.cos α ≤ Real.cos w.im := by
    rw [← Real.cos_abs w.im]
    exact Real.strictAntiOn_cos.antitoneOn
      ⟨abs_nonneg _, hw_lt.le.trans (by linarith [Real.pi_pos])⟩
      ⟨by linarith [abs_nonneg w.im], hα_lt.le.trans (by linarith [Real.pi_pos])⟩ hw
  have hre_ge : ‖Complex.exp w‖ * Real.cos α ≤ (Complex.exp w).re := by
    rw [Complex.norm_exp, Complex.exp_re]
    exact mul_le_mul_of_nonneg_left hcos_le (Real.exp_pos _).le
  have hnorm_pos : 0 < ‖Complex.exp w‖ := norm_pos_iff.mpr (Complex.exp_ne_zero w)
  have hre_inv : ((Complex.exp w).re)⁻¹ ≤ (Real.cos α)⁻¹ * ‖Complex.exp w‖⁻¹ := by
    rw [← mul_inv, mul_comm]
    exact inv_anti₀ (mul_pos hnorm_pos hcos_α_pos) hre_ge
  have hcos_le_one : Real.cos α ≤ 1 := Real.cos_le_one α
  have h1_le : (1 : ℝ) ≤ (Real.cos α)⁻¹ := (one_le_inv₀ hcos_α_pos).mpr hcos_le_one
  have h_sum : 1 + ((Complex.exp w).re)⁻¹ ≤
      (Real.cos α)⁻¹ * (1 + ‖Complex.exp w‖ + ‖Complex.exp w‖⁻¹) := by
    nlinarith [norm_nonneg (Complex.exp w), inv_nonneg.mpr hcos_α_pos.le]
  have h_base := norm_logTimeDamp_mul_le hw_lt
  calc ‖logTimeDamp w‖ * (1 + ((Complex.exp w).re)⁻¹)
      ≤ ‖logTimeDamp w‖ * ((Real.cos α)⁻¹ * (1 + ‖Complex.exp w‖ + ‖Complex.exp w‖⁻¹)) :=
        mul_le_mul_of_nonneg_left h_sum (norm_nonneg _)
    _ = (Real.cos α)⁻¹ * (‖logTimeDamp w‖ * (1 + ‖Complex.exp w‖ + ‖Complex.exp w‖⁻¹)) := by ring
    _ ≤ (Real.cos α)⁻¹ * (3 / 2) :=
        mul_le_mul_of_nonneg_left h_base (inv_nonneg.mpr hcos_α_pos.le)
    _ ≤ (Real.cos α)⁻¹ * 2 :=
        mul_le_mul_of_nonneg_left (by norm_num) (inv_nonneg.mpr hcos_α_pos.le)
    _ = 2 / Real.cos α := by rw [div_eq_mul_inv, mul_comm]

end Phase1LogTime

section Phase1MidpointTube

def MidpointSet {D : ℕ} (U_A U_B : Set (Fin D → ℝ)) : Set (Fin D → ℝ) :=
  { y | ∃ yA ∈ U_A, ∃ yB ∈ U_B, y = (1 / 2 : ℝ) • yA + (1 / 2 : ℝ) • yB }

lemma isOpen_midpointSet {D : ℕ} {U_A U_B : Set (Fin D → ℝ)}
    (hB : IsOpen U_B) :
    IsOpen (MidpointSet U_A U_B) := by
  have h_eq : MidpointSet U_A U_B =
      ⋃ yA ∈ U_A, (fun y => (2 : ℝ) • (y - (1 / 2 : ℝ) • yA)) ⁻¹' U_B := by
    ext y
    simp only [MidpointSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨yA, hyA, yB, hyB, rfl⟩
      refine ⟨yA, hyA, ?_⟩
      have h_simp : (2 : ℝ) • (((1 / 2 : ℝ) • yA + (1 / 2 : ℝ) • yB) - (1 / 2 : ℝ) • yA) = yB := by
        ext j; simp
      rwa [h_simp]
    · rintro ⟨yA, hyA, hyB⟩
      refine ⟨yA, hyA, (2 : ℝ) • (y - (1 / 2 : ℝ) • yA), hyB, ?_⟩
      ext j; simp
  rw [h_eq]
  refine isOpen_biUnion fun yA _ => hB.preimage ?_
  fun_prop

lemma convex_midpointSet {D : ℕ} {U_A U_B : Set (Fin D → ℝ)}
    (hA : Convex ℝ U_A) (hB : Convex ℝ U_B) :
    Convex ℝ (MidpointSet U_A U_B) := by
  rintro x ⟨xA, hxA, xB, hxB, rfl⟩ y ⟨yA, hyA, yB, hyB, rfl⟩ a b ha hb hab
  refine ⟨a • xA + b • yA, hA hxA hyA ha hb hab, a • xB + b • yB, hB hxB hyB ha hb hab, ?_⟩
  ext j; simp; ring

lemma inter_subset_midpointSet {D : ℕ} {U_A U_B : Set (Fin D → ℝ)} :
    U_A ∩ U_B ⊆ MidpointSet U_A U_B := by
  intro y ⟨hyA, hyB⟩
  refine ⟨y, hyA, y, hyB, ?_⟩
  ext j; simp; ring

lemma symmetric_midpointSet {D : ℕ} {U_A U_B : Set (Fin D → ℝ)}
    (hA : ∀ y ∈ U_A, -y ∈ U_A) (hB : ∀ y ∈ U_B, -y ∈ U_B) :
    ∀ y ∈ MidpointSet U_A U_B, -y ∈ MidpointSet U_A U_B := by
  rintro y ⟨yA, hyA, yB, hyB, rfl⟩
  refine ⟨-yA, hA yA hyA, -yB, hB yB hyB, ?_⟩
  ext j; simp; ring

lemma tubeDomain_eqOn_of_starShaped {D : ℕ} {V : Set (Fin D → ℝ)} {δ : ℝ}
    (hV_open : IsOpen V) (hδ : 0 < δ)
    (hV_star : ∀ y ∈ V, ∀ s ∈ Set.Icc (0 : ℝ) 1, s • y ∈ V)
    {f g : (Fin D → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f (TubeDomain V))
    (hg : DifferentiableOn ℂ g (TubeDomain V))
    (h_eq_ball : Set.EqOn f g (TubeDomain (Metric.ball 0 δ))) :
    Set.EqOn f g (TubeDomain V) := by
  intro z₀ hz₀
  let γ : ℂ → (Fin D → ℂ) := fun ζ j => ((z₀ j).re : ℂ) + ζ * (I * ((z₀ j).im : ℂ))
  have hγ_diff : Differentiable ℂ γ :=
    differentiable_pi.mpr fun j =>
      (differentiable_const _).add (differentiable_id.mul (differentiable_const _))
  have hγ_im : ∀ (ζ : ℂ) (j : Fin D), (γ ζ j).im = ζ.re * (z₀ j).im := by
    intro ζ j
    dsimp [γ]
    simp [Complex.mul_im]
  have hγ_mem : ∀ ζ : ℂ, ζ.re • (fun j => (z₀ j).im) ∈ V → γ ζ ∈ TubeDomain V := by
    intro ζ hζ
    change (fun j => (γ ζ j).im) ∈ V
    have h_eq : (fun j => (γ ζ j).im) = ζ.re • (fun j => (z₀ j).im) := by
      ext j; exact hγ_im ζ j
    rw [h_eq]
    exact hζ
  let K : Set ℝ := Set.Icc 0 1
  have h_sub_Icc : ∀ s ∈ K, s • (fun j => (z₀ j).im) ∈ V := fun s hs => hV_star _ hz₀ s hs
  have h_open_pre : IsOpen { s : ℝ | s • (fun j => (z₀ j).im) ∈ V } :=
    hV_open.preimage (continuous_id.smul continuous_const)
  have h_exists_eps : ∃ η > 0, Set.Ioo (-η) (1 + η) ⊆ { s : ℝ | s • (fun j => (z₀ j).im) ∈ V } := by
    have h0 : (0 : ℝ) ∈ { s : ℝ | s • (fun j => (z₀ j).im) ∈ V } := by
      simpa using h_sub_Icc 0 ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ { s : ℝ | s • (fun j => (z₀ j).im) ∈ V } := by
      simpa using h_sub_Icc 1 ⟨zero_le_one, le_rfl⟩
    rcases Metric.isOpen_iff.mp h_open_pre 0 h0 with ⟨η₀, hη₀, hsub₀⟩
    rcases Metric.isOpen_iff.mp h_open_pre 1 h1 with ⟨η₁, hη₁, hsub₁⟩
    refine ⟨min η₀ η₁, lt_min hη₀ hη₁, fun s hs => ?_⟩
    by_cases hs0 : s < 0
    · refine hsub₀ ?_
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg hs0]
      linarith [hs.1, min_le_left η₀ η₁]
    · by_cases hs1 : s ≤ 1
      · exact h_sub_Icc s ⟨not_lt.mp hs0, hs1⟩
      · refine hsub₁ ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
        linarith [hs.2, min_le_right η₀ η₁]
  obtain ⟨η, hη_pos, hη_sub⟩ := h_exists_eps
  let S : Set ℂ := { ζ : ℂ | -η < ζ.re ∧ ζ.re < 1 + η }
  have hS_open : IsOpen S :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hS_conv : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    have ha1 : -η < a.re := ha.1
    have ha2 : a.re < 1 + η := ha.2
    have hb1 : -η < b.re := hb.1
    have hb2 : b.re < 1 + η := hb.2
    refine ⟨?_, ?_⟩
    · change -η < (u • a + v • b).re
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rcases eq_or_lt_of_le hu with rfl | hu' <;> nlinarith
    · change (u • a + v • b).re < 1 + η
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      rcases eq_or_lt_of_le hu with rfl | hu' <;> nlinarith
  have hγ_maps : Set.MapsTo γ S (TubeDomain V) := fun ζ hζ => hγ_mem ζ (hη_sub ⟨hζ.1, hζ.2⟩)
  have hfγ : AnalyticOnNhd ℂ (f ∘ γ) S :=
    (Complex.analyticOnNhd_iff_differentiableOn hS_open).mpr
      (hf.comp hγ_diff.differentiableOn hγ_maps)
  have hgγ : AnalyticOnNhd ℂ (g ∘ γ) S :=
    (Complex.analyticOnNhd_iff_differentiableOn hS_open).mpr
      (hg.comp hγ_diff.differentiableOn hγ_maps)
  have h0_mem : (0 : ℂ) ∈ S := by
    simp only [S, Set.mem_setOf_eq, Complex.zero_re]
    exact ⟨by linarith, by linarith⟩
  have h1_mem : (1 : ℂ) ∈ S := by
    simp only [S, Set.mem_setOf_eq, Complex.one_re]
    exact ⟨by linarith, by linarith⟩
  have h_ev : (f ∘ γ) =ᶠ[𝓝 (0 : ℂ)] (g ∘ γ) := by
    let r₀ : ℝ := min η (δ / (‖fun j => (z₀ j).im‖ + 1))
    have hr₀ : 0 < r₀ := lt_min hη_pos (div_pos hδ (by positivity))
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr₀] with ζ hζ
    have hζ_norm : ‖ζ‖ < r₀ := by simpa [Metric.mem_ball, dist_eq_norm] using hζ
    have hζ_re : |ζ.re| < r₀ := (Complex.abs_re_le_norm ζ).trans_lt hζ_norm
    refine h_eq_ball ?_
    change (fun j => (γ ζ j).im) ∈ Metric.ball 0 δ
    rw [Metric.mem_ball, dist_zero_right]
    have h_eq_im : (fun j => (γ ζ j).im) = ζ.re • (fun j => (z₀ j).im) := by
      ext j; exact hγ_im ζ j
    rw [h_eq_im, norm_smul, Real.norm_eq_abs]
    have h1 : |ζ.re| < δ / (‖fun j => (z₀ j).im‖ + 1) :=
      lt_of_lt_of_le hζ_re (min_le_right _ _)
    have h_den : 0 < ‖fun j => (z₀ j).im‖ + 1 := by positivity
    have h2 := (lt_div_iff₀ h_den).mp h1
    nlinarith [abs_nonneg ζ.re]
  have h_eq_all := hfγ.eqOn_of_preconnected_of_eventuallyEq hgγ hS_conv.isPreconnected h0_mem h_ev
  have h_at_1 := h_eq_all h1_mem
  have hγ1 : γ 1 = z₀ := by
    ext j
    dsimp [γ]
    rw [one_mul, mul_comm I, Complex.re_add_im]
  simpa only [Function.comp_apply, hγ1] using h_at_1

def mzParamMap {D : ℕ} (yA yB : Fin D → ℝ) (z : Fin D → ℂ) (ζ : Fin 2 → ℂ) : Fin D → ℂ :=
  fun j => z j + ζ 0 * (yA j : ℂ) + ζ 1 * (yB j : ℂ)

def mzParamF0 {D : ℕ} (F_A : (Fin D → ℂ) → ℂ) (yA yB : Fin D → ℝ)
    (z : Fin D → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  F_A (mzParamMap yA yB z (fun k => (x k : ℂ)))

def mzParamBr {D : ℕ} (F_A F_B : (Fin D → ℂ) → ℂ) (yA yB : Fin D → ℝ)
    (z : Fin D → ℂ) (m : Fin 2) (ζ : Fin 2 → ℂ) : ℂ :=
  if m = 0 then F_A (mzParamMap yA yB z ζ) else F_B (mzParamMap yA yB z ζ)

lemma mzParamMap_im {D : ℕ} (yA yB : Fin D → ℝ) (z : Fin D → ℂ) (ζ : Fin 2 → ℂ) (j : Fin D) :
    (mzParamMap yA yB z ζ j).im = (z j).im + (ζ 0).im * yA j + (ζ 1).im * yB j := by
  dsimp [mzParamMap]
  simp [Complex.mul_im]

lemma differentiable_mzParamMap_left {D : ℕ} (yA yB : Fin D → ℝ) (ζ : Fin 2 → ℂ) :
    Differentiable ℂ (fun z : Fin D → ℂ => mzParamMap yA yB z ζ) :=
  differentiable_pi.mpr fun j =>
    ((differentiable_apply j).add (differentiable_const _)).add (differentiable_const _)

lemma differentiable_mzParamMap_right {D : ℕ} (yA yB : Fin D → ℝ) (z : Fin D → ℂ) :
    Differentiable ℂ (fun ζ : Fin 2 → ℂ => mzParamMap yA yB z ζ) :=
  differentiable_pi.mpr fun _ =>
    ((differentiable_const _).add ((differentiable_apply 0).mul (differentiable_const _))).add
      ((differentiable_apply 1).mul (differentiable_const _))

lemma differentiable_mzParamMap_uncurry {D : ℕ} (yA yB : Fin D → ℝ) :
    Differentiable ℂ (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) => mzParamMap yA yB p.1 p.2) := by
  refine differentiable_pi.mpr fun j => ?_
  dsimp [mzParamMap]
  fun_prop

lemma norm_deriv_le_of_ball_bound {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball c (2 * R)))
    (hbdd : ∀ u ∈ Metric.ball c (2 * R), ‖f u‖ ≤ M)
    {u : ℂ} (hu : u ∈ Metric.ball c R) :
    ‖deriv f u‖ ≤ M / R := by
  have hsub : Metric.closedBall u R ⊆ Metric.ball c (2 * R) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    rw [Metric.mem_ball, dist_eq_norm] at hu ⊢
    calc ‖w - c‖ = ‖(w - u) + (u - c)‖ := by ring_nf
      _ ≤ ‖w - u‖ + ‖u - c‖ := norm_add_le _ _
      _ < R + R := by linarith
      _ = 2 * R := by ring
  have h_eq : deriv f u = (2 * Real.pi * I : ℂ)⁻¹ • ∮ w in C(u, R), ((w - u) ^ 2)⁻¹ • f w := by
    have h_cauchy := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball hsub hf (Metric.mem_ball_self hR)
    exact h_cauchy.symm
  rw [h_eq, smul_eq_mul, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h_ci : ‖∮ w in C(u, R), ((w - u) ^ 2)⁻¹ • f w‖ ≤ 2 * Real.pi * R * (M / R ^ 2) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hR.le fun w hw => ?_
    have hw_dist : ‖w - u‖ = R := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hw
    rw [smul_eq_mul, norm_mul, norm_inv, norm_pow, hw_dist, ← div_eq_inv_mul]
    exact div_le_div_of_nonneg_right (hbdd w (hsub (Metric.sphere_subset_closedBall hw)))
      (sq_nonneg R)
  have h2pi_pos : 0 < 2 * Real.pi := by positivity
  calc (2 * Real.pi)⁻¹ * ‖∮ w in C(u, R), ((w - u) ^ 2)⁻¹ • f w‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * R * (M / R ^ 2)) :=
        mul_le_mul_of_nonneg_left h_ci (inv_nonneg.mpr h2pi_pos.le)
    _ = M / R := by field_simp [h2pi_pos.ne', hR.ne']

lemma mzParam_slice_holo_and_bdd {D : ℕ} {U U_A U_B : Set (Fin D → ℝ)}
    {yA yB : Fin D → ℝ} {r M : ℝ}
    {F_A F_B : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFB_holo : DifferentiableOn ℂ F_B (TubeDomain U_B))
    (hFA_bdd : ∀ w ∈ TubeDomain U_A, ‖F_A w‖ ≤ M)
    (hFB_bdd : ∀ w ∈ TubeDomain U_B, ‖F_B w‖ ≤ M)
    (h_shift_A : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamMap yA yB z ζ ∈ TubeDomain U_A)
    (h_shift_B : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 1,
      mzParamMap yA yB z ζ ∈ TubeDomain U_B)
    (h_agree : ∀ z ∈ TubeDomain U, ∀ x : Fin 2 → ℝ,
      F_A (mzParamMap yA yB z (fun k => (x k : ℂ))) =
        F_B (mzParamMap yA yB z (fun k => (x k : ℂ))))
    (hr : 0 < r) {z : Fin D → ℂ} (hz : z ∈ TubeDomain U) :
    Continuous (mzParamF0 F_A yA yB z) ∧
    (∀ x : Fin 2 → ℝ, ‖mzParamF0 F_A yA yB z x‖ ≤ M) ∧
    (∀ (m : Fin 2) (x : Fin 2 → ℝ),
      mzParamBr F_A F_B yA yB z m (fun k => (x k : ℂ)) = mzParamF0 F_A yA yB z x) ∧
    (∀ m : Fin 2, ContinuousOn (mzParamBr F_A F_B yA yB z m) (FlatStrip 2 r m)) ∧
    (∀ (m : Fin 2), ∀ ζ ∈ FlatStrip 2 r m, ‖mzParamBr F_A F_B yA yB z m ζ‖ ≤ M) ∧
    (∀ (m : Fin 2) (x : Fin 2 → ℝ),
      DifferentiableOn ℂ
        (fun w => mzParamBr F_A F_B yA yB z m (Function.update (fun k => (x k : ℂ)) m w))
        { w : ℂ | |w.im| < r }) := by
  have hreal_mem0 : ∀ x : Fin 2 → ℝ, (fun k => (x k : ℂ)) ∈ FlatStrip 2 r 0 :=
    fun x => ⟨by simp [hr], fun j _ => by simp⟩
  have h_f0_cont : Continuous (mzParamF0 F_A yA yB z) := by
    refine hFA_holo.continuousOn.comp_continuous ?_ fun x => h_shift_A z hz _ (hreal_mem0 x)
    exact (differentiable_mzParamMap_right yA yB z).continuous.comp
      (continuous_pi fun k => Complex.continuous_ofReal.comp (continuous_apply k))
  have h_f0_bdd : ∀ x : Fin 2 → ℝ, ‖mzParamF0 F_A yA yB z x‖ ≤ M :=
    fun x => hFA_bdd _ (h_shift_A z hz _ (hreal_mem0 x))
  have h_real : ∀ (m : Fin 2) (x : Fin 2 → ℝ),
      mzParamBr F_A F_B yA yB z m (fun k => (x k : ℂ)) = mzParamF0 F_A yA yB z x := by
    intro m x
    fin_cases m
    · rfl
    · dsimp [mzParamBr, mzParamF0]
      exact (h_agree z hz x).symm
  have h_cont_br : ∀ m : Fin 2, ContinuousOn (mzParamBr F_A F_B yA yB z m) (FlatStrip 2 r m) := by
    intro m
    fin_cases m
    · exact hFA_holo.continuousOn.comp
        (differentiable_mzParamMap_right yA yB z).continuous.continuousOn
        fun ζ hζ => h_shift_A z hz ζ hζ
    · exact hFB_holo.continuousOn.comp
        (differentiable_mzParamMap_right yA yB z).continuous.continuousOn
        fun ζ hζ => h_shift_B z hz ζ hζ
  have h_bdd_br : ∀ (m : Fin 2), ∀ ζ ∈ FlatStrip 2 r m, ‖mzParamBr F_A F_B yA yB z m ζ‖ ≤ M := by
    intro m ζ hζ
    fin_cases m
    · exact hFA_bdd _ (h_shift_A z hz ζ hζ)
    · exact hFB_bdd _ (h_shift_B z hz ζ hζ)
  have h_holo_br : ∀ (m : Fin 2) (x : Fin 2 → ℝ),
      DifferentiableOn ℂ
        (fun w => mzParamBr F_A F_B yA yB z m (Function.update (fun k => (x k : ℂ)) m w))
        { w : ℂ | |w.im| < r } := by
    intro m x
    have h_upd_diff : Differentiable ℂ (fun w : ℂ => Function.update (fun k => (x k : ℂ)) m w) := by
      refine differentiable_pi.mpr fun j => ?_
      by_cases hjm : j = m
      · subst hjm; simp only [Function.update_self]; exact differentiable_id
      · simp only [Function.update_of_ne hjm]; exact differentiable_const _
    have h_upd_maps : ∀ w : ℂ, |w.im| < r →
        Function.update (fun k => (x k : ℂ)) m w ∈ FlatStrip 2 r m := by
      intro w hw
      refine ⟨by simpa using hw, fun j hjm => by simp [Function.update_of_ne hjm]⟩
    fin_cases m
    · exact hFA_holo.comp
        ((differentiable_mzParamMap_right yA yB z).comp h_upd_diff).differentiableOn
        fun w hw => h_shift_A z hz _ (h_upd_maps w hw)
    · exact hFB_holo.comp
        ((differentiable_mzParamMap_right yA yB z).comp h_upd_diff).differentiableOn
        fun w hw => h_shift_B z hz _ (h_upd_maps w hw)
  exact ⟨h_f0_cont, h_f0_bdd, h_real, h_cont_br, h_bdd_br, h_holo_br⟩

lemma measurable_deriv_of_continuous_on_ball {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [BorelSpace Ω] {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → Ω → ℂ}
    (hf_cont : ∀ u ∈ Metric.ball c (2 * R), Continuous (f u))
    (hf_diff : ∀ x : Ω, DifferentiableAt ℂ (fun v => f v x) c) :
    Measurable (fun x : Ω => deriv (fun v => f v x) c) := by
  let seq : ℕ → Ω → ℂ := fun n x =>
    ((((n : ℝ) + 1) / R : ℝ) : ℂ) * (f (c + ((R / ((n : ℝ) + 1) : ℝ) : ℂ)) x - f c x)
  have h_meas : ∀ n : ℕ, Measurable (seq n) := by
    intro n
    have h_step_pos : 0 < R / ((n : ℝ) + 1) := by positivity
    have h_step_lt : R / ((n : ℝ) + 1) < 2 * R := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : R / ((n : ℝ) + 1) ≤ R := div_le_self hR.le h1
      linarith
    have hu_mem : c + ((R / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ Metric.ball c (2 * R) := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg h_step_pos.le]
      exact h_step_lt
    have hc_mem : c ∈ Metric.ball c (2 * R) := Metric.mem_ball_self (by positivity)
    exact (continuous_const.mul ((hf_cont _ hu_mem).sub (hf_cont c hc_mem))).measurable
  refine measurable_of_tendsto_metrizable h_meas (tendsto_pi_nhds.mpr fun x => ?_)
  have hsl := (hf_diff x).hasDerivAt.tendsto_slope_zero
  have h_inv : Tendsto (fun n : ℕ => ((R / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => R * ((n : ℝ) + 1)⁻¹) atTop (𝓝 (R * 0)) :=
        (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)).const_mul R
      have h2 : Tendsto (fun n : ℕ => R / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        simpa only [div_eq_mul_inv, mul_zero] using h1
      exact (Complex.continuous_ofReal.tendsto 0).comp h2
    · exact Complex.ofReal_ne_zero.mpr (div_pos hR (by positivity)).ne'
  refine (hsl.comp h_inv).congr fun n => ?_
  dsimp only [Function.comp_apply, seq]
  have hR_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hn_ne : ((n : ℝ) + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact_mod_cast this.ne'
  simp only [smul_eq_mul]
  push_cast
  field_simp [hR_ne, hn_ne]

lemma mzParam_gHat_differentiableAt {D : ℕ} {U U_A : Set (Fin D → ℝ)}
    {yA yB : Fin D → ℝ} {r M ε : ℝ}
    (hU_open : IsOpen U) (hr : 0 < r) (hM : 0 ≤ M) (hε : 0 < ε)
    {F_A : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFA_bdd : ∀ w ∈ TubeDomain U_A, ‖F_A w‖ ≤ M)
    (h_shift_A : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamMap yA yB z ζ ∈ TubeDomain U_A)
    {z₀ : Fin D → ℂ} (hz₀ : z₀ ∈ TubeDomain U) (m : Fin D) (ξ : Fin 2 → ℝ) :
    DifferentiableAt ℂ
      (fun u : ℂ => fourierTransformND
        (mzGaussianDamped (mzParamF0 F_A yA yB (Function.update z₀ m u)) ε) ξ)
      (z₀ m) := by
  have hTU_open : IsOpen (TubeDomain U) := isOpen_TubeDomain hU_open
  rcases Metric.isOpen_iff.mp hTU_open z₀ hz₀ with ⟨R₀, hR₀_pos, hR₀_sub⟩
  let R : ℝ := R₀ / 4
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have h_upd_in : ∀ u ∈ Metric.ball (z₀ m) (2 * R), Function.update z₀ m u ∈ TubeDomain U := by
    intro u hu
    refine hR₀_sub ?_
    rw [Metric.mem_ball] at hu ⊢
    refine (dist_pi_lt_iff hR₀_pos).mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm
      simp only [Function.update_self]
      have : 2 * R < R₀ := by dsimp [R]; linarith
      exact hu.trans this
    · simp [Function.update_of_ne hjm, hR₀_pos]
  let F_int : ℂ → (Fin 2 → ℝ) → ℂ := fun u x =>
    mzGaussianDamped (mzParamF0 F_A yA yB (Function.update z₀ m u)) ε x *
      Complex.exp (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ))
  have h_inner_holo : ∀ x : Fin 2 → ℝ,
      DifferentiableOn ℂ (fun u : ℂ => mzParamF0 F_A yA yB (Function.update z₀ m u) x)
        (Metric.ball (z₀ m) (2 * R)) := by
    intro x
    have h_upd_diff : Differentiable ℂ (fun u : ℂ => Function.update z₀ m u) := by
      refine differentiable_pi.mpr fun j => ?_
      by_cases hjm : j = m
      · subst hjm; simp only [Function.update_self]; exact differentiable_id
      · simp only [Function.update_of_ne hjm]; exact differentiable_const _
    refine hFA_holo.comp
      ((differentiable_mzParamMap_left yA yB (fun k => (x k : ℂ))).comp h_upd_diff).differentiableOn
      fun u hu => h_shift_A _ (h_upd_in u hu) _ ⟨by simp [hr], fun j _ => by simp⟩
  have h_inner_bdd : ∀ (x : Fin 2 → ℝ), ∀ u ∈ Metric.ball (z₀ m) (2 * R),
      ‖mzParamF0 F_A yA yB (Function.update z₀ m u) x‖ ≤ M :=
    fun x u hu => hFA_bdd _ (h_shift_A _ (h_upd_in u hu) _ ⟨by simp [hr], fun j _ => by simp⟩)
  let F'_int : ℂ → (Fin 2 → ℝ) → ℂ := fun u x =>
    deriv (fun v : ℂ => mzParamF0 F_A yA yB (Function.update z₀ m v) x) u *
      Complex.exp (-(ε : ℂ) * ∑ j : Fin 2, ((x j : ℂ) ^ 2)) *
      Complex.exp (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ))
  let bound : (Fin 2 → ℝ) → ℝ := fun x =>
    (M / R) * ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2)
  have h_bound_int : Integrable bound volume := by
    have h1 : Integrable (fun x : Fin 2 → ℝ => ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2)) volume := by
      have h_1d : ∀ _ : Fin 2, Integrable (fun t : ℝ => Real.exp (-ε * t ^ 2)) volume :=
        fun _ => integrable_exp_neg_mul_sq hε
      exact Integrable.fintype_prod h_1d
    exact h1.const_mul (M / R)
  have h_phase_norm : ∀ x : Fin 2 → ℝ,
      ‖Complex.exp (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ))‖ = 1 := by
    intro x
    rw [Complex.norm_exp]
    have h_re : (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ)).re = 0 := by
      rw [Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_eq_zero fun j _ => by simp
    rw [h_re, Real.exp_zero]
  have h_gauss_norm : ∀ x : Fin 2 → ℝ,
      ‖Complex.exp (-(ε : ℂ) * ∑ j : Fin 2, ((x j : ℂ) ^ 2))‖ =
        ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2) := by
    intro x
    rw [Complex.norm_exp, ← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [sq]
  have hf0_cont_on : ∀ u ∈ Metric.ball (z₀ m) (2 * R),
      Continuous (mzParamF0 F_A yA yB (Function.update z₀ m u)) := fun u hu =>
    hFA_holo.continuousOn.comp_continuous
      ((differentiable_mzParamMap_right yA yB _).continuous.comp
        (continuous_pi fun k => Complex.continuous_ofReal.comp (continuous_apply k)))
      fun x => h_shift_A _ (h_upd_in u hu) _ ⟨by simp [hr], fun j _ => by simp⟩
  have h_meas_F : ∀ᶠ u in 𝓝 (z₀ m), AEStronglyMeasurable (F_int u) volume := by
    filter_upwards [Metric.ball_mem_nhds (z₀ m) hR_pos] with u hu
    have hu2 : u ∈ Metric.ball (z₀ m) (2 * R) := Metric.ball_subset_ball (by linarith) hu
    have h_g_cont :
        Continuous (mzGaussianDamped (mzParamF0 F_A yA yB (Function.update z₀ m u)) ε) := by
      unfold mzGaussianDamped
      refine (hf0_cont_on u hu2).mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
      exact continuous_finsetSum Finset.univ fun j _ =>
        (Complex.continuous_ofReal.comp (continuous_apply j)).pow 2
    refine (h_g_cont.mul
      (Complex.continuous_exp.comp (continuous_const.mul ?_))).aestronglyMeasurable
    exact continuous_finsetSum Finset.univ fun j _ =>
      (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const
  have h_int_F0 : Integrable (F_int (z₀ m)) volume := by
    have h_base : Integrable
        (mzGaussianDamped (mzParamF0 F_A yA yB (Function.update z₀ m (z₀ m))) ε) volume :=
      integrable_mzGaussianDamped hM
        (hf0_cont_on (z₀ m) (Metric.mem_ball_self (by positivity)))
        (fun x => h_inner_bdd x (z₀ m) (Metric.mem_ball_self (by positivity))) hε
    refine h_base.norm.mono' (h_meas_F.self_of_nhds) (Filter.Eventually.of_forall fun x => ?_)
    dsimp [F_int]
    rw [norm_mul, h_phase_norm x, mul_one]
  have h_meas_F' : AEStronglyMeasurable (F'_int (z₀ m)) volume := by
    have hm1 : Measurable (fun x : Fin 2 → ℝ =>
        deriv (fun v => mzParamF0 F_A yA yB (Function.update z₀ m v) x) (z₀ m)) :=
      measurable_deriv_of_continuous_on_ball hR_pos hf0_cont_on fun x =>
        (h_inner_holo x).differentiableAt (Metric.isOpen_ball.mem_nhds
          (Metric.mem_ball_self (by positivity)))
    have hc2 : Continuous (fun x : Fin 2 → ℝ =>
        Complex.exp (-(ε : ℂ) * ∑ j : Fin 2, ((x j : ℂ) ^ 2))) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum Finset.univ fun j _ =>
          (Complex.continuous_ofReal.comp (continuous_apply j)).pow 2))
    have hc3 : Continuous (fun x : Fin 2 → ℝ =>
        Complex.exp (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul
        (continuous_finsetSum Finset.univ fun j _ =>
          (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const))
    exact ((hm1.mul hc2.measurable).mul hc3.measurable).aestronglyMeasurable
  have h_bound : ∀ᵐ x ∂volume, ∀ u ∈ Metric.ball (z₀ m) R, ‖F'_int u x‖ ≤ bound x := by
    refine Filter.Eventually.of_forall fun x u hu => ?_
    dsimp [F'_int, bound]
    rw [norm_mul, norm_mul, h_phase_norm x, mul_one, h_gauss_norm x]
    exact mul_le_mul_of_nonneg_right
      (norm_deriv_le_of_ball_bound hR_pos (h_inner_holo x) (h_inner_bdd x) hu)
      (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  have h_deriv : ∀ᵐ x ∂volume, ∀ u ∈ Metric.ball (z₀ m) R,
      HasDerivAt (fun v => F_int v x) (F'_int u x) u := by
    refine Filter.Eventually.of_forall fun x u hu => ?_
    have hda : DifferentiableAt ℂ
        (fun v => mzParamF0 F_A yA yB (Function.update z₀ m v) x) u :=
      (h_inner_holo x).differentiableAt (Metric.isOpen_ball.mem_nhds
        (Metric.ball_subset_ball (by linarith) hu))
    dsimp [F_int, F'_int, mzGaussianDamped]
    exact (hda.hasDerivAt.mul_const _).mul_const _
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (z₀ m) hR_pos) h_meas_F h_int_F0 h_meas_F' h_bound h_bound_int
    h_deriv).2.differentiableAt

lemma mzParam_mzFEps_differentiableAt_left {D : ℕ} {U U_A U_B : Set (Fin D → ℝ)}
    {yA yB : Fin D → ℝ} {r M ε : ℝ}
    (hU_open : IsOpen U) (hr : 0 < r) (hM : 0 ≤ M) (hε : 0 < ε)
    {F_A F_B : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFB_holo : DifferentiableOn ℂ F_B (TubeDomain U_B))
    (hFA_bdd : ∀ w ∈ TubeDomain U_A, ‖F_A w‖ ≤ M)
    (hFB_bdd : ∀ w ∈ TubeDomain U_B, ‖F_B w‖ ≤ M)
    (h_shift_A : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamMap yA yB z ζ ∈ TubeDomain U_A)
    (h_shift_B : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 1,
      mzParamMap yA yB z ζ ∈ TubeDomain U_B)
    (h_agree : ∀ z ∈ TubeDomain U, ∀ x : Fin 2 → ℝ,
      F_A (mzParamMap yA yB z (fun k => (x k : ℂ))) =
        F_B (mzParamMap yA yB z (fun k => (x k : ℂ))))
    {z₀ : Fin D → ℂ} (hz₀ : z₀ ∈ TubeDomain U) (m : Fin D)
    {ζ₀ : Fin 2 → ℂ} (hζ₀ : ζ₀ ∈ TubeDomain (Octahedron 2 r)) :
    DifferentiableAt ℂ
      (fun u : ℂ => mzFEps (mzParamF0 F_A yA yB (Function.update z₀ m u)) ε ζ₀)
      (z₀ m) := by
  have hTU_open : IsOpen (TubeDomain U) := isOpen_TubeDomain hU_open
  rcases Metric.isOpen_iff.mp hTU_open z₀ hz₀ with ⟨R₀, hR₀_pos, hR₀_sub⟩
  let R : ℝ := R₀ / 4
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have h_upd_in : ∀ u ∈ Metric.ball (z₀ m) (2 * R), Function.update z₀ m u ∈ TubeDomain U := by
    intro u hu
    refine hR₀_sub ?_
    rw [Metric.mem_ball] at hu ⊢
    refine (dist_pi_lt_iff hR₀_pos).mpr fun j => ?_
    by_cases hjm : j = m
    · subst hjm
      simp only [Function.update_self]
      have : 2 * R < R₀ := by dsimp [R]; linarith
      exact hu.trans this
    · simp [Function.update_of_ne hjm, hR₀_pos]
  let S_y : ℝ := ∑ j : Fin 2, |(ζ₀ j).im|
  have hSy_lt : S_y < r := hζ₀
  have hSy_nn : 0 ≤ S_y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let β : ℝ := (S_y + r) / 2
  have hβ_pos : 0 < β := by dsimp [β]; linarith
  have hβ_lt : β < r := by dsimp [β]; linarith
  let δ : ℝ := (β - S_y) / 4
  have hδ_pos : 0 < δ := by dsimp [δ, β]; linarith
  let C_β : ℝ := M * Real.exp (ε * β ^ 2) *
    ∫ x : Fin 2 → ℝ, ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2)
  have hC_nn : 0 ≤ C_β :=
    mul_nonneg (mul_nonneg hM (Real.exp_pos _).le)
      (integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  let gHat : ℂ → (Fin 2 → ℝ) → ℂ := fun u ξ =>
    fourierTransformND (mzGaussianDamped (mzParamF0 F_A yA yB (Function.update z₀ m u)) ε) ξ
  have hgHat_holo : ∀ ξ : Fin 2 → ℝ,
      DifferentiableOn ℂ (fun u : ℂ => gHat u ξ) (Metric.ball (z₀ m) (2 * R)) := by
    intro ξ u hu
    have hz_u : Function.update z₀ m u ∈ TubeDomain U := h_upd_in u hu
    have hda := mzParam_gHat_differentiableAt hU_open hr hM hε hFA_holo hFA_bdd h_shift_A hz_u m ξ
    have h_eq : (fun v : ℂ => fourierTransformND
        (mzGaussianDamped
          (mzParamF0 F_A yA yB (Function.update (Function.update z₀ m u) m v)) ε) ξ) =
        fun v => gHat v ξ := by
      ext v; simp [gHat]
    rw [h_eq, Function.update_self] at hda
    exact hda.differentiableWithinAt
  have hgHat_bdd : ∀ u ∈ Metric.ball (z₀ m) (2 * R), ∀ (j : Fin 2) (ξ : Fin 2 → ℝ),
      ‖gHat u ξ‖ ≤ C_β * Real.exp (-β * |ξ j|) := by
    intro u hu j ξ
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree hr
        (h_upd_in u hu)
    exact mz_fourier_bound_coord hr hM h1 h2 h3 h4 h5 h6 hε hβ_pos hβ_lt j ξ
  have hgHat_cont : ∀ u ∈ Metric.ball (z₀ m) (2 * R), Continuous (gHat u) := by
    intro u hu
    obtain ⟨h1, h2, _, _, _, _⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree hr
        (h_upd_in u hu)
    exact continuous_fourierTransformND_of_integrable (integrable_mzGaussianDamped hM h1 h2 hε)
  have hζ_sum_le : ∑ j : Fin 2, |(ζ₀ j).im| ≤ β - ((2 : ℕ) : ℝ) * δ := by
    dsimp [δ, β, S_y]
    linarith
  let F_int : ℂ → (Fin 2 → ℝ) → ℂ := fun u ξ =>
    gHat u ξ * Complex.exp (I * ∑ j : Fin 2, ζ₀ j * (ξ j : ℂ))
  let F'_int : ℂ → (Fin 2 → ℝ) → ℂ := fun u ξ =>
    deriv (fun v => gHat v ξ) u * Complex.exp (I * ∑ j : Fin 2, ζ₀ j * (ξ j : ℂ))
  let bound : (Fin 2 → ℝ) → ℝ := fun ξ =>
    (C_β / R) * Real.exp (-δ * ∑ j : Fin 2, |ξ j|)
  have h_exp_int : Integrable (fun ξ : Fin 2 → ℝ => Real.exp (-δ * ∑ j : Fin 2, |ξ j|)) volume :=
    integrable_exp_neg_abs_sum 2 hδ_pos
  have h_bound_int : Integrable bound volume := h_exp_int.const_mul (C_β / R)
  have h_phase_cont : Continuous (fun ξ : Fin 2 → ℝ =>
      Complex.exp (I * ∑ j : Fin 2, ζ₀ j * (ξ j : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (continuous_finsetSum Finset.univ fun j _ =>
        continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))))
  have h_meas_F : ∀ᶠ u in 𝓝 (z₀ m), AEStronglyMeasurable (F_int u) volume := by
    filter_upwards [Metric.ball_mem_nhds (z₀ m) hR_pos] with u hu
    exact ((hgHat_cont u (Metric.ball_subset_ball (by linarith) hu)).mul
      h_phase_cont).aestronglyMeasurable
  have h_int_F0 : Integrable (F_int (z₀ m)) volume := by
    refine (h_exp_int.const_mul C_β).mono' h_meas_F.self_of_nhds
      (Filter.Eventually.of_forall fun ξ => ?_)
    exact mz_fourier_phase_domination (n := 1) (α := r) hC_nn hδ_pos
      (hgHat_bdd (z₀ m) (Metric.mem_ball_self (by positivity))) hζ_sum_le hr ξ
  have h_meas_F' : AEStronglyMeasurable (F'_int (z₀ m)) volume := by
    have hm1 : Measurable (fun ξ : Fin 2 → ℝ => deriv (fun v => gHat v ξ) (z₀ m)) :=
      measurable_deriv_of_continuous_on_ball hR_pos hgHat_cont fun ξ =>
        (hgHat_holo ξ).differentiableAt (Metric.isOpen_ball.mem_nhds
          (Metric.mem_ball_self (by positivity)))
    exact (hm1.mul h_phase_cont.measurable).aestronglyMeasurable
  have h_bound : ∀ᵐ ξ ∂volume, ∀ u ∈ Metric.ball (z₀ m) R, ‖F'_int u ξ‖ ≤ bound ξ := by
    refine Filter.Eventually.of_forall fun ξ u hu => ?_
    have h_deriv_coord : ∀ (j : Fin 2) (ξ' : Fin 2 → ℝ),
        ‖deriv (fun v => gHat v ξ') u‖ ≤ (C_β / R) * Real.exp (-β * |ξ' j|) := by
      intro j ξ'
      have h1 := norm_deriv_le_of_ball_bound hR_pos (hgHat_holo ξ')
        (fun v hv => hgHat_bdd v hv j ξ') hu
      rwa [mul_div_right_comm] at h1
    exact mz_fourier_phase_domination (n := 1) (α := r) (div_nonneg hC_nn hR_pos.le) hδ_pos
      h_deriv_coord hζ_sum_le hr ξ
  have h_deriv : ∀ᵐ ξ ∂volume, ∀ u ∈ Metric.ball (z₀ m) R,
      HasDerivAt (fun v => F_int v ξ) (F'_int u ξ) u := by
    refine Filter.Eventually.of_forall fun ξ u hu => ?_
    have hda : DifferentiableAt ℂ (fun v => gHat v ξ) u :=
      (hgHat_holo ξ).differentiableAt (Metric.isOpen_ball.mem_nhds
        (Metric.ball_subset_ball (by linarith) hu))
    exact hda.hasDerivAt.mul_const _
  have h_int_da := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds (z₀ m) hR_pos) h_meas_F h_int_F0 h_meas_F' h_bound h_bound_int
    h_deriv).2.differentiableAt
  exact h_int_da.const_mul (((2 * Real.pi)⁻¹ : ℂ) ^ 2)

noncomputable def mzParamLim {D : ℕ} (F_A : (Fin D → ℂ) → ℂ) (yA yB : Fin D → ℝ)
    (z : Fin D → ℂ) (ζ : Fin 2 → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => mzFEps (mzParamF0 F_A yA yB z) ε ζ)

lemma mzParam_mzFEps_continuousOn {D : ℕ} {U U_A U_B : Set (Fin D → ℝ)}
    {yA yB : Fin D → ℝ} {r M ε : ℝ}
    (hU_open : IsOpen U) (hr : 0 < r) (hM : 0 ≤ M) (hε : 0 < ε)
    {F_A F_B : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFB_holo : DifferentiableOn ℂ F_B (TubeDomain U_B))
    (hFA_bdd : ∀ w ∈ TubeDomain U_A, ‖F_A w‖ ≤ M)
    (hFB_bdd : ∀ w ∈ TubeDomain U_B, ‖F_B w‖ ≤ M)
    (h_shift_A : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamMap yA yB z ζ ∈ TubeDomain U_A)
    (h_shift_B : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 1,
      mzParamMap yA yB z ζ ∈ TubeDomain U_B)
    (h_agree : ∀ z ∈ TubeDomain U, ∀ x : Fin 2 → ℝ,
      F_A (mzParamMap yA yB z (fun k => (x k : ℂ))) =
        F_B (mzParamMap yA yB z (fun k => (x k : ℂ)))) :
    ContinuousOn (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) => mzFEps (mzParamF0 F_A yA yB p.1) ε p.2)
      (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)) := by
  have hTU_open : IsOpen (TubeDomain U) := isOpen_TubeDomain hU_open
  have hTO_open : IsOpen (TubeDomain (Octahedron 2 r)) := isOpen_TubeDomain (isOpen_Octahedron 2 r)
  have h_gHat_cont : ∀ ξ : Fin 2 → ℝ,
      ContinuousOn (fun z : Fin D → ℂ =>
        fourierTransformND (mzGaussianDamped (mzParamF0 F_A yA yB z) ε) ξ) (TubeDomain U) := by
    intro ξ
    have h_gauss_int : Integrable (fun x : Fin 2 → ℝ =>
        M * ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2)) volume :=
      (Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq hε).const_mul M
    refine MeasureTheory.continuousOn_of_dominated ?_ ?_ h_gauss_int ?_
    · intro z hz
      have h_cont_f0 : Continuous (mzParamF0 F_A yA yB z) :=
        (mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
          hr hz).1
      have h_cont_gd : Continuous (mzGaussianDamped (mzParamF0 F_A yA yB z) ε) :=
        h_cont_f0.mul (Complex.continuous_exp.comp
          (continuous_const.mul (continuous_finsetSum Finset.univ fun j _ =>
            (Complex.continuous_ofReal.comp (continuous_apply j)).pow 2)))
      have h_cont_ph : Continuous (fun x : Fin 2 → ℝ =>
          Complex.exp (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul
          (continuous_finsetSum Finset.univ fun j _ =>
          (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const))
      exact (h_cont_gd.mul h_cont_ph).aestronglyMeasurable
    · intro z hz
      refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_exp]
      have h_re0 : (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ)).re = 0 := by
        simp only [neg_mul, Complex.neg_re, Complex.I_mul]
        have h_im0 : (∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ)).im = 0 := by
          rw [Complex.im_sum]
          exact Finset.sum_eq_zero fun j _ => by simp
        simp
      rw [h_re0, Real.exp_zero, mul_one]
      have hf0_le : ‖mzParamF0 F_A yA yB z x‖ ≤ M :=
        (mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
          hr hz).2.1 x
      dsimp only [mzGaussianDamped]
      rw [norm_mul, Complex.norm_exp]
      have h_exp_eq : (-↑ε * ∑ j : Fin 2, (x j : ℂ) ^ 2).re = ∑ j : Fin 2, (-ε * (x j) ^ 2) := by
        rw [Finset.mul_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [sq]
      rw [h_exp_eq, Real.exp_sum]
      exact mul_le_mul_of_nonneg_right hf0_le
        (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
    · refine Filter.Eventually.of_forall fun x => ?_
      have h_map_cont : Continuous (fun z : Fin D → ℂ =>
          mzParamMap yA yB z (fun k => (x k : ℂ))) :=
        continuous_pi fun i => by
          dsimp only [mzParamMap]
          exact ((continuous_apply i).add continuous_const).add continuous_const
      have h_FA_comp : ContinuousOn (fun z : Fin D → ℂ =>
          F_A (mzParamMap yA yB z (fun k => (x k : ℂ)))) (TubeDomain U) :=
        hFA_holo.continuousOn.comp h_map_cont.continuousOn fun z hz =>
          h_shift_A z hz (fun k => (x k : ℂ)) ⟨by simp [hr], fun _ _ => by simp⟩
      exact (h_FA_comp.mul continuousOn_const).mul continuousOn_const
  intro p₀ hp₀
  rcases p₀ with ⟨z₀, ζ₀⟩
  rcases hp₀ with ⟨hz₀, hζ₀⟩
  have hζ₀_sum : ∑ j : Fin 2, |(ζ₀ j).im| < r := hζ₀
  let S₀ : ℝ := (∑ j : Fin 2, |(ζ₀ j).im| + r) / 2
  have hS₀_gt : ∑ j : Fin 2, |(ζ₀ j).im| < S₀ := by dsimp [S₀]; linarith
  have hS₀_lt : S₀ < r := by dsimp [S₀]; linarith
  let ρ : ℝ := (S₀ - ∑ j : Fin 2, |(ζ₀ j).im|) / 4
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
  let V : Set ((Fin D → ℂ) × (Fin 2 → ℂ)) :=
    TubeDomain U ×ˢ (TubeDomain (Octahedron 2 r) ∩ Metric.ball ζ₀ ρ)
  have hV_open : IsOpen V := hTU_open.prod (hTO_open.inter Metric.isOpen_ball)
  have hp₀_V : (z₀, ζ₀) ∈ V := ⟨hz₀, hζ₀, Metric.mem_ball_self hρ_pos⟩
  let β : ℝ := (S₀ + r) / 2
  have hβ_pos : 0 < β := by
    have hsum_nn : 0 ≤ ∑ j : Fin 2, |(ζ₀ j).im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [β, S₀]; linarith
  have hβ_lt : β < r := by dsimp [β]; linarith
  let δ : ℝ := (β - S₀) / 2
  have hδ_pos : 0 < δ := by dsimp [δ, β]; linarith
  let C_β : ℝ := M * Real.exp (ε * β ^ 2) *
    ∫ x : Fin 2 → ℝ, ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2)
  have hC_nn : 0 ≤ C_β :=
    mul_nonneg (mul_nonneg hM (Real.exp_pos _).le)
      (integral_nonneg fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  have h_bound_int : Integrable (fun ξ : Fin 2 → ℝ =>
      C_β * Real.exp (-δ * ∑ j : Fin 2, |ξ j|)) volume :=
    (integrable_exp_neg_abs_sum 2 hδ_pos).const_mul C_β
  have h_int_cont : ContinuousOn (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) =>
      ∫ ξ : Fin 2 → ℝ, fourierTransformND (mzGaussianDamped (mzParamF0 F_A yA yB p.1) ε) ξ *
        Complex.exp (I * ∑ j : Fin 2, p.2 j * (ξ j : ℂ))) V := by
    refine MeasureTheory.continuousOn_of_dominated ?_ ?_ h_bound_int ?_
    · intro p hp
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
        mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
          hr hp.1
      have h_g_cont :
          Continuous (fourierTransformND (mzGaussianDamped (mzParamF0 F_A yA yB p.1) ε)) := by
        have h_int_b : Integrable (fun x : Fin 2 → ℝ =>
            M * ∏ j : Fin 2, Real.exp (-ε * (x j) ^ 2)) volume :=
          (Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq hε).const_mul M
        refine MeasureTheory.continuous_of_dominated ?_ ?_ h_int_b ?_
        · intro ξ
          have h_gd_cont : Continuous (mzGaussianDamped (mzParamF0 F_A yA yB p.1) ε) :=
            h1.mul (Complex.continuous_exp.comp (continuous_const.mul
              (continuous_finsetSum Finset.univ fun j _ =>
                (Complex.continuous_ofReal.comp (continuous_apply j)).pow 2)))
          have h_ph : Continuous (fun x : Fin 2 → ℝ =>
              Complex.exp (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ))) :=
            Complex.continuous_exp.comp (continuous_const.mul
              (continuous_finsetSum Finset.univ fun j _ =>
                (Complex.continuous_ofReal.comp (continuous_apply j)).mul continuous_const))
          exact (h_gd_cont.mul h_ph).aestronglyMeasurable
        · intro ξ
          refine Filter.Eventually.of_forall fun x => ?_
          rw [norm_mul, Complex.norm_exp]
          have h_re0 : (-I * ∑ j : Fin 2, (x j : ℂ) * (ξ j : ℂ)).re = 0 := by
            simp only [neg_mul, Complex.neg_re, Complex.I_mul]
            simp
          rw [h_re0, Real.exp_zero, mul_one]
          dsimp only [mzGaussianDamped]
          rw [norm_mul, Complex.norm_exp]
          have h_exp_eq :
              (-↑ε * ∑ j : Fin 2, (x j : ℂ) ^ 2).re = ∑ j : Fin 2, (-ε * (x j) ^ 2) := by
            rw [Finset.mul_sum, Complex.re_sum]
            exact Finset.sum_congr rfl fun j _ => by simp [sq]
          rw [h_exp_eq, Real.exp_sum]
          exact mul_le_mul_of_nonneg_right (h2 x)
            (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
        · refine Filter.Eventually.of_forall fun x => ?_
          exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
            (continuous_finsetSum Finset.univ fun j _ =>
              continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j)))))
      have h_ph_cont : Continuous (fun ξ : Fin 2 → ℝ =>
          Complex.exp (I * ∑ j : Fin 2, p.2 j * (ξ j : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul
          (continuous_finsetSum Finset.univ fun j _ =>
          continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))))
      exact (h_g_cont.mul h_ph_cont).aestronglyMeasurable
    · intro p hp
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
        mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
          hr hp.1
      have h_coord : ∀ m ξ,
          ‖fourierTransformND (mzGaussianDamped (mzParamF0 F_A yA yB p.1) ε) ξ‖ ≤
            C_β * Real.exp (-β * |ξ m|) :=
        fun m ξ => mz_fourier_bound_coord hr hM h1 h2 h3 h4 h5 h6 hε hβ_pos hβ_lt m ξ
      have hp2_sum : ∑ j : Fin 2, |(p.2 j).im| ≤ β - ((1 + 1 : ℕ) : ℝ) * δ := by
        have h_eq : β - ((1 + 1 : ℕ) : ℝ) * δ = S₀ := by dsimp [δ]; ring
        rw [h_eq]
        have h_dist : ‖p.2 - ζ₀‖ < ρ := by simpa [dist_eq_norm] using Metric.mem_ball.mp hp.2.2
        have h_term : ∀ j : Fin 2, |(p.2 j).im| ≤ |(ζ₀ j).im| + ρ := fun j => by
          have hj : |(p.2 j).im - (ζ₀ j).im| < ρ :=
            (Complex.abs_im_le_norm (p.2 j - ζ₀ j)).trans_lt
              ((norm_le_pi_norm (p.2 - ζ₀) j).trans_lt h_dist)
          linarith [abs_sub_abs_le_abs_sub (p.2 j).im (ζ₀ j).im]
        calc ∑ j : Fin 2, |(p.2 j).im| ≤ ∑ j : Fin 2, (|(ζ₀ j).im| + ρ) :=
              Finset.sum_le_sum fun j _ => h_term j
          _ = (∑ j : Fin 2, |(ζ₀ j).im|) + 2 * ρ := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
              simp [nsmul_eq_mul]
          _ ≤ S₀ := by dsimp [ρ]; linarith
      exact Filter.Eventually.of_forall fun ξ =>
        mz_fourier_phase_domination (n := 1) hC_nn hδ_pos h_coord hp2_sum hr ξ
    · refine Filter.Eventually.of_forall fun ξ => ?_
      have h1 : ContinuousOn (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) =>
          fourierTransformND (mzGaussianDamped (mzParamF0 F_A yA yB p.1) ε) ξ) V :=
        (h_gHat_cont ξ).comp continuous_fst.continuousOn (fun p hp => hp.1)
      have h2 : ContinuousOn (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) =>
          Complex.exp (I * ∑ j : Fin 2, p.2 j * (ξ j : ℂ))) V :=
        (Complex.continuous_exp.comp (continuous_const.mul
          (continuous_finsetSum Finset.univ fun j _ =>
            ((continuous_apply j).comp continuous_snd).mul continuous_const))).continuousOn
      exact h1.mul h2
  have h_cont_at : ContinuousAt
      (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) => mzFEps (mzParamF0 F_A yA yB p.1) ε p.2) (z₀, ζ₀) :=
    ((continuousOn_const.mul h_int_cont).continuousAt (hV_open.mem_nhds hp₀_V))
  exact h_cont_at.continuousWithinAt

lemma osgood_prod_fin_two {D : ℕ} {S : Set ((Fin D → ℂ) × (Fin 2 → ℂ))}
    (hS_open : IsOpen S) (G : (Fin D → ℂ) × (Fin 2 → ℂ) → ℂ)
    (hG_cont : ContinuousOn G S)
    (h_left : ∀ z₀ ζ₀, (z₀, ζ₀) ∈ S → ∀ m : Fin D,
      DifferentiableAt ℂ (fun w => G (Function.update z₀ m w, ζ₀)) (z₀ m))
    (h_right : ∀ z₀ ζ₀, (z₀, ζ₀) ∈ S → ∀ k : Fin 2,
      DifferentiableAt ℂ (fun w => G (z₀, Function.update ζ₀ k w)) (ζ₀ k)) :
    DifferentiableOn ℂ G S := by
  let split : (Fin (D + 2) → ℂ) →L[ℂ] (Fin D → ℂ) × (Fin 2 → ℂ) :=
    ContinuousLinearMap.prod
      (ContinuousLinearMap.pi fun i : Fin D => ContinuousLinearMap.proj (Fin.castAdd 2 i))
      (ContinuousLinearMap.pi fun j : Fin 2 => ContinuousLinearMap.proj (Fin.natAdd D j))
  let merge : (Fin D → ℂ) × (Fin 2 → ℂ) →L[ℂ] (Fin (D + 2) → ℂ) :=
    ContinuousLinearMap.pi fun i : Fin (D + 2) =>
      if h : i.val < D then
        (ContinuousLinearMap.proj ⟨i.val, h⟩).comp (ContinuousLinearMap.fst ℂ _ _)
      else
        (ContinuousLinearMap.proj ⟨i.val - D, by omega⟩).comp (ContinuousLinearMap.snd ℂ _ _)
  have h_split_merge : ∀ p : (Fin D → ℂ) × (Fin 2 → ℂ), split (merge p) = p := by
    intro p
    ext i
    · simp [split, merge]
    · simp only [split, merge, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
        ContinuousLinearMap.proj_apply, Fin.val_natAdd, not_lt.mpr (Nat.le_add_right D _),
        ↓reduceDIte, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
      have h_idx : (⟨D + ↑i - D, by omega⟩ : Fin 2) = i := Fin.ext (by simp)
      rw [h_idx]
  let W : Set (Fin (D + 2) → ℂ) := split ⁻¹' S
  have hW_open : IsOpen W := hS_open.preimage split.continuous
  let Gflat : (Fin (D + 2) → ℂ) → ℂ := fun v => G (split v)
  have hGflat_cont : ContinuousOn Gflat W :=
    hG_cont.comp split.continuous.continuousOn (fun _ hv => hv)
  have hGflat_holo : DifferentiableOn ℂ Gflat W := by
    refine osgood_nd (D + 2) hW_open Gflat hGflat_cont ?_
    intro v hv i
    by_cases hi : i.val < D
    · let m : Fin D := ⟨i.val, hi⟩
      have h_upd : ∀ w : ℂ, split (Function.update v i w) =
          (Function.update (split v).1 m w, (split v).2) := by
        intro w
        ext j
        · simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
            ContinuousLinearMap.proj_apply]
          by_cases hjm : j = m
          · subst hjm
            have h_eq : Fin.castAdd 2 m = i := Fin.ext rfl
            rw [h_eq, Function.update_self, Function.update_self]
          · have h_ne : Fin.castAdd 2 j ≠ i := fun h => hjm (Fin.ext (by
              have := congrArg Fin.val h; simpa [m] using this))
            rw [Function.update_of_ne h_ne, Function.update_of_ne hjm]; simp
        · simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
            ContinuousLinearMap.proj_apply]
          have h_ne : Fin.natAdd D j ≠ i := fun h => by
            have := congrArg Fin.val h; simp at this; omega
          rw [Function.update_of_ne h_ne]
      have h_fun : (fun w => Gflat (Function.update v i w)) =
          (fun w => G (Function.update (split v).1 m w, (split v).2)) := by
        ext w; simp only [Gflat, h_upd]
      rw [h_fun]
      have h_val : v i = (split v).1 m := by
        simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
          ContinuousLinearMap.proj_apply]
        congr 1
      rw [h_val]
      exact h_left (split v).1 (split v).2 hv m
    · let k : Fin 2 := ⟨i.val - D, by omega⟩
      have h_upd : ∀ w : ℂ, split (Function.update v i w) =
          ((split v).1, Function.update (split v).2 k w) := by
        intro w
        ext j
        · simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
            ContinuousLinearMap.proj_apply]
          have h_ne : Fin.castAdd 2 j ≠ i := fun h => by
            have := congrArg Fin.val h; simp at this; omega
          rw [Function.update_of_ne h_ne]
        · simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
            ContinuousLinearMap.proj_apply]
          by_cases hjk : j = k
          · subst hjk
            have h_eq : Fin.natAdd D k = i := Fin.ext (by simp [k]; omega)
            rw [h_eq, Function.update_self, Function.update_self]
          · have h_ne : Fin.natAdd D j ≠ i := fun h => hjk (Fin.ext (by
              have := congrArg Fin.val h; simp at this; dsimp [k]; omega))
            rw [Function.update_of_ne h_ne, Function.update_of_ne hjk]; simp
      have h_fun : (fun w => Gflat (Function.update v i w)) =
          (fun w => G ((split v).1, Function.update (split v).2 k w)) := by
        ext w; simp only [Gflat, h_upd]
      rw [h_fun]
      have h_val : v i = (split v).2 k := by
        simp only [split, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
          ContinuousLinearMap.proj_apply]
        congr 1; apply Fin.ext; simp [k]; omega
      rw [h_val]
      exact h_right (split v).1 (split v).2 hv k
  have h_comp := hGflat_holo.comp merge.differentiable.differentiableOn
    (fun p hp => by change split (merge p) ∈ S; rwa [h_split_merge])
  refine h_comp.congr fun p _ => ?_
  simp only [Function.comp_apply, Gflat, h_split_merge]

lemma mzParam_limit_props {D : ℕ} {U U_A U_B : Set (Fin D → ℝ)}
    {yA yB : Fin D → ℝ} {r M : ℝ}
    (hU_open : IsOpen U) (hr : 0 < r) (hM : 0 ≤ M)
    {F_A F_B : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFB_holo : DifferentiableOn ℂ F_B (TubeDomain U_B))
    (hFA_bdd : ∀ w ∈ TubeDomain U_A, ‖F_A w‖ ≤ M)
    (hFB_bdd : ∀ w ∈ TubeDomain U_B, ‖F_B w‖ ≤ M)
    (h_shift_A : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamMap yA yB z ζ ∈ TubeDomain U_A)
    (h_shift_B : ∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 1,
      mzParamMap yA yB z ζ ∈ TubeDomain U_B)
    (h_agree : ∀ z ∈ TubeDomain U, ∀ x : Fin 2 → ℝ,
      F_A (mzParamMap yA yB z (fun k => (x k : ℂ))) =
        F_B (mzParamMap yA yB z (fun k => (x k : ℂ)))) :
    DifferentiableOn ℂ (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) => mzParamLim F_A yA yB p.1 p.2)
      (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)) ∧
    (∀ z ∈ TubeDomain U, ∀ ζ ∈ TubeDomain (Octahedron 2 r),
      ‖mzParamLim F_A yA yB z ζ‖ ≤ M) ∧
    (∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamLim F_A yA yB z ζ = F_A (mzParamMap yA yB z ζ)) ∧
    (∀ z ∈ TubeDomain U, ∀ ζ ∈ FlatStrip 2 r 1,
      mzParamLim F_A yA yB z ζ = F_B (mzParamMap yA yB z ζ)) := by
  have hTU_open : IsOpen (TubeDomain U) := isOpen_TubeDomain hU_open
  have hTO_open : IsOpen (TubeDomain (Octahedron 2 r)) := isOpen_TubeDomain (isOpen_Octahedron 2 r)
  have hProd_open : IsOpen (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)) := hTU_open.prod hTO_open
  have h_unif_ball : ∀ z₀ ∈ TubeDomain U, ∀ ζ₀ ∈ TubeDomain (Octahedron 2 r),
      ∃ η > 0, Metric.ball (z₀, ζ₀) η ⊆ TubeDomain U ×ˢ TubeDomain (Octahedron 2 r) ∧
        TendstoUniformlyOn
          (fun ε (p : (Fin D → ℂ) × (Fin 2 → ℂ)) => mzFEps (mzParamF0 F_A yA yB p.1) ε p.2)
          (fun p => mzParamLim F_A yA yB p.1 p.2)
          (𝓝[>] (0 : ℝ)) (Metric.ball (z₀, ζ₀) η) := by
    intro z₀ hz₀ ζ₀ hζ₀
    rcases Metric.isOpen_iff.mp hProd_open (z₀, ζ₀) ⟨hz₀, hζ₀⟩ with ⟨η, hη, hsub⟩
    refine ⟨η, hη, hsub, Bochner.tendstoUniformlyOn_limUnder_of_uniform_cauchy _ ?_⟩
    intro γ hγ
    let B : ℝ := ‖ζ₀‖ + η + 1
    have hB_pos : 0 < B := by dsimp [B]; positivity
    obtain ⟨ε₀, hε₀, hbd⟩ := mzFEps_bounded_cauchy_uniform (n := 1) hr hM 2 hB_pos hγ
    refine ⟨ε₀, hε₀, fun ε₁ hε₁ ε₂ hε₂ p hp => ?_⟩
    have hp_in := hsub hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
        hr hp_in.1
    have hp2_norm : ‖p.2‖ ≤ B := by
      have hd : ‖p.2 - ζ₀‖ < η := by
        have hball : dist p (z₀, ζ₀) < η := Metric.mem_ball.mp hp
        have hle : dist p.2 ζ₀ ≤ dist p (z₀, ζ₀) := le_max_right _ _
        have hlt : dist p.2 ζ₀ < η := hle.trans_lt hball
        rwa [dist_eq_norm] at hlt
      calc ‖p.2‖ = ‖(p.2 - ζ₀) + ζ₀‖ := by ring_nf
        _ ≤ ‖p.2 - ζ₀‖ + ‖ζ₀‖ := norm_add_le _ _
        _ ≤ B := by dsimp [B]; linarith
    exact hbd h1 h2 h3 h4 h5 h6 ε₁ hε₁ ε₂ hε₂ Finset.univ (by simp) p.2
      ⟨hp_in.2, fun j hj => (hj (Finset.mem_univ j)).elim⟩ hp2_norm
  have h_loc : TendstoLocallyUniformlyOn
      (fun ε (p : (Fin D → ℂ) × (Fin 2 → ℂ)) => mzFEps (mzParamF0 F_A yA yB p.1) ε p.2)
      (fun p => mzParamLim F_A yA yB p.1 p.2)
      (𝓝[>] (0 : ℝ)) (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)) := by
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun p₀ hp₀ => ?_
    obtain ⟨η, hη, _, hunif⟩ := h_unif_ball p₀.1 hp₀.1 p₀.2 hp₀.2
    exact ⟨Metric.ball p₀ η, nhdsWithin_le_nhds (Metric.ball_mem_nhds p₀ hη), hunif⟩
  have h_cont : ContinuousOn
      (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) => mzParamLim F_A yA yB p.1 p.2)
      (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)) := by
    intro p₀ hp₀
    obtain ⟨η, hη, hsub, hunif⟩ := h_unif_ball p₀.1 hp₀.1 p₀.2 hp₀.2
    have h_ev_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ContinuousOn (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) =>
          mzFEps (mzParamF0 F_A yA yB p.1) ε p.2) (Metric.ball p₀ η) :=
      eventually_nhdsWithin_of_forall fun ε hε =>
        (mzParam_mzFEps_continuousOn hU_open hr hM hε hFA_holo hFB_holo hFA_bdd hFB_bdd
          h_shift_A h_shift_B h_agree).mono hsub
    exact (hunif.continuousOn h_ev_cont.frequently |>.continuousAt
      (Metric.ball_mem_nhds p₀ hη)).continuousWithinAt
  have h_diff_left : ∀ z₀ ∈ TubeDomain U, ∀ ζ₀ ∈ TubeDomain (Octahedron 2 r), ∀ m : Fin D,
      DifferentiableAt ℂ (fun w => mzParamLim F_A yA yB (Function.update z₀ m w) ζ₀) (z₀ m) := by
    intro z₀ hz₀ ζ₀ hζ₀ m
    let φ : ℂ → (Fin D → ℂ) × (Fin 2 → ℂ) := fun w => (Function.update z₀ m w, ζ₀)
    have hφ_diff : Differentiable ℂ φ :=
      (differentiable_pi.mpr fun j => by
        by_cases hjm : j = m
        · subst hjm; simp only [Function.update_self]; exact differentiable_id
        · simp only [Function.update_of_ne hjm]; exact differentiable_const _).prodMk
        (differentiable_const ζ₀)
    let S_m : Set ℂ := φ ⁻¹' (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r))
    have hSm_open : IsOpen S_m := hProd_open.preimage hφ_diff.continuous
    have h_loc_sl : TendstoLocallyUniformlyOn
        (fun ε w => mzFEps (mzParamF0 F_A yA yB (Function.update z₀ m w)) ε ζ₀)
        (fun w => mzParamLim F_A yA yB (Function.update z₀ m w) ζ₀) (𝓝[>] (0 : ℝ)) S_m :=
      h_loc.comp φ (fun _ hw => hw) hφ_diff.continuous.continuousOn
    have h_ev_sl : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        DifferentiableOn ℂ (fun w => mzFEps (mzParamF0 F_A yA yB (Function.update z₀ m w)) ε ζ₀)
          S_m := by
      refine eventually_nhdsWithin_of_forall fun ε hε w hw => ?_
      have h_da := mzParam_mzFEps_differentiableAt_left hU_open hr hM hε hFA_holo hFB_holo
        hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree hw.1 m hw.2
      have h_eq : (fun v => mzFEps
          (mzParamF0 F_A yA yB (Function.update (Function.update z₀ m w) m v)) ε ζ₀) =
          (fun v => mzFEps (mzParamF0 F_A yA yB (Function.update z₀ m v)) ε ζ₀) := by
        ext v; simp [Function.update_idem]
      dsimp only [φ] at h_da
      rw [h_eq, Function.update_self] at h_da
      exact h_da.differentiableWithinAt
    have h_diffOn := h_loc_sl.differentiableOn h_ev_sl hSm_open
    have hzm : z₀ m ∈ S_m := by
      change (Function.update z₀ m (z₀ m), ζ₀) ∈ TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)
      rw [Function.update_eq_self]
      exact ⟨hz₀, hζ₀⟩
    exact (h_diffOn (z₀ m) hzm).differentiableAt (hSm_open.mem_nhds hzm)
  have h_diff_right : ∀ z₀ ∈ TubeDomain U, ∀ ζ₀ ∈ TubeDomain (Octahedron 2 r), ∀ k : Fin 2,
      DifferentiableAt ℂ (fun w => mzParamLim F_A yA yB z₀ (Function.update ζ₀ k w)) (ζ₀ k) := by
    intro z₀ hz₀ ζ₀ hζ₀ k
    let φ : ℂ → (Fin D → ℂ) × (Fin 2 → ℂ) := fun w => (z₀, Function.update ζ₀ k w)
    have hφ_diff : Differentiable ℂ φ :=
      (differentiable_const z₀).prodMk (differentiable_pi.mpr fun j => by
        by_cases hjk : j = k
        · subst hjk; simp only [Function.update_self]; exact differentiable_id
        · simp only [Function.update_of_ne hjk]; exact differentiable_const _)
    let S_k : Set ℂ := φ ⁻¹' (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r))
    have hSk_open : IsOpen S_k := hProd_open.preimage hφ_diff.continuous
    have h_loc_sl : TendstoLocallyUniformlyOn
        (fun ε w => mzFEps (mzParamF0 F_A yA yB z₀) ε (Function.update ζ₀ k w))
        (fun w => mzParamLim F_A yA yB z₀ (Function.update ζ₀ k w)) (𝓝[>] (0 : ℝ)) S_k :=
      h_loc.comp φ (fun _ hw => hw) hφ_diff.continuous.continuousOn
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
        hr hz₀
    have h_ev_sl : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        DifferentiableOn ℂ (fun w => mzFEps (mzParamF0 F_A yA yB z₀) ε (Function.update ζ₀ k w))
          S_k := by
      refine eventually_nhdsWithin_of_forall fun ε hε => ?_
      have h_holo := mzFEps_holomorphic (n := 1) hr hM h1 h2 h3 h4 h5 h6 hε
      have h_upd_diff : Differentiable ℂ (Function.update ζ₀ k) :=
        differentiable_pi.mpr fun j => by
          by_cases hjk : j = k
          · subst hjk; simp only [Function.update_self]; exact differentiable_id
          · simp only [Function.update_of_ne hjk]; exact differentiable_const _
      exact h_holo.comp h_upd_diff.differentiableOn (fun _ hw => hw.2)
    have h_diffOn := h_loc_sl.differentiableOn h_ev_sl hSk_open
    have hζk : ζ₀ k ∈ S_k := by
      change (z₀, Function.update ζ₀ k (ζ₀ k)) ∈ TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)
      rw [Function.update_eq_self]
      exact ⟨hz₀, hζ₀⟩
    exact (h_diffOn (ζ₀ k) hζk).differentiableAt (hSk_open.mem_nhds hζk)
  have h_holo : DifferentiableOn ℂ
      (fun p : (Fin D → ℂ) × (Fin 2 → ℂ) => mzParamLim F_A yA yB p.1 p.2)
      (TubeDomain U ×ˢ TubeDomain (Octahedron 2 r)) :=
    osgood_prod_fin_two hProd_open (fun p => mzParamLim F_A yA yB p.1 p.2) h_cont
      (fun z₀ ζ₀ h m => h_diff_left z₀ h.1 ζ₀ h.2 m)
      (fun z₀ ζ₀ h k => h_diff_right z₀ h.1 ζ₀ h.2 k)
  refine ⟨h_holo, ?_, ?_, ?_⟩
  · intro z hz ζ hζ
    obtain ⟨η, hη, _, hunif⟩ := h_unif_ball z hz ζ hζ
    have h_tendsto : Tendsto (fun ε => mzFEps (mzParamF0 F_A yA yB z) ε ζ)
        (𝓝[>] (0 : ℝ)) (𝓝 (mzParamLim F_A yA yB z ζ)) :=
      hunif.tendsto_at (x := (z, ζ)) (Metric.mem_ball_self hη)
    have h_rhs : Tendsto (fun ε : ℝ => M * Real.exp (ε * r ^ 2)) (𝓝[>] (0 : ℝ)) (𝓝 M) := by
      have hc : Continuous (fun ε : ℝ => M * Real.exp (ε * r ^ 2)) :=
        continuous_const.mul (Real.continuous_exp.comp (continuous_id.mul continuous_const))
      simpa using tendsto_nhdsWithin_of_tendsto_nhds
        (s := Set.Ioi (0 : ℝ)) (hc.continuousAt (x := 0)).tendsto
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree hr hz
    refine le_of_tendsto_of_tendsto h_tendsto.norm h_rhs ?_
    exact eventually_nhdsWithin_of_forall fun ε hε =>
      mzFEps_norm_le_all (n := 1) hr hM h1 h2 h3 h4 h5 h6 hε hζ
  · intro z hz ζ hζ
    have hζ_tube : ζ ∈ TubeDomain (Octahedron 2 r) := by
      change ∑ j : Fin 2, |(ζ j).im| < r
      rw [Finset.sum_eq_single (0 : Fin 2)]
      · exact hζ.1
      · intro j _ hj; simp [hζ.2 j hj]
      · intro h; exact (h (Finset.mem_univ _)).elim
    obtain ⟨η, hη, _, hunif⟩ := h_unif_ball z hz ζ hζ_tube
    have h_t1 : Tendsto (fun ε => mzFEps (mzParamF0 F_A yA yB z) ε ζ)
        (𝓝[>] (0 : ℝ)) (𝓝 (mzParamLim F_A yA yB z ζ)) :=
      hunif.tendsto_at (x := (z, ζ)) (Metric.mem_ball_self hη)
    let s : ℂ := ∑ j : Fin 2, (ζ j) ^ 2
    have h_t2 : Tendsto (fun ε : ℝ => F_A (mzParamMap yA yB z ζ) * Complex.exp (-↑ε * s))
        (𝓝[>] (0 : ℝ)) (𝓝 (F_A (mzParamMap yA yB z ζ))) := by
      have hc : Continuous (fun ε : ℝ => F_A (mzParamMap yA yB z ζ) * Complex.exp (-↑ε * s)) :=
        continuous_const.mul (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.neg).mul continuous_const))
      simpa using tendsto_nhdsWithin_of_tendsto_nhds
        (s := Set.Ioi (0 : ℝ)) (hc.continuousAt (x := 0)).tendsto
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree hr hz
    have h_ev : (fun ε => mzFEps (mzParamF0 F_A yA yB z) ε ζ) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => F_A (mzParamMap yA yB z ζ) * Complex.exp (-↑ε * s) :=
      eventually_nhdsWithin_of_forall fun ε hε => by
        have h := mzFEps_eq_on_flatStrip (n := 1) hr hM h1 h2 h3 h4 h5 h6 hε (0 : Fin 2) hζ
        simpa [mzParamBr, s] using h
    exact tendsto_nhds_unique h_t1 (h_t2.congr' h_ev.symm)
  · intro z hz ζ hζ
    have hζ_tube : ζ ∈ TubeDomain (Octahedron 2 r) := by
      change ∑ j : Fin 2, |(ζ j).im| < r
      rw [Finset.sum_eq_single (1 : Fin 2)]
      · exact hζ.1
      · intro j _ hj; simp [hζ.2 j hj]
      · intro h; exact (h (Finset.mem_univ _)).elim
    obtain ⟨η, hη, _, hunif⟩ := h_unif_ball z hz ζ hζ_tube
    have h_t1 : Tendsto (fun ε => mzFEps (mzParamF0 F_A yA yB z) ε ζ)
        (𝓝[>] (0 : ℝ)) (𝓝 (mzParamLim F_A yA yB z ζ)) :=
      hunif.tendsto_at (x := (z, ζ)) (Metric.mem_ball_self hη)
    let s : ℂ := ∑ j : Fin 2, (ζ j) ^ 2
    have h_t2 : Tendsto (fun ε : ℝ => F_B (mzParamMap yA yB z ζ) * Complex.exp (-↑ε * s))
        (𝓝[>] (0 : ℝ)) (𝓝 (F_B (mzParamMap yA yB z ζ))) := by
      have hc : Continuous (fun ε : ℝ => F_B (mzParamMap yA yB z ζ) * Complex.exp (-↑ε * s)) :=
        continuous_const.mul (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.neg).mul continuous_const))
      simpa using tendsto_nhdsWithin_of_tendsto_nhds
        (s := Set.Ioi (0 : ℝ)) (hc.continuousAt (x := 0)).tendsto
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
      mzParam_slice_holo_and_bdd hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree hr hz
    have h_ev : (fun ε => mzFEps (mzParamF0 F_A yA yB z) ε ζ) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => F_B (mzParamMap yA yB z ζ) * Complex.exp (-↑ε * s) :=
      eventually_nhdsWithin_of_forall fun ε hε => by
        have h := mzFEps_eq_on_flatStrip (n := 1) hr hM h1 h2 h3 h4 h5 h6 hε (1 : Fin 2) hζ
        simpa [mzParamBr, s] using h
    exact tendsto_nhds_unique h_t1 (h_t2.congr' h_ev.symm)

lemma mzParamLim_diag_shift_invariant {D : ℕ} {δ r M : ℝ}
    {U_A U_B : Set (Fin D → ℝ)} {yA yB : Fin D → ℝ}
    (hr : 0 < r) (hM : 0 ≤ M)
    {F_A F_B : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFB_holo : DifferentiableOn ℂ F_B (TubeDomain U_B))
    (hFA_bdd : ∀ w ∈ TubeDomain U_A, ‖F_A w‖ ≤ M)
    (hFB_bdd : ∀ w ∈ TubeDomain U_B, ‖F_B w‖ ≤ M)
    (h_shift_A : ∀ z ∈ TubeDomain (Metric.ball 0 δ), ∀ ζ ∈ FlatStrip 2 r 0,
      mzParamMap yA yB z ζ ∈ TubeDomain U_A)
    (h_shift_B : ∀ z ∈ TubeDomain (Metric.ball 0 δ), ∀ ζ ∈ FlatStrip 2 r 1,
      mzParamMap yA yB z ζ ∈ TubeDomain U_B)
    (h_agree : ∀ z ∈ TubeDomain (Metric.ball 0 δ), ∀ x : Fin 2 → ℝ,
      F_A (mzParamMap yA yB z (fun k => (x k : ℂ))) =
        F_B (mzParamMap yA yB z (fun k => (x k : ℂ))))
    {z : Fin D → ℂ} (hz : z ∈ TubeDomain (Metric.ball 0 δ))
    {s₁ s₂ : ℝ} (hs₁ : |s₁| < r) (hs₂ : |s₂| < r)
    (hz' : (fun j => z j - (I * ((s₂ - s₁ : ℝ) : ℂ)) * (((yA j + yB j) / 2 : ℝ) : ℂ)) ∈
      TubeDomain (Metric.ball 0 δ)) :
    mzParamLim F_A yA yB
        (fun j => z j - (I * ((s₂ - s₁ : ℝ) : ℂ)) * (((yA j + yB j) / 2 : ℝ) : ℂ))
        (fun _ => I * ((s₂ : ℂ) / 2)) =
      mzParamLim F_A yA yB z (fun _ => I * ((s₁ : ℂ) / 2)) := by
  obtain ⟨hG_holo, _, hG_A, _⟩ := mzParam_limit_props Metric.isOpen_ball hr hM
    hFA_holo hFB_holo hFA_bdd hFB_bdd h_shift_A h_shift_B h_agree
  let y₀ : Fin D → ℝ := fun j => (yA j + yB j) / 2
  have h_diag_mem : ∀ μ : ℂ, |μ.im| < r →
      (fun _ : Fin 2 => μ / 2) ∈ TubeDomain (Octahedron 2 r) := by
    intro μ hμ
    change ∑ _ : Fin 2, |(μ / 2).im| < r
    have h_im : (μ / 2).im = μ.im / 2 := by simp
    simp only [h_im, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have h_real_shift : ∀ (z₁ : Fin D → ℂ), z₁ ∈ TubeDomain (Metric.ball 0 δ) →
      ∀ (μ₁ : ℂ), |μ₁.im| < r → ∀ (h : ℝ),
        mzParamLim F_A yA yB (fun j => z₁ j - (h : ℂ) * (y₀ j : ℂ))
          (fun _ => (μ₁ + (h : ℂ)) / 2) =
          mzParamLim F_A yA yB z₁ (fun _ => μ₁ / 2) := by
    intro z₁ hz₁ μ₁ hμ₁ h
    have hz₁_norm : ‖fun j => (z₁ j).im‖ < δ := by
      simpa [TubeDomain, Metric.mem_ball, dist_zero_right] using hz₁
    let R_s : ℝ := min ((δ - ‖fun j => (z₁ j).im‖) / (2 * (‖fun j => (z₁ j).im‖ + 1)) + 1)
      ((r - |μ₁.im|) / (2 * (|μ₁.im| + 1)) + 1)
    have hRs_gt : 1 < R_s := by
      have h1 : 0 < (δ - ‖fun j => (z₁ j).im‖) / (2 * (‖fun j => (z₁ j).im‖ + 1)) :=
        div_pos (sub_pos.mpr hz₁_norm) (by positivity)
      have h2 : 0 < (r - |μ₁.im|) / (2 * (|μ₁.im| + 1)) :=
        div_pos (sub_pos.mpr hμ₁) (by positivity)
      dsimp [R_s]
      exact lt_min (by linarith) (by linarith)
    have hRs_z : R_s * ‖fun j => (z₁ j).im‖ < δ := by
      have hle : R_s ≤ (δ - ‖fun j => (z₁ j).im‖) / (2 * (‖fun j => (z₁ j).im‖ + 1)) + 1 :=
        min_le_left _ _
      have hnn : 0 ≤ ‖fun j => (z₁ j).im‖ := norm_nonneg _
      have hden : 0 < 2 * (‖fun j => (z₁ j).im‖ + 1) := by positivity
      have h_mul := mul_le_mul_of_nonneg_right hle hnn
      have h_lt : ((δ - ‖fun j => (z₁ j).im‖) / (2 * (‖fun j => (z₁ j).im‖ + 1)) + 1) *
          ‖fun j => (z₁ j).im‖ < δ := by
        have h_num : (δ - ‖fun j => (z₁ j).im‖) * ‖fun j => (z₁ j).im‖ <
            (δ - ‖fun j => (z₁ j).im‖) * (2 * (‖fun j => (z₁ j).im‖ + 1)) := by nlinarith
        have h_div : (δ - ‖fun j => (z₁ j).im‖) / (2 * (‖fun j => (z₁ j).im‖ + 1)) *
            ‖fun j => (z₁ j).im‖ < δ - ‖fun j => (z₁ j).im‖ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          exact h_num
        linarith
      exact h_mul.trans_lt h_lt
    have hRs_μ : R_s * |μ₁.im| < r := by
      have hle : R_s ≤ (r - |μ₁.im|) / (2 * (|μ₁.im| + 1)) + 1 := min_le_right _ _
      have hnn : 0 ≤ |μ₁.im| := abs_nonneg _
      have hden : 0 < 2 * (|μ₁.im| + 1) := by positivity
      have h_mul := mul_le_mul_of_nonneg_right hle hnn
      have h_lt : ((r - |μ₁.im|) / (2 * (|μ₁.im| + 1)) + 1) * |μ₁.im| < r := by
        have h_num : (r - |μ₁.im|) * |μ₁.im| < (r - |μ₁.im|) * (2 * (|μ₁.im| + 1)) := by nlinarith
        have h_div : (r - |μ₁.im|) / (2 * (|μ₁.im| + 1)) * |μ₁.im| < r - |μ₁.im| := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
          exact h_num
        linarith
      exact h_mul.trans_lt h_lt
    let S : Set ℂ := {s : ℂ | |s.re| < R_s}
    have hS_open : IsOpen S :=
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
    have hS_conv : Convex ℝ S := by
      intro s₁ hs₁ s₂ hs₂ a b ha hb hab
      simp only [S, Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hs₁' : |s₁.re| < R_s := hs₁
      have hs₂' : |s₂.re| < R_s := hs₂
      calc |a * s₁.re + b * s₂.re| ≤ |a * s₁.re| + |b * s₂.re| := abs_add_le _ _
        _ = a * |s₁.re| + b * |s₂.re| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ < a * R_s + b * R_s := by
            rcases eq_or_lt_of_le ha with rfl | ha'
            · simp only [zero_add] at hab; subst hab; nlinarith [hs₂']
            · rcases eq_or_lt_of_le hb with rfl | hb'
              · simp only [add_zero] at hab; subst hab; nlinarith [hs₁']
              · nlinarith [hs₁', hs₂']
        _ = R_s := by nlinarith
    let zMap : ℂ → (Fin D → ℂ) := fun s j => ((z₁ j).re : ℂ) + s * (I * ((z₁ j).im : ℂ))
    let μMap : ℂ → ℂ := fun s => (μ₁.re : ℂ) + s * (I * (μ₁.im : ℂ))
    have hzMap_im : ∀ s j, (zMap s j).im = s.re * (z₁ j).im := fun s j => by
      dsimp [zMap]; simp [Complex.mul_im]
    have hμMap_im : ∀ s, (μMap s).im = s.re * μ₁.im := fun s => by
      dsimp [μMap]; simp [Complex.mul_im]
    have hzMap_in : ∀ s ∈ S, zMap s ∈ TubeDomain (Metric.ball 0 δ) := by
      intro s hs
      change (fun j => (zMap s j).im) ∈ Metric.ball 0 δ
      rw [Metric.mem_ball, dist_zero_right]
      have h_eq : (fun j => (zMap s j).im) = s.re • (fun j => (z₁ j).im) := by
        ext j; exact hzMap_im s j
      rw [h_eq, norm_smul, Real.norm_eq_abs]
      calc |s.re| * ‖fun j => (z₁ j).im‖ ≤ R_s * ‖fun j => (z₁ j).im‖ :=
            mul_le_mul_of_nonneg_right (le_of_lt hs) (norm_nonneg _)
        _ < δ := hRs_z
    have hμMap_in : ∀ s ∈ S, |(μMap s).im| < r := by
      intro s hs
      rw [hμMap_im, abs_mul]
      calc |s.re| * |μ₁.im| ≤ R_s * |μ₁.im| :=
            mul_le_mul_of_nonneg_right (le_of_lt hs) (abs_nonneg _)
        _ < r := hRs_μ
    let φ₁ : ℂ → (Fin D → ℂ) × (Fin 2 → ℂ) :=
      fun s => (fun j => zMap s j - (h : ℂ) * (y₀ j : ℂ), fun _ => (μMap s + (h : ℂ)) / 2)
    let φ₂ : ℂ → (Fin D → ℂ) × (Fin 2 → ℂ) :=
      fun s => (zMap s, fun _ => μMap s / 2)
    have hzMap_diff : Differentiable ℂ zMap :=
      differentiable_pi.mpr fun j =>
        (differentiable_const _).add (differentiable_id.mul (differentiable_const _))
    have hμMap_diff : Differentiable ℂ μMap :=
      (differentiable_const _).add (differentiable_id.mul (differentiable_const _))
    have hφ₁_diff : Differentiable ℂ φ₁ :=
      (differentiable_pi.mpr fun j =>
        ((differentiable_apply j).comp hzMap_diff).sub (differentiable_const _)).prodMk
        (differentiable_pi.mpr fun _ => (hμMap_diff.add (differentiable_const _)).div_const 2)
    have hφ₂_diff : Differentiable ℂ φ₂ :=
      hzMap_diff.prodMk (differentiable_pi.mpr fun _ => hμMap_diff.div_const 2)
    let g₁ : ℂ → ℂ := fun s => mzParamLim F_A yA yB (φ₁ s).1 (φ₁ s).2
    let g₂ : ℂ → ℂ := fun s => mzParamLim F_A yA yB (φ₂ s).1 (φ₂ s).2
    have hg₁_holo : DifferentiableOn ℂ g₁ S :=
      hG_holo.comp hφ₁_diff.differentiableOn fun s hs => by
        refine ⟨?_, h_diag_mem _ ?_⟩
        · change (fun j => (zMap s j - (h : ℂ) * (y₀ j : ℂ)).im) ∈ Metric.ball 0 δ
          have h_im_eq : (fun j => (zMap s j - (h : ℂ) * (y₀ j : ℂ)).im) =
              fun j => (zMap s j).im := by ext j; simp
          rw [h_im_eq]; exact hzMap_in s hs
        · simpa using hμMap_in s hs
    have hg₂_holo : DifferentiableOn ℂ g₂ S :=
      hG_holo.comp hφ₂_diff.differentiableOn fun s hs =>
        ⟨hzMap_in s hs, h_diag_mem _ (hμMap_in s hs)⟩
    have h_eq_im_axis : ∀ t : ℝ, g₁ (I * (t : ℂ)) = g₂ (I * (t : ℂ)) := by
      intro t
      have ht_S : I * (t : ℂ) ∈ S := by
        change |(I * (t : ℂ)).re| < R_s
        simp; linarith
      have h_z1_in : (φ₁ (I * (t : ℂ))).1 ∈ TubeDomain (Metric.ball 0 δ) := by
        change (fun j => (zMap (I * (t : ℂ)) j - (h : ℂ) * (y₀ j : ℂ)).im) ∈ Metric.ball 0 δ
        have h_im_eq : (fun j => (zMap (I * (t : ℂ)) j - (h : ℂ) * (y₀ j : ℂ)).im) =
            fun j => (zMap (I * (t : ℂ)) j).im := by ext j; simp
        rw [h_im_eq]; exact hzMap_in _ ht_S
      have h_z2_in : (φ₂ (I * (t : ℂ))).1 ∈ TubeDomain (Metric.ball 0 δ) := hzMap_in _ ht_S
      have h_μ_im0 : (μMap (I * (t : ℂ))).im = 0 := by rw [hμMap_im]; simp
      have h_f1 : (φ₁ (I * (t : ℂ))).2 ∈ FlatStrip 2 r 0 := by
        refine ⟨?_, fun j _ => ?_⟩
        · simp [φ₁, h_μ_im0, hr]
        · simp [φ₁, h_μ_im0]
      have h_f2 : (φ₂ (I * (t : ℂ))).2 ∈ FlatStrip 2 r 0 := by
        refine ⟨?_, fun j _ => ?_⟩
        · simp [φ₂, h_μ_im0, hr]
        · simp [φ₂, h_μ_im0]
      dsimp only [g₁, g₂]
      rw [hG_A _ h_z1_in _ h_f1, hG_A _ h_z2_in _ h_f2]
      congr 1
      ext j
      simp only [φ₁, φ₂, mzParamMap, y₀, Complex.ofReal_div, Complex.ofReal_add,
        Complex.ofReal_ofNat]
      ring
    have h_freq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), g₁ s = g₂ s := by
      rw [Filter.frequently_iff]
      intro U hU
      rw [mem_nhdsWithin] at hU
      rcases hU with ⟨V, hV_open, h0V, hV_sub⟩
      rcases Metric.isOpen_iff.mp hV_open 0 h0V with ⟨η, hη, h_ball⟩
      let s₀ : ℂ := I * ((η / 2 : ℝ) : ℂ)
      have hs₀_ne : s₀ ≠ 0 := by
        intro heq
        have h1 : ‖s₀‖ = η / 2 := by
          dsimp [s₀]; rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_of_nonneg (by positivity)]
        rw [heq, norm_zero] at h1
        linarith
      have hs₀_V : s₀ ∈ V := h_ball (by
        rw [Metric.mem_ball, dist_zero_right]
        dsimp [s₀]
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        linarith)
      exact ⟨s₀, hV_sub ⟨hs₀_V, hs₀_ne⟩, h_eq_im_axis (η / 2)⟩
    have h_eqOn := (hg₁_holo.analyticOnNhd hS_open).eqOn_of_preconnected_of_frequently_eq
      (hg₂_holo.analyticOnNhd hS_open) hS_conv.isPreconnected
      (by change |(0 : ℂ).re| < R_s; simp; linarith)
      h_freq
    have h1_S : (1 : ℂ) ∈ S := by change |(1 : ℂ).re| < R_s; simp [hRs_gt]
    have h_at1 := h_eqOn h1_S
    have hzMap1 : zMap 1 = z₁ := by
      ext j; dsimp [zMap]; rw [one_mul, mul_comm I, Complex.re_add_im]
    have hμMap1 : μMap 1 = μ₁ := by
      dsimp [μMap]; rw [one_mul, mul_comm I, Complex.re_add_im]
    simpa [g₁, g₂, φ₁, φ₂, hzMap1, hμMap1] using h_at1
  let H : Set ℂ := {w : ℂ |
    (fun j => (z j).im - w.im * y₀ j) ∈ Metric.ball 0 δ ∧ |s₁ + w.im| < r}
  have hH_open : IsOpen H := by
    have h1 : Continuous (fun w : ℂ => fun j : Fin D => (z j).im - w.im * y₀ j) :=
      continuous_pi fun j => continuous_const.sub (Complex.continuous_im.mul continuous_const)
    have h2 : Continuous (fun w : ℂ => |s₁ + w.im|) :=
      continuous_abs.comp (continuous_const.add Complex.continuous_im)
    exact (Metric.isOpen_ball.preimage h1).inter (isOpen_lt h2 continuous_const)
  have hH_conv : Convex ℝ H := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨?_, ?_⟩
    · have h_eq : (fun j => (z j).im - (a • w₁ + b • w₂).im * y₀ j) =
          a • (fun j => (z j).im - w₁.im * y₀ j) + b • (fun j => (z j).im - w₂.im * y₀ j) := by
        ext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_im,
          Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          add_zero]
        have : (z j).im = (a + b) * (z j).im := by rw [hab, one_mul]
        linarith
      rw [h_eq]
      exact (convex_ball (0 : Fin D → ℝ) δ) hw₁.1 hw₂.1 ha hb hab
    · have h_eq : s₁ + (a • w₁ + b • w₂).im = a * (s₁ + w₁.im) + b * (s₁ + w₂.im) := by
        simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero]
        have : s₁ = (a + b) * s₁ := by rw [hab, one_mul]
        linarith
      rw [h_eq]
      calc |a * (s₁ + w₁.im) + b * (s₁ + w₂.im)|
          ≤ |a * (s₁ + w₁.im)| + |b * (s₁ + w₂.im)| := abs_add_le _ _
        _ = a * |s₁ + w₁.im| + b * |s₁ + w₂.im| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ < a * r + b * r := by
            rcases eq_or_lt_of_le ha with rfl | ha'
            · simp only [zero_add] at hab; subst hab; nlinarith [hw₂.2]
            · rcases eq_or_lt_of_le hb with rfl | hb'
              · simp only [add_zero] at hab; subst hab; nlinarith [hw₁.2]
              · nlinarith [hw₁.2, hw₂.2]
        _ = r := by nlinarith
  let ψ : ℂ → (Fin D → ℂ) × (Fin 2 → ℂ) :=
    fun w => (fun j => z j - w * (y₀ j : ℂ), fun _ => (I * (s₁ : ℂ) + w) / 2)
  have hψ_diff : Differentiable ℂ ψ :=
    (differentiable_pi.mpr fun j =>
      (differentiable_const _).sub (differentiable_id.mul (differentiable_const _))).prodMk
      (differentiable_pi.mpr fun _ => ((differentiable_const _).add differentiable_id).div_const 2)
  let Fh : ℂ → ℂ := fun w => mzParamLim F_A yA yB (ψ w).1 (ψ w).2
  have hFh_holo : DifferentiableOn ℂ Fh H :=
    hG_holo.comp hψ_diff.differentiableOn fun w hw => by
      refine ⟨?_, h_diag_mem _ ?_⟩
      · change (fun j => (z j - w * (y₀ j : ℂ)).im) ∈ Metric.ball 0 δ
        simpa [Complex.sub_im, Complex.mul_im] using hw.1
      · simpa [Complex.add_im, Complex.mul_im] using hw.2
  have h0_H : (0 : ℂ) ∈ H := by
    refine ⟨?_, by simpa using hs₁⟩
    simpa [TubeDomain] using hz
  have h_freq_h : ∃ᶠ w in 𝓝[≠] (0 : ℂ),
      Fh w = mzParamLim F_A yA yB z (fun _ => I * ((s₁ : ℂ) / 2)) := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    rcases hU with ⟨V, hV_open, h0V, hV_sub⟩
    rcases Metric.isOpen_iff.mp hV_open 0 h0V with ⟨η, hη, h_ball⟩
    let w₀ : ℂ := ((η / 2 : ℝ) : ℂ)
    have hw₀_ne : w₀ ≠ 0 := by
      dsimp [w₀]; exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hw₀_V : w₀ ∈ V := h_ball (by
      rw [Metric.mem_ball, dist_zero_right]
      dsimp [w₀]; rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]; linarith)
    refine ⟨w₀, hV_sub ⟨hw₀_V, hw₀_ne⟩, ?_⟩
    have h_r := h_real_shift z hz (I * (s₁ : ℂ)) (by simpa using hs₁) (η / 2)
    have h_div : (fun _ : Fin 2 => I * (s₁ : ℂ) / 2) = fun _ : Fin 2 => I * ((s₁ : ℂ) / 2) := by
      ext _; ring
    simpa [Fh, ψ, w₀, h_div] using h_r
  have h_eqOn_H := (hFh_holo.analyticOnNhd hH_open).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_const) hH_conv.isPreconnected h0_H h_freq_h
  have hw_target : I * ((s₂ - s₁ : ℝ) : ℂ) ∈ H := by
    refine ⟨?_, ?_⟩
    · have h_im : (I * ((s₂ - s₁ : ℝ) : ℂ)).im = s₂ - s₁ := by simp
      rw [h_im]
      simpa [TubeDomain, y₀, Complex.sub_im, Complex.mul_im] using hz'
    · have h_im : (I * ((s₂ - s₁ : ℝ) : ℂ)).im = s₂ - s₁ := by simp
      rw [h_im]
      simpa [add_sub_cancel] using hs₂
  have h_res := h_eqOn_H hw_target
  have h_arg2 : (fun _ : Fin 2 => (I * (s₁ : ℂ) + I * ((s₂ - s₁ : ℝ) : ℂ)) / 2) =
      fun _ : Fin 2 => I * ((s₂ : ℂ) / 2) := by
    ext _
    rw [Complex.ofReal_sub]
    ring
  dsimp only [Fh, ψ] at h_res
  rw [h_arg2] at h_res
  exact h_res

lemma exists_midpoint_pair_radius {D : ℕ} {U_A U_B : Set (Fin D → ℝ)}
    (hA_open : IsOpen U_A) (hB_open : IsOpen U_B)
    (hA_conv : Convex ℝ U_A) (hB_conv : Convex ℝ U_B)
    (hA_symm : ∀ y ∈ U_A, -y ∈ U_A) (hB_symm : ∀ y ∈ U_B, -y ∈ U_B)
    (hA_zero : (0 : Fin D → ℝ) ∈ U_A) (hB_zero : (0 : Fin D → ℝ) ∈ U_B)
    {yA yB : Fin D → ℝ} (hyA : yA ∈ U_A) (hyB : yB ∈ U_B) :
    ∃ r > (1 : ℝ), ∃ δ > (0 : ℝ),
      Metric.ball (0 : Fin D → ℝ) δ ⊆ U_A ∩ U_B ∧
      (∀ w ∈ Metric.ball (0 : Fin D → ℝ) δ, ∀ t ∈ Set.Ioo (-r) r, w + t • yA ∈ U_A) ∧
      (∀ w ∈ Metric.ball (0 : Fin D → ℝ) δ, ∀ t ∈ Set.Ioo (-r) r, w + t • yB ∈ U_B) := by
  have h_scale_A : ∃ rA > (1 : ℝ), rA • yA ∈ U_A := by
    have h_cont : Continuous (fun t : ℝ => t • yA) := continuous_id.smul continuous_const
    have h_open : IsOpen ((fun t : ℝ => t • yA) ⁻¹' U_A) := hA_open.preimage h_cont
    have h1_mem : (1 : ℝ) ∈ (fun t : ℝ => t • yA) ⁻¹' U_A := by simpa using hyA
    rcases Metric.isOpen_iff.mp h_open 1 h1_mem with ⟨ε, hε, hsub⟩
    refine ⟨1 + ε / 2, by linarith, hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < 1 + ε / 2 - 1)]
    linarith
  have h_scale_B : ∃ rB > (1 : ℝ), rB • yB ∈ U_B := by
    have h_cont : Continuous (fun t : ℝ => t • yB) := continuous_id.smul continuous_const
    have h_open : IsOpen ((fun t : ℝ => t • yB) ⁻¹' U_B) := hB_open.preimage h_cont
    have h1_mem : (1 : ℝ) ∈ (fun t : ℝ => t • yB) ⁻¹' U_B := by simpa using hyB
    rcases Metric.isOpen_iff.mp h_open 1 h1_mem with ⟨ε, hε, hsub⟩
    refine ⟨1 + ε / 2, by linarith, hsub ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith : 0 < 1 + ε / 2 - 1)]
    linarith
  rcases h_scale_A with ⟨rA, hrA, hrA_mem⟩
  rcases h_scale_B with ⟨rB, hrB, hrB_mem⟩
  let r : ℝ := min rA rB
  have hr_gt1 : 1 < r := lt_min hrA hrB
  have hr_pos : 0 < r := zero_lt_one.trans hr_gt1
  have hr_yA : r • yA ∈ U_A := by
    have h_eq : r • yA = (1 - r / rA) • (0 : Fin D → ℝ) + (r / rA) • (rA • yA) := by
      rw [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ (by linarith)]
    rw [h_eq]
    refine hA_conv hA_zero hrA_mem ?_ (by positivity) (by ring)
    have hle : r ≤ rA := min_le_left _ _
    have hdiv : r / rA ≤ 1 := (div_le_one (by linarith)).mpr hle
    linarith
  have hr_yB : r • yB ∈ U_B := by
    have h_eq : r • yB = (1 - r / rB) • (0 : Fin D → ℝ) + (r / rB) • (rB • yB) := by
      rw [smul_zero, zero_add, smul_smul, div_mul_cancel₀ _ (by linarith)]
    rw [h_eq]
    refine hB_conv hB_zero hrB_mem ?_ (by positivity) (by ring)
    have hle : r ≤ rB := min_le_right _ _
    have hdiv : r / rB ≤ 1 := (div_le_one (by linarith)).mpr hle
    linarith
  rcases Metric.isOpen_iff.mp (hA_open.inter hB_open) 0 ⟨hA_zero, hB_zero⟩ with ⟨δ₀, hδ₀, hsub₀⟩
  rcases Metric.isOpen_iff.mp hA_open (r • yA) hr_yA with ⟨δ₁, hδ₁, hsub₁⟩
  rcases Metric.isOpen_iff.mp hA_open (-(r • yA)) (hA_symm _ hr_yA) with ⟨δ₂, hδ₂, hsub₂⟩
  rcases Metric.isOpen_iff.mp hB_open (r • yB) hr_yB with ⟨δ₃, hδ₃, hsub₃⟩
  rcases Metric.isOpen_iff.mp hB_open (-(r • yB)) (hB_symm _ hr_yB) with ⟨δ₄, hδ₄, hsub₄⟩
  let δ : ℝ := min δ₀ (min (min δ₁ δ₂) (min δ₃ δ₄))
  have hδ_pos : 0 < δ := lt_min hδ₀ (lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hδ₄))
  refine ⟨r, hr_gt1, δ, hδ_pos, ?_, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hsub₀
  · intro w hw t ht
    have hw_norm : ‖w‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have hw_pos : w + r • yA ∈ U_A := hsub₁ (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
      exact hw_norm.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))))
    have hw_neg : w - r • yA ∈ U_A := hsub₂ (by
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, sub_add_cancel]
      exact hw_norm.trans_le
        ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
    have h_comb : w + t • yA =
        ((r + t) / (2 * r)) • (w + r • yA) + ((r - t) / (2 * r)) • (w - r • yA) := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hr_pos.ne']
      ring
    rw [h_comb]
    refine hA_conv hw_pos hw_neg (div_nonneg (by linarith [ht.1]) (by positivity))
      (div_nonneg (by linarith [ht.2]) (by positivity)) ?_
    field_simp [hr_pos.ne']
    ring
  · intro w hw t ht
    have hw_norm : ‖w‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hw
    have hw_pos : w + r • yB ∈ U_B := hsub₃ (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]
      exact hw_norm.trans_le
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hw_neg : w - r • yB ∈ U_B := hsub₄ (by
      rw [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add, sub_add_cancel]
      exact hw_norm.trans_le
        ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have h_comb : w + t • yB =
        ((r + t) / (2 * r)) • (w + r • yB) + ((r - t) / (2 * r)) • (w - r • yB) := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hr_pos.ne']
      ring
    rw [h_comb]
    refine hB_conv hw_pos hw_neg (div_nonneg (by linarith [ht.1]) (by positivity))
      (div_nonneg (by linarith [ht.2]) (by positivity)) ?_
    field_simp [hr_pos.ne']
    ring

theorem symmetric_tube_midpoint_extension {D : ℕ} {U_A U_B : Set (Fin D → ℝ)} {M : ℝ}
    (hA_open : IsOpen U_A) (hB_open : IsOpen U_B)
    (hA_conv : Convex ℝ U_A) (hB_conv : Convex ℝ U_B)
    (hA_symm : ∀ y ∈ U_A, -y ∈ U_A) (hB_symm : ∀ y ∈ U_B, -y ∈ U_B)
    (hA_zero : (0 : Fin D → ℝ) ∈ U_A) (hB_zero : (0 : Fin D → ℝ) ∈ U_B)
    (hM : 0 ≤ M)
    {F_A F_B : (Fin D → ℂ) → ℂ}
    (hFA_holo : DifferentiableOn ℂ F_A (TubeDomain U_A))
    (hFB_holo : DifferentiableOn ℂ F_B (TubeDomain U_B))
    (hFA_bdd : ∀ z ∈ TubeDomain U_A, ‖F_A z‖ ≤ M)
    (hFB_bdd : ∀ z ∈ TubeDomain U_B, ‖F_B z‖ ≤ M)
    (h_agree : ∀ z ∈ TubeDomain (U_A ∩ U_B), F_A z = F_B z) :
    ∃ F : (Fin D → ℂ) → ℂ,
      DifferentiableOn ℂ F (TubeDomain (MidpointSet U_A U_B)) ∧
      (∀ z ∈ TubeDomain (MidpointSet U_A U_B), ‖F z‖ ≤ M) ∧
      (∀ z ∈ TubeDomain (U_A ∩ U_B), F z = F_A z) ∧
      (∀ z ∈ TubeDomain (MidpointSet U_A U_B ∩ U_A), F z = F_A z) ∧
      (∀ z ∈ TubeDomain (MidpointSet U_A U_B ∩ U_B), F z = F_B z) := by
  classical
  have h_local : ∀ yA ∈ U_A, ∀ yB ∈ U_B,
      ∃ (T : Set (Fin D → ℝ)) (G : (Fin D → ℂ) → ℂ) (δ : ℝ),
        IsOpen T ∧ Convex ℝ T ∧ (0 : Fin D → ℝ) ∈ T ∧
        ((fun j => (yA j + yB j) / 2) ∈ T) ∧
        0 < δ ∧ Metric.ball (0 : Fin D → ℝ) δ ⊆ T ∩ (U_A ∩ U_B) ∧
        DifferentiableOn ℂ G (TubeDomain T) ∧
        (∀ w ∈ TubeDomain T, ‖G w‖ ≤ M) ∧
        (∀ w ∈ TubeDomain (Metric.ball 0 δ), G w = F_A w) := by
    intro yA hyA yB hyB
    obtain ⟨r, hr1, δ, hδ, hball_sub, hshiftA, hshiftB⟩ :=
      exists_midpoint_pair_radius hA_open hB_open hA_conv hB_conv hA_symm hB_symm hA_zero hB_zero
        hyA hyB
    have hr : 0 < r := zero_lt_one.trans hr1
    let y₀ : Fin D → ℝ := fun j => (yA j + yB j) / 2
    have h_shA : ∀ z ∈ TubeDomain (Metric.ball 0 δ), ∀ ζ ∈ FlatStrip 2 r 0,
        mzParamMap yA yB z ζ ∈ TubeDomain U_A := by
      intro z hz ζ hζ
      change (fun j => (mzParamMap yA yB z ζ j).im) ∈ U_A
      have h_eq : (fun j => (mzParamMap yA yB z ζ j).im) =
          (fun j => (z j).im) + (ζ 0).im • yA := by
        ext j; rw [mzParamMap_im, hζ.2 1 (by decide)]; simp
      rw [h_eq]
      exact hshiftA (fun j => (z j).im) hz (ζ 0).im (abs_lt.mp hζ.1)
    have h_shB : ∀ z ∈ TubeDomain (Metric.ball 0 δ), ∀ ζ ∈ FlatStrip 2 r 1,
        mzParamMap yA yB z ζ ∈ TubeDomain U_B := by
      intro z hz ζ hζ
      change (fun j => (mzParamMap yA yB z ζ j).im) ∈ U_B
      have h_eq : (fun j => (mzParamMap yA yB z ζ j).im) =
          (fun j => (z j).im) + (ζ 1).im • yB := by
        ext j; rw [mzParamMap_im, hζ.2 0 (by decide)]; simp
      rw [h_eq]
      exact hshiftB (fun j => (z j).im) hz (ζ 1).im (abs_lt.mp hζ.1)
    have h_agr : ∀ z ∈ TubeDomain (Metric.ball 0 δ), ∀ x : Fin 2 → ℝ,
        F_A (mzParamMap yA yB z (fun k => (x k : ℂ))) =
          F_B (mzParamMap yA yB z (fun k => (x k : ℂ))) := by
      intro z hz x
      refine h_agree _ ?_
      change (fun j => (mzParamMap yA yB z (fun k => (x k : ℂ)) j).im) ∈ U_A ∩ U_B
      have h_eq : (fun j => (mzParamMap yA yB z (fun k => (x k : ℂ)) j).im) =
          fun j => (z j).im := by ext j; rw [mzParamMap_im]; simp
      rw [h_eq]
      exact hball_sub hz
    obtain ⟨hL_holo, hL_bdd, hL_A, _⟩ := mzParam_limit_props Metric.isOpen_ball hr hM
      hFA_holo hFB_holo hFA_bdd hFB_bdd h_shA h_shB h_agr
    let T : Set (Fin D → ℝ) := {y : Fin D → ℝ | ∃ t ∈ Set.Ioo (-r) r, y - t • y₀ ∈ Metric.ball 0 δ}
    have hT_open : IsOpen T := by
      rw [isOpen_iff_forall_mem_open]
      rintro y ⟨t, ht, hyt⟩
      let S_t : Set (Fin D → ℝ) := {y' | y' - t • y₀ ∈ Metric.ball 0 δ}
      refine ⟨S_t, fun y' hy' => ⟨t, ht, hy'⟩,
        Metric.isOpen_ball.preimage (continuous_id.sub continuous_const), hyt⟩
    have hT_conv : Convex ℝ T := by
      rintro y₁ ⟨t₁, ht₁, hy₁⟩ y₂ ⟨t₂, ht₂, hy₂⟩ a b ha hb hab
      refine ⟨a * t₁ + b * t₂, ?_, ?_⟩
      · exact convex_Ioo (-r) r ht₁ ht₂ ha hb hab
      · have h_eq : (a • y₁ + b • y₂) - (a * t₁ + b * t₂) • y₀ =
            a • (y₁ - t₁ • y₀) + b • (y₂ - t₂ • y₀) := by
          ext j; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
        rw [h_eq]
        exact (convex_ball (0 : Fin D → ℝ) δ) hy₁ hy₂ ha hb hab
    have h0_T : (0 : Fin D → ℝ) ∈ T := ⟨0, ⟨by linarith, hr⟩, by simp [hδ]⟩
    have hy₀_T : y₀ ∈ T := ⟨1, ⟨by linarith, hr1⟩, by simp [hδ]⟩
    have hball_T : Metric.ball (0 : Fin D → ℝ) δ ⊆ T :=
      fun y hy => ⟨0, ⟨by linarith, hr⟩, by simpa using hy⟩
    let G : (Fin D → ℂ) → ℂ := fun w =>
      if h : ∃ t ∈ Set.Ioo (-r) r, (fun j => (w j).im) - t • y₀ ∈ Metric.ball 0 δ then
        let t := Classical.choose h
        mzParamLim F_A yA yB (fun j => w j - (I * (t : ℂ)) * (y₀ j : ℂ))
          (fun _ => I * ((t : ℂ) / 2))
      else 0
    have hG_eval : ∀ w : Fin D → ℂ, ∀ t ∈ Set.Ioo (-r) r,
        (fun j => (w j).im) - t • y₀ ∈ Metric.ball 0 δ →
        G w = mzParamLim F_A yA yB (fun j => w j - (I * (t : ℂ)) * (y₀ j : ℂ))
          (fun _ => I * ((t : ℂ) / 2)) := by
      intro w t ht hwt
      have hex : ∃ s ∈ Set.Ioo (-r) r, (fun j => (w j).im) - s • y₀ ∈ Metric.ball 0 δ :=
        ⟨t, ht, hwt⟩
      dsimp only [G]
      rw [dif_pos hex]
      set t₀ := Classical.choose hex
      have ht₀ : t₀ ∈ Set.Ioo (-r) r := (Classical.choose_spec hex).1
      have hwt₀ : (fun j => (w j).im) - t₀ • y₀ ∈ Metric.ball 0 δ := (Classical.choose_spec hex).2
      let z₁ : Fin D → ℂ := fun j => w j - (I * (t : ℂ)) * (y₀ j : ℂ)
      have hz₁_in : z₁ ∈ TubeDomain (Metric.ball 0 δ) := by
        change (fun j => (z₁ j).im) ∈ Metric.ball 0 δ
        have h_im_eq : (fun j => (z₁ j).im) = (fun j => (w j).im) - t • y₀ := by
          ext j; simp [z₁, Complex.mul_im]
        rw [h_im_eq]; exact hwt
      have hz₂_eq : (fun j => z₁ j - (I * ((t₀ - t : ℝ) : ℂ)) * (((yA j + yB j) / 2 : ℝ) : ℂ)) =
          fun j => w j - (I * (t₀ : ℂ)) * (y₀ j : ℂ) := by
        ext j; dsimp [z₁, y₀]; rw [Complex.ofReal_sub]; ring
      have hz₂_in : (fun j => z₁ j - (I * ((t₀ - t : ℝ) : ℂ)) * (((yA j + yB j) / 2 : ℝ) : ℂ)) ∈
          TubeDomain (Metric.ball 0 δ) := by
        rw [hz₂_eq]
        change (fun j => (w j - (I * (t₀ : ℂ)) * (y₀ j : ℂ)).im) ∈ Metric.ball 0 δ
        have h_im_eq : (fun j => (w j - (I * (t₀ : ℂ)) * (y₀ j : ℂ)).im) =
            (fun j => (w j).im) - t₀ • y₀ := by ext j; simp [Complex.mul_im]
        rw [h_im_eq]; exact hwt₀
      have h_inv := mzParamLim_diag_shift_invariant hr hM hFA_holo hFB_holo hFA_bdd hFB_bdd
        h_shA h_shB h_agr hz₁_in (abs_lt.mpr ht) (abs_lt.mpr ht₀) hz₂_in
      rw [hz₂_eq] at h_inv
      exact h_inv
    have hG_holo : DifferentiableOn ℂ G (TubeDomain T) := by
      intro w₀ hw₀
      rcases hw₀ with ⟨t, ht, hwt⟩
      let V : Set (Fin D → ℂ) :=
        {w : Fin D → ℂ | (fun j => (w j).im) - t • y₀ ∈ Metric.ball 0 δ}
      have hV_open : IsOpen V :=
        Metric.isOpen_ball.preimage
          ((continuous_pi fun j => Complex.continuous_im.comp (continuous_apply j)).sub
            continuous_const)
      have hw₀_V : w₀ ∈ V := hwt
      let φ : (Fin D → ℂ) → (Fin D → ℂ) × (Fin 2 → ℂ) :=
        fun w => (fun j => w j - (I * (t : ℂ)) * (y₀ j : ℂ), fun _ => I * ((t : ℂ) / 2))
      have hφ_diff : Differentiable ℂ φ :=
        (differentiable_pi.mpr fun j =>
          (differentiable_apply j).sub (differentiable_const _)).prodMk (differentiable_const _)
      have h_comp : DifferentiableOn ℂ (fun w => mzParamLim F_A yA yB (φ w).1 (φ w).2) V :=
        hL_holo.comp hφ_diff.differentiableOn fun w hw => by
          refine ⟨?_, ?_⟩
          · change (fun j => (w j - (I * (t : ℂ)) * (y₀ j : ℂ)).im) ∈ Metric.ball 0 δ
            have h_im_eq : (fun j => (w j - (I * (t : ℂ)) * (y₀ j : ℂ)).im) =
                (fun j => (w j).im) - t • y₀ := by ext j; simp [Complex.mul_im]
            rw [h_im_eq]; exact hw
          · change ∑ _ : Fin 2, |(I * ((t : ℂ) / 2)).im| < r
            have h_im : (I * ((t : ℂ) / 2)).im = t / 2 := by simp
            simp only [h_im, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            linarith [abs_lt.mpr ht]
      have h_da : DifferentiableAt ℂ (fun w => mzParamLim F_A yA yB (φ w).1 (φ w).2) w₀ :=
        (h_comp w₀ hw₀_V).differentiableAt (hV_open.mem_nhds hw₀_V)
      have h_ev : G =ᶠ[𝓝 w₀] fun w => mzParamLim F_A yA yB (φ w).1 (φ w).2 :=
        Filter.eventually_of_mem (hV_open.mem_nhds hw₀_V) fun w hw => hG_eval w t ht hw
      exact (h_da.congr_of_eventuallyEq h_ev).differentiableWithinAt
    have hG_bdd : ∀ w ∈ TubeDomain T, ‖G w‖ ≤ M := by
      rintro w ⟨t, ht, hwt⟩
      rw [hG_eval w t ht hwt]
      refine hL_bdd _ ?_ _ ?_
      · change (fun j => (w j - (I * (t : ℂ)) * (y₀ j : ℂ)).im) ∈ Metric.ball 0 δ
        have h_im_eq : (fun j => (w j - (I * (t : ℂ)) * (y₀ j : ℂ)).im) =
            (fun j => (w j).im) - t • y₀ := by ext j; simp [Complex.mul_im]
        rw [h_im_eq]; exact hwt
      · change ∑ _ : Fin 2, |(I * ((t : ℂ) / 2)).im| < r
        have h_im : (I * ((t : ℂ) / 2)).im = t / 2 := by simp
        simp only [h_im, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        linarith [abs_lt.mpr ht]
    have hG_eqA : ∀ w ∈ TubeDomain (Metric.ball 0 δ), G w = F_A w := by
      intro w hw
      rw [hG_eval w 0 ⟨by linarith, hr⟩ (by simpa [TubeDomain] using hw)]
      have h0_flat : (fun _ : Fin 2 => I * ((0 : ℂ) / 2)) ∈ FlatStrip 2 r 0 := by
        refine ⟨by simp [hr], fun _ _ => by simp⟩
      have h_eq := hL_A w hw _ h0_flat
      have h_w_eq : (fun j => w j - (I * ((0 : ℝ) : ℂ)) * (y₀ j : ℂ)) = w := by ext j; simp
      have h_map_eq : mzParamMap yA yB w (fun _ : Fin 2 => I * ((0 : ℂ) / 2)) = w := by
        ext j; simp [mzParamMap]
      rw [h_w_eq]
      simp only [Complex.ofReal_zero]
      rw [h_eq, h_map_eq]
    exact ⟨T, G, δ, hT_open, hT_conv, h0_T, hy₀_T, hδ,
      fun y hy => ⟨hball_T hy, hball_sub hy⟩, hG_holo, hG_bdd, hG_eqA⟩
  let P : Set ((Fin D → ℝ) × (Fin D → ℝ)) := U_A ×ˢ U_B
  let chartT : ∀ p : (Fin D → ℝ) × (Fin D → ℝ), p ∈ P → Set (Fin D → ℝ) :=
    fun p hp => Classical.choose (h_local p.1 hp.1 p.2 hp.2)
  let chartG : ∀ p : (Fin D → ℝ) × (Fin D → ℝ), p ∈ P → (Fin D → ℂ) → ℂ :=
    fun p hp => Classical.choose (Classical.choose_spec (h_local p.1 hp.1 p.2 hp.2))
  let chartδ : ∀ p : (Fin D → ℝ) × (Fin D → ℝ), p ∈ P → ℝ :=
    fun p hp => Classical.choose (Classical.choose_spec
      (Classical.choose_spec (h_local p.1 hp.1 p.2 hp.2)))
  have hchart_spec : ∀ p (hp : p ∈ P),
      IsOpen (chartT p hp) ∧ Convex ℝ (chartT p hp) ∧ (0 : Fin D → ℝ) ∈ chartT p hp ∧
      ((fun j => (p.1 j + p.2 j) / 2) ∈ chartT p hp) ∧
      0 < chartδ p hp ∧ Metric.ball (0 : Fin D → ℝ) (chartδ p hp) ⊆ chartT p hp ∩ (U_A ∩ U_B) ∧
      DifferentiableOn ℂ (chartG p hp) (TubeDomain (chartT p hp)) ∧
      (∀ w ∈ TubeDomain (chartT p hp), ‖chartG p hp w‖ ≤ M) ∧
      (∀ w ∈ TubeDomain (Metric.ball 0 (chartδ p hp)), chartG p hp w = F_A w) :=
    fun p hp => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (h_local p.1 hp.1 p.2 hp.2)))
  have h_chart_agree : ∀ p₁ (hp₁ : p₁ ∈ P) p₂ (hp₂ : p₂ ∈ P),
      ∀ w ∈ TubeDomain (chartT p₁ hp₁ ∩ chartT p₂ hp₂), chartG p₁ hp₁ w = chartG p₂ hp₂ w := by
    intro p₁ hp₁ p₂ hp₂ w hw
    obtain ⟨hT1_o, hT1_c, h0_1, _, hδ1, _, hG1_h, _, hG1_A⟩ := hchart_spec p₁ hp₁
    obtain ⟨hT2_o, hT2_c, h0_2, _, hδ2, _, hG2_h, _, hG2_A⟩ := hchart_spec p₂ hp₂
    let δm : ℝ := min (chartδ p₁ hp₁) (chartδ p₂ hp₂)
    have hδm : 0 < δm := lt_min hδ1 hδ2
    have h_star : ∀ y ∈ chartT p₁ hp₁ ∩ chartT p₂ hp₂, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        s • y ∈ chartT p₁ hp₁ ∩ chartT p₂ hp₂ := by
      intro y hy s hs
      have h_eq : s • y = (1 - s) • (0 : Fin D → ℝ) + s • y := by rw [smul_zero, zero_add]
      rw [h_eq]
      exact ⟨hT1_c h0_1 hy.1 (by linarith [hs.2]) hs.1 (by ring),
        hT2_c h0_2 hy.2 (by linarith [hs.2]) hs.1 (by ring)⟩
    have h_eq_ball : Set.EqOn (chartG p₁ hp₁) (chartG p₂ hp₂) (TubeDomain (Metric.ball 0 δm)) := by
      intro z hz
      have hz1 : z ∈ TubeDomain (Metric.ball 0 (chartδ p₁ hp₁)) :=
        Metric.ball_subset_ball (min_le_left _ _) hz
      have hz2 : z ∈ TubeDomain (Metric.ball 0 (chartδ p₂ hp₂)) :=
        Metric.ball_subset_ball (min_le_right _ _) hz
      rw [hG1_A z hz1, hG2_A z hz2]
    exact tubeDomain_eqOn_of_starShaped (hT1_o.inter hT2_o) hδm h_star
      (hG1_h.mono fun _ h => h.1) (hG2_h.mono fun _ h => h.2) h_eq_ball hw
  let F : (Fin D → ℂ) → ℂ := fun w =>
    if h : ∃ p : (Fin D → ℝ) × (Fin D → ℝ), ∃ hp : p ∈ P, w ∈ TubeDomain (chartT p hp) then
      let p := Classical.choose h
      let hp := Classical.choose (Classical.choose_spec h)
      chartG p hp w
    else 0
  have hF_eval : ∀ p (hp : p ∈ P), ∀ w ∈ TubeDomain (chartT p hp), F w = chartG p hp w := by
    intro p hp w hw
    have hex : ∃ q : (Fin D → ℝ) × (Fin D → ℝ), ∃ hq : q ∈ P, w ∈ TubeDomain (chartT q hq) :=
      ⟨p, hp, hw⟩
    dsimp only [F]
    rw [dif_pos hex]
    set q := Classical.choose hex
    set hq := Classical.choose (Classical.choose_spec hex)
    have hwq : w ∈ TubeDomain (chartT q hq) := Classical.choose_spec (Classical.choose_spec hex)
    exact h_chart_agree q hq p hp w ⟨hwq, hw⟩
  have h_mid_cover : ∀ w ∈ TubeDomain (MidpointSet U_A U_B),
      ∃ p : (Fin D → ℝ) × (Fin D → ℝ), ∃ hp : p ∈ P, w ∈ TubeDomain (chartT p hp) := by
    rintro w ⟨yA, hyA, yB, hyB, hy_eq⟩
    have hp : (yA, yB) ∈ P := ⟨hyA, hyB⟩
    refine ⟨(yA, yB), hp, ?_⟩
    change (fun j => (w j).im) ∈ chartT (yA, yB) hp
    have h_mid_eq : (fun j => (w j).im) = fun j => (yA j + yB j) / 2 := by
      rw [hy_eq]; ext j; simp; ring
    rw [h_mid_eq]
    exact (hchart_spec (yA, yB) hp).2.2.2.1
  have hF_holo : DifferentiableOn ℂ F (TubeDomain (MidpointSet U_A U_B)) := by
    intro w₀ hw₀
    obtain ⟨p, hp, hwp⟩ := h_mid_cover w₀ hw₀
    have hT_open : IsOpen (TubeDomain (chartT p hp)) :=
      isOpen_TubeDomain (hchart_spec p hp).1
    have h_da : DifferentiableAt ℂ (chartG p hp) w₀ :=
      ((hchart_spec p hp).2.2.2.2.2.2.1 w₀ hwp).differentiableAt (hT_open.mem_nhds hwp)
    have h_ev : F =ᶠ[𝓝 w₀] chartG p hp :=
      Filter.eventually_of_mem (hT_open.mem_nhds hwp) fun w hw => hF_eval p hp w hw
    exact (h_da.congr_of_eventuallyEq h_ev).differentiableWithinAt
  have hF_bdd : ∀ w ∈ TubeDomain (MidpointSet U_A U_B), ‖F w‖ ≤ M := by
    intro w hw
    obtain ⟨p, hp, hwp⟩ := h_mid_cover w hw
    rw [hF_eval p hp w hwp]
    exact (hchart_spec p hp).2.2.2.2.2.2.2.1 w hwp
  have h0_P : ((0 : Fin D → ℝ), (0 : Fin D → ℝ)) ∈ P := ⟨hA_zero, hB_zero⟩
  let δ₀ : ℝ := chartδ (0, 0) h0_P
  have hδ₀_pos : 0 < δ₀ := (hchart_spec (0, 0) h0_P).2.2.2.2.1
  have hF_ball : Set.EqOn F F_A (TubeDomain (Metric.ball 0 δ₀)) := by
    intro w hw
    have hwT : w ∈ TubeDomain (chartT (0, 0) h0_P) :=
      ((hchart_spec (0, 0) h0_P).2.2.2.2.2.1 hw).1
    rw [hF_eval (0, 0) h0_P w hwT]
    exact (hchart_spec (0, 0) h0_P).2.2.2.2.2.2.2.2 w hw
  have hF_ball_B : Set.EqOn F F_B (TubeDomain (Metric.ball 0 δ₀)) := by
    intro w hw
    rw [hF_ball hw]
    exact h_agree w ((hchart_spec (0, 0) h0_P).2.2.2.2.2.1 hw).2
  have hMid_open : IsOpen (MidpointSet U_A U_B) := isOpen_midpointSet hB_open
  have hMid_conv : Convex ℝ (MidpointSet U_A U_B) := convex_midpointSet hA_conv hB_conv
  have h0_Mid : (0 : Fin D → ℝ) ∈ MidpointSet U_A U_B :=
    inter_subset_midpointSet ⟨hA_zero, hB_zero⟩
  have hF_eq_A : ∀ w ∈ TubeDomain (MidpointSet U_A U_B ∩ U_A), F w = F_A w := by
    have h_star : ∀ y ∈ MidpointSet U_A U_B ∩ U_A, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        s • y ∈ MidpointSet U_A U_B ∩ U_A := by
      intro y hy s hs
      have h_eq : s • y = (1 - s) • (0 : Fin D → ℝ) + s • y := by rw [smul_zero, zero_add]
      rw [h_eq]
      exact ⟨hMid_conv h0_Mid hy.1 (by linarith [hs.2]) hs.1 (by ring),
        hA_conv hA_zero hy.2 (by linarith [hs.2]) hs.1 (by ring)⟩
    exact tubeDomain_eqOn_of_starShaped (hMid_open.inter hA_open) hδ₀_pos h_star
      (hF_holo.mono fun _ h => h.1) (hFA_holo.mono fun _ h => h.2) hF_ball
  have hF_eq_B : ∀ w ∈ TubeDomain (MidpointSet U_A U_B ∩ U_B), F w = F_B w := by
    have h_star : ∀ y ∈ MidpointSet U_A U_B ∩ U_B, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        s • y ∈ MidpointSet U_A U_B ∩ U_B := by
      intro y hy s hs
      have h_eq : s • y = (1 - s) • (0 : Fin D → ℝ) + s • y := by rw [smul_zero, zero_add]
      rw [h_eq]
      exact ⟨hMid_conv h0_Mid hy.1 (by linarith [hs.2]) hs.1 (by ring),
        hB_conv hB_zero hy.2 (by linarith [hs.2]) hs.1 (by ring)⟩
    exact tubeDomain_eqOn_of_starShaped (hMid_open.inter hB_open) hδ₀_pos h_star
      (hF_holo.mono fun _ h => h.1) (hFB_holo.mono fun _ h => h.2) hF_ball_B
  refine ⟨F, hF_holo, hF_bdd, ?_, hF_eq_A, hF_eq_B⟩
  intro w hw
  exact hF_eq_A w ⟨inter_subset_midpointSet hw, hw.1⟩

end Phase1MidpointTube

end QFT
