import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Topology.Sets.Opens
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import SCVAnalysis
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Normed.Group.Tannery

open Set TopologicalSpace ContinuousLinearMap QFT MeasureTheory Metric Complex Analysis
open scoped Distributions Manifold NNReal ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
variable (Ω : Opens E)

def VanishesOn (T : 𝓓'(Ω, F)) (U : Opens E) (_ : (U : Set E) ⊆ (Ω : Set E)) : Prop :=
  ∀ f : 𝓓(Ω, ℝ), tsupport (fun x => f x) ⊆ (U : Set E) → T f = 0

def support (T : 𝓓'(Ω, F)) : Set E :=
  (Ω : Set E) \ ⋃ (U : Opens E) (hU : (U : Set E) ⊆ (Ω : Set E))
    (_ : VanishesOn Ω T U hU), (U : Set E)

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma compl_support_eq (T : 𝓓'(Ω, F)) :
    (Ω : Set E) \ Distribution.support Ω T =
    ⋃ (U : Opens E) (hU : (U : Set E) ⊆ (Ω : Set E)) (_ : VanishesOn Ω T U hU), (U : Set E) := by
  rw [Distribution.support]
  have h_sub : (⋃ (U : Opens E) (hU : (U : Set E) ⊆ (Ω : Set E))
      (_ : VanishesOn Ω T U hU), (U : Set E)) ⊆ (Ω : Set E) := by
    intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨U, hU, _, hxU⟩
    exact hU hxU
  exact sdiff_sdiff_cancel_left h_sub

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma isOpen_compl_support (T : 𝓓'(Ω, F)) : IsOpen ((Ω : Set E) \ Distribution.support Ω T) := by
  rw [compl_support_eq]
  apply isOpen_iUnion
  intro U
  apply isOpen_iUnion
  intro _
  apply isOpen_iUnion
  intro _
  exact U.isOpen

def HasCompactSupport (T : 𝓓'(Ω, F)) : Prop :=
  IsCompact (Distribution.support Ω T)

def VanishIndex (T : 𝓓'(Ω, F)) :=
  { U : Opens E // ∃ (hU : (U : Set E) ⊆ (Ω : Set E)), VanishesOn Ω T U hU }

def VanishCover (T : 𝓓'(Ω, F)) (i : VanishIndex Ω T) : Set E :=
  (i.1 : Set E)

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma isOpen_VanishCover (T : 𝓓'(Ω, F)) (i : VanishIndex Ω T) : IsOpen (VanishCover Ω T i) :=
  i.1.isOpen

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma iUnion_VanishCover_eq (T : 𝓓'(Ω, F)) :
    ⋃ i : VanishIndex Ω T, VanishCover Ω T i = (Ω : Set E) \ Distribution.support Ω T := by
  rw [compl_support_eq]
  ext x
  simp only [VanishCover, mem_iUnion]
  constructor
  · rintro ⟨⟨U, hU, hV⟩, hx⟩
    exact ⟨U, hU, hV, hx⟩
  · rintro ⟨U, hU, hV, hx⟩
    exact ⟨⟨U, hU, hV⟩, hx⟩

noncomputable def pouTestFunc (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x)))
    (i : VanishIndex Ω T) : 𝓓(Ω, ℝ) :=
  {
    toFun := fun x => p i x * f x
    contDiff' := ContDiff.mul (ContMDiff.contDiff (p i).contMDiff) f.contDiff'
    hasCompactSupport' := by
      apply HasCompactSupport.of_support_subset_isCompact f.hasCompactSupport'
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx
      apply subset_closure
      simp only [Function.mem_support, ne_eq]
      intro h_f
      exact hx (by rw [show f x = 0 from h_f, mul_zero])
    tsupport_subset' := by
      calc
        tsupport (fun x => p i x * f x) ⊆ tsupport (fun x => f x) := by
          apply closure_mono
          intro x hx
          simp only [Function.mem_support, ne_eq] at hx
          simp only [Function.mem_support, ne_eq]
          intro h_f
          exact hx (by rw [show f x = 0 from h_f, mul_zero])
        _ ⊆ (Ω : Set E) := f.tsupport_subset'
  }

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pouTestFunc_tsupport_subset (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x)))
    (hp_sub : p.IsSubordinate (VanishCover Ω T)) (i : VanishIndex Ω T) :
    tsupport (fun x => (pouTestFunc Ω T f p i) x) ⊆ VanishCover Ω T i := by
  calc
    tsupport (fun x => p i x * f x) ⊆ tsupport (p i) := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx
      simp only [Function.mem_support, ne_eq]
      intro h_p
      exact hx (by rw [show p i x = 0 from h_p, zero_mul])
    _ ⊆ VanishCover Ω T i := hp_sub i

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pouTestFunc_eval_zero (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x)))
    (hp_sub : p.IsSubordinate (VanishCover Ω T)) (i : VanishIndex Ω T) :
    T (pouTestFunc Ω T f p i) = 0 := by
  have h_supp := pouTestFunc_tsupport_subset Ω T f p hp_sub i
  have h_ex := i.2
  rcases h_ex with ⟨hU, h_vanish⟩
  exact h_vanish (pouTestFunc Ω T f p i) h_supp

noncomputable def POUFinset (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x))) :
    Finset (VanishIndex Ω T) :=
  (p.locallyFinite.finite_nonempty_inter_compact f.hasCompactSupport').toFinset

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pou_sum_eq (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x))) (x : E) :
    ∑ i ∈ POUFinset Ω T f p, p i x * f x = f x := by
  by_cases hf : f x = 0
  · rw [hf]
    simp only [mul_zero, Finset.sum_const_zero]
  · have hx_supp : x ∈ tsupport (fun x => f x) := subset_closure hf
    have h_sum1 := p.sum_eq_one hx_supp
    have h_finsum : ∑ᶠ i, p i x = ∑ i ∈ POUFinset Ω T f p, p i x := by
      apply finsum_eq_sum_of_support_subset
      intro i hi
      have h_nonempty : (Function.support (p i) ∩ tsupport (fun x => f x)).Nonempty :=
        ⟨x, ⟨hi, hx_supp⟩⟩
      have h_mem : i ∈ POUFinset Ω T f p := by
        simp only [POUFinset, Finite.mem_toFinset, mem_setOf_eq]
        exact h_nonempty
      exact h_mem
    rw [h_finsum] at h_sum1
    calc
      ∑ i ∈ POUFinset Ω T f p, p i x * f x = (∑ i ∈ POUFinset Ω T f p, p i x) * f x := by
        rw [Finset.sum_mul]
      _ = 1 * f x := by rw [h_sum1]
      _ = f x := by rw [one_mul]

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pou_sum_eq_testFunc (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x))) :
    ∑ i ∈ POUFinset Ω T f p, pouTestFunc Ω T f p i = f := by
  ext x
  have h_sum : (∑ i ∈ POUFinset Ω T f p, pouTestFunc Ω T f p i) x =
      ∑ i ∈ POUFinset Ω T f p, (pouTestFunc Ω T f p i) x := by
    simp
  rw [h_sum]
  exact pou_sum_eq Ω T f p x

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma vanishing_on_disjoint_support (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (h_disj : tsupport (fun x => f x) ⊆ (Ω : Set E) \ Distribution.support Ω T) : T f = 0 := by
  have h_K_closed : IsClosed (tsupport (fun x => f x)) := isClosed_closure
  have h_cov : tsupport (fun x => f x) ⊆ ⋃ i : VanishIndex Ω T, VanishCover Ω T i := by
    rw [iUnion_VanishCover_eq]
    exact h_disj
  rcases SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) h_K_closed
    (VanishCover Ω T) (isOpen_VanishCover Ω T) h_cov with ⟨p, hp_sub⟩
  have h_decomp := pou_sum_eq_testFunc Ω T f p
  rw [← h_decomp]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact pouTestFunc_eval_zero Ω T f p hp_sub i

noncomputable def applySmoothFun (T : 𝓓'(Ω, F)) (_ : HasCompactSupport Ω T)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens E) (_ : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (_ : ∀ x ∈ (V : Set E), χ x = 1) : 𝓓(Ω, ℝ) :=
  {
    toFun := fun x => χ.toFun x * ψ x
    contDiff' := by
      exact ContDiff.mul χ.contDiff' hψ
    hasCompactSupport' := by
      apply HasCompactSupport.of_support_subset_isCompact χ.hasCompactSupport'
      intro x hx
      apply subset_closure
      intro h
      apply hx
      dsimp only
      have h_toFun : χ.toFun x = 0 := h
      rw [h_toFun, zero_mul]
    tsupport_subset' := by
      calc
        tsupport (fun x => χ.toFun x * ψ x) ⊆ tsupport χ := by
          apply closure_mono
          intro x hx h
          apply hx
          dsimp only
          have h_toFun : χ.toFun x = 0 := h
          rw [h_toFun, zero_mul]
        _ ⊆ Ω := χ.tsupport_subset'
  }

noncomputable def applySmooth (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) : F :=
  T (applySmoothFun Ω T hT ψ hψ V hV χ hχ_one)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_indep (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V₁ V₂ : Opens E)
    (hV₁ : Distribution.support Ω T ⊆ (V₁ : Set E))
    (hV₂ : Distribution.support Ω T ⊆ (V₂ : Set E))
    (χ₁ χ₂ : 𝓓(Ω, ℝ))
    (hχ₁ : ∀ x ∈ (V₁ : Set E), χ₁ x = 1)
    (hχ₂ : ∀ x ∈ (V₂ : Set E), χ₂ x = 1) :
    applySmooth Ω T hT ψ hψ V₁ hV₁ χ₁ hχ₁ = applySmooth Ω T hT ψ hψ V₂ hV₂ χ₂ hχ₂ := by
  let F₁ := applySmoothFun Ω T hT ψ hψ V₁ hV₁ χ₁ hχ₁
  let F₂ := applySmoothFun Ω T hT ψ hψ V₂ hV₂ χ₂ hχ₂
  have h_eq : T F₁ - T F₂ = 0 := by
    rw [← map_sub T F₁ F₂]
    apply vanishing_on_disjoint_support
    let S := {x : E | χ₁.toFun x * ψ x - χ₂.toFun x * ψ x ≠ 0}
    have hS : S ⊆ (V₁ : Set E)ᶜ ∪ (V₂ : Set E)ᶜ := by
      intro x hx
      have hx_prop : χ₁.toFun x * ψ x - χ₂.toFun x * ψ x ≠ 0 := hx
      by_contra h
      simp only [mem_union, mem_compl_iff] at h
      push Not at h
      have h1 := hχ₁ x h.1
      have h2 := hχ₂ x h.2
      have h_eval : χ₁.toFun x * ψ x - χ₂.toFun x * ψ x = 1 * ψ x - 1 * ψ x := by
        rw [show χ₁.toFun x = 1 from h1, show χ₂.toFun x = 1 from h2]
      rw [h_eval, sub_self] at hx_prop
      exact hx_prop rfl
    have h_closed : IsClosed ((V₁ : Set E)ᶜ ∪ (V₂ : Set E)ᶜ) := by
      apply IsClosed.union
      · exact V₁.isOpen.isClosed_compl
      · exact V₂.isOpen.isClosed_compl
    have h_closure : closure S ⊆ (V₁ : Set E)ᶜ ∪ (V₂ : Set E)ᶜ := closure_minimal hS h_closed
    have h_subset_Ω : closure S ⊆ (Ω : Set E) := by
      calc
        closure S ⊆ closure (Function.support (fun x => χ₁.toFun x) ∪
          Function.support (fun x => χ₂.toFun x)) := by
          apply closure_mono
          intro x hx
          have hx_prop : χ₁.toFun x * ψ x - χ₂.toFun x * ψ x ≠ 0 := hx
          have h_not_zero : χ₁.toFun x ≠ 0 ∨ χ₂.toFun x ≠ 0 := by
            by_contra h_both
            push Not at h_both
            rw [h_both.1, h_both.2] at hx_prop
            rw [sub_self] at hx_prop
            exact hx_prop rfl
          simp only [mem_union, Function.mem_support, ne_eq]
          exact h_not_zero
        _ = tsupport (fun x => χ₁.toFun x) ∪ tsupport (fun x => χ₂.toFun x) := by
          rw [closure_union]
          rfl
        _ ⊆ (Ω : Set E) := by
          apply union_subset
          · exact χ₁.tsupport_subset'
          · exact χ₂.tsupport_subset'
    intro x hx
    simp only [mem_sdiff]
    refine ⟨h_subset_Ω hx, ?_⟩
    intro hx_supp
    have h_in_union := h_closure hx
    simp only [mem_union, mem_compl_iff] at h_in_union
    cases h_in_union with
    | inl h1 => exact h1 (hV₁ hx_supp)
    | inr h2 => exact h2 (hV₂ hx_supp)
  exact sub_eq_zero.mp h_eq

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_congr (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f g : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (h_eq : ∀ x, f x = g x)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT f hf V hV χ hχ_one = applySmooth Ω T hT g hg V hV χ hχ_one := by
  dsimp [applySmooth]
  congr 1
  ext x
  dsimp [applySmoothFun]
  rw [h_eq x]

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_zero (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun _ => 0) contDiff_const V hV χ hχ_one = 0 := by
  dsimp [applySmooth]
  have h_zero : applySmoothFun Ω T hT (fun _ => 0) contDiff_const V hV χ hχ_one = 0 := by
    ext x
    dsimp [applySmoothFun]
    exact mul_zero (χ.toFun x)
  rw [h_zero]
  exact map_zero T

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_add (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f g : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => f x + g x) (hf.add hg) V hV χ hχ_one =
      applySmooth Ω T hT f hf V hV χ hχ_one + applySmooth Ω T hT g hg V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_add : applySmoothFun Ω T hT (fun x => f x + g x) (hf.add hg) V hV χ hχ_one =
      applySmoothFun Ω T hT f hf V hV χ hχ_one + applySmoothFun Ω T hT g hg V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    exact mul_add (χ.toFun x) (f x) (g x)
  rw [h_add]
  exact map_add T _ _

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_sub (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f g : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => f x - g x) (hf.sub hg) V hV χ hχ_one =
      applySmooth Ω T hT f hf V hV χ hχ_one - applySmooth Ω T hT g hg V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_sub : applySmoothFun Ω T hT (fun x => f x - g x) (hf.sub hg) V hV χ hχ_one =
      applySmoothFun Ω T hT f hf V hV χ hχ_one - applySmoothFun Ω T hT g hg V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    exact mul_sub (χ.toFun x) (f x) (g x)
  rw [h_sub]
  exact map_sub T _ _

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_smul (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (c : ℝ) (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => c * f x) (contDiff_const.mul hf) V hV χ hχ_one =
      c • applySmooth Ω T hT f hf V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_smul : applySmoothFun Ω T hT (fun x => c * f x) (contDiff_const.mul hf) V hV χ hχ_one =
      c • applySmoothFun Ω T hT f hf V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    change χ.toFun x * (c * f x) = c * (χ.toFun x * f x)
    ring
  rw [h_smul]
  exact map_smul T c _

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_sum {ι : Type*} (s : Finset ι)
    (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f i))
    (hsum : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i ∈ s, f i x))
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => ∑ i ∈ s, f i x) hsum V hV χ hχ_one =
      ∑ i ∈ s, applySmooth Ω T hT (f i) (hf i) V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_sum_fun : applySmoothFun Ω T hT (fun x => ∑ i ∈ s, f i x) hsum V hV χ hχ_one =
      ∑ i ∈ s, applySmoothFun Ω T hT (f i) (hf i) V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    rw [Finset.mul_sum]
    exact (_root_.sum_apply s (fun i => applySmoothFun Ω T hT (f i) (hf i) V hV χ hχ_one) x).symm
  rw [h_sum_fun]
  exact map_sum T (fun i => applySmoothFun Ω T hT (f i) (hf i) V hV χ hχ_one) s

variable {n : ℕ} (V_plus : Set (Fin n → ℝ)) (Ω_n : Opens (Fin n → ℝ))

noncomputable def boundaryIntegral (f : (Fin n → ℂ) → ℂ) (φ : 𝓓(Ω_n, ℝ)) (y : Fin n → ℝ) : ℂ :=
  ∫ (x : Fin n → ℝ), f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)

def HasBoundaryValue (f : (Fin n → ℂ) → ℂ) (V : Set (Fin n → ℝ)) (T : 𝓓'(Ω_n, ℂ)) : Prop :=
  ∀ φ : 𝓓(Ω_n, ℝ), Filter.Tendsto (boundaryIntegral Ω_n f φ) (nhdsWithin 0 V) (nhds (T φ))

lemma boundary_limit_exists (f : (Fin n → ℂ) → ℂ) (T : 𝓓'(Ω_n, ℂ))
    (h_bval : HasBoundaryValue Ω_n f V_plus T) (φ : 𝓓(Ω_n, ℝ)) :
    ∃ (c : ℂ), Filter.Tendsto (boundaryIntegral Ω_n f φ) (nhdsWithin 0 V_plus) (nhds c) :=
  ⟨T φ, h_bval φ⟩

noncomputable def BoundaryValueDistribution
    (f : (Fin n → ℂ) → ℂ)
    (h_bval : ∃ T : 𝓓'(Ω_n, ℂ), HasBoundaryValue Ω_n f V_plus T) : 𝓓'(Ω_n, ℂ) :=
  Classical.choose h_bval

lemma boundaryValueDistribution_spec
    (f : (Fin n → ℂ) → ℂ)
    (h_bval : ∃ T : 𝓓'(Ω_n, ℂ), HasBoundaryValue Ω_n f V_plus T) :
    HasBoundaryValue Ω_n f V_plus (BoundaryValueDistribution V_plus Ω_n f h_bval) :=
  Classical.choose_spec h_bval

lemma tendsto_boundaryIntegral_of_dominated
    (f : (Fin n → ℂ) → ℂ)
    (f₀ : (Fin n → ℝ) → ℂ)
    (φ : 𝓓(Ω_n, ℝ))
    (bound : (Fin n → ℝ) → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ᶠ y in nhdsWithin 0 V_plus,
      AEStronglyMeasurable
        (fun x => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)) volume)
    (h_bound : ∀ᶠ y in nhdsWithin 0 V_plus, ∀ᵐ x ∂volume,
      ‖f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)‖ ≤ bound x)
    (h_tendsto : ∀ᵐ x ∂volume,
      Filter.Tendsto (fun y => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ))
        (nhdsWithin 0 V_plus) (nhds (f₀ x * (φ x : ℂ)))) :
    Filter.Tendsto (boundaryIntegral Ω_n f φ) (nhdsWithin 0 V_plus)
      (nhds (∫ x, f₀ x * (φ x : ℂ))) :=
  tendsto_integral_boundary V_plus
    (fun y x => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ))
    (fun x => f₀ x * (φ x : ℂ))
    bound h_bound_integrable h_f_meas h_bound h_tendsto

lemma distribution_compact_bound
    (T : 𝓓'(Ω_n, ℂ)) (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω_n) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (f : 𝓓_{K}(Fin n → ℝ, ℝ)),
      ‖T (TestFunction.ofSupportedIn hK f)‖ ≤
        (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K) f) := by
  let TK : 𝓓_{K}(Fin n → ℝ, ℝ) →L[ℝ] ℂ :=
    (T : 𝓓(Ω_n, ℝ) →L[ℝ] ℂ).comp (TestFunction.ofSupportedInCLM ℝ hK)
  let q : Seminorm ℝ 𝓓_{K}(Fin n → ℝ, ℝ) :=
    (normSeminorm ℝ ℂ).comp TK.toLinearMap
  have hq_cont : Continuous q := by
    dsimp [q]
    exact continuous_norm.comp TK.continuous
  have hp := ContDiffMapSupportedIn.withSeminorms ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K
  rcases Seminorm.bound_of_continuous hp q hq_cont with ⟨s, C, _, h_le⟩
  refine ⟨s, C, ?_⟩
  intro f
  have h_eval := h_le f
  dsimp [q] at h_eval
  exact h_eval

lemma distribution_iteratedFDeriv_bound
    (T : 𝓓'(Ω_n, ℂ)) (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω_n) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (f : 𝓓_{K}(Fin n → ℝ, ℝ)) (B : ℝ) (_ : 0 ≤ B),
      (∀ i ∈ s, ∀ x ∈ K, ‖iteratedFDeriv ℝ i (⇑f) x‖ ≤ B) →
      ‖T (TestFunction.ofSupportedIn hK f)‖ ≤ (C : ℝ) * B := by
  rcases distribution_compact_bound Ω_n T K hK with ⟨s, C, h_bound⟩
  refine ⟨s, C, ?_⟩
  intro f B hB h_deriv_bound
  have h_sup : (s.sup (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K)) f ≤ B := by
    rw [Seminorm.finset_sup_apply]
    have h_le_nn : (s.sup fun i => ⟨(ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K i) f,
        apply_nonneg (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K i) f⟩) ≤
          (⟨B, hB⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      have h_real : (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K i) f ≤ B := by
        rw [ContDiffMapSupportedIn.seminorm_le_iff (𝕜 := ℝ) hB i f]
        intro _ x hx
        exact h_deriv_bound i hi x hx
      exact h_real
    exact h_le_nn
  have h_mul := mul_le_mul_of_nonneg_left h_sup (NNReal.coe_nonneg C)
  exact (h_bound f).trans h_mul

def applySmoothSupportedIn (T : 𝓓'(Ω_n, ℂ)) (_ : HasCompactSupport Ω_n T)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens (Fin n → ℝ)) (_ : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (_ : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    𝓓_{K}(Fin n → ℝ, ℝ) where
  toFun := fun x => χ.toFun x * ψ x
  contDiff' := ContDiff.mul χ.contDiff' hψ
  zero_on_compl' := by
    intro x hx
    have h_not_tsupp : x ∉ tsupport χ := hx
    have h_zero : χ.toFun x = 0 := by
      by_contra h_ne
      exact h_not_tsupp (subset_tsupport χ h_ne)
    dsimp only
    rw [h_zero, zero_mul]
    rfl

lemma ofSupportedIn_applySmoothSupportedIn (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    TestFunction.ofSupportedIn (K := K) χ.tsupport_subset'
      (applySmoothSupportedIn Ω_n T hT ψ hψ V hV χ hχ_one) =
      applySmoothFun Ω_n T hT ψ hψ V hV χ hχ_one := by
  ext x
  rfl

lemma applySmooth_bound
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
      (B : ℝ) (_ : 0 ≤ B),
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * ψ y) x‖ ≤ B) →
      ‖applySmooth Ω_n T hT ψ hψ V hV χ hχ_one‖ ≤ (C : ℝ) * B := by
  let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
  rcases distribution_iteratedFDeriv_bound Ω_n T K χ.tsupport_subset' with ⟨s, C, h_bound⟩
  refine ⟨s, C, ?_⟩
  intro ψ hψ B hB h_deriv
  dsimp [applySmooth]
  rw [← ofSupportedIn_applySmoothSupportedIn Ω_n T hT ψ hψ V hV χ hχ_one]
  exact h_bound (applySmoothSupportedIn Ω_n T hT ψ hψ V hV χ hχ_one) B hB h_deriv

noncomputable def applySmoothComplex (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (ψ : (Fin n → ℝ) → ℂ) (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
    (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) : ℂ :=
  let ψ_re := fun x => (ψ x).re
  let ψ_im := fun x => (ψ x).im
  applySmooth Ω_n T hT ψ_re hψ_re V hV χ hχ_one +
    Complex.I * applySmooth Ω_n T hT ψ_im hψ_im V hV χ hχ_one

lemma applySmoothComplex_bound
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (ψ : (Fin n → ℝ) → ℂ)
      (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
      (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
      (B : ℝ) (_ : 0 ≤ B),
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (ψ y).re) x‖ ≤ B) →
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (ψ y).im) x‖ ≤ B) →
      ‖applySmoothComplex Ω_n T hT ψ hψ_re hψ_im V hV χ hχ_one‖ ≤ (2 * (C : ℝ)) * B := by
  rcases applySmooth_bound Ω_n T hT V hV χ hχ_one with ⟨s, C, h_bound⟩
  refine ⟨s, C, ?_⟩
  intro ψ hψ_re hψ_im B hB h_re h_im
  dsimp [applySmoothComplex]
  have h_norm := norm_add_le (applySmooth Ω_n T hT (fun x => (ψ x).re) hψ_re V hV χ hχ_one)
    (Complex.I * applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one)
  have h_I : ‖Complex.I * applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one‖ =
      ‖applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [h_I] at h_norm
  have h1 := h_bound (fun x => (ψ x).re) hψ_re B hB h_re
  have h2 := h_bound (fun x => (ψ x).im) hψ_im B hB h_im
  linarith

lemma applySmoothComplex_add (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (f g : (Fin n → ℝ) → ℂ)
    (hf_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).re))
    (hf_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).im))
    (hg_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).re))
    (hg_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).im)) :
    applySmoothComplex Ω_n T hT (fun x => f x + g x) (hf_re.add hg_re) (hf_im.add hg_im)
      V hV χ hχ_one =
      applySmoothComplex Ω_n T hT f hf_re hf_im V hV χ hχ_one +
      applySmoothComplex Ω_n T hT g hg_re hg_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  rw [applySmooth_add Ω_n T hT (fun x => (f x).re) (fun x => (g x).re) hf_re hg_re V hV χ hχ_one]
  rw [applySmooth_add Ω_n T hT (fun x => (f x).im) (fun x => (g x).im) hf_im hg_im V hV χ hχ_one]
  ring

lemma applySmoothComplex_sub (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (f g : (Fin n → ℝ) → ℂ)
    (hf_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).re))
    (hf_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).im))
    (hg_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).re))
    (hg_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).im)) :
    applySmoothComplex Ω_n T hT (fun x => f x - g x) (hf_re.sub hg_re) (hf_im.sub hg_im)
      V hV χ hχ_one =
      applySmoothComplex Ω_n T hT f hf_re hf_im V hV χ hχ_one -
      applySmoothComplex Ω_n T hT g hg_re hg_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  rw [applySmooth_sub Ω_n T hT (fun x => (f x).re) (fun x => (g x).re) hf_re hg_re V hV χ hχ_one]
  rw [applySmooth_sub Ω_n T hT (fun x => (f x).im) (fun x => (g x).im) hf_im hg_im V hV χ hχ_one]
  ring

lemma applySmoothComplex_sub_sub
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (f₁ f₂ f₃ : (Fin n → ℝ) → ℂ)
    (hf₁_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₁ x).re))
    (hf₁_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₁ x).im))
    (hf₂_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₂ x).re))
    (hf₂_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₂ x).im))
    (hf₃_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₃ x).re))
    (hf₃_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₃ x).im)) :
    applySmoothComplex Ω_n T hT (fun x => f₁ x - f₂ x - f₃ x)
      (((hf₁_re.sub hf₂_re).sub hf₃_re)) (((hf₁_im.sub hf₂_im).sub hf₃_im)) V hV χ hχ_one =
      applySmoothComplex Ω_n T hT f₁ hf₁_re hf₁_im V hV χ hχ_one -
      applySmoothComplex Ω_n T hT f₂ hf₂_re hf₂_im V hV χ hχ_one -
      applySmoothComplex Ω_n T hT f₃ hf₃_re hf₃_im V hV χ hχ_one := by
  have h1 := applySmoothComplex_sub Ω_n T hT V hV χ hχ_one (fun x => f₁ x - f₂ x) f₃
    (hf₁_re.sub hf₂_re) (hf₁_im.sub hf₂_im) hf₃_re hf₃_im
  have h2 := applySmoothComplex_sub Ω_n T hT V hV χ hχ_one f₁ f₂ hf₁_re hf₁_im hf₂_re hf₂_im
  rw [h1, h2]

lemma applySmoothComplex_const_mul
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (c : ℂ) (ψ : (Fin n → ℝ) → ℂ)
    (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
    (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
    (hcψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (c * ψ x).re))
    (hcψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (c * ψ x).im)) :
    applySmoothComplex Ω_n T hT (fun x => c * ψ x) hcψ_re hcψ_im V hV χ hχ_one =
    c * applySmoothComplex Ω_n T hT ψ hψ_re hψ_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  have h_re_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => c.re * (ψ x).re - c.im * (ψ x).im) :=
    (contDiff_const.mul hψ_re).sub (contDiff_const.mul hψ_im)
  have h_im_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => c.re * (ψ x).im + c.im * (ψ x).re) :=
    (contDiff_const.mul hψ_im).add (contDiff_const.mul hψ_re)
  have h1 : applySmooth Ω_n T hT (fun x => (c * ψ x).re) hcψ_re V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => c.re * (ψ x).re - c.im * (ψ x).im)
        h_re_diff V hV χ hχ_one := by
    apply applySmooth_congr Ω_n T hT _ _ _ _ (fun x => by simp [Complex.mul_re])
  have h2 : applySmooth Ω_n T hT (fun x => (c * ψ x).im) hcψ_im V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => c.re * (ψ x).im + c.im * (ψ x).re)
        h_im_diff V hV χ hχ_one := by
    apply applySmooth_congr Ω_n T hT _ _ _ _ (fun x => by simp [Complex.mul_im])
  rw [h1, h2]
  rw [applySmooth_sub Ω_n T hT _ _ (contDiff_const.mul hψ_re) (contDiff_const.mul hψ_im)
    V hV χ hχ_one]
  rw [applySmooth_add Ω_n T hT _ _ (contDiff_const.mul hψ_im) (contDiff_const.mul hψ_re)
    V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.re _ hψ_re V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.im _ hψ_im V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.re _ hψ_im V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.im _ hψ_re V hV χ hχ_one]
  simp only [Complex.real_smul]
  conv_rhs =>
    rw [show c = (c.re : ℂ) + (c.im : ℂ) * Complex.I from (Complex.re_add_im c).symm]
  have h_I_sq := Complex.I_sq
  linear_combination
    -((c.im : ℂ) * applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one) * h_I_sq

lemma applySmoothComplex_zero
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT (fun _ => 0) contDiff_const contDiff_const V hV χ hχ_one = 0 := by
  dsimp [applySmoothComplex]
  have h := applySmooth_zero Ω_n T hT V hV χ hχ_one
  rw [h]
  simp

open Finset

lemma applySmoothComplex_sum {ι : Type*} (s : Finset ι)
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (f : ι → (Fin n → ℝ) → ℂ)
    (hf_re : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f i x).re))
    (hf_im : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f i x).im))
    (hsum_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (∑ i ∈ s, f i x).re))
    (hsum_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (∑ i ∈ s, f i x).im))
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT (fun x => ∑ i ∈ s, f i x) hsum_re hsum_im V hV χ hχ_one =
      ∑ i ∈ s, applySmoothComplex Ω_n T hT (f i) (hf_re i) (hf_im i) V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  have h_re_eq : (fun x => (∑ i ∈ s, f i x).re) = fun x => ∑ i ∈ s, (f i x).re := by
    ext x
    simp only [Complex.re_sum]
  have h_im_eq : (fun x => (∑ i ∈ s, f i x).im) = fun x => ∑ i ∈ s, (f i x).im := by
    ext x
    simp only [Complex.im_sum]
  have h_re_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i ∈ s, (f i x).re) := by
    apply ContDiff.sum
    intro i _
    exact hf_re i
  have h_im_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i ∈ s, (f i x).im) := by
    apply ContDiff.sum
    intro i _
    exact hf_im i
  have h1 : applySmooth Ω_n T hT (fun x => (∑ i ∈ s, f i x).re) hsum_re V hV χ hχ_one =
      ∑ i ∈ s, applySmooth Ω_n T hT (fun x => (f i x).re) (hf_re i) V hV χ hχ_one := by
    rw [applySmooth_congr Ω_n T hT _ _ hsum_re h_re_diff (congrFun h_re_eq) V hV χ hχ_one]
    exact applySmooth_sum Ω_n s T hT (fun i x => (f i x).re) hf_re h_re_diff V hV χ hχ_one
  have h2 : applySmooth Ω_n T hT (fun x => (∑ i ∈ s, f i x).im) hsum_im V hV χ hχ_one =
      ∑ i ∈ s, applySmooth Ω_n T hT (fun x => (f i x).im) (hf_im i) V hV χ hχ_one := by
    rw [applySmooth_congr Ω_n T hT _ _ hsum_im h_im_diff (congrFun h_im_eq) V hV χ hχ_one]
    exact applySmooth_sum Ω_n s T hT (fun i x => (f i x).im) hf_im h_im_diff V hV χ hχ_one
  rw [h1, h2]
  rw [mul_sum, ← sum_add_distrib]

lemma applySmoothComplex_congr (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (f g : (Fin n → ℝ) → ℂ)
    (hf_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).re))
    (hf_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).im))
    (hg_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).re))
    (hg_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).im))
    (h_eq : ∀ x, f x = g x)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT f hf_re hf_im V hV χ hχ_one =
      applySmoothComplex Ω_n T hT g hg_re hg_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  have h_re : applySmooth Ω_n T hT (fun x => (f x).re) hf_re V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => (g x).re) hg_re V hV χ hχ_one :=
    applySmooth_congr Ω_n T hT _ _ hf_re hg_re (fun x => by rw [h_eq x]) V hV χ hχ_one
  have h_im : applySmooth Ω_n T hT (fun x => (f x).im) hf_im V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => (g x).im) hg_im V hV χ hχ_one :=
    applySmooth_congr Ω_n T hT _ _ hf_im hg_im (fun x => by rw [h_eq x]) V hV χ hχ_one
  rw [h_re, h_im]

lemma x_i_smooth (i : Fin n) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => (x i : ℂ)) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => x i) :=
    contDiff_pi.mp contDiff_id i
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (y : ℝ) => (y : ℂ)) :=
    ContinuousLinearMap.contDiff Complex.ofRealCLM
  exact h2.comp h1

lemma exp_izx_smooth (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))) := by
  apply ContDiff.cexp
  apply ContDiff.mul
  · exact contDiff_const
  · apply ContDiff.sum
    intro i _
    apply ContDiff.mul
    · exact contDiff_const
    · exact x_i_smooth i

lemma exp_izx_re_smooth (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).re) := by
  exact Complex.reCLM.contDiff.comp (exp_izx_smooth z)

lemma exp_izx_im_smooth (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).im) := by
  exact Complex.imCLM.contDiff.comp (exp_izx_smooth z)

lemma x_mul_exp_izx_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => (x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))) :=
  (x_i_smooth k).mul (exp_izx_smooth z)

lemma x_mul_exp_izx_re_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).re) :=
  Complex.reCLM.contDiff.comp (x_mul_exp_izx_smooth z k)

lemma x_mul_exp_izx_im_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).im) :=
  Complex.imCLM.contDiff.comp (x_mul_exp_izx_smooth z k)

noncomputable def FourierLaplaceDeriv (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (k : Fin n) (z : Fin n → ℂ) : ℂ :=
  let x_e_izx := fun (x : Fin n → ℝ) =>
    (x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))
  (-Complex.I) * applySmoothComplex Ω_n T hT x_e_izx (x_mul_exp_izx_re_smooth z k)
    (x_mul_exp_izx_im_smooth z k) V hV χ hχ_one

noncomputable def FourierLaplaceTotalDeriv (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ k, (ContinuousLinearMap.proj k).smulRight (FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z)

lemma FourierLaplaceTotalDeriv_apply (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ)
    (h : Fin n → ℂ) :
    FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z h =
      ∑ k, h k * FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z := by
  dsimp [FourierLaplaceTotalDeriv]
  simp only [_root_.sum_apply, smulRight_apply, proj_apply, smul_eq_mul]

noncomputable def FourierLaplaceTransform (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) : ℂ :=
  let e_izx := fun (x : Fin n → ℝ) => Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))
  applySmoothComplex Ω_n T hT e_izx (exp_izx_re_smooth z) (exp_izx_im_smooth z) V hV χ hχ_one

lemma fourier_diff_zero (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (hn : n = 0) :
    Differentiable ℂ (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) := by
  intro z
  have h_subsingleton : Subsingleton (Fin n → ℂ) := by
    subst hn
    infer_instance
  have h_const : ∀ w : Fin n → ℂ, w = z := fun w => Subsingleton.elim w z
  have h_eq : (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) =
      fun _ => FourierLaplaceTransform Ω_n T hT V hV χ hχ_one z := by
    ext w
    rw [h_const w]
  rw [h_eq]
  exact differentiableAt_const _

lemma applySmooth_empty_support (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (h_supp : Distribution.support Ω_n T = ∅)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmooth Ω_n T hT ψ hψ V hV χ hχ_one = 0 := by
  dsimp [applySmooth]
  apply vanishing_on_disjoint_support
  intro x hx
  simp only [h_supp, sdiff_empty]
  exact (applySmoothFun Ω_n T hT ψ hψ V hV χ hχ_one).tsupport_subset' hx

lemma applySmoothComplex_empty_support (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (h_supp : Distribution.support Ω_n T = ∅)
    (ψ : (Fin n → ℝ) → ℂ)
    (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
    (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT ψ hψ_re hψ_im V hV χ hχ_one = 0 := by
  dsimp [applySmoothComplex]
  rw [applySmooth_empty_support Ω_n T hT h_supp _ hψ_re V hV χ hχ_one]
  rw [applySmooth_empty_support Ω_n T hT h_supp _ hψ_im V hV χ hχ_one]
  simp

lemma fourier_laplace_empty_support (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (h_supp : Distribution.support Ω_n T = ∅)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) :
    HasFDerivAt (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one)
      (FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z) z := by
  have h_flt : (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) = fun _ => 0 := by
    ext w
    dsimp [FourierLaplaceTransform]
    exact applySmoothComplex_empty_support Ω_n T hT h_supp _ _ _ V hV χ hχ_one
  have h_deriv : FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z = 0 := by
    ext h
    rw [FourierLaplaceTotalDeriv_apply]
    have h_k : ∀ k, FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z = 0 := by
      intro k
      dsimp [FourierLaplaceDeriv]
      rw [applySmoothComplex_empty_support Ω_n T hT h_supp _ _ _ V hV χ hχ_one]
      ring
    simp [h_k]
  rw [h_flt, h_deriv]
  exact hasFDerivAt_const (𝕜 := ℂ) 0 z

noncomputable def expTaylorRem (z h : Fin n → ℂ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp (-Complex.I * (∑ i, (z i + h i) * (x i : ℂ))) -
  Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) -
  (∑ k, h k * ((-Complex.I * (x k : ℂ)) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))))

lemma expTaylorRem_zero (z : Fin n → ℂ) (x : Fin n → ℝ) :
    expTaylorRem z 0 x = 0 := by
  dsimp [expTaylorRem]
  simp

lemma expTaylorRem_factor (z h : Fin n → ℂ) (x : Fin n → ℝ) :
    expTaylorRem z h x =
      Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) *
        (Complex.exp (-Complex.I * (∑ i, h i * (x i : ℂ))) - 1 -
          (-Complex.I * (∑ i, h i * (x i : ℂ)))) := by
  dsimp [expTaylorRem]
  have h_add : (-Complex.I * (∑ i, (z i + h i) * (x i : ℂ))) =
      (-Complex.I * (∑ i, z i * (x i : ℂ))) + (-Complex.I * (∑ i, h i * (x i : ℂ))) := by
    simp_rw [add_mul, Finset.sum_add_distrib, mul_add]
  rw [h_add, Complex.exp_add]
  have h_sum :
      (∑ k, h k * ((-Complex.I * (x k : ℂ)) *
        Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))) =
      Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) *
        (-Complex.I * (∑ i, h i * (x i : ℂ))) := by
    calc ∑ k, h k * ((-Complex.I * (x k : ℂ)) *
          Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))
      _ = ∑ k, (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) * -Complex.I) *
            (h k * (x k : ℂ)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) * -Complex.I) *
            (∑ k, h k * (x k : ℂ)) := by
        rw [← Finset.mul_sum]
      _ = Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) *
            (-Complex.I * (∑ i, h i * (x i : ℂ))) := by
        ring
  rw [h_sum]
  ring

lemma exp_two_rem (u : ℂ) :
    ‖Complex.exp u - 1 - u‖ ≤ ‖u‖^2 * Real.exp ‖u‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp u 2
  have h_sum : (∑ m ∈ Finset.range 2, u ^ m / (m.factorial : ℂ)) = 1 + u := by
    simp [Finset.sum_range_succ]
  rw [h_sum] at h
  have h_eq : Complex.exp u - (1 + u) = Complex.exp u - 1 - u := by ring
  rw [h_eq] at h
  exact h

lemma expTaylorRem_smooth (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => expTaylorRem z h x) := by
  dsimp [expTaylorRem]
  apply ContDiff.sub
  · apply ContDiff.sub
    · exact exp_izx_smooth (z + h)
    · exact exp_izx_smooth z
  · apply ContDiff.sum
    intro k _
    apply ContDiff.mul
    · exact contDiff_const
    · apply ContDiff.mul
      · apply ContDiff.mul
        · exact contDiff_const
        · exact x_i_smooth k
      · exact exp_izx_smooth z

lemma expTaylorRem_re_smooth (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => (expTaylorRem z h x).re) :=
  Complex.reCLM.contDiff.comp (expTaylorRem_smooth z h)

lemma expTaylorRem_im_smooth (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => (expTaylorRem z h x).im) :=
  Complex.imCLM.contDiff.comp (expTaylorRem_smooth z h)

lemma norm_re_iteratedFDeriv_le (i : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ i (fun y => (f y).re) x‖ ≤ ‖iteratedFDeriv ℝ i f x‖ := by
  have h_comp : (fun y => (f y).re) = Complex.reCLM ∘ f := rfl
  rw [h_comp]
  have h_diff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) f x := hf.contDiffAt
  have h_le : (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.reCLM h_diff h_le]
  have h_le :=
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le Complex.reCLM
      (iteratedFDeriv ℝ i f x)
  have h_norm : ‖Complex.reCLM‖ = 1 := Complex.reCLM_norm
  calc ‖Complex.reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖
    _ ≤ ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ i f x‖ := h_le
    _ = 1 * ‖iteratedFDeriv ℝ i f x‖ := by rw [h_norm]
    _ = ‖iteratedFDeriv ℝ i f x‖ := one_mul _

lemma norm_im_iteratedFDeriv_le (i : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ i (fun y => (f y).im) x‖ ≤ ‖iteratedFDeriv ℝ i f x‖ := by
  have h_comp : (fun y => (f y).im) = Complex.imCLM ∘ f := rfl
  rw [h_comp]
  have h_diff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) f x := hf.contDiffAt
  have h_le : (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.imCLM h_diff h_le]
  have h_le :=
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le Complex.imCLM
      (iteratedFDeriv ℝ i f x)
  have h_norm : ‖Complex.imCLM‖ = 1 := Complex.imCLM_norm
  calc ‖Complex.imCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖
    _ ≤ ‖Complex.imCLM‖ * ‖iteratedFDeriv ℝ i f x‖ := h_le
    _ = 1 * ‖iteratedFDeriv ℝ i f x‖ := by rw [h_norm]
    _ = ‖iteratedFDeriv ℝ i f x‖ := one_mul _

lemma chi_mul_rem_smooth (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ)) := by
    have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ.toFun := χ.contDiff' (n := ⊤)
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp hχ
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (expTaylorRem z h) :=
    expTaylorRem_smooth z h
  exact h1.mul h2

noncomputable def deriv_k_term (z : Fin n → ℂ) (k : Fin n) (x : Fin n → ℝ) : ℂ :=
  (-Complex.I * (x k : ℂ)) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))

lemma deriv_k_term_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => deriv_k_term z k x) := by
  dsimp [deriv_k_term]
  apply ContDiff.mul
  · apply ContDiff.mul
    · exact contDiff_const
    · exact x_i_smooth k
  · exact exp_izx_smooth z

lemma deriv_k_term_re_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (deriv_k_term z k x).re) :=
  Complex.reCLM.contDiff.comp (deriv_k_term_smooth z k)

lemma deriv_k_term_im_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (deriv_k_term z k x).im) :=
  Complex.imCLM.contDiff.comp (deriv_k_term_smooth z k)

lemma fourier_laplace_deriv_eq
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z : Fin n → ℂ) (k : Fin n) :
    FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z =
    applySmoothComplex Ω_n T hT (deriv_k_term z k)
      (deriv_k_term_re_smooth z k) (deriv_k_term_im_smooth z k) V hV χ hχ_one := by
  dsimp [FourierLaplaceDeriv]
  have h_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) =>
      (-Complex.I * ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (x_mul_exp_izx_smooth z k))
  have h_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) =>
      (-Complex.I * ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))).im) :=
    Complex.imCLM.contDiff.comp (contDiff_const.mul (x_mul_exp_izx_smooth z k))
  have h_const := applySmoothComplex_const_mul Ω_n T hT V hV χ hχ_one (-Complex.I)
    (fun (x : Fin n → ℝ) => (x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))
    (x_mul_exp_izx_re_smooth z k) (x_mul_exp_izx_im_smooth z k)
    h_re h_im
  rw [← h_const]
  apply applySmoothComplex_congr Ω_n T hT _ _ h_re h_im
    (deriv_k_term_re_smooth z k) (deriv_k_term_im_smooth z k) (fun x => by
    dsimp [deriv_k_term]
    ring)

lemma fourier_laplace_deriv_term
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z : Fin n → ℂ) (k : Fin n) (c : ℂ) :
    c * FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z =
    applySmoothComplex Ω_n T hT (fun x => c * deriv_k_term z k x)
      (Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
      (Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
      V hV χ hχ_one := by
  rw [fourier_laplace_deriv_eq]
  have h_const := applySmoothComplex_const_mul Ω_n T hT V hV χ hχ_one c
    (deriv_k_term z k) (deriv_k_term_re_smooth z k) (deriv_k_term_im_smooth z k)
    (Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
    (Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
  rw [h_const]

lemma fourier_laplace_total_deriv_eq
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z h : Fin n → ℂ) :
    FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z h =
    applySmoothComplex Ω_n T hT
      (fun x => ∑ k, h k * deriv_k_term z k x)
      (Complex.reCLM.contDiff.comp
        (ContDiff.sum (fun k _ => contDiff_const.mul (deriv_k_term_smooth z k))))
      (Complex.imCLM.contDiff.comp
        (ContDiff.sum (fun k _ => contDiff_const.mul (deriv_k_term_smooth z k))))
      V hV χ hχ_one := by
  rw [FourierLaplaceTotalDeriv_apply]
  have h_term : (fun k => h k * FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z) =
      fun k => applySmoothComplex Ω_n T hT (fun x => h k * deriv_k_term z k x)
        (Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
        (Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
        V hV χ hχ_one := by
    ext k
    exact fourier_laplace_deriv_term Ω_n T hT V hV χ hχ_one z k (h k)
  rw [h_term]
  exact (applySmoothComplex_sum Ω_n Finset.univ T hT
    (fun k x => h k * deriv_k_term z k x)
    (fun k => Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
    (fun k => Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
    _ _ V hV χ hχ_one).symm

lemma fourier_laplace_diff_rem
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z h : Fin n → ℂ) :
    FourierLaplaceTransform Ω_n T hT V hV χ hχ_one (z + h) -
    FourierLaplaceTransform Ω_n T hT V hV χ hχ_one z -
    FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z h =
    applySmoothComplex Ω_n T hT (expTaylorRem z h)
      (expTaylorRem_re_smooth z h) (expTaylorRem_im_smooth z h) V hV χ hχ_one := by
  dsimp [FourierLaplaceTransform]
  rw [fourier_laplace_total_deriv_eq]
  rw [← applySmoothComplex_sub_sub]
  apply applySmoothComplex_congr Ω_n T hT _ _ _ _ _ _ (fun x => by
    rfl)

lemma bound_mul_le (C : ℝ≥0) (c : ℝ) (hc : 0 ≤ c) (h : Fin n → ℂ) (B : ℝ)
    (hB : B ≤ (c / (2 * (C : ℝ) + 1)) * ‖h‖) :
    (2 * (C : ℝ)) * B ≤ c * ‖h‖ := by
  have h_pos : 0 < 2 * (C : ℝ) + 1 := by positivity
  have h_nonneg : 0 ≤ 2 * (C : ℝ) := by positivity
  have h_norm : 0 ≤ ‖h‖ := norm_nonneg h
  have h_frac : (2 * (C : ℝ)) * (c / (2 * (C : ℝ) + 1)) ≤ c := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ h_pos]
    nlinarith
  calc (2 * (C : ℝ)) * B
    _ ≤ (2 * (C : ℝ)) * ((c / (2 * (C : ℝ) + 1)) * ‖h‖) :=
      mul_le_mul_of_nonneg_left hB h_nonneg
    _ = ((2 * (C : ℝ)) * (c / (2 * (C : ℝ) + 1))) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ :=
      mul_le_mul_of_nonneg_right h_frac h_norm

lemma expTaylorRem_bound_exists_of_single
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ)
    (h_single : ∀ (i : ℕ) (c : ℝ), 0 < c → ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (⟨tsupport χ, χ.hasCompactSupport'⟩ : Compacts (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) x‖ ≤ c * ‖h‖)
    (s : Finset ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).re) x‖ ≤ c * ‖h‖) ∧
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).im) x‖ ≤ c * ‖h‖) := by
  intro K c hc
  rw [Filter.eventually_and]
  constructor
  · rw [Filter.eventually_all_finset]
    intro i _hi
    have h_ev := h_single i c hc
    filter_upwards [h_ev] with h hh x hx
    have h_re := norm_re_iteratedFDeriv_le i
      (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y)
      (chi_mul_rem_smooth Ω_n χ z h) x
    have h_eval : (fun y => ((χ.toFun y : ℂ) * expTaylorRem z h y).re) =
        fun y => χ.toFun y * (expTaylorRem z h y).re := by
      ext y
      simp [Complex.mul_re]
    rw [h_eval] at h_re
    exact h_re.trans (hh x hx)
  · rw [Filter.eventually_all_finset]
    intro i _hi
    have h_ev := h_single i c hc
    filter_upwards [h_ev] with h hh x hx
    have h_im := norm_im_iteratedFDeriv_le i
      (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y)
      (chi_mul_rem_smooth Ω_n χ z h) x
    have h_eval : (fun y => ((χ.toFun y : ℂ) * expTaylorRem z h y).im) =
        fun y => χ.toFun y * (expTaylorRem z h y).im := by
      ext y
      simp [Complex.mul_im]
    rw [h_eval] at h_im
    exact h_im.trans (hh x hx)

lemma norm_expTaylorRem_le (z h : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖expTaylorRem z h x‖ ≤
      ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ *
        (‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ^ 2 *
          Real.exp ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖) := by
  rw [expTaylorRem_factor]
  rw [norm_mul]
  gcongr
  exact exp_two_rem _

lemma norm_sum_h_x_le (h : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ ∑ i, ‖h i‖ * |x i| := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

lemma norm_sum_h_x_le_pi (h : Fin n → ℂ) (x : Fin n → ℝ) :
    (∑ i, ‖h i‖ * |x i|) ≤ (n : ℝ) * ‖h‖ * ‖x‖ := by
  have h1 : ∀ i, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have h2 : ∀ i, |x i| ≤ ‖x‖ := fun i => norm_le_pi_norm x i
  have h3 : ∀ i, ‖h i‖ * |x i| ≤ ‖h‖ * ‖x‖ := by
    intro i
    exact mul_le_mul (h1 i) (h2 i) (abs_nonneg _) (norm_nonneg _)
  calc ∑ i, ‖h i‖ * |x i|
    _ ≤ ∑ i : Fin n, ‖h‖ * ‖x‖ := Finset.sum_le_sum (fun i _ => h3 i)
    _ = (n : ℝ) * (‖h‖ * ‖x‖) := by simp
    _ = (n : ℝ) * ‖h‖ * ‖x‖ := by ring

lemma norm_exp_izx_le (z : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ ≤
      Real.exp ((n : ℝ) * ‖z‖ * ‖x‖) := by
  rw [Complex.norm_exp]
  have h_re : (-Complex.I * (∑ i, z i * (x i : ℂ))).re = ∑ i, (z i).im * x i := by
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul]
    have h_im : (∑ i, z i * (x i : ℂ)).im = ∑ i, ((z i * (x i : ℂ)).im) :=
      map_sum Complex.imCLM _ _
    rw [zero_sub, neg_neg, h_im]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [h_re]
  apply Real.exp_le_exp_of_le
  calc ∑ i, (z i).im * x i
    _ ≤ ∑ i, |(z i).im * x i| := Finset.sum_le_sum (fun i _ => le_abs_self _)
    _ = ∑ i, |(z i).im| * |x i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, ‖z i‖ * |x i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm (z i)) (abs_nonneg _)
    _ ≤ (n : ℝ) * ‖z‖ * ‖x‖ := by
      have h1 : ∀ i, ‖z i‖ ≤ ‖z‖ := fun i => norm_le_pi_norm z i
      have h2 : ∀ i, |x i| ≤ ‖x‖ := fun i => norm_le_pi_norm x i
      have h3 : ∀ i, ‖z i‖ * |x i| ≤ ‖z‖ * ‖x‖ := by
        intro i
        exact mul_le_mul (h1 i) (h2 i) (abs_nonneg _) (norm_nonneg _)
      calc ∑ i, ‖z i‖ * |x i|
        _ ≤ ∑ i : Fin n, ‖z‖ * ‖x‖ := Finset.sum_le_sum (fun i _ => h3 i)
        _ = (n : ℝ) * (‖z‖ * ‖x‖) := by simp
        _ = (n : ℝ) * ‖z‖ * ‖x‖ := by ring

lemma exists_norm_le_of_compact (K : Compacts (Fin n → ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖x‖ ≤ M := by
  rcases K.isCompact'.isBounded.subset_ball 0 with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x hx
  have h := hM hx
  rw [Metric.mem_ball, dist_zero_right] at h
  exact h.le.trans (le_max_right 0 M)

lemma exists_norm_iteratedFDeriv_bound (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (j : ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun y => (χ.toFun y : ℂ)) x‖ ≤ M := by
  intro K
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ)) := by
    have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) χ.toFun := χ.contDiff' (n := ⊤)
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp h1
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_cont : Continuous (fun x => ‖iteratedFDeriv ℝ j (fun y => (χ.toFun y : ℂ)) x‖) :=
    (hχ.continuous_iteratedFDeriv hj).norm
  rcases K.isCompact'.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x hx
  have h := hM (mem_image_of_mem _ hx)
  exact h.trans (le_max_right 0 M)

lemma expTaylorRem_zero_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖(χ.toFun x : ℂ) * expTaylorRem z h x‖ ≤ c * ‖h‖ := by
  intro K c hc
  rcases exists_norm_le_of_compact K with ⟨MK, hMK, hxMK⟩
  rcases exists_norm_iteratedFDeriv_bound Ω_n χ 0 with ⟨Mχ, hMχ, hxMχ⟩
  simp only [norm_iteratedFDeriv_zero] at hxMχ
  let Ez := Real.exp ((n : ℝ) * ‖z‖ * MK)
  have hEz_pos : 0 < Ez := Real.exp_pos _
  let Eh1 := Real.exp ((n : ℝ) * 1 * MK)
  let C := Mχ * Ez * ((n : ℝ) * MK)^2 * Eh1
  have hC_nonneg : 0 ≤ C := by positivity
  let δ := min (1 : ℝ) (c / (C + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hc (by linarith))
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, ?_⟩
  intro h hh x hx
  rw [dist_zero_right] at hh
  have hh1 : ‖h‖ ≤ 1 := (le_of_lt hh).trans (min_le_left 1 _)
  have hhC : ‖h‖ ≤ c / (C + 1) := (le_of_lt hh).trans (min_le_right 1 _)
  have hx_le : ‖x‖ ≤ MK := hxMK x hx
  have h_exp_z : ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ ≤ Ez := by
    have h1 := norm_exp_izx_le z x
    have h2 : (n : ℝ) * ‖z‖ * ‖x‖ ≤ (n : ℝ) * ‖z‖ * MK := by
      gcongr
    exact h1.trans (Real.exp_le_exp_of_le h2)
  have hu_le : ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ (n : ℝ) * ‖h‖ * MK := by
    have h1 := norm_sum_h_x_le h x
    have h2 := norm_sum_h_x_le_pi h x
    have h3 : (n : ℝ) * ‖h‖ * ‖x‖ ≤ (n : ℝ) * ‖h‖ * MK := by
      gcongr
    exact (h1.trans h2).trans h3
  have hu_le1 : ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ (n : ℝ) * 1 * MK := by
    calc ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖
      _ ≤ (n : ℝ) * ‖h‖ * MK := hu_le
      _ ≤ (n : ℝ) * 1 * MK := by gcongr
  have h_exp_u : Real.exp ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ Eh1 :=
    Real.exp_le_exp_of_le hu_le1
  have h_rem := norm_expTaylorRem_le z h x
  have h_u2 : ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ^ 2 ≤ ((n : ℝ) * MK)^2 * ‖h‖^2 := by
    have h_nonneg : 0 ≤ ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ := norm_nonneg _
    have h_ring : ((n : ℝ) * ‖h‖ * MK)^2 = ((n : ℝ) * MK)^2 * ‖h‖^2 := by ring
    rw [← h_ring]
    nlinarith
  have h_rem_bound : ‖expTaylorRem z h x‖ ≤ Ez * (((n : ℝ) * MK)^2 * Eh1) * ‖h‖^2 := by
    calc ‖expTaylorRem z h x‖
      _ ≤ ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ *
            (‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ^ 2 *
              Real.exp ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖) := h_rem
      _ ≤ Ez * (((n : ℝ) * MK)^2 * ‖h‖^2 * Eh1) := by
        apply mul_le_mul h_exp_z _ (by positivity) (by positivity)
        apply mul_le_mul h_u2 h_exp_u (by positivity) (by positivity)
      _ = Ez * (((n : ℝ) * MK)^2 * Eh1) * ‖h‖^2 := by ring
  calc ‖(χ.toFun x : ℂ) * expTaylorRem z h x‖
    _ = ‖(χ.toFun x : ℂ)‖ * ‖expTaylorRem z h x‖ := norm_mul _ _
    _ ≤ Mχ * (Ez * (((n : ℝ) * MK)^2 * Eh1) * ‖h‖^2) :=
      mul_le_mul (hxMχ x hx) h_rem_bound (norm_nonneg _) hMχ
    _ = C * ‖h‖^2 := by
      dsimp [C]
      ring
    _ = (C * ‖h‖) * ‖h‖ := by ring
    _ ≤ (C * (c / (C + 1))) * ‖h‖ := by
      gcongr
    _ ≤ c * ‖h‖ := by
      have h_frac : C * (c / (C + 1)) ≤ c := by
        rw [mul_div_assoc']
        have h_pos : 0 < C + 1 := by positivity
        rw [div_le_iff₀ h_pos]
        nlinarith
      exact mul_le_mul_of_nonneg_right h_frac (norm_nonneg _)

lemma expTaylorRem_single_zero_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ 0 (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) x‖ ≤ c * ‖h‖ := by
  intro K c hc
  have h := expTaylorRem_zero_bound_exists Ω_n χ z c hc
  filter_upwards [h] with w hw x hx
  rw [norm_iteratedFDeriv_zero]
  exact hw x hx

noncomputable def g_rem (w : ℂ) : ℂ := Complex.exp w - 1 - w

lemma g_rem_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g_rem := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun w => Complex.exp w - 1 - w)
  exact ContDiff.sub (ContDiff.sub contDiff_id.cexp contDiff_const) contDiff_id

noncomputable def L_h (h : Fin n → ℂ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  -Complex.I • (∑ i, (h i) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)))

lemma L_h_apply (h : Fin n → ℂ) (x : Fin n → ℝ) :
    L_h h x = -Complex.I * (∑ i, h i * (x i : ℂ)) := by
  dsimp [L_h]
  simp only [smul_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]

lemma opNorm_L_h_le (h : Fin n → ℂ) :
    ‖L_h h‖ ≤ (n : ℝ) * ‖h‖ := by
  have h_nonneg : 0 ≤ (n : ℝ) * ‖h‖ := by positivity
  refine opNorm_le_bound _ h_nonneg ?_
  intro x
  rw [L_h_apply]
  have h1 := norm_sum_h_x_le h x
  have h2 := norm_sum_h_x_le_pi h x
  exact h1.trans h2

lemma norm_L_h_apply_le (h : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖L_h h x‖ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := by
  rw [L_h_apply]
  have h1 := norm_sum_h_x_le h x
  have h2 := norm_sum_h_x_le_pi h x
  exact h1.trans h2

lemma norm_iteratedFDeriv_comp_L_h_le (h : Fin n → ℂ) (k : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k (g_rem ∘ L_h h) x‖ ≤
      ‖iteratedFDeriv ℝ k g_rem (L_h h x)‖ * ‖L_h h‖ ^ k := by
  have hk : (k : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (L_h h) g_rem_smooth x hk]
  have h_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g_rem (L_h h x)) (fun _ => L_h h)
  refine h_le.trans ?_
  have h_prod : (∏ _i : Fin k, ‖L_h h‖) = ‖L_h h‖ ^ k := by
    simp
  rw [h_prod]

lemma hasFDerivAt_g_rem_zero : HasFDerivAt g_rem (0 : ℂ →L[ℝ] ℂ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  let δ := min (1 : ℝ) (c / (Real.exp 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨δ, hδ_pos, ?_⟩
  intro w hw
  rw [dist_zero_right] at hw
  have hw1 : ‖w‖ ≤ 1 := (le_of_lt hw).trans (min_le_left 1 _)
  have hwc : ‖w‖ ≤ c / (Real.exp 1) := (le_of_lt hw).trans (min_le_right 1 _)
  dsimp [g_rem]
  simp only [zero_add, Complex.exp_zero, sub_self, sub_zero, zero_apply]
  have h_rem := exp_two_rem w
  have h_exp : Real.exp ‖w‖ ≤ Real.exp 1 := Real.exp_le_exp_of_le hw1
  calc ‖Complex.exp w - 1 - w‖
    _ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := h_rem
    _ ≤ (‖w‖ * (c / Real.exp 1)) * Real.exp 1 := by
      have h_w2 : ‖w‖ ^ 2 ≤ ‖w‖ * (c / Real.exp 1) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hwc (norm_nonneg _)
      exact mul_le_mul h_w2 h_exp (Real.exp_pos _).le (by positivity)
    _ = ‖w‖ * ((c / Real.exp 1) * Real.exp 1) := by ring
    _ = ‖w‖ * c := by
      have h_ne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
      rw [div_mul_cancel₀ _ h_ne]
    _ = c * ‖w‖ := mul_comm _ _

lemma fderiv_g_rem_zero : fderiv ℝ g_rem 0 = 0 :=
  hasFDerivAt_g_rem_zero.fderiv

lemma norm_iteratedFDeriv_one_g_rem_le (R : ℝ) (hR : 0 ≤ R) (C2 : ℝ)
    (hC2 : ∀ w : ℂ, ‖w‖ ≤ R → ‖iteratedFDeriv ℝ 2 g_rem w‖ ≤ C2) :
    ∀ w : ℂ, ‖w‖ ≤ R → ‖iteratedFDeriv ℝ 1 g_rem w‖ ≤ C2 * ‖w‖ := by
  intro w hw
  have hle : (1 : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_contdiff : ContDiff ℝ 1 (fderiv ℝ g_rem) :=
    ContDiff.fderiv_right (m := 1) g_rem_smooth hle
  have h_diff : ∀ y ∈ Metric.closedBall (0 : ℂ) R,
      DifferentiableAt ℝ (fderiv ℝ g_rem) y := by
    intro y _
    exact (h_contdiff.differentiable one_ne_zero).differentiableAt
  have h_bound : ∀ y ∈ Metric.closedBall (0 : ℂ) R,
      ‖fderiv ℝ (fderiv ℝ g_rem) y‖ ≤ C2 := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have h1 : ‖fderiv ℝ (fderiv ℝ g_rem) y‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g_rem) y‖ := by
      rw [norm_iteratedFDeriv_one]
    have h2 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ g_rem) y‖ = ‖iteratedFDeriv ℝ 2 g_rem y‖ := by
      exact norm_iteratedFDeriv_fderiv (n := 1)
    rw [h1, h2]
    exact hC2 y hy
  have h_conv : Convex ℝ (Metric.closedBall (0 : ℂ) R) := convex_closedBall 0 R
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw
  have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact hR
  have h_mvt := Convex.norm_image_sub_le_of_norm_fderiv_le h_diff h_bound h_conv h0_mem hw_mem
  rw [fderiv_g_rem_zero, sub_zero, sub_zero] at h_mvt
  rw [norm_iteratedFDeriv_one]
  exact h_mvt

lemma exists_norm_iteratedFDeriv_g_rem_bound (k : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖iteratedFDeriv ℝ k g_rem w‖ ≤ C := by
  by_cases hR : 0 ≤ R
  · have hk : (k : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have h_cont : Continuous (fun w => ‖iteratedFDeriv ℝ k g_rem w‖) :=
      (g_rem_smooth.continuous_iteratedFDeriv hk).norm
    have h_comp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
    rcases h_comp.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
    refine ⟨max 0 M, le_max_left 0 M, ?_⟩
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hw
    have hw_mem : (fun w => ‖iteratedFDeriv ℝ k g_rem w‖) w ∈
        (fun w => ‖iteratedFDeriv ℝ k g_rem w‖) '' Metric.closedBall (0 : ℂ) R :=
      mem_image_of_mem _ hw'
    exact (hM hw_mem).trans (le_max_right 0 M)
  · refine ⟨0, le_rfl, ?_⟩
    intro w hw
    have : 0 ≤ ‖w‖ := norm_nonneg _
    linarith

lemma pow_mul_norm_sq_le (h : Fin n → ℂ) (hh : ‖h‖ ≤ 1) (k : ℕ) (hk : 2 ≤ k) :
    ((n : ℝ) * ‖h‖) ^ k ≤ (n : ℝ) ^ k * ‖h‖ ^ 2 := by
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_of_le_one (norm_nonneg _) hh hk

lemma exists_g_rem_comp_L_h_bound_sq (MK : ℝ) (hMK : 0 ≤ MK) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Fin n → ℂ) (_hh : ‖h‖ ≤ 1) (x : Fin n → ℝ) (_hx : ‖x‖ ≤ MK),
      ‖iteratedFDeriv ℝ k (g_rem ∘ L_h h) x‖ ≤ C * ‖h‖ ^ 2 := by
  let R := (n : ℝ) * MK
  have hR : 0 ≤ R := by positivity
  rcases k with _ | k
  · refine ⟨((n : ℝ) * MK) ^ 2 * Real.exp R, by positivity, ?_⟩
    intro h hh x hx
    rw [norm_iteratedFDeriv_zero]
    dsimp [Function.comp]
    have h_rem := exp_two_rem (L_h h x)
    have hx_le : ‖L_h h x‖ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := norm_L_h_apply_le h x
    have hx_le' : ‖L_h h x‖ ≤ ((n : ℝ) * MK) * ‖h‖ := by
      calc ‖L_h h x‖
        _ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := hx_le
        _ ≤ (n : ℝ) * ‖h‖ * MK :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        _ = ((n : ℝ) * MK) * ‖h‖ := by ring
    have h_w_le_R : ‖L_h h x‖ ≤ R := by
      calc ‖L_h h x‖
        _ ≤ ((n : ℝ) * MK) * ‖h‖ := hx_le'
        _ ≤ ((n : ℝ) * MK) * 1 :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = R := by ring
    have h_exp : Real.exp ‖L_h h x‖ ≤ Real.exp R := Real.exp_le_exp_of_le h_w_le_R
    have h_sq : ‖L_h h x‖ ^ 2 ≤ (((n : ℝ) * MK) * ‖h‖) ^ 2 := by
      have : 0 ≤ ‖L_h h x‖ := norm_nonneg _
      exact sq_le_sq' (by linarith) hx_le'
    calc ‖Complex.exp (L_h h x) - 1 - L_h h x‖
      _ ≤ ‖L_h h x‖ ^ 2 * Real.exp ‖L_h h x‖ := h_rem
      _ ≤ (((n : ℝ) * MK) * ‖h‖) ^ 2 * Real.exp R :=
        mul_le_mul h_sq h_exp (Real.exp_pos _).le (by positivity)
      _ = (((n : ℝ) * MK) ^ 2 * Real.exp R) * ‖h‖ ^ 2 := by ring
  · rcases k with _ | k
    · rcases exists_norm_iteratedFDeriv_g_rem_bound 2 R with ⟨C2, hC2_nonneg, hC2⟩
      refine ⟨C2 * (n : ℝ) ^ 2 * MK, by positivity, ?_⟩
      intro h hh x hx
      have h_comp_le := norm_iteratedFDeriv_comp_L_h_le h 1 x
      rw [pow_one] at h_comp_le
      have hx_le : ‖L_h h x‖ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := norm_L_h_apply_le h x
      have hx_le' : ‖L_h h x‖ ≤ ((n : ℝ) * MK) * ‖h‖ := by
        calc ‖L_h h x‖
          _ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := hx_le
          _ ≤ (n : ℝ) * ‖h‖ * MK :=
            mul_le_mul_of_nonneg_left hx (by positivity)
          _ = ((n : ℝ) * MK) * ‖h‖ := by ring
      have h_w_le_R : ‖L_h h x‖ ≤ R := by
        calc ‖L_h h x‖
          _ ≤ ((n : ℝ) * MK) * ‖h‖ := hx_le'
          _ ≤ ((n : ℝ) * MK) * 1 :=
            mul_le_mul_of_nonneg_left hh (by positivity)
          _ = R := by ring
      have h_g1 : ‖iteratedFDeriv ℝ 1 g_rem (L_h h x)‖ ≤ C2 * ‖L_h h x‖ :=
        norm_iteratedFDeriv_one_g_rem_le R hR C2 hC2 (L_h h x) h_w_le_R
      have h_op : ‖L_h h‖ ≤ (n : ℝ) * ‖h‖ := opNorm_L_h_le h
      calc ‖iteratedFDeriv ℝ 1 (g_rem ∘ L_h h) x‖
        _ ≤ ‖iteratedFDeriv ℝ 1 g_rem (L_h h x)‖ * ‖L_h h‖ := h_comp_le
        _ ≤ (C2 * ‖L_h h x‖) * ((n : ℝ) * ‖h‖) :=
          mul_le_mul h_g1 h_op (norm_nonneg _) (by positivity)
        _ ≤ (C2 * (((n : ℝ) * MK) * ‖h‖)) * ((n : ℝ) * ‖h‖) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hx_le' hC2_nonneg
        _ = (C2 * (n : ℝ) ^ 2 * MK) * ‖h‖ ^ 2 := by ring
    · let m := k + 2
      have hm : 2 ≤ m := by omega
      rcases exists_norm_iteratedFDeriv_g_rem_bound m R with ⟨Cm, hCm_nonneg, hCm⟩
      refine ⟨Cm * (n : ℝ) ^ m, by positivity, ?_⟩
      intro h hh x hx
      have h_comp_le := norm_iteratedFDeriv_comp_L_h_le h m x
      have h_w_le_R : ‖L_h h x‖ ≤ R := by
        have hx_le := norm_L_h_apply_le h x
        calc ‖L_h h x‖
          _ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := hx_le
          _ ≤ (n : ℝ) * 1 * MK := by
            refine mul_le_mul ?_ hx (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hh (by positivity)
          _ = R := by ring
      have h_gm : ‖iteratedFDeriv ℝ m g_rem (L_h h x)‖ ≤ Cm := hCm (L_h h x) h_w_le_R
      have h_op : ‖L_h h‖ ≤ (n : ℝ) * ‖h‖ := opNorm_L_h_le h
      have h_op_pow : ‖L_h h‖ ^ m ≤ ((n : ℝ) * ‖h‖) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) h_op m
      have h_pow_le : ((n : ℝ) * ‖h‖) ^ m ≤ (n : ℝ) ^ m * ‖h‖ ^ 2 :=
        pow_mul_norm_sq_le h hh m hm
      calc ‖iteratedFDeriv ℝ m (g_rem ∘ L_h h) x‖
        _ ≤ ‖iteratedFDeriv ℝ m g_rem (L_h h x)‖ * ‖L_h h‖ ^ m := h_comp_le
        _ ≤ Cm * ((n : ℝ) ^ m * ‖h‖ ^ 2) := by
          refine mul_le_mul h_gm (h_op_pow.trans h_pow_le) (by positivity) hCm_nonneg
        _ = (Cm * (n : ℝ) ^ m) * ‖h‖ ^ 2 := by ring

lemma expTaylorRem_eq_mul (z h : Fin n → ℂ) (x : Fin n → ℝ) :
    expTaylorRem z h x =
      Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) * (g_rem ∘ L_h h) x := by
  rw [expTaylorRem_factor]
  dsimp [g_rem, Function.comp]
  rw [L_h_apply]

noncomputable def chi_mul_exp (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    (Fin n → ℝ) → ℂ :=
  fun y => (χ.toFun y : ℂ) * Complex.exp (-Complex.I * (∑ k, z k * (y k : ℂ)))

lemma chi_mul_exp_smooth (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (chi_mul_exp Ω_n χ z) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ)) := by
    have hχ' : ContDiff ℝ (↑(⊤ : ℕ∞)) χ.toFun := χ.contDiff' (n := ⊤)
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp hχ'
  have h2 := exp_izx_smooth z
  exact h1.mul h2

lemma exists_chi_mul_exp_bound (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) (j : ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ ≤ M := by
  intro K
  have hF := chi_mul_exp_smooth Ω_n χ z
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_cont : Continuous (fun x => ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖) :=
    (hF.continuous_iteratedFDeriv hj).norm
  rcases K.isCompact'.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x hx
  have h := hM (mem_image_of_mem _ hx)
  exact h.trans (le_max_right 0 M)

lemma expTaylorRem_fun_eq (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z h : Fin n → ℂ) :
    (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) =
      (fun y => (chi_mul_exp Ω_n χ z y) * (g_rem ∘ L_h h) y) := by
  ext y
  dsimp [chi_mul_exp, Function.comp]
  rw [expTaylorRem_eq_mul]
  dsimp [Function.comp]
  ring

lemma expTaylorRem_single_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) (i : ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) x‖ ≤ c * ‖h‖ := by
  intro K c hc
  rcases exists_norm_le_of_compact K with ⟨MK, hMK, hxMK⟩
  have h_bound_F : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ (K : Set (Fin n → ℝ)), ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ ≤ M :=
    fun j => exists_chi_mul_exp_bound Ω_n χ z j
  have h_bound_G : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Fin n → ℂ) (hh : ‖h‖ ≤ 1) (x : Fin n → ℝ) (hx : ‖x‖ ≤ MK),
        ‖iteratedFDeriv ℝ k (g_rem ∘ L_h h) x‖ ≤ C * ‖h‖ ^ 2 :=
    fun k => exists_g_rem_comp_L_h_bound_sq MK hMK k
  choose M_F hM_F_nonneg hM_F using h_bound_F
  choose C_G hC_G_nonneg hC_G using h_bound_G
  let C_total := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_F j * C_G (i - j)
  have hC_total_nonneg : 0 ≤ C_total := by
    refine Finset.sum_nonneg ?_
    intro j _
    have h1 : 0 ≤ (i.choose j : ℝ) := by positivity
    have h2 := hM_F_nonneg j
    have h3 := hC_G_nonneg (i - j)
    positivity
  let δ := min (1 : ℝ) (c / (C_total + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hc (by positivity))
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, ?_⟩
  intro h hh
  rw [dist_zero_right] at hh
  have hh1 : ‖h‖ ≤ 1 := (le_of_lt hh).trans (min_le_left 1 _)
  have hhc : ‖h‖ ≤ c / (C_total + 1) := (le_of_lt hh).trans (min_le_right 1 _)
  intro x hx
  rw [expTaylorRem_fun_eq]
  have hF_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (chi_mul_exp Ω_n χ z) :=
    chi_mul_exp_smooth Ω_n χ z
  have hG_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (g_rem ∘ L_h h) :=
    g_rem_smooth.comp (L_h h).contDiff
  have hi : (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_leibniz := norm_iteratedFDeriv_mul_le hF_smooth hG_smooth x (n := i) hi
  have h_term : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖ ≤
        ((i.choose j : ℝ) * M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by
    intro j _
    have hF_le := hM_F j x hx
    have hG_le := hC_G (i - j) h hh1 x (hxMK x hx)
    have h_mul1 : ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
        ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖ ≤
      (M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by
      calc ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖
        _ ≤ M_F j * (C_G (i - j) * ‖h‖ ^ 2) :=
          mul_le_mul hF_le hG_le (norm_nonneg _) (hM_F_nonneg j)
        _ = (M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by ring
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖
      _ = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖) := by ring
      _ ≤ (i.choose j : ℝ) * ((M_F j * C_G (i - j)) * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_mul1 (by positivity)
      _ = ((i.choose j : ℝ) * M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by ring
  calc ‖iteratedFDeriv ℝ i (fun y => (chi_mul_exp Ω_n χ z y) * (g_rem ∘ L_h h) y) x‖
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
            ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖ := h_leibniz
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          ((i.choose j : ℝ) * M_F j * C_G (i - j)) * ‖h‖ ^ 2 :=
        Finset.sum_le_sum h_term
    _ = C_total * ‖h‖ ^ 2 := by
      rw [← Finset.sum_mul]
    _ = (C_total * ‖h‖) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h_c : C_total * ‖h‖ ≤ C_total * (c / (C_total + 1)) :=
        mul_le_mul_of_nonneg_left hhc hC_total_nonneg
      refine h_c.trans ?_
      calc C_total * (c / (C_total + 1))
        _ = (C_total / (C_total + 1)) * c := by ring
        _ ≤ 1 * c := by
          refine mul_le_mul_of_nonneg_right ?_ hc.le
          have : C_total ≤ C_total + 1 := by linarith
          exact div_le_one_of_le₀ this (by positivity)
        _ = c := one_mul c

lemma expTaylorRem_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) (s : Finset ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).re) x‖ ≤ c * ‖h‖) ∧
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).im) x‖ ≤ c * ‖h‖) := by
  apply expTaylorRem_bound_exists_of_single Ω_n χ z (expTaylorRem_single_bound_exists Ω_n χ z)

lemma fourier_laplace_hasFDerivAt
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) :
    HasFDerivAt (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one)
      (FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z) z := by
  by_cases hn : n = 0
  · subst hn
    have h_deriv_zero : FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z = 0 := by
      ext h
      rw [FourierLaplaceTotalDeriv_apply]
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
    rw [h_deriv_zero]
    have h_subsingleton : Subsingleton (Fin 0 → ℂ) := inferInstance
    have h_const : ∀ w : Fin 0 → ℂ, w = z := fun w => Subsingleton.elim w z
    have h_eq : (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) =
        fun _ => FourierLaplaceTransform Ω_n T hT V hV χ hχ_one z := by
      ext w
      rw [h_const w]
    rw [h_eq]
    exact hasFDerivAt_const (𝕜 := ℂ) _ z
  · by_cases h_supp : Distribution.support Ω_n T = ∅
    · exact fourier_laplace_empty_support Ω_n T hT h_supp V hV χ hχ_one z
    · have h_bound := applySmoothComplex_bound Ω_n T hT V hV χ hχ_one
      rcases h_bound with ⟨s, C, h_eval⟩
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      have hc_pos : 0 < c / (2 * (C : ℝ) + 1) := by
        have h_denom : 0 < 2 * (C : ℝ) + 1 := by positivity
        exact div_pos hc h_denom
      have h_ev := expTaylorRem_bound_exists Ω_n χ z s (c / (2 * (C : ℝ) + 1)) hc_pos
      filter_upwards [h_ev] with h hh
      rw [fourier_laplace_diff_rem]
      have hB_nonneg : 0 ≤ (c / (2 * (C : ℝ) + 1)) * ‖h‖ :=
        mul_nonneg hc_pos.le (norm_nonneg h)
      have h_app := h_eval (expTaylorRem z h) (expTaylorRem_re_smooth z h)
        (expTaylorRem_im_smooth z h) ((c / (2 * (C : ℝ) + 1)) * ‖h‖) hB_nonneg hh.1 hh.2
      exact h_app.trans (bound_mul_le C c hc.le h _ le_rfl)

lemma FourierLaplaceTransform_is_entire
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    Differentiable ℂ (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) := by
  intro z
  exact (fourier_laplace_hasFDerivAt Ω_n T hT V hV χ hχ_one z).differentiableAt

lemma FourierLaplaceTransform_is_holomorphic
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    DifferentiableOn ℂ (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) (TubeDomain V_plus) := by
  exact (FourierLaplaceTransform_is_entire Ω_n T hT V hV χ hχ_one).differentiableOn

def EqualOn (T₁ T₂ : 𝓓'(Ω_n, ℂ)) (U : Opens (Fin n → ℝ))
    (_hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n) : Prop :=
  ∀ φ : 𝓓(Ω_n, ℝ), tsupport (fun x => φ x) ⊆ (U : Set (Fin n → ℝ)) → T₁ φ = T₂ φ

inductive EOWCoverIdx (U : Set (Fin n → ℝ))
  | plus : EOWCoverIdx U
  | minus : EOWCoverIdx U
  | loc (x : U) : EOWCoverIdx U

def eowCoverSet (V_plus V_minus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) : EOWCoverIdx U → Set (Fin n → ℂ)
  | .plus => TubeDomain V_plus
  | .minus => TubeDomain V_minus
  | .loc ⟨x, _hx⟩ => Metric.ball (fun i => (x i : ℂ)) (r x)

def eowCoverFun (U : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ) :
    EOWCoverIdx U → (Fin n → ℂ) → ℂ
  | .plus => f_plus
  | .minus => f_minus
  | .loc ⟨x, _hx⟩ => F_loc x

lemma isOpen_eowCoverSet (V_plus V_minus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (hVp : IsOpen V_plus) (hVm : IsOpen V_minus)
    (r : (Fin n → ℝ) → ℝ) (i : EOWCoverIdx U) :
    IsOpen (eowCoverSet V_plus V_minus U r i) := by
  cases i with
  | plus => exact isOpen_TubeDomain hVp
  | minus => exact isOpen_TubeDomain hVm
  | loc x => exact Metric.isOpen_ball

lemma local_eow_glue (V_plus V_minus : Set (Fin n → ℝ)) (U : Opens (Fin n → ℝ))
    (hVp : IsOpen V_plus) (hVm : IsOpen V_minus)
    (h_disj : Disjoint (TubeDomain V_plus) (TubeDomain V_minus))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_holo : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_eq_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_eq_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus))
    (hF_compat : ∀ (x y : (U : Set (Fin n → ℝ))),
      EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have hs_open : ∀ i : EOWCoverIdx (U : Set (Fin n → ℝ)),
      IsOpen (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i) :=
    isOpen_eowCoverSet V_plus V_minus U hVp hVm r
  have h_diff : ∀ i : EOWCoverIdx (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc i)
        (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i) := by
    intro i
    cases i with
    | plus => exact hf_plus
    | minus => exact hf_minus
    | loc x => exact hF_holo x.1 x.2
  have h_compat : ∀ i j : EOWCoverIdx (U : Set (Fin n → ℝ)),
      EqOn (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc i)
           (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc j)
           (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i ∩
            eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r j) := by
    intro i j z hz
    cases i with
    | plus =>
      cases j with
      | plus => rfl
      | minus =>
        have h_inter : z ∈ TubeDomain V_plus ∩ TubeDomain V_minus := hz
        exact False.elim (Set.disjoint_iff.mp h_disj h_inter)
      | loc x =>
        exact (hF_eq_plus x.1 x.2 ⟨hz.2, hz.1⟩).symm
    | minus =>
      cases j with
      | plus =>
        have h_inter : z ∈ TubeDomain V_plus ∩ TubeDomain V_minus := ⟨hz.2, hz.1⟩
        exact False.elim (Set.disjoint_iff.mp h_disj h_inter)
      | minus => rfl
      | loc x =>
        exact (hF_eq_minus x.1 x.2 ⟨hz.2, hz.1⟩).symm
    | loc x =>
      cases j with
      | plus => exact hF_eq_plus x.1 x.2 ⟨hz.1, hz.2⟩
      | minus => exact hF_eq_minus x.1 x.2 ⟨hz.1, hz.2⟩
      | loc y => exact hF_compat x y hz
  rcases differentiableOn_iUnion_of_locally_differentiable
    (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r) hs_open
    (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc) h_diff h_compat with
    ⟨F, hF_diff, hF_eq_i⟩
  let W_set := ⋃ i, eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i
  have hW_open : IsOpen W_set := isOpen_iUnion hs_open
  let W : Opens (Fin n → ℂ) := ⟨W_set, hW_open⟩
  refine ⟨W, F, ?_, hF_diff, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.2 ⟨.loc ⟨x, hx⟩, Metric.mem_ball_self (hr x hx)⟩
  · intro z hz
    have hz_W : z ∈ eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r .plus := hz.2
    exact hF_eq_i .plus hz_W
  · intro z hz
    have hz_W : z ∈ eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r .minus := hz.2
    exact hF_eq_i .minus hz_W

structure LocalEpsteinData
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ) where
  r : ℝ
  hr : 0 < r
  F : (Fin n → ℂ) → ℂ
  hF_diff : DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) r)
  hF_plus : EqOn F f_plus (Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_plus)
  hF_minus : EqOn F f_minus (Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_minus)

lemma norm_im_le_norm_sub_real (z : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖fun i => (z i).im‖ ≤ ‖z - (fun i => (x i : ℂ))‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have h1 : (z i).im = ((z - (fun i => (x i : ℂ))) i).im := by
    simp only [Pi.sub_apply, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [h1]
  have h2 : ‖((z - (fun i => (x i : ℂ))) i).im‖ ≤ ‖(z - (fun i => (x i : ℂ))) i‖ := by
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  exact h2.trans (norm_le_pi_norm (z - (fun i => (x i : ℂ))) i)

lemma local_eow_glue_balls (V_plus V_minus : Set (Fin n → ℝ)) (U : Opens (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_holo : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_eq_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_eq_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus))
    (hF_compat : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  let ball_set : {x // x ∈ (U : Set (Fin n → ℝ))} → Set (Fin n → ℂ) :=
    fun x => Metric.ball (fun i => (x.1 i : ℂ)) (r x.1)
  have hs_open : ∀ x : {x // x ∈ (U : Set (Fin n → ℝ))}, IsOpen (ball_set x) :=
    fun _ => Metric.isOpen_ball
  have h_diff : ∀ x : {x // x ∈ (U : Set (Fin n → ℝ))},
      DifferentiableOn ℂ (F_loc x.1) (ball_set x) :=
    fun x => hF_holo x.1 x.2
  have h_compat : ∀ x y : {x // x ∈ (U : Set (Fin n → ℝ))},
      EqOn (F_loc x.1) (F_loc y.1) (ball_set x ∩ ball_set y) :=
    fun x y => hF_compat x y
  rcases differentiableOn_iUnion_of_locally_differentiable
    ball_set hs_open (fun x => F_loc x.1) h_diff h_compat with ⟨F, hF_diff, hF_eq_i⟩
  let W_set := ⋃ x : {x // x ∈ (U : Set (Fin n → ℝ))}, ball_set x
  have hW_open : IsOpen W_set := isOpen_iUnion hs_open
  let W : Opens (Fin n → ℂ) := ⟨W_set, hW_open⟩
  have hF_diff' : DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) := hF_diff
  refine ⟨W, F, ?_, hF_diff', ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hr x hx)⟩
  · intro z hz
    rcases mem_iUnion.1 hz.1 with ⟨x, hzx⟩
    have hF_eq := hF_eq_i x hzx
    have hF_plus := hF_eq_plus x.1 x.2 ⟨hzx, hz.2⟩
    rw [hF_eq, hF_plus]
  · intro z hz
    rcases mem_iUnion.1 hz.1 with ⟨x, hzx⟩
    have hF_eq := hF_eq_i x hzx
    have hF_minus := hF_eq_minus x.1 x.2 ⟨hzx, hz.2⟩
    rw [hF_eq, hF_minus]

lemma local_eow_epstein_from_data
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (h_compat : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (data x.1 x.2).F (data y.1 y.2).F
        (Metric.ball (fun i => (x.1 i : ℂ)) (data x.1 x.2).r ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (data y.1 y.2).r)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  classical
  let r : (Fin n → ℝ) → ℝ := fun x =>
    if hx : x ∈ (U : Set (Fin n → ℝ)) then (data x hx).r else 1
  let F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ := fun x =>
    if hx : x ∈ (U : Set (Fin n → ℝ)) then (data x hx).F else 0
  have hr_pos : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x := by
    intro x hx
    dsimp [r]
    rw [dif_pos hx]
    exact (data x hx).hr
  have hF_holo : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)) := by
    intro x hx
    dsimp [F_loc, r]
    rw [dif_pos hx, dif_pos hx]
    exact (data x hx).hF_diff
  have hF_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus) := by
    intro x hx
    dsimp [F_loc, r]
    rw [dif_pos hx, dif_pos hx]
    exact (data x hx).hF_plus
  have hF_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus) := by
    intro x hx
    dsimp [F_loc, r]
    rw [dif_pos hx, dif_pos hx]
    exact (data x hx).hF_minus
  have hF_c : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1)) := by
    intro x y
    dsimp [F_loc, r]
    rw [dif_pos x.2, dif_pos x.2, dif_pos y.2, dif_pos y.2]
    exact h_compat x y
  exact local_eow_glue_balls V_plus V_minus U f_plus f_minus r hr_pos F_loc
    hF_holo hF_plus hF_minus hF_c

lemma local_epstein_extension_of_common_F
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F : (Fin n → ℂ) → ℂ)
    (hF_diff : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn F f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn F f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus)) :
    ∃ (W : Opens (Fin n → ℂ)) (F_ext : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F_ext (W : Set (Fin n → ℂ)) ∧
      EqOn F_ext f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F_ext f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have h_compat : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn F F
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1)) := by
    intro x y z hz
    rfl
  exact local_eow_glue_balls V_plus V_minus U f_plus f_minus r hr
    (fun _ => F) hF_diff hF_plus hF_minus h_compat

def localEpsteinData_of_open_matches
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (hV_minus_open : IsOpen V_minus) (hV_minus_conv : Convex ℝ V_minus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (x : Fin n → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : (Fin n → ℂ) → ℂ)
    (hF_diff : DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ))
    (W₁ : Set (Fin n → ℂ)) (hW₁_open : IsOpen W₁) (hW₁_ne : W₁.Nonempty)
    (hW₁_sub : W₁ ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus)
    (hF_eq1 : EqOn F f_plus W₁)
    (W₂ : Set (Fin n → ℂ)) (hW₂_open : IsOpen W₂) (hW₂_ne : W₂.Nonempty)
    (hW₂_sub : W₂ ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_minus)
    (hF_eq2 : EqOn F f_minus W₂) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  have hB_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ) := Metric.isOpen_ball
  have hB_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ) := convex_ball _ _
  have hT_plus_open : IsOpen (TubeDomain V_plus) := isOpen_TubeDomain hV_plus_open
  have hT_minus_open : IsOpen (TubeDomain V_minus) := isOpen_TubeDomain hV_minus_open
  have hT_plus_conv : Convex ℝ (TubeDomain V_plus) := convex_TubeDomain hV_plus_conv
  have hT_minus_conv : Convex ℝ (TubeDomain V_minus) := convex_TubeDomain hV_minus_conv
  let S₁ := Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus
  have hS₁_open : IsOpen S₁ := hB_open.inter hT_plus_open
  have hS₁_conv : Convex ℝ S₁ := hB_conv.inter hT_plus_conv
  have hd₁ : DifferentiableOn ℂ (F - f_plus) S₁ :=
    (hF_diff.mono inter_subset_left).sub (hf_plus_holo.mono inter_subset_right)
  have h_zero1 : EqOn (F - f_plus) 0 S₁ := by
    apply eqOn_zero_of_convex_differentiableOn hS₁_open hS₁_conv hd₁ hW₁_open hW₁_sub hW₁_ne
    intro z hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact hF_eq1 hz
  have hF_plus : EqOn F f_plus S₁ := by
    intro z hz
    have := h_zero1 hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  let S₂ := Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_minus
  have hS₂_open : IsOpen S₂ := hB_open.inter hT_minus_open
  have hS₂_conv : Convex ℝ S₂ := hB_conv.inter hT_minus_conv
  have hd₂ : DifferentiableOn ℂ (F - f_minus) S₂ :=
    (hF_diff.mono inter_subset_left).sub (hf_minus_holo.mono inter_subset_right)
  have h_zero2 : EqOn (F - f_minus) 0 S₂ := by
    apply eqOn_zero_of_convex_differentiableOn hS₂_open hS₂_conv hd₂ hW₂_open hW₂_sub hW₂_ne
    intro z hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact hF_eq2 hz
  have hF_minus : EqOn F f_minus S₂ := by
    intro z hz
    have := h_zero2 hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  exact ⟨ρ, hρ, F, hF_diff, hF_plus, hF_minus⟩

lemma isOpen_neg_image {s : Set (Fin n → ℝ)} (hs : IsOpen s) :
    IsOpen ((fun v => -v) '' s) := by
  have : ((fun v => -v) '' s) = (fun v => -v) ⁻¹' s := by
    ext v; simp
  rw [this]
  exact hs.preimage continuous_neg

lemma convex_neg_image {s : Set (Fin n → ℝ)} (hs : Convex ℝ s) :
    Convex ℝ ((fun v => -v) '' s) := by
  rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ a b ha hb hab
  exact ⟨a • v₁ + b • v₂, hs hv₁ hv₂ ha hb hab, by simp [add_comm]⟩

noncomputable def localEpsteinData_of_core
    (V_plus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ)
    (h_core : LocalEOWCore V_plus f x) :
    LocalEpsteinData V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) f f x := by
  have h_ex :
      ∃ (d : LocalEpsteinData V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) f f x),
        True := by
    obtain ⟨ρ, hρ, F, hF_an, ⟨W₁, hW₁o, hW₁n, hW₁s, hW₁e⟩, ⟨W₂, hW₂o, hW₂n, hW₂s, hW₂e⟩⟩ := h_core
    have hVm_conv : Convex ℝ ((fun v : Fin n → ℝ => -v) '' V_plus) := convex_neg_image hV_plus_conv
    have hVm_open : IsOpen ((fun v : Fin n → ℝ => -v) '' V_plus) := isOpen_neg_image hV_plus_open
    exact ⟨localEpsteinData_of_open_matches V_plus ((fun v : Fin n → ℝ => -v) '' V_plus)
      hV_plus_open hV_plus_conv hVm_open hVm_conv
      f f hf_plus_holo hf_minus_holo x ρ hρ F hF_an.differentiableOn
      W₁ hW₁o hW₁n hW₁s hW₁e W₂ hW₂o hW₂n hW₂s hW₂e, trivial⟩
  exact Classical.choose h_ex

def localEpsteinData_of_disjoint
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h_disj_plus : Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus = ∅)
    (h_disj_minus : Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_minus = ∅) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  refine ⟨ρ, hρ, fun _ => 0, ?_, ?_, ?_⟩
  · exact differentiable_const 0 |>.differentiableOn
  · rw [h_disj_plus]
    exact eqOn_empty _ _
  · rw [h_disj_minus]
    exact eqOn_empty _ _

def localEpsteinData_shrink
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ)
    (d : LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (r' : ℝ) (hr'_pos : 0 < r') (hr'_le : r' ≤ d.r) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  have h_sub : Metric.ball (fun i => (x i : ℂ)) r' ⊆ Metric.ball (fun i => (x i : ℂ)) d.r :=
    Metric.ball_subset_ball hr'_le
  refine ⟨r', hr'_pos, d.F, ?_, ?_, ?_⟩
  · exact d.hF_diff.mono h_sub
  · exact d.hF_plus.mono (inter_subset_inter_left _ h_sub)
  · exact d.hF_minus.mono (inter_subset_inter_left _ h_sub)

lemma localEpsteinData_compat_of_inter_nonempty
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x y : Fin n → ℝ)
    (dx : LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (dy : LocalEpsteinData V_plus V_minus f_plus f_minus y)
    (h_inter_nonempty : (Metric.ball (fun i => (x i : ℂ)) dx.r ∩
                         Metric.ball (fun i => (y i : ℂ)) dy.r ∩
                         TubeDomain V_plus).Nonempty) :
    EqOn dx.F dy.F (Metric.ball (fun i => (x i : ℂ)) dx.r ∩
                    Metric.ball (fun i => (y i : ℂ)) dy.r) := by
  let B := Metric.ball (fun i => (x i : ℂ)) dx.r ∩ Metric.ball (fun i => (y i : ℂ)) dy.r
  have hB_open : IsOpen B := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hB_conv : Convex ℝ B := (convex_ball _ _).inter (convex_ball _ _)
  have hd : DifferentiableOn ℂ (dx.F - dy.F) B :=
    (dx.hF_diff.mono inter_subset_left).sub (dy.hF_diff.mono inter_subset_right)
  let W := B ∩ TubeDomain V_plus
  have hW_open : IsOpen W := hB_open.inter (isOpen_TubeDomain hV_plus_open)
  have hW_sub : W ⊆ B := inter_subset_left
  have hW_eq : EqOn (dx.F - dy.F) 0 W := by
    intro z hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    have hz_x : z ∈ Metric.ball (fun i => (x i : ℂ)) dx.r ∩ TubeDomain V_plus :=
      ⟨hz.1.1, hz.2⟩
    have hz_y : z ∈ Metric.ball (fun i => (y i : ℂ)) dy.r ∩ TubeDomain V_plus :=
      ⟨hz.1.2, hz.2⟩
    rw [dx.hF_plus hz_x, dy.hF_plus hz_y]
  have h_zero := eqOn_zero_of_convex_differentiableOn
    hB_open hB_conv hd hW_open hW_sub h_inter_nonempty hW_eq
  intro z hz
  have hz0 := h_zero hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hz0
  exact hz0

lemma re_mem_ball_of_mem_ball (x : Fin n → ℝ) (r : ℝ) (z : Fin n → ℂ)
    (hz : z ∈ Metric.ball (fun i => (x i : ℂ)) r) :
    (fun i => (z i).re) ∈ Metric.ball x r := by
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  have hr_pos : 0 < r := (norm_nonneg _).trans_lt hz
  rw [pi_norm_lt_iff hr_pos] at hz ⊢
  intro i
  have h1 : ‖((fun i => (z i).re) - x) i‖ = |(z i).re - x i| := by
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have h2 : |(z i).re - x i| = |(z i - (x i : ℂ)).re| := by
    simp only [Complex.sub_re, Complex.ofReal_re]
  have h3 : |(z i - (x i : ℂ)).re| ≤ ‖(z - (fun i => (x i : ℂ))) i‖ := by
    simp only [Pi.sub_apply]
    exact Complex.abs_re_le_norm _
  rw [h1, h2]
  exact h3.trans_lt (hz i)

lemma re_mem_inter_balls (x y : Fin n → ℝ) (rx ry : ℝ) (z : Fin n → ℂ)
    (hz : z ∈ Metric.ball (fun i => (x i : ℂ)) rx ∩ Metric.ball (fun i => (y i : ℂ)) ry) :
    (fun i => (z i).re) ∈ Metric.ball x rx ∩ Metric.ball y ry :=
  ⟨re_mem_ball_of_mem_ball x rx z hz.1, re_mem_ball_of_mem_ball y ry z hz.2⟩

lemma norm_real_add_I_sub_le (p x u : Fin n → ℝ) :
    ‖(fun i => (p i : ℂ) + (u i : ℂ) * Complex.I) - (fun i => (x i : ℂ))‖ ≤
      ‖p - x‖ + ‖u‖ := by
  let z : Fin n → ℂ := fun i => (p i : ℂ) + (u i : ℂ) * Complex.I
  have h_comp : ∀ i, ‖(z - (fun i => (x i : ℂ))) i‖ ≤ ‖p - x‖ + ‖u‖ := by
    intro i
    have h_eq : (z - (fun i => (x i : ℂ))) i = ((p i - x i : ℝ) : ℂ) + (u i : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [h_eq]
    have h_add := norm_add_le ((p i - x i : ℝ) : ℂ) ((u i : ℂ) * Complex.I)
    have h1 : ‖((p i - x i : ℝ) : ℂ)‖ = ‖p i - x i‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(u i : ℂ) * Complex.I‖ = ‖u i‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2] at h_add
    have h_p_le : ‖p i - x i‖ ≤ ‖p - x‖ := by
      have : ‖p i - x i‖ = ‖(p - x) i‖ := by simp only [Pi.sub_apply]
      rw [this]
      exact norm_le_pi_norm (p - x) i
    have h_u_le : ‖u i‖ ≤ ‖u‖ := norm_le_pi_norm u i
    exact h_add.trans (add_le_add h_p_le h_u_le)
  have h_nonneg : 0 ≤ ‖p - x‖ + ‖u‖ := by positivity
  exact (pi_norm_le_iff_of_nonneg h_nonneg).mpr h_comp

lemma inter_balls_tube_nonempty_of_mem_inter_real
    (V_plus : Set (Fin n → ℝ)) (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (x y : Fin n → ℝ) (rx ry : ℝ)
    (p : Fin n → ℝ) (hp : p ∈ Metric.ball x rx ∩ Metric.ball y ry) :
    (Metric.ball (fun i => (x i : ℂ)) rx ∩ Metric.ball (fun i => (y i : ℂ)) ry ∩
     TubeDomain V_plus).Nonempty := by
  have hpx : ‖p - x‖ < rx := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hp.1
  have hpy : ‖p - y‖ < ry := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hp.2
  let δx := rx - ‖p - x‖
  let δy := ry - ‖p - y‖
  have hδx : 0 < δx := sub_pos.mpr hpx
  have hδy : 0 < δy := sub_pos.mpr hpy
  let δ := min δx δy
  have hδ : 0 < δ := lt_min hδx hδy
  rw [Metric.mem_closure_iff] at h0
  rcases h0 δ hδ with ⟨u, hu_V, hu_dist⟩
  have hu_norm : ‖u‖ < δ := by
    rw [dist_zero_left] at hu_dist
    exact hu_dist
  let z : Fin n → ℂ := fun i => (p i : ℂ) + (u i : ℂ) * Complex.I
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have h_le := norm_real_add_I_sub_le p x u
    have h_lt : ‖p - x‖ + ‖u‖ < rx := by
      have : ‖u‖ < δx := hu_norm.trans_le (min_le_left _ _)
      linarith
    exact h_le.trans_lt h_lt
  · rw [Metric.mem_ball, dist_eq_norm]
    have h_le := norm_real_add_I_sub_le p y u
    have h_lt : ‖p - y‖ + ‖u‖ < ry := by
      have : ‖u‖ < δy := hu_norm.trans_le (min_le_right _ _)
      linarith
    exact h_le.trans_lt h_lt
  · dsimp [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => (z i).im) = u := by
      ext i
      simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
                 zero_add]
    rw [h_im]
    exact hu_V

lemma localEpsteinData_compat
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x y : Fin n → ℝ)
    (dx : LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (dy : LocalEpsteinData V_plus V_minus f_plus f_minus y) :
    EqOn dx.F dy.F (Metric.ball (fun i => (x i : ℂ)) dx.r ∩
                    Metric.ball (fun i => (y i : ℂ)) dy.r) := by
  let B := Metric.ball (fun i => (x i : ℂ)) dx.r ∩ Metric.ball (fun i => (y i : ℂ)) dy.r
  by_cases h_inter : B.Nonempty
  · rcases h_inter with ⟨w, hw⟩
    let p : Fin n → ℝ := fun i => (w i).re
    have hp : p ∈ Metric.ball x dx.r ∩ Metric.ball y dy.r :=
      re_mem_inter_balls x y dx.r dy.r w hw
    have h_tube_nonempty : (B ∩ TubeDomain V_plus).Nonempty :=
      inter_balls_tube_nonempty_of_mem_inter_real V_plus h0 x y dx.r dy.r p hp
    exact localEpsteinData_compat_of_inter_nonempty V_plus V_minus hV_plus_open
      f_plus f_minus x y dx dy h_tube_nonempty
  · intro z hz
    exact False.elim (h_inter ⟨z, hz⟩)

lemma localEpsteinData_family_compat
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (data x.1 x.2).F (data y.1 y.2).F
        (Metric.ball (fun i => (x.1 i : ℂ)) (data x.1 x.2).r ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (data y.1 y.2).r) := by
  intro x y
  exact localEpsteinData_compat V_plus V_minus hV_plus_open h0 f_plus f_minus
    x.1 y.1 (data x.1 x.2) (data y.1 y.2)

lemma local_eow_epstein_of_data_family
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have h_compat :=
    localEpsteinData_family_compat V_plus V_minus hV_plus_open h0 f_plus f_minus U data
  exact local_eow_epstein_from_data V_plus V_minus f_plus f_minus U data h_compat

lemma local_eow_epstein_of_core_family
    (V_plus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (U : Opens (Fin n → ℝ))
    (h_core : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEOWCore V_plus f x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f ((W : Set (Fin n → ℂ)) ∩ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)),
      LocalEpsteinData V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) f f x :=
    fun x hx => localEpsteinData_of_core V_plus hV_plus_open hV_plus_conv f
      hf_plus_holo hf_minus_holo x (h_core x hx)
  exact local_eow_epstein_of_data_family V_plus ((fun v : Fin n → ℝ => -v) '' V_plus)
    hV_plus_open h0 f f U data

lemma local_eow_epstein_of_local_balls
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_diff : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x :=
    fun x hx => ⟨r x, hr x hx, F_loc x, hF_diff x hx, hF_plus x hx, hF_minus x hx⟩
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 f_plus f_minus U data

lemma local_epstein_extension_of_data_exists
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (h_data_ex : Nonempty (∀ x ∈ (U : Set (Fin n → ℝ)),
      LocalEpsteinData V_plus V_minus f_plus f_minus x)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  rcases h_data_ex with ⟨data⟩
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 f_plus f_minus U data

def localEpsteinData_of_entire
    (V_plus V_minus : Set (Fin n → ℝ))
    (G : (Fin n → ℂ) → ℂ) (hG : Differentiable ℂ G)
    (x : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    LocalEpsteinData V_plus V_minus G G x :=
  ⟨ρ, hρ, G, hG.differentiableOn, fun _ _ => rfl, fun _ _ => rfl⟩

theorem local_eow_epstein_of_entire
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (G : (Fin n → ℂ) → ℂ) (hG : Differentiable ℂ G)
    (U : Opens (Fin n → ℝ)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F G ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F G ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus G G x :=
    fun x _hx => localEpsteinData_of_entire V_plus V_minus G hG x 1 Real.zero_lt_one
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 G G U data

section BoundaryValueAPI

lemma EqualOn.refl {Ω_n : Opens (Fin n → ℝ)} (T : 𝓓'(Ω_n, ℂ))
    (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n) :
    EqualOn Ω_n T T U hU :=
  fun _ _ => rfl

lemma EqualOn.symm {Ω_n : Opens (Fin n → ℝ)} {T₁ T₂ : 𝓓'(Ω_n, ℂ)}
    {U : Opens (Fin n → ℝ)} {hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n}
    (h : EqualOn Ω_n T₁ T₂ U hU) :
    EqualOn Ω_n T₂ T₁ U hU :=
  fun φ hφ => (h φ hφ).symm

lemma EqualOn.trans {Ω_n : Opens (Fin n → ℝ)} {T₁ T₂ T₃ : 𝓓'(Ω_n, ℂ)}
    {U : Opens (Fin n → ℝ)} {hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n}
    (h₁₂ : EqualOn Ω_n T₁ T₂ U hU) (h₂₃ : EqualOn Ω_n T₂ T₃ U hU) :
    EqualOn Ω_n T₁ T₃ U hU :=
  fun φ hφ => (h₁₂ φ hφ).trans (h₂₃ φ hφ)

lemma EqualOn.mono {Ω_n : Opens (Fin n → ℝ)} {T₁ T₂ : 𝓓'(Ω_n, ℂ)}
    {U₁ U₂ : Opens (Fin n → ℝ)}
    {hU₁ : (U₁ : Set (Fin n → ℝ)) ⊆ Ω_n} {hU₂ : (U₂ : Set (Fin n → ℝ)) ⊆ Ω_n}
    (hsub : (U₁ : Set (Fin n → ℝ)) ⊆ (U₂ : Set (Fin n → ℝ)))
    (h : EqualOn Ω_n T₁ T₂ U₂ hU₂) :
    EqualOn Ω_n T₁ T₂ U₁ hU₁ :=
  fun φ hφ => h φ (hφ.trans hsub)

lemma equalOn_iff_vanishesOn_sub {Ω_n : Opens (Fin n → ℝ)}
    (T₁ T₂ : 𝓓'(Ω_n, ℂ)) (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n) :
    EqualOn Ω_n T₁ T₂ U hU ↔ VanishesOn Ω_n (T₁ - T₂) U hU := by
  constructor
  · intro h φ hφ
    change T₁ φ - T₂ φ = 0
    exact sub_eq_zero.mpr (h φ hφ)
  · intro h φ hφ
    have h0 : T₁ φ - T₂ φ = 0 := h φ hφ
    exact sub_eq_zero.mp h0

lemma integrable_boundaryIntegrand_of_continuousOn
    {Ω_n : Opens (Fin n → ℝ)} {V : Set (Fin n → ℝ)} {f : (Fin n → ℂ) → ℂ}
    (hf : ContinuousOn f (TubeDomain V)) (φ : 𝓓(Ω_n, ℝ))
    {y : Fin n → ℝ} (hy : y ∈ V) :
    Integrable
      (fun x : Fin n → ℝ => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ))
      volume := by
  let emb : (Fin n → ℝ) → (Fin n → ℂ) := fun x i => (x i : ℂ) + (y i : ℂ) * Complex.I
  have hemb_cont : Continuous emb := by
    apply continuous_pi
    intro i
    exact (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const
  have hemb_mem : ∀ x : Fin n → ℝ, emb x ∈ TubeDomain V := by
    intro x
    change (fun i => (emb x i).im) ∈ V
    have him : (fun i => (emb x i).im) = y := by
      ext i
      simp [emb]
    rw [him]
    exact hy
  have hf_cont : Continuous (fun x => f (emb x)) :=
    hf.comp_continuous hemb_cont hemb_mem
  have hφ_cont : Continuous (fun x : Fin n → ℝ => (φ x : ℂ)) :=
    Complex.continuous_ofReal.comp φ.contDiff'.continuous
  have hφ_supp : _root_.HasCompactSupport (fun x : Fin n → ℝ => (φ x : ℂ)) :=
    φ.hasCompactSupport'.comp_left Complex.ofReal_zero
  exact (hf_cont.mul hφ_cont).integrable_of_hasCompactSupport hφ_supp.mul_left

lemma HasBoundaryValue.zero (Ω_n : Opens (Fin n → ℝ)) (V : Set (Fin n → ℝ)) :
    HasBoundaryValue Ω_n 0 V 0 := by
  intro φ
  have h_eq : boundaryIntegral Ω_n 0 φ = fun _ => 0 := by
    ext y
    simp [boundaryIntegral]
  rw [h_eq]
  exact tendsto_const_nhds

lemma HasBoundaryValue.neg {Ω_n : Opens (Fin n → ℝ)} {V : Set (Fin n → ℝ)}
    {f : (Fin n → ℂ) → ℂ} {T : 𝓓'(Ω_n, ℂ)}
    (h : HasBoundaryValue Ω_n f V T) :
    HasBoundaryValue Ω_n (-f) V (-T) := by
  intro φ
  have h_eq : boundaryIntegral Ω_n (-f) φ = fun y => -boundaryIntegral Ω_n f φ y := by
    ext y
    dsimp [boundaryIntegral]
    simp_rw [neg_mul]
    exact integral_neg _
  rw [h_eq]
  exact (h φ).neg

noncomputable def smulComplex (Ω : Opens E) (c : ℂ) (T : 𝓓'(Ω, ℂ)) : 𝓓'(Ω, ℂ) :=
  Distribution.mapCLM (ContinuousLinearMap.mul ℝ ℂ c) T

omit [FiniteDimensional ℝ E] in
@[simp]
lemma smulComplex_apply (Ω : Opens E) (c : ℂ) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℝ)) :
    smulComplex Ω c T φ = c * T φ :=
  rfl

lemma HasBoundaryValue.const_mul {Ω_n : Opens (Fin n → ℝ)} {V : Set (Fin n → ℝ)}
    {f : (Fin n → ℂ) → ℂ} {T : 𝓓'(Ω_n, ℂ)} (c : ℂ)
    (h : HasBoundaryValue Ω_n f V T) :
    HasBoundaryValue Ω_n (fun z => c * f z) V (smulComplex Ω_n c T) := by
  intro φ
  have h_eq : boundaryIntegral Ω_n (fun z => c * f z) φ =
      fun y => c * boundaryIntegral Ω_n f φ y := by
    ext y
    dsimp [boundaryIntegral]
    simp_rw [mul_assoc]
    exact integral_const_mul c _
  rw [h_eq]
  exact (h φ).const_mul c

lemma HasBoundaryValue.add {Ω_n : Opens (Fin n → ℝ)} {V : Set (Fin n → ℝ)}
    {f₁ f₂ : (Fin n → ℂ) → ℂ} {T₁ T₂ : 𝓓'(Ω_n, ℂ)}
    (hf₁ : ContinuousOn f₁ (TubeDomain V)) (hf₂ : ContinuousOn f₂ (TubeDomain V))
    (h₁ : HasBoundaryValue Ω_n f₁ V T₁) (h₂ : HasBoundaryValue Ω_n f₂ V T₂) :
    HasBoundaryValue Ω_n (f₁ + f₂) V (T₁ + T₂) := by
  intro φ
  have h_ev : boundaryIntegral Ω_n (f₁ + f₂) φ =ᶠ[nhdsWithin 0 V]
      fun y => boundaryIntegral Ω_n f₁ φ y + boundaryIntegral Ω_n f₂ φ y := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    dsimp [boundaryIntegral]
    simp_rw [add_mul]
    exact integral_add
      (integrable_boundaryIntegrand_of_continuousOn hf₁ φ hy)
      (integrable_boundaryIntegrand_of_continuousOn hf₂ φ hy)
  exact ((h₁ φ).add (h₂ φ)).congr' h_ev.symm

lemma HasBoundaryValue.sub {Ω_n : Opens (Fin n → ℝ)} {V : Set (Fin n → ℝ)}
    {f₁ f₂ : (Fin n → ℂ) → ℂ} {T₁ T₂ : 𝓓'(Ω_n, ℂ)}
    (hf₁ : ContinuousOn f₁ (TubeDomain V)) (hf₂ : ContinuousOn f₂ (TubeDomain V))
    (h₁ : HasBoundaryValue Ω_n f₁ V T₁) (h₂ : HasBoundaryValue Ω_n f₂ V T₂) :
    HasBoundaryValue Ω_n (f₁ - f₂) V (T₁ - T₂) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add hf₁ hf₂.neg h₂.neg

lemma HasBoundaryValue.unique {Ω_n : Opens (Fin n → ℝ)} {V : Set (Fin n → ℝ)}
    (h0 : (0 : Fin n → ℝ) ∈ closure V)
    {f : (Fin n → ℂ) → ℂ} {T₁ T₂ : 𝓓'(Ω_n, ℂ)}
    (h₁ : HasBoundaryValue Ω_n f V T₁) (h₂ : HasBoundaryValue Ω_n f V T₂) :
    T₁ = T₂ := by
  haveI : (nhdsWithin (0 : Fin n → ℝ) V).NeBot := mem_closure_iff_nhdsWithin_neBot.mp h0
  ext φ
  exact tendsto_nhds_unique (h₁ φ) (h₂ φ)

lemma closure_neg_zero_mem {V : Set (Fin n → ℝ)} (h0 : (0 : Fin n → ℝ) ∈ closure V) :
    (0 : Fin n → ℝ) ∈ closure ((fun y : Fin n → ℝ => -y) '' V) := by
  rw [Metric.mem_closure_iff] at h0 ⊢
  intro ε hε
  obtain ⟨u, hu, hdist⟩ := h0 ε hε
  refine ⟨-u, ⟨u, hu, rfl⟩, ?_⟩
  simpa [dist_eq_norm] using hdist

noncomputable def restrictDistribution {Ω₁ Ω₂ : Opens E} (_h : (Ω₁ : Set E) ⊆ (Ω₂ : Set E))
    (T : 𝓓'(Ω₂, ℂ)) : 𝓓'(Ω₁, ℂ) where
  toFun φ := T (TestFunction.monoCLM ℝ φ)
  map_add' f g := by rw [map_add, map_add]
  map_smul' c f := by simp
  cont := T.cont.comp (TestFunction.monoCLM ℝ).cont

omit [FiniteDimensional ℝ E] in
@[simp]
lemma restrictDistribution_apply {Ω₁ Ω₂ : Opens E} (h : (Ω₁ : Set E) ⊆ (Ω₂ : Set E))
    (T : 𝓓'(Ω₂, ℂ)) (φ : 𝓓(Ω₁, ℝ)) :
    restrictDistribution h T φ = T (TestFunction.monoCLM ℝ φ) :=
  rfl

lemma HasBoundaryValue.restrict {Ω₁ Ω₂ : Opens (Fin n → ℝ)}
    (h : (Ω₁ : Set (Fin n → ℝ)) ⊆ (Ω₂ : Set (Fin n → ℝ)))
    {V : Set (Fin n → ℝ)} {f : (Fin n → ℂ) → ℂ} {T : 𝓓'(Ω₂, ℂ)}
    (hT : HasBoundaryValue Ω₂ f V T) :
    HasBoundaryValue Ω₁ f V (restrictDistribution h T) := by
  intro φ
  have h_ord : Ω₁ ≤ Ω₂ := h
  have h_coe : ∀ x, (TestFunction.monoCLM ℝ φ : 𝓓(Ω₂, ℝ)) x = φ x := by
    intro x
    simp [h_ord]
  have h_eq : boundaryIntegral Ω₁ f φ = boundaryIntegral Ω₂ f (TestFunction.monoCLM ℝ φ) := by
    ext y
    dsimp [boundaryIntegral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [h_coe x]
  rw [h_eq, restrictDistribution_apply]
  exact hT (TestFunction.monoCLM ℝ φ)

def realWindow (S : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  { z : Fin n → ℂ | (fun i => (z i).re) ∈ S ∧ (fun i => (z i).im) = 0 }

noncomputable def ofLocallyIntegrableOn (Ω : Opens (Fin n → ℝ))
    (g : (Fin n → ℝ) → ℂ) : 𝓓'(Ω, ℂ) where
  toFun φ := TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) volume g φ
  map_add' := map_add _
  map_smul' := map_smul _
  cont := (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) volume g).cont

lemma ofLocallyIntegrableOn_apply {Ω : Opens (Fin n → ℝ)} {g : (Fin n → ℝ) → ℂ}
    (hg : LocallyIntegrableOn g Ω volume) (φ : 𝓓(Ω, ℝ)) :
    ofLocallyIntegrableOn Ω g φ = ∫ x, g x * (φ x : ℂ) := by
  change TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) volume g φ = _
  rw [TestFunction.integralAgainstBilinCLM_eq_integral hg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change (φ x : ℝ) • g x = g x * (φ x : ℂ)
  rw [Complex.real_smul, mul_comm]

lemma compact_wedge_uniform_bound
    {Ω_n : Opens (Fin n → ℝ)} {V_plus : Set (Fin n → ℝ)}
    {f : (Fin n → ℂ) → ℂ}
    (hf : ContinuousOn f (TubeDomain V_plus ∪ realWindow (Ω_n : Set (Fin n → ℝ))))
    {K : Set (Fin n → ℝ)} (hK_comp : IsCompact K) (hK_sub : K ⊆ (Ω_n : Set (Fin n → ℝ))) :
    ∃ δ > 0, ∃ M ≥ 0, ∀ y ∈ V_plus, ‖y‖ < δ → ∀ x ∈ K,
      ‖f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ M := by
  classical
  let S := TubeDomain V_plus ∪ realWindow (Ω_n : Set (Fin n → ℝ))
  by_cases hK_ne : K.Nonempty
  · have h_pt : ∀ x ∈ K, ∃ δ > 0, ∀ z ∈ S,
        dist z (fun i => (x i : ℂ)) < 2 * δ → ‖f z‖ ≤ ‖f (fun i => (x i : ℂ))‖ + 1 := by
      intro x hx
      have hxS : (fun i => (x i : ℂ)) ∈ S := by
        right
        refine ⟨?_, ?_⟩
        · simpa using hK_sub hx
        · ext i; simp
      have h_cont_at := Metric.continuousWithinAt_iff.mp (hf (fun i => (x i : ℂ)) hxS) 1 zero_lt_one
      rcases h_cont_at with ⟨r, hr_pos, hr⟩
      refine ⟨r / 2, half_pos hr_pos, ?_⟩
      intro z hzS hz_dist
      have hz_r : dist z (fun i => (x i : ℂ)) < r := by linarith
      have h_d := hr hzS hz_r
      rw [dist_eq_norm] at h_d
      have h_tri := norm_sub_norm_le (f z) (f (fun i => (x i : ℂ)))
      linarith
    let δ : (Fin n → ℝ) → ℝ := fun x => if hx : x ∈ K then Classical.choose (h_pt x hx) else 1
    have hδ_pos : ∀ x ∈ K, 0 < δ x := by
      intro x hx
      simpa [δ, hx] using (Classical.choose_spec (h_pt x hx)).1
    have hδ_bound : ∀ x (hx : x ∈ K), ∀ z ∈ S,
        dist z (fun i => (x i : ℂ)) < 2 * δ x → ‖f z‖ ≤ ‖f (fun i => (x i : ℂ))‖ + 1 := by
      intro x hx
      simpa [δ, hx] using (Classical.choose_spec (h_pt x hx)).2
    obtain ⟨t, ht_sub, ht_cover⟩ := hK_comp.elim_nhds_subcover
      (fun p => Metric.ball p (δ p))
      (fun p hp => Metric.ball_mem_nhds p (hδ_pos p hp))
    have ht_ne : t.Nonempty := by
      rcases hK_ne with ⟨x₀, hx₀⟩
      have hx₀_mem := ht_cover hx₀
      rw [mem_iUnion₂] at hx₀_mem
      rcases hx₀_mem with ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    let δ₀ : ℝ := t.inf' ht_ne δ
    have hδ₀_pos : 0 < δ₀ := (Finset.lt_inf'_iff ht_ne).mpr (fun p hp => hδ_pos p (ht_sub p hp))
    let M₀ : ℝ := t.sup' ht_ne (fun p => ‖f (fun i => (p i : ℂ))‖ + 1)
    have hM₀_nonneg : 0 ≤ M₀ := by
      rcases ht_ne with ⟨p₀, hp₀⟩
      have h0 : 0 ≤ ‖f (fun i => (p₀ i : ℂ))‖ + 1 := by positivity
      exact h0.trans (Finset.le_sup' (fun p : Fin n → ℝ => ‖f (fun i => (p i : ℂ))‖ + 1) hp₀)
    refine ⟨δ₀, hδ₀_pos, M₀, hM₀_nonneg, ?_⟩
    intro y hy hynorm x hx
    have hx_cov := ht_cover hx
    rw [mem_iUnion₂] at hx_cov
    rcases hx_cov with ⟨p, hp_t, hx_ball⟩
    let z : Fin n → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I
    have hzS : z ∈ S := by
      left
      change (fun i => (z i).im) ∈ V_plus
      have him : (fun i => (z i).im) = y := by ext i; simp [z]
      rw [him]
      exact hy
    have hz_dist : dist z (fun i => (p i : ℂ)) < 2 * δ p := by
      rw [dist_eq_norm]
      have h_le := norm_real_add_I_sub_le x p y
      have hxp : ‖x - p‖ < δ p := by simpa [dist_eq_norm] using Metric.mem_ball.mp hx_ball
      have hy_le : δ₀ ≤ δ p := Finset.inf'_le δ hp_t
      linarith
    have h_le_p := hδ_bound p (ht_sub p hp_t) z hzS hz_dist
    exact h_le_p.trans (Finset.le_sup' (fun q : Fin n → ℝ => ‖f (fun i => (q i : ℂ))‖ + 1) hp_t)
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne
    refine ⟨1, zero_lt_one, 0, le_rfl, ?_⟩
    intro _ _ _ x hx
    rw [hK_ne] at hx
    exact False.elim hx

lemma hasBoundaryValue_of_continuousOn
    (Ω_n : Opens (Fin n → ℝ)) (V_plus : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (hf : ContinuousOn f (TubeDomain V_plus ∪ realWindow (Ω_n : Set (Fin n → ℝ)))) :
    HasBoundaryValue Ω_n f V_plus
      (ofLocallyIntegrableOn Ω_n (fun x => f (fun i => (x i : ℂ)))) := by
  let f₀ : (Fin n → ℝ) → ℂ := fun x => f (fun i => (x i : ℂ))
  have hf₀_cont : ContinuousOn f₀ Ω_n := by
    have hemb : Continuous (fun x : Fin n → ℝ => fun i => (x i : ℂ)) :=
      continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
    refine hf.comp hemb.continuousOn ?_
    intro x hx
    right
    exact ⟨by simpa using hx, by ext i; simp⟩
  have hf₀_loc : LocallyIntegrableOn f₀ Ω_n volume :=
    hf₀_cont.locallyIntegrableOn Ω_n.isOpen.measurableSet
  have hf_tube : ContinuousOn f (TubeDomain V_plus) :=
    hf.mono (subset_union_left.trans le_rfl)
  intro φ
  rw [ofLocallyIntegrableOn_apply hf₀_loc φ]
  obtain ⟨δ, hδ_pos, M, hM_nonneg, hM_bound⟩ :=
    compact_wedge_uniform_bound hf φ.hasCompactSupport' φ.tsupport_subset'
  let bound : (Fin n → ℝ) → ℝ := fun x => M * ‖φ x‖
  have h_bound_cont : Continuous bound :=
    continuous_const.mul φ.contDiff'.continuous.norm
  have h_bound_supp : _root_.HasCompactSupport bound :=
    (φ.hasCompactSupport'.norm).mul_left
  have h_bound_int : Integrable bound volume :=
    h_bound_cont.integrable_of_hasCompactSupport h_bound_supp
  have h_ev_mem : ∀ᶠ y in nhdsWithin (0 : Fin n → ℝ) V_plus, y ∈ V_plus ∧ ‖y‖ < δ := by
    have h1 : V_plus ∈ nhdsWithin (0 : Fin n → ℝ) V_plus := self_mem_nhdsWithin
    have h2 : Metric.ball (0 : Fin n → ℝ) δ ∈ nhdsWithin (0 : Fin n → ℝ) V_plus :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 hδ_pos)
    filter_upwards [h1, h2] with y hy1 hy2
    exact ⟨hy1, by simpa [dist_eq_norm] using Metric.mem_ball.mp hy2⟩
  refine tendsto_boundaryIntegral_of_dominated V_plus Ω_n f f₀ φ bound h_bound_int ?_ ?_ ?_
  · filter_upwards [h_ev_mem] with y hy
    exact (integrable_boundaryIntegrand_of_continuousOn hf_tube φ hy.1).aestronglyMeasurable
  · filter_upwards [h_ev_mem] with y hy
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport (fun z => φ z)
    · calc
        ‖f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)‖
            = ‖f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ * ‖(φ x : ℂ)‖ := norm_mul _ _
        _ = ‖f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ * ‖φ x‖ := by
            rw [Complex.norm_real]
        _ ≤ M * ‖φ x‖ :=
            mul_le_mul_of_nonneg_right (hM_bound y hy.1 hy.2 x hx) (norm_nonneg _)
    · have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [bound, hφ0]
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ tsupport (fun z => φ z)
    · have hxΩ : x ∈ (Ω_n : Set (Fin n → ℝ)) := φ.tsupport_subset' hx
      let S := TubeDomain V_plus ∪ realWindow (Ω_n : Set (Fin n → ℝ))
      have hxS : (fun i => (x i : ℂ)) ∈ S := by
        right
        exact ⟨by simpa using hxΩ, by ext i; simp⟩
      let emb_x : (Fin n → ℝ) → (Fin n → ℂ) := fun y i => (x i : ℂ) + (y i : ℂ) * Complex.I
      have hemb_cont : Continuous emb_x := by
        apply continuous_pi
        intro i
        exact continuous_const.add
          ((Complex.continuous_ofReal.comp (continuous_apply i)).mul continuous_const)
      have hemb_0 : emb_x 0 = (fun i => (x i : ℂ)) := by ext i; simp [emb_x]
      have hemb_maps : MapsTo emb_x V_plus S := by
        intro y hy
        left
        change (fun i => (emb_x y i).im) ∈ V_plus
        have him : (fun i => (emb_x y i).im) = y := by ext i; simp [emb_x]
        rw [him]
        exact hy
      have h_lim_f : Filter.Tendsto (fun y => f (emb_x y))
          (nhdsWithin 0 V_plus) (nhds (f₀ x)) := by
        have h_cwa : ContinuousWithinAt f S (emb_x 0) := by
          rw [hemb_0]
          exact hf (fun i => (x i : ℂ)) hxS
        have h_comp := h_cwa.tendsto.comp
          (hemb_cont.continuousWithinAt.tendsto_nhdsWithin hemb_maps)
        rw [hemb_0] at h_comp
        exact h_comp
      exact h_lim_f.mul_const (φ x : ℂ)
    · have hφ0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have h_zero : (fun y : Fin n → ℝ =>
          f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)) = fun _ => 0 := by
        ext y
        simp [hφ0]
      rw [h_zero, hφ0, Complex.ofReal_zero, mul_zero]
      exact tendsto_const_nhds

lemma eqOn_zero_of_integral_testFunction_eq_zero
    {Ω_n : Opens (Fin n → ℝ)} {U : Opens (Fin n → ℝ)}
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    {g : (Fin n → ℝ) → ℂ} (hg_cont : ContinuousOn g U)
    (h_int : ∀ φ : 𝓓(Ω_n, ℝ), tsupport (fun x => φ x) ⊆ U → ∫ x, g x * (φ x : ℂ) = 0) :
    EqOn g 0 U := by
  have hg_loc : LocallyIntegrableOn g U volume :=
    hg_cont.locallyIntegrableOn U.isOpen.measurableSet
  have h_ae : ∀ᵐ x ∂volume, x ∈ (U : Set (Fin n → ℝ)) → g x = 0 := by
    refine U.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hg_loc ?_
    intro ψ hψ_diff hψ_comp hψ_supp
    let φ : 𝓓(Ω_n, ℝ) := ⟨ψ, hψ_diff, hψ_comp, hψ_supp.trans hU⟩
    have h_eq : (∫ x, ψ x • g x) = ∫ x, g x * (φ x : ℂ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change ψ x • g x = g x * (ψ x : ℂ)
      rw [Complex.real_smul, mul_comm]
    rw [h_eq]
    exact h_int φ hψ_supp
  intro x₀ hx₀
  by_contra hne
  have hg_at : ContinuousAt g x₀ := hg_cont.continuousAt (U.isOpen.mem_nhds hx₀)
  have hpos : 0 < ‖g x₀‖ / 2 := half_pos (norm_pos_iff.mpr hne)
  have h_nhds : {x | dist (g x) (g x₀) < ‖g x₀‖ / 2} ∩ (U : Set (Fin n → ℝ)) ∈ nhds x₀ :=
    Filter.inter_mem (Metric.continuousAt_iff'.mp hg_at _ hpos) (U.isOpen.mem_nhds hx₀)
  rcases Metric.mem_nhds_iff.mp h_nhds with ⟨r, hr_pos, hr_sub⟩
  have h_null : volume (Metric.ball x₀ r) = 0 := by
    refine measure_mono_null (fun x hx => ?_) ((ae_iff).mp h_ae)
    rcases hr_sub hx with ⟨hx_dist, hx_U⟩
    change dist (g x) (g x₀) < ‖g x₀‖ / 2 at hx_dist
    intro h_imp
    have hgx0 : g x = 0 := h_imp hx_U
    rw [hgx0, dist_zero_left] at hx_dist
    linarith
  have h_ne_zero : volume (Metric.ball x₀ r) ≠ 0 :=
    Metric.isOpen_ball.measure_ne_zero volume (Metric.nonempty_ball.mpr hr_pos)
  exact h_ne_zero h_null

lemma integrable_mul_testFunction_of_continuousOn
    {Ω_n : Opens (Fin n → ℝ)} {U : Opens (Fin n → ℝ)}
    {g : (Fin n → ℝ) → ℂ} (hg_cont : ContinuousOn g U)
    (φ : 𝓓(Ω_n, ℝ)) (hφ : tsupport (fun x => φ x) ⊆ U) :
    Integrable (fun x : Fin n → ℝ => g x * (φ x : ℂ)) volume := by
  have hφ_cont : Continuous (fun x : Fin n → ℝ => (φ x : ℂ)) :=
    Complex.continuous_ofReal.comp φ.contDiff'.continuous
  have h_prod_cont : Continuous (fun x : Fin n → ℝ => g x * (φ x : ℂ)) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxU : x ∈ (U : Set (Fin n → ℝ))
    · exact (hg_cont.continuousAt (U.isOpen.mem_nhds hxU)).mul hφ_cont.continuousAt
    · have hx_not : x ∉ tsupport (fun z => φ z) := fun hx_supp => hxU (hφ hx_supp)
      have h_compl_open : IsOpen ((tsupport (fun z => φ z))ᶜ) :=
        (isClosed_tsupport _).isOpen_compl
      have h_ev : (fun y : Fin n → ℝ => g y * (φ y : ℂ)) =ᶠ[nhds x] 0 := by
        filter_upwards [h_compl_open.mem_nhds hx_not] with y hy
        have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [hφy]
      exact continuousAt_const.congr h_ev.symm
  have hφ_supp : _root_.HasCompactSupport (fun x : Fin n → ℝ => (φ x : ℂ)) :=
    φ.hasCompactSupport'.comp_left Complex.ofReal_zero
  exact h_prod_cont.integrable_of_hasCompactSupport hφ_supp.mul_left

lemma eqOn_of_equalOn_continuousOn
    {Ω_n : Opens (Fin n → ℝ)} {U : Opens (Fin n → ℝ)}
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    {g₁ g₂ : (Fin n → ℝ) → ℂ}
    (hg₁_loc : LocallyIntegrableOn g₁ Ω_n volume)
    (hg₂_loc : LocallyIntegrableOn g₂ Ω_n volume)
    (hg₁_cont : ContinuousOn g₁ U) (hg₂_cont : ContinuousOn g₂ U)
    (h_eq : EqualOn Ω_n (ofLocallyIntegrableOn Ω_n g₁) (ofLocallyIntegrableOn Ω_n g₂) U hU) :
    EqOn g₁ g₂ U := by
  have h_diff_zero : EqOn (g₁ - g₂) 0 U := by
    refine eqOn_zero_of_integral_testFunction_eq_zero hU (hg₁_cont.sub hg₂_cont) ?_
    intro φ hφ
    have h12 := h_eq φ hφ
    rw [ofLocallyIntegrableOn_apply hg₁_loc φ, ofLocallyIntegrableOn_apply hg₂_loc φ] at h12
    have h_sub : (∫ x, (g₁ - g₂) x * (φ x : ℂ)) =
        (∫ x, g₁ x * (φ x : ℂ)) - (∫ x, g₂ x * (φ x : ℂ)) := by
      simp_rw [Pi.sub_apply, sub_mul]
      exact integral_sub
        (integrable_mul_testFunction_of_continuousOn hg₁_cont φ hφ)
        (integrable_mul_testFunction_of_continuousOn hg₂_cont φ hφ)
    rw [h_sub, h12, sub_self]
  intro x hx
  exact sub_eq_zero.mp (h_diff_zero hx)

lemma eqOn_boundary_of_hasBoundaryValue_equalOn
    {Ω_n : Opens (Fin n → ℝ)} {U : Opens (Fin n → ℝ)}
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    {V_plus V_minus : Set (Fin n → ℝ)}
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    {f_plus f_minus : (Fin n → ℂ) → ℂ}
    (hf_plus_cont : ContinuousOn f_plus (TubeDomain V_plus ∪ realWindow (U : Set (Fin n → ℝ))))
    (hf_minus_cont : ContinuousOn f_minus (TubeDomain V_minus ∪ realWindow (U : Set (Fin n → ℝ))))
    {T_plus T_minus : 𝓓'(Ω_n, ℂ)}
    (hT_plus : HasBoundaryValue Ω_n f_plus V_plus T_plus)
    (hT_minus : HasBoundaryValue Ω_n f_minus V_minus T_minus)
    (h_match : EqualOn Ω_n T_plus T_minus U hU) :
    ∀ x ∈ U, f_plus (fun i => (x i : ℂ)) = f_minus (fun i => (x i : ℂ)) := by
  have h0_minus : (0 : Fin n → ℝ) ∈ closure V_minus := by
    rw [h_opposite]
    exact closure_neg_zero_mem h0
  let g_plus : (Fin n → ℝ) → ℂ := fun x => f_plus (fun i => (x i : ℂ))
  let g_minus : (Fin n → ℝ) → ℂ := fun x => f_minus (fun i => (x i : ℂ))
  have hg_plus_cont : ContinuousOn g_plus U := by
    refine hf_plus_cont.comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn ?_
    intro x hx
    right
    exact ⟨by simpa using hx, by ext i; simp⟩
  have hg_minus_cont : ContinuousOn g_minus U := by
    refine hf_minus_cont.comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn ?_
    intro x hx
    right
    exact ⟨by simpa using hx, by ext i; simp⟩
  have h_bv_p1 : HasBoundaryValue U f_plus V_plus (restrictDistribution hU T_plus) :=
    hT_plus.restrict hU
  have h_bv_p2 : HasBoundaryValue U f_plus V_plus (ofLocallyIntegrableOn U g_plus) :=
    hasBoundaryValue_of_continuousOn U V_plus f_plus hf_plus_cont
  have h_eq_p : restrictDistribution hU T_plus = ofLocallyIntegrableOn U g_plus :=
    HasBoundaryValue.unique h0 h_bv_p1 h_bv_p2
  have h_bv_m1 : HasBoundaryValue U f_minus V_minus (restrictDistribution hU T_minus) :=
    hT_minus.restrict hU
  have h_bv_m2 : HasBoundaryValue U f_minus V_minus (ofLocallyIntegrableOn U g_minus) :=
    hasBoundaryValue_of_continuousOn U V_minus f_minus hf_minus_cont
  have h_eq_m : restrictDistribution hU T_minus = ofLocallyIntegrableOn U g_minus :=
    HasBoundaryValue.unique h0_minus h_bv_m1 h_bv_m2
  have h_eq_U : EqualOn U (ofLocallyIntegrableOn U g_plus) (ofLocallyIntegrableOn U g_minus)
      U subset_rfl := by
    intro φ _hφ
    rw [← h_eq_p, ← h_eq_m, restrictDistribution_apply, restrictDistribution_apply]
    have h_ord : U ≤ Ω_n := hU
    have h_fn : (fun x => (TestFunction.monoCLM ℝ φ : 𝓓(Ω_n, ℝ)) x) = fun x => φ x := by
      ext x
      simp [h_ord]
    refine h_match (TestFunction.monoCLM ℝ φ) ?_
    rw [h_fn]
    exact φ.tsupport_subset'
  exact eqOn_of_equalOn_continuousOn subset_rfl
    (hg_plus_cont.locallyIntegrableOn U.isOpen.measurableSet)
    (hg_minus_cont.locallyIntegrableOn U.isOpen.measurableSet)
    hg_plus_cont hg_minus_cont h_eq_U

end BoundaryValueAPI

section TotallyRealAndConcreteEOW

lemma analyticOnNhd_eqOn_zero_polydisc_step
    {F : (Fin n → ℂ) → ℂ} {x₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hF : AnalyticOnNhd ℂ F (Metric.ball (fun i => (x₀ i : ℂ)) r))
    (hF_real : ∀ x ∈ Metric.ball x₀ r, F (fun i => (x i : ℂ)) = 0) :
    ∀ m : ℕ, m ≤ n → ∀ z ∈ Metric.ball (fun i => (x₀ i : ℂ)) r,
      (∀ i : Fin n, m ≤ i.1 → (z i).im = 0) → F z = 0 := by
  intro m hm
  induction m with
  | zero =>
    intro z hz hz_im
    let x : Fin n → ℝ := fun i => (z i).re
    have hx_ball : x ∈ Metric.ball x₀ r := re_mem_ball_of_mem_ball x₀ r z hz
    have hzx : (fun i => (x i : ℂ)) = z := by
      ext i
      exact Complex.ext rfl (hz_im i (Nat.zero_le i.1)).symm
    rw [← hzx]
    exact hF_real x hx_ball
  | succ m ih =>
    have hm_lt : m < n := hm
    let idx : Fin n := ⟨m, hm_lt⟩
    intro z hz hz_im
    let D : Set ℂ := Metric.ball (x₀ idx : ℂ) r
    let upd : ℂ → (Fin n → ℂ) := fun w => Function.update z idx w
    have hupd_diff : Differentiable ℂ upd := by
      rw [differentiable_pi]
      intro i
      by_cases hi : i = idx
      · subst hi
        simp [upd]
      · simp [upd, hi]
    have hupd_maps : ∀ w ∈ D, upd w ∈ Metric.ball (fun i => (x₀ i : ℂ)) r := by
      intro w hw
      rw [Metric.mem_ball, dist_pi_lt_iff hr] at hz ⊢
      intro i
      by_cases hi : i = idx
      · subst hi
        simpa [upd] using Metric.mem_ball.mp hw
      · simpa [upd, hi] using hz i
    let g : ℂ → ℂ := fun w => F (upd w)
    have hg_diff : DifferentiableOn ℂ g D :=
      hF.differentiableOn.comp hupd_diff.differentiableOn hupd_maps
    have hg_an : AnalyticOnNhd ℂ g D := hg_diff.analyticOnNhd Metric.isOpen_ball
    have hD_conn : IsPreconnected D := (convex_ball (x₀ idx : ℂ) r).isPreconnected
    have hc_mem : (x₀ idx : ℂ) ∈ D := Metric.mem_ball_self hr
    have hg_freq : ∃ᶠ w in nhdsWithin (x₀ idx : ℂ) {(x₀ idx : ℂ)}ᶜ, g w = 0 := by
      rw [Filter.frequently_iff]
      intro V hV
      rw [mem_nhdsWithin] at hV
      rcases hV with ⟨O, hO_open, hcO, hOV⟩
      rcases Metric.isOpen_iff.mp hO_open (x₀ idx : ℂ) hcO with ⟨δ, hδ_pos, hδO⟩
      let ε : ℝ := min (r / 2) (δ / 2)
      have hε_pos : 0 < ε := lt_min (half_pos hr) (half_pos hδ_pos)
      let t : ℝ := x₀ idx + ε
      let w₀ : ℂ := (t : ℂ)
      have hw₀_O : w₀ ∈ O := by
        apply hδO
        rw [Metric.mem_ball, dist_eq_norm]
        have h_eq : w₀ - (x₀ idx : ℂ) = (ε : ℂ) := by simp [w₀, t]
        rw [h_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
        have hle : ε ≤ δ / 2 := min_le_right _ _
        linarith
      have hw₀_ne : w₀ ≠ (x₀ idx : ℂ) := by
        intro h_eq
        have h_re : t = x₀ idx := by simpa [w₀] using congrArg Complex.re h_eq
        linarith
      have hw₀_V : w₀ ∈ V := hOV ⟨hw₀_O, hw₀_ne⟩
      have hw₀_D : w₀ ∈ D := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_eq : w₀ - (x₀ idx : ℂ) = (ε : ℂ) := by simp [w₀, t]
        rw [h_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
        have hle : ε ≤ r / 2 := min_le_left _ _
        linarith
      have hg_w₀ : g w₀ = 0 := by
        refine ih (Nat.le_of_succ_le hm) (upd w₀) (hupd_maps w₀ hw₀_D) ?_
        intro i hi_ge
        by_cases hi : i = idx
        · subst hi
          simp [upd, w₀]
        · have hi_ne : i.1 ≠ m := fun hval => hi (Fin.ext hval)
          have hi_succ : m + 1 ≤ i.1 := Nat.succ_le_of_lt (lt_of_le_of_ne hi_ge hi_ne.symm)
          simpa [upd, hi] using hz_im i hi_succ
      exact ⟨w₀, hw₀_V, hg_w₀⟩
    have hg_zero : EqOn g 0 D :=
      hg_an.eqOn_zero_of_preconnected_of_frequently_eq_zero hD_conn hc_mem hg_freq
    have hz_idx_D : z idx ∈ D := by
      rw [Metric.mem_ball]
      exact (dist_pi_lt_iff hr).mp (Metric.mem_ball.mp hz) idx
    have h_upd_self : upd (z idx) = z := Function.update_eq_self idx z
    have h_res := hg_zero hz_idx_D
    dsimp [g] at h_res
    rwa [h_upd_self] at h_res

theorem analyticOnNhd_eqOn_zero_of_real_open
    {F : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)}
    (hW_open : IsOpen W) (hW_conn : IsPreconnected W)
    (hF : AnalyticOnNhd ℂ F W)
    {U : Set (Fin n → ℝ)} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_sub : ∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W)
    (hF_real : ∀ x ∈ U, F (fun i => (x i : ℂ)) = 0) :
    EqOn F 0 W := by
  rcases hU_ne with ⟨x₀, hx₀⟩
  let z₀ : Fin n → ℂ := fun i => (x₀ i : ℂ)
  have hz₀_W : z₀ ∈ W := hU_sub x₀ hx₀
  rcases Metric.isOpen_iff.mp hU_open x₀ hx₀ with ⟨r₁, hr₁_pos, hr₁_sub⟩
  rcases Metric.isOpen_iff.mp hW_open z₀ hz₀_W with ⟨r₂, hr₂_pos, hr₂_sub⟩
  let r : ℝ := min r₁ r₂
  have hr_pos : 0 < r := lt_min hr₁_pos hr₂_pos
  have h_ball_W : Metric.ball z₀ r ⊆ W :=
    (Metric.ball_subset_ball (min_le_right r₁ r₂)).trans hr₂_sub
  have h_ball_U : Metric.ball x₀ r ⊆ U :=
    (Metric.ball_subset_ball (min_le_left r₁ r₂)).trans hr₁_sub
  have hF_ball : AnalyticOnNhd ℂ F (Metric.ball z₀ r) := hF.mono h_ball_W
  have hF_real_ball : ∀ x ∈ Metric.ball x₀ r, F (fun i => (x i : ℂ)) = 0 :=
    fun x hx => hF_real x (h_ball_U hx)
  have h_step := analyticOnNhd_eqOn_zero_polydisc_step hr_pos hF_ball hF_real_ball n le_rfl
  have h_ev : F =ᶠ[nhds z₀] 0 := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr_pos] with z hz
    exact h_step z hz (fun i hi => absurd hi (not_le_of_gt i.2))
  exact hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hW_conn hz₀_W h_ev

theorem analyticOnNhd_eqOn_of_real_open
    {F₁ F₂ : (Fin n → ℂ) → ℂ} {W : Set (Fin n → ℂ)}
    (hW_open : IsOpen W) (hW_conn : IsPreconnected W)
    (hF₁ : AnalyticOnNhd ℂ F₁ W) (hF₂ : AnalyticOnNhd ℂ F₂ W)
    {U : Set (Fin n → ℝ)} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_sub : ∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W)
    (h_real : ∀ x ∈ U, F₁ (fun i => (x i : ℂ)) = F₂ (fun i => (x i : ℂ))) :
    EqOn F₁ F₂ W := by
  have h_zero : EqOn (F₁ - F₂) 0 W :=
    analyticOnNhd_eqOn_zero_of_real_open hW_open hW_conn (hF₁.sub hF₂) hU_open hU_ne hU_sub
      (fun x hx => sub_eq_zero.mpr (h_real x hx))
  intro z hz
  exact sub_eq_zero.mp (h_zero hz)

noncomputable def localEpsteinData_of_nhds_extension
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ)
    (h_ext : ∃ N ∈ nhds (fun i => (x i : ℂ)), ∃ G : (Fin n → ℂ) → ℂ,
      IsOpen N ∧ DifferentiableOn ℂ G N ∧
      EqOn G f_plus (N ∩ TubeDomain V_plus) ∧
      EqOn G f_minus (N ∩ TubeDomain V_minus)) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  let N := Classical.choose h_ext
  have hN_spec := Classical.choose_spec h_ext
  let hN_mem := hN_spec.1
  let G := Classical.choose hN_spec.2
  have hG_spec := Classical.choose_spec hN_spec.2
  have h_ex_r : ∃ r > 0, Metric.ball (fun i => (x i : ℂ)) r ⊆ N :=
    Metric.mem_nhds_iff.mp hN_mem
  let r := Classical.choose h_ex_r
  have hr_spec := Classical.choose_spec h_ex_r
  refine ⟨r, hr_spec.1, G, hG_spec.2.1.mono hr_spec.2, ?_, ?_⟩
  · exact hG_spec.2.2.1.mono (inter_subset_inter_left _ hr_spec.2)
  · exact hG_spec.2.2.2.mono (inter_subset_inter_left _ hr_spec.2)

lemma disjoint_opposite_of_convex_zero_not_mem
    {V_plus V_minus : Set (Fin n → ℝ)}
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (hV_conv : Convex ℝ V_plus)
    (h0_not : (0 : Fin n → ℝ) ∉ V_plus) :
    Disjoint V_plus V_minus := by
  rw [Set.disjoint_left]
  intro y hy_p hy_m
  rw [h_opposite] at hy_m
  rcases hy_m with ⟨u, hu_p, rfl⟩
  have h_mid : (1 / 2 : ℝ) • (-u) + (1 / 2 : ℝ) • u ∈ V_plus :=
    hV_conv hy_p hu_p (by positivity) (by positivity) (by norm_num)
  have h_zero : (1 / 2 : ℝ) • (-u) + (1 / 2 : ℝ) • u = 0 := by
    ext i
    simp [Pi.add_apply, Pi.smul_apply]
  rw [h_zero] at h_mid
  exact h0_not h_mid

noncomputable def glueWedgeFun
    (V_plus : Set (Fin n → ℝ)) (f_plus f_minus : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) : ℂ :=
  open Classical in
  if z ∈ TubeDomain V_plus then f_plus z
  else if (fun i => (z i).im) = 0 then f_plus z
  else f_minus z

lemma glueWedgeFun_eq_plus {V_plus : Set (Fin n → ℝ)} {f_plus f_minus : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hz : z ∈ TubeDomain V_plus) :
    glueWedgeFun V_plus f_plus f_minus z = f_plus z := by
  simp [glueWedgeFun, hz]

lemma glueWedgeFun_eq_real {V_plus : Set (Fin n → ℝ)} {f_plus f_minus : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hz : (fun i => (z i).im) = 0) :
    glueWedgeFun V_plus f_plus f_minus z = f_plus z := by
  unfold glueWedgeFun
  split_ifs <;> rfl

lemma glueWedgeFun_eq_minus {V_plus V_minus : Set (Fin n → ℝ)}
    (h_disj : Disjoint V_plus V_minus) (h0_minus : (0 : Fin n → ℝ) ∉ V_minus)
    {f_plus f_minus : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (hz : z ∈ TubeDomain V_minus) :
    glueWedgeFun V_plus f_plus f_minus z = f_minus z := by
  have hz_not_p : z ∉ TubeDomain V_plus :=
    Set.disjoint_left.mp h_disj.symm hz
  have hz_im_ne : (fun i => (z i).im) ≠ 0 := by
    intro h0
    have : (fun i => (z i).im) ∈ V_minus := hz
    rw [h0] at this
    exact h0_minus this
  simp [glueWedgeFun, hz_not_p, hz_im_ne]

lemma continuousOn_glueWedgeFun
    {V_plus V_minus U : Set (Fin n → ℝ)}
    (hV_plus_open : IsOpen V_plus) (hV_minus_open : IsOpen V_minus)
    (h_disj : Disjoint V_plus V_minus) (h0_minus : (0 : Fin n → ℝ) ∉ V_minus)
    {f_plus f_minus : (Fin n → ℂ) → ℂ}
    (hf_plus_cont : ContinuousOn f_plus (TubeDomain V_plus ∪ realWindow U))
    (hf_minus_cont : ContinuousOn f_minus (TubeDomain V_minus ∪ realWindow U))
    (h_eq_U : ∀ x ∈ U, f_plus (fun i => (x i : ℂ)) = f_minus (fun i => (x i : ℂ))) :
    ContinuousOn (glueWedgeFun V_plus f_plus f_minus) (WedgeDomain V_plus V_minus U) := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  rcases hz with (hz_pm | hz_real)
  · rcases hz_pm with (hz_p | hz_m)
    · have h_open_p : IsOpen (TubeDomain V_plus) := isOpen_TubeDomain hV_plus_open
      rcases Metric.isOpen_iff.mp h_open_p z hz_p with ⟨r₁, hr₁_pos, hr₁_sub⟩
      have h_cwa := Metric.continuousWithinAt_iff.mp
        (hf_plus_cont z (Or.inl hz_p)) ε hε
      rcases h_cwa with ⟨r₂, hr₂_pos, hr₂⟩
      refine ⟨min r₁ r₂, lt_min hr₁_pos hr₂_pos, ?_⟩
      intro w _hw hw_dist
      have hw_p : w ∈ TubeDomain V_plus :=
        hr₁_sub (Metric.mem_ball.mpr (hw_dist.trans_le (min_le_left _ _)))
      rw [glueWedgeFun_eq_plus hw_p, glueWedgeFun_eq_plus hz_p]
      exact hr₂ (Or.inl hw_p) (hw_dist.trans_le (min_le_right _ _))
    · have h_open_m : IsOpen (TubeDomain V_minus) := isOpen_TubeDomain hV_minus_open
      rcases Metric.isOpen_iff.mp h_open_m z hz_m with ⟨r₁, hr₁_pos, hr₁_sub⟩
      have h_cwa := Metric.continuousWithinAt_iff.mp
        (hf_minus_cont z (Or.inl hz_m)) ε hε
      rcases h_cwa with ⟨r₂, hr₂_pos, hr₂⟩
      refine ⟨min r₁ r₂, lt_min hr₁_pos hr₂_pos, ?_⟩
      intro w _hw hw_dist
      have hw_m : w ∈ TubeDomain V_minus :=
        hr₁_sub (Metric.mem_ball.mpr (hw_dist.trans_le (min_le_left _ _)))
      rw [glueWedgeFun_eq_minus h_disj h0_minus hw_m,
          glueWedgeFun_eq_minus h_disj h0_minus hz_m]
      exact hr₂ (Or.inl hw_m) (hw_dist.trans_le (min_le_right _ _))
  · have hz_rw : z ∈ realWindow U := hz_real
    have hz_eq_re : (fun i => (((z i).re : ℝ) : ℂ)) = z := by
      ext i
      have him : (z i).im = 0 := congrFun hz_real.2 i
      exact Complex.ext rfl him.symm
    have hz_pm_eq : f_plus z = f_minus z := by
      rw [← hz_eq_re]
      exact h_eq_U (fun i => (z i).re) hz_real.1
    rcases Metric.continuousWithinAt_iff.mp (hf_plus_cont z (Or.inr hz_rw)) ε hε with
      ⟨r₁, hr₁_pos, hr₁⟩
    rcases Metric.continuousWithinAt_iff.mp (hf_minus_cont z (Or.inr hz_rw)) ε hε with
      ⟨r₂, hr₂_pos, hr₂⟩
    refine ⟨min r₁ r₂, lt_min hr₁_pos hr₂_pos, ?_⟩
    intro w hw hw_dist
    rw [glueWedgeFun_eq_real hz_real.2]
    rcases hw with ((hw_p | hw_m) | hw_r)
    · rw [glueWedgeFun_eq_plus hw_p]
      exact hr₁ (Or.inl hw_p) (hw_dist.trans_le (min_le_left _ _))
    · rw [glueWedgeFun_eq_minus h_disj h0_minus hw_m, hz_pm_eq]
      exact hr₂ (Or.inl hw_m) (hw_dist.trans_le (min_le_right _ _))
    · rw [glueWedgeFun_eq_real hw_r.2]
      exact hr₁ (Or.inr hw_r) (hw_dist.trans_le (min_le_left _ _))

theorem local_eow_1d_of_continuous_boundary
    (Ω_1 : Opens (Fin 1 → ℝ))
    (V_plus V_minus : Set (Fin 1 → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_conv : Convex ℝ V_plus)
    (hV_ne : V_plus.Nonempty)
    (h0_not_mem : (0 : Fin 1 → ℝ) ∉ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ c : ℝ, c > 0 → (fun i => c * v i) ∈ V_plus)
    (f_plus f_minus : (Fin 1 → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (U : Opens (Fin 1 → ℝ)) (hU : (U : Set (Fin 1 → ℝ)) ⊆ Ω_1)
    (hf_plus_cont : ContinuousOn f_plus (TubeDomain V_plus ∪ realWindow (U : Set (Fin 1 → ℝ))))
    (hf_minus_cont : ContinuousOn f_minus (TubeDomain V_minus ∪ realWindow (U : Set (Fin 1 → ℝ))))
    (T_plus : 𝓓'(Ω_1, ℂ)) (hT_plus : HasBoundaryValue Ω_1 f_plus V_plus T_plus)
    (T_minus : 𝓓'(Ω_1, ℂ)) (hT_minus : HasBoundaryValue Ω_1 f_minus V_minus T_minus)
    (h_match : EqualOn Ω_1 T_plus T_minus U hU) :
    ∃ (W : Opens (Fin 1 → ℂ)) (F : (Fin 1 → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin 1 → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin 1 → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin 1 → ℂ)) ∩ TubeDomain V_minus) := by
  have h0 : (0 : Fin 1 → ℝ) ∈ closure V_plus := by
    rcases hV_ne with ⟨v, hv⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    let c : ℝ := ε / (2 * (‖v‖ + 1))
    have hc_pos : 0 < c := by positivity
    refine ⟨fun i => c * v i, hV_plus_cone v hv c hc_pos, ?_⟩
    rw [dist_zero_left]
    have h_norm : ‖fun i : Fin 1 => c * v i‖ = c * ‖v‖ := by
      change ‖c • v‖ = c * ‖v‖
      rw [norm_smul, Real.norm_of_nonneg hc_pos.le]
    rw [h_norm]
    have h_lt : c * ‖v‖ < ε := by
      dsimp [c]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    exact h_lt
  have h_disj : Disjoint V_plus V_minus :=
    disjoint_opposite_of_convex_zero_not_mem h_opposite hV_plus_conv h0_not_mem
  have h0_minus : (0 : Fin 1 → ℝ) ∉ V_minus := by
    rw [h_opposite]
    rintro ⟨u, hu, hu0⟩
    have hu_zero : u = 0 := neg_eq_zero.mp hu0
    rw [hu_zero] at hu
    exact h0_not_mem hu
  have hV_minus_open : IsOpen V_minus := by
    rw [h_opposite]
    exact isOpen_neg_image hV_plus_open
  have h_eq_U : ∀ x ∈ U, f_plus (fun i => (x i : ℂ)) = f_minus (fun i => (x i : ℂ)) :=
    eqOn_boundary_of_hasBoundaryValue_equalOn hU h_opposite h0
      hf_plus_cont hf_minus_cont hT_plus hT_minus h_match
  let fg := glueWedgeFun V_plus f_plus f_minus
  have hfg_cont :
      ContinuousOn fg (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U) := by
    rw [← h_opposite]
    exact continuousOn_glueWedgeFun hV_plus_open hV_minus_open h_disj h0_minus
      hf_plus_cont hf_minus_cont h_eq_U
  have hfg_plus : DifferentiableOn ℂ fg (TubeDomain V_plus) :=
    hf_plus_holo.congr (fun _ hz => glueWedgeFun_eq_plus hz)
  have hfg_minus : DifferentiableOn ℂ fg (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)) := by
    rw [← h_opposite]
    exact hf_minus_holo.congr (fun _ hz => glueWedgeFun_eq_minus h_disj h0_minus hz)
  have h_ext_all : ∀ x ∈ (U : Set (Fin 1 → ℝ)),
      ∃ N ∈ nhds (fun i => (x i : ℂ)), ∃ G : (Fin 1 → ℂ) → ℂ,
        IsOpen N ∧ DifferentiableOn ℂ G N ∧
        EqOn G f_plus (N ∩ TubeDomain V_plus) ∧
        EqOn G f_minus (N ∩ TubeDomain V_minus) := by
    intro x hx
    rcases Metric.isOpen_iff.mp U.isOpen x hx with ⟨r₁, hr₁_pos, hr₁_sub⟩
    rcases exists_local_analytic_extension_cauchy_1d V_plus U hV_plus_open hV_plus_cone
      hV_ne U.isOpen fg hfg_cont hfg_plus hfg_minus x hx r₁ hr₁_pos hr₁_sub with
      ⟨Fx, hFx_an, hFx_eq⟩
    rcases hFx_an.eventually_analyticAt.exists_mem with ⟨N₀, hN₀_nhds, hN₀⟩
    rcases Metric.mem_nhds_iff.mp hN₀_nhds with ⟨r₂, hr₂_pos, hr₂_sub⟩
    let ρ : ℝ := min r₁ r₂
    have hρ_pos : 0 < ρ := lt_min hr₁_pos hr₂_pos
    let B := Metric.ball (fun i => (x i : ℂ)) ρ
    have hB_diff : DifferentiableOn ℂ Fx B := by
      intro z hz
      have hzN₀ : z ∈ N₀ := hr₂_sub (Metric.ball_subset_ball (min_le_right r₁ r₂) hz)
      exact (hN₀ z hzN₀).differentiableAt.differentiableWithinAt
    refine ⟨B, Metric.ball_mem_nhds _ hρ_pos, Fx, Metric.isOpen_ball, hB_diff, ?_, ?_⟩
    · intro z hz
      have hz_r₁ : z ∈ Metric.ball (fun i => (x i : ℂ)) r₁ :=
        Metric.ball_subset_ball (min_le_left r₁ r₂) hz.1
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U :=
        Or.inl (Or.inl hz.2)
      rw [hFx_eq ⟨hz_r₁, hz_wedge⟩]
      exact glueWedgeFun_eq_plus hz.2
    · intro z hz
      have hz_r₁ : z ∈ Metric.ball (fun i => (x i : ℂ)) r₁ :=
        Metric.ball_subset_ball (min_le_left r₁ r₂) hz.1
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U := by
        rw [← h_opposite]
        exact Or.inl (Or.inr hz.2)
      rw [hFx_eq ⟨hz_r₁, hz_wedge⟩]
      exact glueWedgeFun_eq_minus h_disj h0_minus hz.2
  let data : ∀ x ∈ (U : Set (Fin 1 → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x :=
    fun x hx => localEpsteinData_of_nhds_extension V_plus V_minus f_plus f_minus x
      (h_ext_all x hx)
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 f_plus f_minus U data

lemma local_eow_unique_on_preconnected
    {V_plus : Set (Fin n → ℝ)} (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    {f_plus : (Fin n → ℂ) → ℂ}
    {W : Set (Fin n → ℂ)} (hW_open : IsOpen W) (hW_conn : IsPreconnected W)
    {U : Set (Fin n → ℝ)} (hU_ne : U.Nonempty)
    (hU_sub : ∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W)
    {F₁ F₂ : (Fin n → ℂ) → ℂ}
    (hF₁ : AnalyticOnNhd ℂ F₁ W) (hF₂ : AnalyticOnNhd ℂ F₂ W)
    (h₁ : EqOn F₁ f_plus (W ∩ TubeDomain V_plus))
    (h₂ : EqOn F₂ f_plus (W ∩ TubeDomain V_plus)) :
    EqOn F₁ F₂ W := by
  rcases hU_ne with ⟨x₀, hx₀⟩
  have hz₀_W : (fun i => (x₀ i : ℂ)) ∈ W := hU_sub x₀ hx₀
  rcases Metric.isOpen_iff.mp hW_open _ hz₀_W with ⟨r, hr_pos, hr_sub⟩
  have h_ne : (Metric.ball (fun i => (x₀ i : ℂ)) r ∩
      Metric.ball (fun i => (x₀ i : ℂ)) r ∩ TubeDomain V_plus).Nonempty :=
    inter_balls_tube_nonempty_of_mem_inter_real V_plus h0 x₀ x₀ r r x₀
      ⟨Metric.mem_ball_self hr_pos, Metric.mem_ball_self hr_pos⟩
  rcases h_ne with ⟨w₀, hw₀_b, hw₀_t⟩
  have hw₀_W : w₀ ∈ W := hr_sub hw₀_b.1
  have h_open_inter : IsOpen (W ∩ TubeDomain V_plus) :=
    hW_open.inter (isOpen_TubeDomain hV_plus_open)
  have h_ev : F₁ =ᶠ[nhds w₀] F₂ := by
    filter_upwards [h_open_inter.mem_nhds ⟨hw₀_W, hw₀_t⟩] with z hz
    rw [h₁ hz, h₂ hz]
  exact hF₁.eqOn_of_preconnected_of_eventuallyEq hF₂ hW_conn hw₀_W h_ev

end TotallyRealAndConcreteEOW

section TemperedBridge

open scoped ContDiff

noncomputable def contDiffSupportedInToSchwartzLM (K : Compacts E) :
    𝓓_{K}(E, ℝ) →ₗ[ℝ] SchwartzMap E ℂ where
  toFun f :=
    (f.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp f.contDiff)
  map_add' f g := by
    ext x
    simp
  map_smul' c f := by
    ext x
    simp [Complex.real_smul]

omit [FiniteDimensional ℝ E] in
lemma contDiffSupportedInToSchwartzLM_bound (K : Compacts E) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : 𝓓_{K}(E, ℝ)) (x : E),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (contDiffSupportedInToSchwartzLM K f) x‖ ≤
        C * ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K m f := by
  rcases K.isCompact.isBounded.subset_closedBall (0 : E) with ⟨R, hR⟩
  let M : ℝ := max R 0
  have hM_nonneg : 0 ≤ M := le_max_right R 0
  let C : ℝ := M ^ k * ‖Complex.ofRealCLM‖
  have hC_nonneg : 0 ≤ C := by positivity
  refine ⟨C, hC_nonneg, ?_⟩
  intro f x
  have h_coe : ⇑(contDiffSupportedInToSchwartzLM K f) = Complex.ofRealCLM ∘ ⇑f := rfl
  rw [h_coe]
  have h_fderiv : iteratedFDeriv ℝ m (Complex.ofRealCLM ∘ ⇑f) x =
      Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ m (⇑f) x) :=
    Complex.ofRealCLM.iteratedFDeriv_comp_left f.contDiff.contDiffAt (mod_cast le_top)
  rw [h_fderiv]
  by_cases hx : x ∈ (K : Set E)
  · have hx_norm : ‖x‖ ≤ M := by
      have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
      exact hxR.trans (le_max_left R 0)
    have h_pow : ‖x‖ ^ k ≤ M ^ k := pow_le_pow_left₀ (norm_nonneg x) hx_norm k
    have h_op : ‖Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ m (⇑f) x)‖ ≤
        ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ m (⇑f) x‖ :=
      Complex.ofRealCLM.norm_compContinuousMultilinearMap_le _
    have h_sem : ‖iteratedFDeriv ℝ m (⇑f) x‖ ≤
        ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K m f :=
      ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ
    calc
      ‖x‖ ^ k * ‖Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ m (⇑f) x)‖
          ≤ M ^ k * (‖Complex.ofRealCLM‖ * ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K m f) := by
            refine mul_le_mul h_pow (h_op.trans ?_) (norm_nonneg _) (pow_nonneg hM_nonneg k)
            exact mul_le_mul_of_nonneg_left h_sem (norm_nonneg _)
      _ = C * ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K m f := by
            dsimp [C]; ring
  · have hx_compl : x ∈ (K : Set E)ᶜ := hx
    have h0 : Complex.ofRealCLM.compContinuousMultilinearMap
        (iteratedFDeriv ℝ m (⇑f) x) = 0 := by
      rw [f.iteratedFDeriv_zero_on_compl hx_compl]
      ext v
      simp
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hC_nonneg (apply_nonneg (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K m) f)

omit [FiniteDimensional ℝ E] in
lemma continuous_contDiffSupportedInToSchwartzLM (K : Compacts E) :
    Continuous (contDiffSupportedInToSchwartzLM K) := by
  refine WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms ℝ E ℝ ⊤ K)
    (schwartz_withSeminorms ℝ E ℂ)
    (contDiffSupportedInToSchwartzLM K) ?_
  rintro ⟨k, m⟩
  rcases contDiffSupportedInToSchwartzLM_bound K k m with ⟨C, hC_nonneg, h_bound⟩
  refine ⟨{m}, ⟨C, hC_nonneg⟩, fun f => ?_⟩
  simp only [SchwartzMap.schwartzSeminormFamily_apply, Seminorm.comp_apply, Finset.sup_singleton,
    smul_apply, NNReal.smul_def, smul_eq_mul]
  exact SchwartzMap.seminorm_le_bound ℝ k m (contDiffSupportedInToSchwartzLM K f)
    (mul_nonneg hC_nonneg (apply_nonneg (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K m) f))
    (h_bound f)

noncomputable def testFunctionToSchwartzCLM (Ω : Opens E) :
    𝓓(Ω, ℝ) →L[ℝ] SchwartzMap E ℂ :=
  TestFunction.mkCLM ℝ
    (fun φ => (φ.hasCompactSupport'.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp φ.contDiff'))
    (fun f g => by ext x; simp)
    (fun c f => by ext x; simp [Complex.real_smul])
    (fun K hK => by
      have h_eq : ((fun φ : 𝓓(Ω, ℝ) =>
          (φ.hasCompactSupport'.comp_left Complex.ofReal_zero).toSchwartzMap
            (Complex.ofRealCLM.contDiff.comp φ.contDiff')) ∘
          TestFunction.ofSupportedIn hK) = contDiffSupportedInToSchwartzLM K := by
        ext f x
        rfl
      rw [h_eq]
      exact continuous_contDiffSupportedInToSchwartzLM K)

omit [FiniteDimensional ℝ E] in
@[simp]
lemma testFunctionToSchwartzCLM_apply (Ω : Opens E) (φ : 𝓓(Ω, ℝ)) (x : E) :
    testFunctionToSchwartzCLM Ω φ x = (φ x : ℂ) :=
  rfl

omit [FiniteDimensional ℝ E] in
lemma tsupport_testFunctionToSchwartzCLM_subset (Ω : Opens E) (φ : 𝓓(Ω, ℝ)) :
    tsupport (fun x => testFunctionToSchwartzCLM Ω φ x) ⊆ tsupport (fun x => φ x) := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support, ne_eq, testFunctionToSchwartzCLM_apply,
    Complex.ofReal_eq_zero] at hx ⊢
  exact hx

noncomputable def temperedToDistribution (Ω : Opens E)
    (T : TemperedDistribution E ℂ) : 𝓓'(Ω, ℂ) where
  toFun φ := T (testFunctionToSchwartzCLM Ω φ)
  map_add' f g := by rw [map_add, map_add]
  map_smul' c f := by
    rw [map_smul]
    have h_smul : c • testFunctionToSchwartzCLM Ω f =
        (c : ℂ) • testFunctionToSchwartzCLM Ω f := by
      ext x
      simp [Complex.real_smul]
    rw [h_smul, map_smul, Complex.real_smul]
    rfl
  cont := T.cont.comp (testFunctionToSchwartzCLM Ω).cont

omit [FiniteDimensional ℝ E] in
@[simp]
lemma temperedToDistribution_apply (Ω : Opens E)
    (T : TemperedDistribution E ℂ) (φ : 𝓓(Ω, ℝ)) :
    temperedToDistribution Ω T φ = T (testFunctionToSchwartzCLM Ω φ) :=
  rfl

omit [FiniteDimensional ℝ E] in
lemma temperedToDistribution_add (Ω : Opens E)
    (T₁ T₂ : TemperedDistribution E ℂ) :
    temperedToDistribution Ω (T₁ + T₂) =
      temperedToDistribution Ω T₁ + temperedToDistribution Ω T₂ := by
  ext φ
  rfl

omit [FiniteDimensional ℝ E] in
lemma temperedToDistribution_sub (Ω : Opens E)
    (T₁ T₂ : TemperedDistribution E ℂ) :
    temperedToDistribution Ω (T₁ - T₂) =
      temperedToDistribution Ω T₁ - temperedToDistribution Ω T₂ := by
  ext φ
  rfl

omit [FiniteDimensional ℝ E] in
lemma temperedToDistribution_smul (Ω : Opens E)
    (c : ℂ) (T : TemperedDistribution E ℂ) :
    temperedToDistribution Ω (c • T) = smulComplex Ω c (temperedToDistribution Ω T) := by
  ext φ
  rfl

lemma equalOn_temperedToDistribution_of_schwartz_eq
    {Ω_n : Opens (Fin n → ℝ)} {U : Opens (Fin n → ℝ)}
    (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    {T₁ T₂ : TemperedDistribution (Fin n → ℝ) ℂ}
    (h_eq : ∀ ψ : SchwartzMap (Fin n → ℝ) ℂ,
      tsupport (fun x => ψ x) ⊆ (U : Set (Fin n → ℝ)) → T₁ ψ = T₂ ψ) :
    EqualOn Ω_n (temperedToDistribution Ω_n T₁) (temperedToDistribution Ω_n T₂) U hU := by
  intro φ hφ
  rw [temperedToDistribution_apply, temperedToDistribution_apply]
  exact h_eq (testFunctionToSchwartzCLM Ω_n φ)
    ((tsupport_testFunctionToSchwartzCLM_subset Ω_n φ).trans hφ)

end TemperedBridge

end Distribution

namespace Distribution

section TemperedEOW

theorem local_eow_of_continuous_boundary {n : ℕ}
    (Ω_n : Opens (Fin n → ℝ))
    (V_plus V_minus : Set (Fin n → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_conv : Convex ℝ V_plus)
    (hV_ne : V_plus.Nonempty)
    (h0_not_mem : (0 : Fin n → ℝ) ∉ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ c : ℝ, c > 0 → (fun i => c * v i) ∈ V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (hf_plus_cont : ContinuousOn f_plus (TubeDomain V_plus ∪ realWindow (U : Set (Fin n → ℝ))))
    (hf_minus_cont : ContinuousOn f_minus (TubeDomain V_minus ∪ realWindow (U : Set (Fin n → ℝ))))
    (T_plus : 𝓓'(Ω_n, ℂ)) (hT_plus : HasBoundaryValue Ω_n f_plus V_plus T_plus)
    (T_minus : 𝓓'(Ω_n, ℂ)) (hT_minus : HasBoundaryValue Ω_n f_minus V_minus T_minus)
    (h_match : EqualOn Ω_n T_plus T_minus U hU) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have h0 : (0 : Fin n → ℝ) ∈ closure V_plus := by
    rcases hV_ne with ⟨v, hv⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    let c : ℝ := ε / (2 * (‖v‖ + 1))
    have hc_pos : 0 < c := by positivity
    refine ⟨fun i => c * v i, hV_plus_cone v hv c hc_pos, ?_⟩
    rw [dist_zero_left]
    have h_norm : ‖fun i : Fin n => c * v i‖ = c * ‖v‖ := by
      change ‖c • v‖ = c * ‖v‖
      rw [norm_smul, Real.norm_of_nonneg hc_pos.le]
    rw [h_norm]
    dsimp [c]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have h_disj : Disjoint V_plus V_minus :=
    disjoint_opposite_of_convex_zero_not_mem h_opposite hV_plus_conv h0_not_mem
  have h0_minus : (0 : Fin n → ℝ) ∉ V_minus := by
    rw [h_opposite]
    rintro ⟨u, hu, hu0⟩
    exact h0_not_mem (neg_eq_zero.mp hu0 ▸ hu)
  have hV_minus_open : IsOpen V_minus := h_opposite ▸ isOpen_neg_image hV_plus_open
  have h_eq_U : ∀ x ∈ U, f_plus (fun i => (x i : ℂ)) = f_minus (fun i => (x i : ℂ)) :=
    eqOn_boundary_of_hasBoundaryValue_equalOn hU h_opposite h0
      hf_plus_cont hf_minus_cont hT_plus hT_minus h_match
  let fg := glueWedgeFun V_plus f_plus f_minus
  have hfg_cont :
      ContinuousOn fg (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
    rw [← h_opposite]
    exact continuousOn_glueWedgeFun hV_plus_open hV_minus_open h_disj h0_minus
      hf_plus_cont hf_minus_cont h_eq_U
  have hfg_plus : DifferentiableOn ℂ fg (TubeDomain V_plus) :=
    hf_plus_holo.congr (fun _ hz => glueWedgeFun_eq_plus hz)
  have hfg_minus : DifferentiableOn ℂ fg (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
    rw [← h_opposite]
    exact hf_minus_holo.congr (fun _ hz => glueWedgeFun_eq_minus h_disj h0_minus hz)
  have h_ext_all : ∀ x ∈ (U : Set (Fin n → ℝ)),
      ∃ N ∈ nhds (fun i => (x i : ℂ)), ∃ G : (Fin n → ℂ) → ℂ,
        IsOpen N ∧ DifferentiableOn ℂ G N ∧
        EqOn G f_plus (N ∩ TubeDomain V_plus) ∧
        EqOn G f_minus (N ∩ TubeDomain V_minus) := by
    intro x hx
    rcases QFT.eow_local_exists_all_dim V_plus U hV_plus_open hV_plus_conv hV_plus_cone
      hV_ne U.isOpen fg hfg_cont hfg_plus hfg_minus x hx with
      ⟨r_x, hr_x_pos, _hr_sub, Fx, hFx_an, hFx_eq⟩
    let B := Metric.ball (fun i => (x i : ℂ)) r_x
    refine ⟨B, Metric.ball_mem_nhds _ hr_x_pos, Fx, Metric.isOpen_ball,
      hFx_an.differentiableOn, ?_, ?_⟩
    · intro z hz
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U :=
        Or.inl (Or.inl hz.2)
      rw [hFx_eq ⟨hz.1, hz_wedge⟩]
      exact glueWedgeFun_eq_plus hz.2
    · intro z hz
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U := by
        rw [← h_opposite]
        exact Or.inl (Or.inr hz.2)
      rw [hFx_eq ⟨hz.1, hz_wedge⟩]
      exact glueWedgeFun_eq_minus h_disj h0_minus hz.2
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x :=
    fun x hx => localEpsteinData_of_nhds_extension V_plus V_minus f_plus f_minus x
      (h_ext_all x hx)
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 f_plus f_minus U data

def HasPolynomialTubeGrowth {n : ℕ} (V : Set (Fin n → ℝ)) (f : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ (K L : Set (Fin n → ℝ)), IsCompact K → IsCompact L → L ⊆ V →
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ x ∈ K, ∀ y ∈ L, ∀ s : ℝ, 0 < s → s ≤ 1 →
        ‖f (fun i => (x i : ℂ) + ((s * y i : ℝ) : ℂ) * Complex.I)‖ ≤ C / s ^ N

lemma HasPolynomialTubeGrowth.mono {n : ℕ} {V₁ V₂ : Set (Fin n → ℝ)} {f : (Fin n → ℂ) → ℂ}
    (h : HasPolynomialTubeGrowth V₂ f) (hsub : V₁ ⊆ V₂) :
    HasPolynomialTubeGrowth V₁ f :=
  fun K L hK hL hLV => h K L hK hL (hLV.trans hsub)

lemma HasPolynomialTubeGrowth.const_mul {n : ℕ} {V : Set (Fin n → ℝ)} {f : (Fin n → ℂ) → ℂ}
    (c : ℂ) (h : HasPolynomialTubeGrowth V f) :
    HasPolynomialTubeGrowth V (fun z => c * f z) := by
  intro K L hK hL hLV
  rcases h K L hK hL hLV with ⟨N, C, hC_nn, hbd⟩
  refine ⟨N, ‖c‖ * C, mul_nonneg (norm_nonneg c) hC_nn, fun x hx y hy s hs0 hs1 => ?_⟩
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (hbd x hx y hy s hs0 hs1) (norm_nonneg c)

lemma ode_step_pow_ge_two {F G : ℝ → ℂ} {k : ℕ} {M₀ A : ℝ} (hM₀ : 0 ≤ M₀) (hA : 0 ≤ A)
    (h_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (Complex.I * G t) t)
    (h_half : ‖F (1 / 2)‖ ≤ M₀)
    (hG_bd : ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖G s‖ ≤ A / s ^ (k + 2)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F t‖ ≤ (M₀ + A) / t ^ (k + 1) := by
  intro t ⟨ht0, ht12⟩
  let g : ℝ → ℂ := fun u => F (1 / 2 - u)
  let g' : ℝ → ℂ := fun u => -(Complex.I * G (1 / 2 - u))
  let B : ℝ → ℝ := fun u => M₀ + A / ((k + 1 : ℕ) : ℝ) * ((1 / 2 - u) ^ (k + 1))⁻¹
  let B' : ℝ → ℝ := fun u => A / (1 / 2 - u) ^ (k + 2)
  have hg_cont : ContinuousOn g (Set.Icc 0 (1 / 2 - t)) := by
    intro u hu
    have h_in : (1 / 2 - u : ℝ) ∈ Set.Ioo 0 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    exact ((h_deriv _ h_in).continuousAt.comp (continuous_const.sub continuous_id).continuousAt
      ).continuousWithinAt
  have hg_deriv : ∀ u ∈ Set.Ico 0 (1 / 2 - t), HasDerivWithinAt g (g' u) (Set.Ici u) u := by
    intro u hu
    have h_in : (1 / 2 - u : ℝ) ∈ Set.Ioo 0 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h_sub : HasDerivAt (fun r : ℝ => 1 / 2 - r) (-1) u := by
      simpa using (hasDerivAt_id' u).const_sub (1 / 2 : ℝ)
    have hc : HasDerivAt g (g' u) u :=
      (HasDerivAt.scomp u (h_deriv _ h_in) h_sub).congr_deriv (by simp [g'])
    exact hc.hasDerivWithinAt
  have hB_deriv : ∀ u ∈ Set.Icc 0 (1 / 2 - t), HasDerivAt B (B' u) u := by
    intro u hu
    have h_pos : 0 < 1 / 2 - u := by linarith [hu.2]
    have h_sub : HasDerivAt (fun r : ℝ => 1 / 2 - r) (-1) u := by
      simpa using (hasDerivAt_id' u).const_sub (1 / 2 : ℝ)
    have h_pow := h_sub.pow (k + 1)
    have h_inv := h_pow.inv (pow_ne_zero (k + 1) h_pos.ne')
    have h_sc := (h_inv.const_mul (A / ((k + 1 : ℕ) : ℝ))).const_add M₀
    refine h_sc.congr_deriv ?_
    have hk1_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    dsimp [B']
    rw [div_mul_div_comm]
    have h_ne1 : (1 / 2 - u) ^ (k + 1) ≠ 0 := pow_ne_zero _ h_pos.ne'
    have h_ne2 : (1 / 2 - u) ^ (k + 2) ≠ 0 := pow_ne_zero _ h_pos.ne'
    rw [div_eq_div_iff (mul_ne_zero hk1_ne (pow_ne_zero 2 h_ne1)) h_ne2]
    simp only [pow_succ]
    ring
  have ha : ‖g 0‖ ≤ B 0 := by
    dsimp [g, B]
    rw [sub_zero]
    have h_nn : 0 ≤ A / ((k + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ (k + 1))⁻¹ := by positivity
    linarith [h_half]
  have h_le := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    hg_cont hg_deriv ha
    (fun u hu => (hB_deriv u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hB_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => by
      dsimp [g', B']
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      exact hG_bd (1 / 2 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    (show (1 / 2 - t : ℝ) ∈ Set.Icc 0 (1 / 2 - t) from ⟨by linarith, le_rfl⟩)
  have h_gt : g (1 / 2 - t) = F t := by dsimp [g]; ring_nf
  have h_Bt : B (1 / 2 - t) ≤ (M₀ + A) / t ^ (k + 1) := by
    dsimp [B]
    have h_sub_eq : 1 / 2 - (1 / 2 - t) = t := by ring
    rw [h_sub_eq]
    have ht_pow_pos : 0 < t ^ (k + 1) := pow_pos ht0 (k + 1)
    have ht_pow_le : t ^ (k + 1) ≤ 1 := pow_le_one₀ ht0.le (by linarith)
    have hk1_ge : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    have h1 : M₀ ≤ M₀ / t ^ (k + 1) := by
      rw [le_div_iff₀ ht_pow_pos]
      nlinarith
    have h2 : A / ((k + 1 : ℕ) : ℝ) * (t ^ (k + 1))⁻¹ ≤ A / t ^ (k + 1) := by
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (div_le_self hA hk1_ge) ht_pow_pos.le
    rw [add_div]
    linarith
  rw [h_gt] at h_le
  exact h_le.trans h_Bt

lemma ode_step_one_to_const {F₁ F₂ F₃ : ℝ → ℂ} {M₁ M₂ A : ℝ}
    (_hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hA : 0 ≤ A)
    (h_d1 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F₁ (Complex.I * F₂ t) t)
    (h_d2 : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F₂ (Complex.I * F₃ t) t)
    (h_half1 : ‖F₁ (1 / 2)‖ ≤ M₁)
    (h_half2 : ‖F₂ (1 / 2)‖ ≤ M₂)
    (hF₃_bd : ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F₃ s‖ ≤ A / s) :
    ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F₁ t‖ ≤ M₁ + 2 * (M₂ + 2 * A) := by
  have hF₂_sqrt : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F₂ t‖ ≤ (M₂ + 2 * A) / Real.sqrt t := by
    intro t ⟨ht0, ht12⟩
    let g : ℝ → ℂ := fun u => F₂ (1 / 2 - u)
    let g' : ℝ → ℂ := fun u => -(Complex.I * F₃ (1 / 2 - u))
    let B : ℝ → ℝ := fun u => M₂ + 2 * A * (Real.sqrt (1 / 2 - u))⁻¹
    let B' : ℝ → ℝ := fun u => A / ((1 / 2 - u) * Real.sqrt (1 / 2 - u))
    have hg_cont : ContinuousOn g (Set.Icc 0 (1 / 2 - t)) := by
      intro u hu
      have h_in : (1 / 2 - u : ℝ) ∈ Set.Ioo 0 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      exact ((h_d2 _ h_in).continuousAt.comp
        (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
    have hg_deriv : ∀ u ∈ Set.Ico 0 (1 / 2 - t), HasDerivWithinAt g (g' u) (Set.Ici u) u := by
      intro u hu
      have h_in : (1 / 2 - u : ℝ) ∈ Set.Ioo 0 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have h_sub : HasDerivAt (fun r : ℝ => 1 / 2 - r) (-1) u := by
        simpa using (hasDerivAt_id' u).const_sub (1 / 2 : ℝ)
      have hc : HasDerivAt g (g' u) u :=
        (HasDerivAt.scomp u (h_d2 _ h_in) h_sub).congr_deriv (by simp [g'])
      exact hc.hasDerivWithinAt
    have hB_deriv : ∀ u ∈ Set.Icc 0 (1 / 2 - t), HasDerivAt B (B' u) u := by
      intro u hu
      have h_pos : 0 < 1 / 2 - u := by linarith [hu.2]
      have h_sq_pos : 0 < Real.sqrt (1 / 2 - u) := Real.sqrt_pos.mpr h_pos
      have h_sub : HasDerivAt (fun r : ℝ => 1 / 2 - r) (-1) u := by
        simpa using (hasDerivAt_id' u).const_sub (1 / 2 : ℝ)
      have h_sq := (Real.hasDerivAt_sqrt h_pos.ne').comp u h_sub
      have h_inv := h_sq.inv h_sq_pos.ne'
      have h_sc := (h_inv.const_mul (2 * A)).const_add M₂
      refine h_sc.congr_deriv ?_
      dsimp [B']
      rw [Real.sq_sqrt h_pos.le]
      field_simp [h_pos.ne', h_sq_pos.ne']
    have ha : ‖g 0‖ ≤ B 0 := by
      dsimp [g, B]
      rw [sub_zero]
      have h_nn : 0 ≤ 2 * A * (Real.sqrt (1 / 2))⁻¹ := by positivity
      linarith [h_half2]
    have h_le := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
      hg_cont hg_deriv ha
      (fun u hu => (hB_deriv u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hB_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
      (fun u hu => by
        dsimp [g', B']
        rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
        have hs_pos : 0 < 1 / 2 - u := by linarith [hu.2]
        have hs_le : 1 / 2 - u ≤ 1 / 2 := by linarith [hu.1]
        have h_sq_le : Real.sqrt (1 / 2 - u) ≤ 1 :=
          Real.sqrt_le_one.mpr (by linarith)
        have h1 := hF₃_bd (1 / 2 - u) ⟨hs_pos, hs_le⟩
        have h2 : A / (1 / 2 - u) ≤ A / ((1 / 2 - u) * Real.sqrt (1 / 2 - u)) := by
          rw [div_le_div_iff₀ hs_pos (by positivity)]
          have h_m : (1 / 2 - u) * Real.sqrt (1 / 2 - u) ≤ 1 / 2 - u :=
            mul_le_of_le_one_right hs_pos.le h_sq_le
          exact mul_le_mul_of_nonneg_left h_m hA
        exact h1.trans h2)
      (show (1 / 2 - t : ℝ) ∈ Set.Icc 0 (1 / 2 - t) from ⟨by linarith, le_rfl⟩)
    have h_gt : g (1 / 2 - t) = F₂ t := by dsimp [g]; ring_nf
    rw [h_gt] at h_le
    refine h_le.trans ?_
    dsimp [B]
    have h_sub_eq : 1 / 2 - (1 / 2 - t) = t := by ring
    rw [h_sub_eq]
    have h_sq_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h_sq_le : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    rw [add_div, div_eq_mul_inv (2 * A)]
    have hM2_le : M₂ ≤ M₂ / Real.sqrt t := by
      rw [le_div_iff₀ h_sq_pos]
      nlinarith
    linarith
  intro t ⟨ht0, ht12⟩
  let A₁ : ℝ := M₂ + 2 * A
  have hA₁ : 0 ≤ A₁ := by positivity
  let g : ℝ → ℂ := fun u => F₁ (1 / 2 - u)
  let g' : ℝ → ℂ := fun u => -(Complex.I * F₂ (1 / 2 - u))
  let B : ℝ → ℝ := fun u => M₁ + 2 * A₁ * (1 - Real.sqrt (1 / 2 - u))
  let B' : ℝ → ℝ := fun u => A₁ / Real.sqrt (1 / 2 - u)
  have hg_cont : ContinuousOn g (Set.Icc 0 (1 / 2 - t)) := by
    intro u hu
    have h_in : (1 / 2 - u : ℝ) ∈ Set.Ioo 0 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    exact ((h_d1 _ h_in).continuousAt.comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hg_deriv : ∀ u ∈ Set.Ico 0 (1 / 2 - t), HasDerivWithinAt g (g' u) (Set.Ici u) u := by
    intro u hu
    have h_in : (1 / 2 - u : ℝ) ∈ Set.Ioo 0 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h_sub : HasDerivAt (fun r : ℝ => 1 / 2 - r) (-1) u := by
      simpa using (hasDerivAt_id' u).const_sub (1 / 2 : ℝ)
    have hc : HasDerivAt g (g' u) u :=
      (HasDerivAt.scomp u (h_d1 _ h_in) h_sub).congr_deriv (by simp [g'])
    exact hc.hasDerivWithinAt
  have hB_deriv : ∀ u ∈ Set.Icc 0 (1 / 2 - t), HasDerivAt B (B' u) u := by
    intro u hu
    have h_pos : 0 < 1 / 2 - u := by linarith [hu.2]
    have h_sq_pos : 0 < Real.sqrt (1 / 2 - u) := Real.sqrt_pos.mpr h_pos
    have h_sub : HasDerivAt (fun r : ℝ => 1 / 2 - r) (-1) u := by
      simpa using (hasDerivAt_id' u).const_sub (1 / 2 : ℝ)
    have h_sq := (Real.hasDerivAt_sqrt h_pos.ne').comp u h_sub
    have h_one_sub := h_sq.const_sub (1 : ℝ)
    have h_sc := (h_one_sub.const_mul (2 * A₁)).const_add M₁
    refine h_sc.congr_deriv ?_
    dsimp [B']
    field_simp [h_sq_pos.ne']
  have ha : ‖g 0‖ ≤ B 0 := by
    dsimp [g, B]
    rw [sub_zero]
    have h_sq_le : Real.sqrt (1 / 2) ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
    have h_nn : 0 ≤ 2 * A₁ * (1 - Real.sqrt (1 / 2)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr h_sq_le)
    linarith [h_half1]
  have h_le := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    hg_cont hg_deriv ha
    (fun u hu => (hB_deriv u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hB_deriv u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt)
    (fun u hu => by
      dsimp [g', B']
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul]
      exact hF₂_sqrt (1 / 2 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩)
    (show (1 / 2 - t : ℝ) ∈ Set.Icc 0 (1 / 2 - t) from ⟨by linarith, le_rfl⟩)
  have h_gt : g (1 / 2 - t) = F₁ t := by dsimp [g]; ring_nf
  rw [h_gt] at h_le
  refine h_le.trans ?_
  dsimp [B]
  have h_sq_nn : 0 ≤ Real.sqrt (1 / 2 - (1 / 2 - t)) := Real.sqrt_nonneg _
  nlinarith

def odeReduceBound : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, C, m => C (m + 2)
  | k + 1, C, m => odeReduceBound k (fun j => (2 : ℝ) ^ (k + 2) * C j + C (j + 1)) m

lemma odeReduceBound_nonneg (k : ℕ) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (m : ℕ) :
    0 ≤ odeReduceBound k C m := by
  induction k generalizing C m with
  | zero => exact hC (m + 2)
  | succ k ih =>
    exact ih (fun j => add_nonneg (mul_nonneg (by positivity) (hC j)) (hC (j + 1))) m

lemma ode_reduce_to_inv_t (k : ℕ) {F : ℕ → ℝ → ℂ} {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j)
    (h_deriv : ∀ j, ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (F j) (Complex.I * F (j + 1) t) t)
    (h_init : ∀ j, ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F j s‖ ≤ C j / s ^ (k + 1)) :
    ∀ m, ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F (m + 2) t‖ ≤ odeReduceBound k C m / t := by
  induction k generalizing C with
  | zero =>
    intro m t ht
    simpa [odeReduceBound, pow_one] using h_init (m + 2) t ht
  | succ k ih =>
    have h_step_all : ∀ j, ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2),
        ‖F j t‖ ≤ ((2 : ℝ) ^ (k + 2) * C j + C (j + 1)) / t ^ (k + 1) := by
      intro j t ht
      have h_half : ‖F j (1 / 2)‖ ≤ (2 : ℝ) ^ (k + 2) * C j := by
        have h1 := h_init j (1 / 2) ⟨by norm_num, le_rfl⟩
        have h_eq : C j / (1 / 2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k + 2) * C j := by
          rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
        rwa [h_eq] at h1
      exact ode_step_pow_ge_two (mul_nonneg (by positivity) (hC j)) (hC (j + 1))
        (h_deriv j) h_half (h_init (j + 1)) t ht
    intro m t ht
    exact ih (fun j => add_nonneg (mul_nonneg (by positivity) (hC j)) (hC (j + 1)))
      h_step_all m t ht

def odeLipschitzBound (N : ℕ) (C : ℕ → ℝ) : ℝ :=
  match N with
  | 0 => C 1
  | k + 1 =>
    (2 : ℝ) ^ (k + 1) * C 1 +
      2 * ((2 : ℝ) ^ (k + 1) * C 2 + 2 * odeReduceBound k C 1)

lemma odeLipschitzBound_nonneg (N : ℕ) {C : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) :
    0 ≤ odeLipschitzBound N C := by
  cases N with
  | zero => exact hC 1
  | succ k =>
    dsimp [odeLipschitzBound]
    have hb := odeReduceBound_nonneg k hC 1
    have hc1 := hC 1
    have hc2 := hC 2
    positivity

lemma ode_poly_singularity_lipschitz {N : ℕ} {F : ℕ → ℝ → ℂ} {C : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j)
    (h_deriv : ∀ j, ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (F j) (Complex.I * F (j + 1) t) t)
    (h_bd : ∀ j, ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F j s‖ ≤ C j / s ^ N) :
    ∀ t₁ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ t₂ ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖F 0 t₁ - F 0 t₂‖ ≤ odeLipschitzBound N C * |t₁ - t₂| := by
  have hF1_bd : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2), ‖F 1 t‖ ≤ odeLipschitzBound N C := by
    cases N with
    | zero =>
      intro t ht
      simpa [odeLipschitzBound, pow_zero, div_one] using h_bd 1 t ht
    | succ k =>
      have hF3_inv : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2),
          ‖F 3 t‖ ≤ odeReduceBound k C 1 / t :=
        ode_reduce_to_inv_t k hC h_deriv h_bd 1
      have h_half1 : ‖F 1 (1 / 2)‖ ≤ (2 : ℝ) ^ (k + 1) * C 1 := by
        have h1 := h_bd 1 (1 / 2) ⟨by norm_num, le_rfl⟩
        have h_eq : C 1 / (1 / 2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * C 1 := by
          rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
        rwa [h_eq] at h1
      have h_half2 : ‖F 2 (1 / 2)‖ ≤ (2 : ℝ) ^ (k + 1) * C 2 := by
        have h2 := h_bd 2 (1 / 2) ⟨by norm_num, le_rfl⟩
        have h_eq : C 2 / (1 / 2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 1) * C 2 := by
          rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
        rwa [h_eq] at h2
      intro t ht
      exact ode_step_one_to_const
        (mul_nonneg (by positivity) (hC 1))
        (mul_nonneg (by positivity) (hC 2))
        (odeReduceBound_nonneg k hC 1)
        (h_deriv 1) (h_deriv 2) h_half1 h_half2 hF3_inv t ht
  intro t₁ ht₁ t₂ ht₂
  have h_conv : Convex ℝ (Set.Ioc (0 : ℝ) (1 / 2)) := convex_Ioc 0 (1 / 2)
  have h_dw : ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2),
      HasDerivWithinAt (F 0) (Complex.I * F 1 s) (Set.Ioc 0 (1 / 2)) s := by
    intro s hs
    exact (h_deriv 0 s ⟨hs.1, by linarith [hs.2]⟩).hasDerivWithinAt
  have h_nb : ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖Complex.I * F 1 s‖ ≤ odeLipschitzBound N C := by
    intro s hs
    rw [norm_mul, Complex.norm_I, one_mul]
    exact hF1_bd s hs
  simpa [Real.norm_eq_abs, abs_sub_comm] using
    h_conv.norm_image_sub_le_of_norm_hasDerivWithin_le h_dw h_nb ht₂ ht₁

lemma clm_pi_eq_sum_proj {n : ℕ} (L : (Fin n → ℂ) →L[ℂ] ℂ) :
    L = ∑ i : Fin n, (L (Pi.single i 1)) • ContinuousLinearMap.proj (R := ℂ) i := by
  ext w
  simp only [_root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hw : w = ∑ i : Fin n, (w i) • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne (Ne.symm hji)]
    · intro hi; exact False.elim (hi (Finset.mem_univ i))
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma continuousOn_fderiv_of_differentiableOn {n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  intro z₀ hz₀
  rcases (Metric.nhds_basis_closedBall.mem_iff).mp (hU.mem_nhds hz₀) with ⟨r₀, hr₀_pos, hr₀_sub⟩
  let δ : ℝ := r₀ / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have h3δ_sub : Metric.closedBall z₀ (3 * δ) ⊆ U := by
    have heq : 3 * δ = r₀ := by dsimp [δ]; ring
    rwa [heq]
  have hf_cont_3δ : ContinuousOn f (Metric.closedBall z₀ (3 * δ)) := hf.continuousOn.mono h3δ_sub
  rcases ((isCompact_closedBall z₀ (3 * δ)).image_of_continuousOn
    hf_cont_3δ).isBounded.exists_norm_le with ⟨M₀, hM₀⟩
  let M : ℝ := max M₀ 0
  have hM_nn : 0 ≤ M := le_max_right _ _
  have hM_bd : ∀ w ∈ Metric.closedBall z₀ (3 * δ), ‖f w‖ ≤ M := fun w hw =>
    (hM₀ (f w) ⟨w, hw, rfl⟩).trans (le_max_left _ _)
  have h_coord_cont : ∀ i : Fin n,
      ContinuousOn (fun z => fderiv ℂ f z (Pi.single i 1)) (Metric.closedBall z₀ δ) := by
    intro i
    let e_i : Fin n → ℂ := Pi.single i 1
    have he_norm : ‖e_i‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
      by_cases hij : j = i
      · subst hij; simp [e_i]
      · simp [e_i, hij]
    have h_in_3δ : ∀ z ∈ Metric.closedBall z₀ δ, ∀ ζ ∈ Metric.closedBall (0 : ℂ) δ,
        z + ζ • e_i ∈ Metric.closedBall z₀ (3 * δ) := by
      intro z hz ζ hζ
      rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
      rw [Metric.mem_closedBall, dist_zero_right] at hζ
      calc ‖z + ζ • e_i - z₀‖
          = ‖(z - z₀) + ζ • e_i‖ := by abel_nf
        _ ≤ ‖z - z₀‖ + ‖ζ • e_i‖ := norm_add_le _ _
        _ = ‖z - z₀‖ + ‖ζ‖ * ‖e_i‖ := by rw [norm_smul]
        _ ≤ δ + δ * 1 := by nlinarith [norm_nonneg ζ, norm_nonneg e_i]
        _ ≤ 3 * δ := by linarith
    let δ_nn : NNReal := ⟨δ, hδ.le⟩
    have hδ_nn_pos : (0 : NNReal) < δ_nn := NNReal.coe_pos.mp hδ
    have h_eq : ∀ z ∈ Metric.closedBall z₀ δ, fderiv ℂ f z e_i =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ *
          ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
            deriv (circleMap 0 δ) θ *
              ((1 / circleMap 0 δ θ) ^ 1 *
                ((circleMap 0 δ θ)⁻¹ * f (z + circleMap 0 δ θ • e_i))) := by
      intro z hz
      have hz_U : z ∈ U := h3δ_sub (Metric.closedBall_subset_closedBall (by linarith) hz)
      have hdf_z : HasFDerivAt f (fderiv ℂ f z) z :=
        (hf.differentiableAt (hU.mem_nhds hz_U)).hasFDerivAt
      have hd_line : HasDerivAt (fun ζ : ℂ => z + ζ • e_i) e_i 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const e_i).const_add z
      have hz0 : z + (0 : ℂ) • e_i = z := by simp
      have hdf_z0 : HasFDerivAt f (fderiv ℂ f z) (z + (0 : ℂ) • e_i) := hz0.symm ▸ hdf_z
      have hd1 : HasDerivAt (fun ζ : ℂ => f (z + ζ • e_i)) (fderiv ℂ f z e_i) 0 :=
        hdf_z0.comp_hasDerivAt 0 hd_line
      have hdiff_on : DifferentiableOn ℂ (fun ζ : ℂ => f (z + ζ • e_i))
          (Metric.closedBall 0 (δ_nn : ℝ)) := by
        refine hf.comp ?_ fun ζ hζ => h3δ_sub (h_in_3δ z hz ζ hζ)
        exact (differentiable_const z).add (differentiable_id.smul_const e_i) |>.differentiableOn
      have hP := hdiff_on.hasFPowerSeriesOnBall hδ_nn_pos
      have hd2 := hP.hasFPowerSeriesAt.hasDerivAt
      have h_u := hd1.unique hd2
      rw [h_u, cauchyPowerSeries_apply, circleIntegral]
      simp only [sub_zero, smul_eq_mul]
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
      rfl
    refine ContinuousOn.congr ?_ h_eq
    refine continuousOn_const.mul ?_
    let G : (Fin n → ℂ) → ℝ → ℂ := fun z θ =>
      deriv (circleMap 0 δ) θ *
        ((1 / circleMap 0 δ θ) ^ 1 *
          ((circleMap 0 δ θ)⁻¹ * f (z + circleMap 0 δ θ • e_i)))
    have h_cm : Continuous (circleMap (0 : ℂ) δ) := continuous_circleMap 0 δ
    have h_dcm : Continuous (deriv (circleMap (0 : ℂ) δ)) := by
      have hd : deriv (circleMap (0 : ℂ) δ) = fun θ => circleMap 0 δ θ * Complex.I := by
        ext θ; exact deriv_circleMap 0 δ θ
      rw [hd]
      exact h_cm.mul continuous_const
    have h_ne : ∀ θ : ℝ, circleMap (0 : ℂ) δ θ ≠ 0 := fun θ =>
      norm_ne_zero_iff.mp (by rw [norm_circleMap_zero, abs_of_pos hδ]; exact hδ.ne')
    have h_cm_mem : ∀ θ : ℝ, circleMap (0 : ℂ) δ θ ∈ Metric.closedBall (0 : ℂ) δ := fun θ => by
      rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero, abs_of_pos hδ]
    have hG_cont_θ : ∀ z ∈ Metric.closedBall z₀ δ, Continuous (G z) := by
      intro z hz
      have h_fθ : Continuous (fun θ : ℝ => f (z + circleMap 0 δ θ • e_i)) :=
        hf_cont_3δ.comp_continuous (continuous_const.add (h_cm.smul continuous_const))
          (fun θ => h_in_3δ z hz _ (h_cm_mem θ))
      exact h_dcm.mul (((continuous_const.div h_cm h_ne).pow 1).mul ((h_cm.inv₀ h_ne).mul h_fθ))
    have h_fin_ioc : volume (Set.Ioc (0 : ℝ) (2 * Real.pi)) < ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    refine MeasureTheory.continuousOn_of_dominated
      (bound := fun _ => M / δ)
      (fun z hz => (hG_cont_θ z hz).aestronglyMeasurable)
      (fun z hz => Filter.Eventually.of_forall fun θ => ?_)
      (integrableOn_const (hs := h_fin_ioc.ne))
      (Filter.Eventually.of_forall fun θ => ?_)
    · change ‖G z θ‖ ≤ M / δ
      dsimp [G]
      rw [deriv_circleMap, norm_mul, norm_mul, norm_I, mul_one, norm_circleMap_zero,
        abs_of_pos hδ, norm_mul, norm_mul, one_div, pow_one, norm_inv,
        norm_circleMap_zero, abs_of_pos hδ]
      have hf_le : ‖f (z + circleMap 0 δ θ • e_i)‖ ≤ M := hM_bd _ (h_in_3δ z hz _ (h_cm_mem θ))
      calc δ * (δ⁻¹ * (δ⁻¹ * ‖f (z + circleMap 0 δ θ • e_i)‖))
          ≤ δ * (δ⁻¹ * (δ⁻¹ * M)) := by
            refine mul_le_mul_of_nonneg_left ?_ hδ.le
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hδ.le)
            exact mul_le_mul_of_nonneg_left hf_le (inv_nonneg.mpr hδ.le)
        _ = M / δ := by field_simp [hδ.ne']
    · refine continuousOn_const.mul (continuousOn_const.mul (continuousOn_const.mul ?_))
      exact hf_cont_3δ.comp (continuous_id.add continuous_const).continuousOn
        (fun z hz => h_in_3δ z hz _ (h_cm_mem θ))
  have h_sum_cont : ContinuousOn
      (fun z => ∑ i : Fin n, (fderiv ℂ f z (Pi.single i 1)) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i)
      (Metric.closedBall z₀ δ) := by
    refine continuousOn_finsetSum _ fun i _ => ?_
    let p_i : (Fin n → ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i
    exact (((ContinuousLinearMap.id ℂ ℂ).smulRight p_i).continuous.comp_continuousOn
      (h_coord_cont i)).congr fun z _ => by ext v; simp [p_i]
  have h_fderiv_cont : ContinuousOn (fderiv ℂ f) (Metric.closedBall z₀ δ) :=
    h_sum_cont.congr fun z _ => clm_pi_eq_sum_proj (fderiv ℂ f z)
  exact (h_fderiv_cont.continuousAt (Metric.closedBall_mem_nhds z₀ hδ)).continuousWithinAt

noncomputable def tubeConv {n : ℕ} (f : (Fin n → ℂ) → ℂ) (ψ : (Fin n → ℝ) → ℝ)
    (z : Fin n → ℂ) : ℂ :=
  ∫ t : Fin n → ℝ, f (fun i => z i - (t i : ℂ)) * (ψ t : ℂ)

lemma tube_sub_ofReal_mem {n : ℕ} {V : Set (Fin n → ℝ)} {z : Fin n → ℂ}
    (hz : z ∈ TubeDomain V) (t : Fin n → ℝ) :
    (fun i => z i - (t i : ℂ)) ∈ TubeDomain V := by
  change (fun i => (z i - (t i : ℂ)).im) ∈ V
  have him : (fun i => (z i - (t i : ℂ)).im) = fun i => (z i).im := by
    ext i; simp
  rw [him]
  exact hz

lemma differentiableOn_tubeConv {n : ℕ} {V : Set (Fin n → ℝ)} (hV_open : IsOpen V)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (TubeDomain V))
    {ψ : (Fin n → ℝ) → ℝ} (hψ_cont : Continuous ψ) (hψ_supp : _root_.HasCompactSupport ψ) :
    DifferentiableOn ℂ (tubeConv f ψ) (TubeDomain V) := by
  have hTV_open : IsOpen (TubeDomain V) := isOpen_TubeDomain hV_open
  have hdf_cont : ContinuousOn (fderiv ℂ f) (TubeDomain V) :=
    continuousOn_fderiv_of_differentiableOn hTV_open hf
  intro z₀ hz₀
  rcases (Metric.nhds_basis_closedBall.mem_iff).mp (hTV_open.mem_nhds hz₀) with
    ⟨r₀, hr₀_pos, hr₀_sub⟩
  let δ : ℝ := r₀ / 2
  have hδ : 0 < δ := half_pos hr₀_pos
  have hδ_sub : Metric.closedBall z₀ δ ⊆ TubeDomain V :=
    (Metric.closedBall_subset_closedBall (half_le_self hr₀_pos.le)).trans hr₀_sub
  let K_t : Set (Fin n → ℝ) := tsupport ψ
  have hKt_comp : IsCompact K_t := hψ_supp
  have hKt_meas : MeasurableSet K_t := isClosed_tsupport ψ |>.measurableSet
  have hKt_fin : volume K_t < ⊤ := hKt_comp.measure_lt_top
  let shiftMap : (Fin n → ℂ) × (Fin n → ℝ) → (Fin n → ℂ) :=
    fun p i => p.1 i - (p.2 i : ℂ)
  have hshift_cont : Continuous shiftMap :=
    continuous_pi fun i =>
      ((continuous_apply i).comp continuous_fst).sub
        (Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd))
  let K_prod := Metric.closedBall z₀ δ ×ˢ K_t
  have hKprod_comp : IsCompact K_prod := (isCompact_closedBall z₀ δ).prod hKt_comp
  have hKimg_sub : shiftMap '' K_prod ⊆ TubeDomain V := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, _⟩, rfl⟩
    exact tube_sub_ofReal_mem (hδ_sub hz) t
  rcases ((hKprod_comp.image hshift_cont).image_of_continuousOn
    (hdf_cont.mono hKimg_sub)).isBounded.exists_norm_le with ⟨M_df0, hM_df0⟩
  rcases (hKt_comp.image hψ_cont).isBounded.exists_norm_le with ⟨M_ψ0, hM_ψ0⟩
  let M_df : ℝ := max M_df0 0
  let M_ψ : ℝ := max M_ψ0 0
  let F : (Fin n → ℂ) → (Fin n → ℝ) → ℂ := fun z t => f (fun i => z i - (t i : ℂ)) * (ψ t : ℂ)
  let F' : (Fin n → ℂ) → (Fin n → ℝ) → ((Fin n → ℂ) →L[ℂ] ℂ) :=
    fun z t => (ψ t : ℂ) • fderiv ℂ f (fun i => z i - (t i : ℂ))
  let bound : (Fin n → ℝ) → ℝ := Set.indicator K_t (fun _ => M_ψ * M_df)
  have h_bound_int : Integrable bound volume :=
    (integrableOn_const (hs := hKt_fin.ne) (hC := ENNReal.coe_ne_top)).integrable_indicator hKt_meas
  have hF_meas : ∀ z ∈ Metric.ball z₀ δ, AEStronglyMeasurable (F z) volume := by
    intro z hz
    have hz_TV : z ∈ TubeDomain V := hδ_sub (Metric.ball_subset_closedBall hz)
    have h1 : Continuous (fun t : Fin n → ℝ => f (fun i => z i - (t i : ℂ))) :=
      hf.continuousOn.comp_continuous
        (continuous_pi fun i =>
          continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
        (fun t => tube_sub_ofReal_mem hz_TV t)
    exact (h1.mul (Complex.continuous_ofReal.comp hψ_cont)).aestronglyMeasurable
  have hF_int : Integrable (F z₀) volume := by
    have h1 : Continuous (fun t : Fin n → ℝ => f (fun i => z₀ i - (t i : ℂ))) :=
      hf.continuousOn.comp_continuous
        (continuous_pi fun i =>
          continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
        (fun t => tube_sub_ofReal_mem hz₀ t)
    exact (h1.mul (Complex.continuous_ofReal.comp hψ_cont)).integrable_of_hasCompactSupport
      ((hψ_supp.comp_left Complex.ofReal_zero).mul_left)
  have hF'_meas : AEStronglyMeasurable (F' z₀) volume := by
    have h1 : Continuous (fun t : Fin n → ℝ => fderiv ℂ f (fun i => z₀ i - (t i : ℂ))) :=
      hdf_cont.comp_continuous
        (continuous_pi fun i =>
          continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
        (fun t => tube_sub_ofReal_mem hz₀ t)
    exact ((Complex.continuous_ofReal.comp hψ_cont).smul h1).aestronglyMeasurable
  have h_fderiv : HasFDerivAt (tubeConv f ψ) (∫ t, F' z₀ t) z₀ :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (Metric.ball_mem_nhds z₀ hδ)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hδ) hF_meas)
      hF_int
      hF'_meas
      (Filter.Eventually.of_forall fun t z hz => by
        by_cases ht : t ∈ K_t
        · change ‖F' z t‖ ≤ bound t
          simp only [F', bound, Set.indicator_of_mem ht, norm_smul, Complex.norm_real]
          have hz_cb : z ∈ Metric.closedBall z₀ δ := Metric.ball_subset_closedBall hz
          have hψ_le : ‖ψ t‖ ≤ M_ψ := (hM_ψ0 (ψ t) ⟨t, ht, rfl⟩).trans (le_max_left _ _)
          have hdf_le : ‖fderiv ℂ f (fun i => z i - (t i : ℂ))‖ ≤ M_df :=
            (hM_df0 _ ⟨_, ⟨(z, t), ⟨hz_cb, ht⟩, rfl⟩, rfl⟩).trans (le_max_left _ _)
          exact mul_le_mul hψ_le hdf_le (norm_nonneg _) (le_max_right _ _)
        · change ‖F' z t‖ ≤ bound t
          have hψ0 : ψ t = 0 := image_eq_zero_of_notMem_tsupport ht
          have hF'0 : F' z t = 0 := by
            ext v
            simp [F', hψ0]
          rw [hF'0, norm_zero]
          exact Set.indicator_apply_nonneg fun _ =>
            mul_nonneg (le_max_right _ _) (le_max_right _ _))
      h_bound_int
      (Filter.Eventually.of_forall fun t z hz => by
        have hz_TV : z ∈ TubeDomain V := hδ_sub (Metric.ball_subset_closedBall hz)
        have hw_TV : (fun i => z i - (t i : ℂ)) ∈ TubeDomain V := tube_sub_ofReal_mem hz_TV t
        have hdf_w : HasFDerivAt f (fderiv ℂ f (fun i => z i - (t i : ℂ)))
            (fun i => z i - (t i : ℂ)) :=
          (hf.differentiableAt (hTV_open.mem_nhds hw_TV)).hasFDerivAt
        have h_sub_fderiv : HasFDerivAt (fun w : Fin n → ℂ => fun i => w i - (t i : ℂ))
            (ContinuousLinearMap.id ℂ (Fin n → ℂ)) z := by
          have heq : (fun w : Fin n → ℂ => fun i => w i - (t i : ℂ)) =
              fun w => w - fun i => (t i : ℂ) := by ext w i; rfl
          rw [heq]
          exact (hasFDerivAt_id z).sub_const _
        have h_comp := hdf_w.comp z h_sub_fderiv
        have h_mul := h_comp.mul_const (ψ t : ℂ)
        simpa [F, F', ContinuousLinearMap.comp_id, smul_eq_mul, mul_comm] using h_mul)
  exact h_fderiv.differentiableAt.differentiableWithinAt

noncomputable def dirDerivIter {n : ℕ} (θ' : Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (m : ℕ) (u : Fin n → ℝ) : ℝ :=
  iteratedFDeriv ℝ m ψ u (fun _ : Fin m => θ')

lemma continuous_dirDerivIter {n : ℕ} (θ' : Fin n → ℝ) {ψ : (Fin n → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (m : ℕ) :
    Continuous (dirDerivIter θ' ψ m) := by
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Fin n → ℝ) ℝ (fun _ => θ')
  exact ev.continuous.comp
    (hψ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : (m : ℕ∞) ≤ ⊤)))

lemma tsupport_dirDerivIter_subset {n : ℕ} (θ' : Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ) (m : ℕ) :
    tsupport (dirDerivIter θ' ψ m) ⊆ tsupport ψ := by
  refine closure_minimal ?_ (isClosed_tsupport ψ)
  intro u hu
  by_contra h_not
  have h_ev : ψ =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds h_not] with w hw
    exact image_eq_zero_of_notMem_tsupport hw
  have h_ifd : iteratedFDeriv ℝ m ψ u = 0 := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_ev m).self_of_nhds, iteratedFDeriv_fun_zero]
    rfl
  apply hu
  dsimp [dirDerivIter]
  rw [h_ifd]
  simp

lemma hasCompactSupport_dirDerivIter {n : ℕ} (θ' : Fin n → ℝ) {ψ : (Fin n → ℝ) → ℝ}
    (hψ_supp : _root_.HasCompactSupport ψ) (m : ℕ) :
    _root_.HasCompactSupport (dirDerivIter θ' ψ m) :=
  HasCompactSupport.of_support_subset_isCompact hψ_supp
    (subset_tsupport _ |>.trans (tsupport_dirDerivIter_subset θ' ψ m))

lemma norm_dirDerivIter_le {n : ℕ} (θ' : Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (m : ℕ) (u : Fin n → ℝ) :
    ‖dirDerivIter θ' ψ m u‖ ≤ ‖iteratedFDeriv ℝ m ψ u‖ * ‖θ'‖ ^ m := by
  dsimp [dirDerivIter]
  have h := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ m ψ u) (fun _ : Fin m => θ')
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

lemma hasDerivAt_tubeConv_im_ray {n : ℕ} {V : Set (Fin n → ℝ)} (hV_open : IsOpen V)
    (hV_cone : ∀ v ∈ V, ∀ c : ℝ, c > 0 → (fun i => c * v i) ∈ V)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (TubeDomain V))
    {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_supp : _root_.HasCompactSupport ψ)
    (x θ' : Fin n → ℝ) (hθ' : θ' ∈ V) (m : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt
      (fun t : ℝ => tubeConv f (dirDerivIter θ' ψ m)
        (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I))
      (Complex.I * tubeConv f (dirDerivIter θ' ψ (m + 1))
        (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I)) s := by
  have hTV_open : IsOpen (TubeDomain V) := isOpen_TubeDomain hV_open
  let G_m := tubeConv f (dirDerivIter θ' ψ m)
  have hGm_diff : DifferentiableOn ℂ G_m (TubeDomain V) :=
    differentiableOn_tubeConv hV_open hf (continuous_dirDerivIter θ' hψ m)
      (hasCompactSupport_dirDerivIter θ' hψ_supp m)
  let z_s : Fin n → ℂ := fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I
  have hzs_mem : z_s ∈ TubeDomain V := by
    change (fun i => (z_s i).im) ∈ V
    have him : (fun i => (z_s i).im) = fun i => s * θ' i := by
      ext i; simp [z_s]
    rw [him]
    exact hV_cone θ' hθ' s hs
  have hdf_zs : HasFDerivAt G_m (fderiv ℂ G_m z_s) z_s :=
    (hGm_diff.differentiableAt (hTV_open.mem_nhds hzs_mem)).hasFDerivAt
  let θ_c : Fin n → ℂ := fun i => (θ' i : ℂ)
  have hd_im_line : HasDerivAt
      (fun t : ℝ => fun i : Fin n => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I)
      (Complex.I • θ_c) s := by
    rw [hasDerivAt_pi]
    intro i
    have h1 : HasDerivAt (fun t : ℝ => ((t * θ' i : ℝ) : ℂ)) (θ' i : ℂ) s := by
      have hr : HasDerivAt (fun t : ℝ => t * θ' i) (1 * θ' i) s :=
        (hasDerivAt_id s).mul_const (θ' i)
      rw [one_mul] at hr
      exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hr
    have h2 := (h1.mul_const Complex.I).const_add (x i : ℂ)
    simpa [θ_c, mul_comm Complex.I] using h2
  have hd_im : HasDerivAt
      (fun t : ℝ => G_m (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I))
      (Complex.I * fderiv ℂ G_m z_s θ_c) s := by
    have hc := (hdf_zs.restrictScalars ℝ).comp_hasDerivAt s hd_im_line
    rwa [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul] at hc
  let γ_re : ℝ → (Fin n → ℂ) := fun r i => z_s i + ((r * θ' i : ℝ) : ℂ)
  have hd_re_line : HasDerivAt γ_re θ_c 0 := by
    rw [hasDerivAt_pi]
    intro i
    have hr : HasDerivAt (fun r : ℝ => r * θ' i) (1 * θ' i) 0 :=
      (hasDerivAt_id (0 : ℝ)).mul_const (θ' i)
    rw [one_mul] at hr
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hr).const_add (z_s i)
    simpa [γ_re, θ_c] using hc
  have hγ0 : γ_re 0 = z_s := by ext i; simp [γ_re]
  have hd_re1 : HasDerivAt (fun r : ℝ => G_m (γ_re r)) (fderiv ℂ G_m z_s θ_c) 0 := by
    have hdf0 : HasFDerivAt G_m (fderiv ℂ G_m z_s) (γ_re 0) := hγ0.symm ▸ hdf_zs
    exact (hdf0.restrictScalars ℝ).comp_hasDerivAt 0 hd_re_line
  have h_shift_eq : ∀ r : ℝ, G_m (γ_re r) =
      ∫ u : Fin n → ℝ, f (fun i => z_s i - (u i : ℂ)) *
        (dirDerivIter θ' ψ m (u + r • θ') : ℂ) := by
    intro r
    dsimp [G_m, tubeConv]
    have h_congr : (fun t : Fin n → ℝ => f (fun i => γ_re r i - (t i : ℂ)) *
        (dirDerivIter θ' ψ m t : ℂ)) =
        fun t => f (fun i => z_s i - ((t - r • θ') i : ℂ)) *
          (dirDerivIter θ' ψ m ((t - r • θ') + r • θ') : ℂ) := by
      ext t
      rw [sub_add_cancel]
      congr 2
      ext i
      simp [γ_re]
      ring
    rw [h_congr]
    exact MeasureTheory.integral_sub_right_eq_self
      (fun u => f (fun i => z_s i - (u i : ℂ)) * (dirDerivIter θ' ψ m (u + r • θ') : ℂ)) (r • θ')
  rcases hψ_supp.isBounded.subset_closedBall (0 : Fin n → ℝ) with ⟨R_ψ, hR_ψ⟩
  let R_u : ℝ := max R_ψ 0 + ‖θ'‖ + 1
  have hRu_pos : 0 < R_u := by dsimp [R_u]; positivity
  let K_u : Set (Fin n → ℝ) := Metric.closedBall 0 R_u
  have hKu_meas : MeasurableSet K_u := Metric.isClosed_closedBall.measurableSet
  have hKu_fin : volume K_u < ⊤ := measure_closedBall_lt_top
  have h_supp_u : ∀ r ∈ Set.Ioo (-1 : ℝ) 1, ∀ u : Fin n → ℝ,
      u ∉ K_u → u + r • θ' ∉ tsupport ψ := by
    intro r hr u hu h_mem
    apply hu
    rw [Metric.mem_closedBall, dist_zero_right]
    have h_ur : ‖u + r • θ'‖ ≤ max R_ψ 0 := by
      have h1 : ‖u + r • θ'‖ ≤ R_ψ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hR_ψ h_mem
      exact h1.trans (le_max_left _ _)
    have hr_abs : |r| ≤ 1 := abs_le.mpr ⟨hr.1.le, hr.2.le⟩
    calc ‖u‖ = ‖(u + r • θ') - r • θ'‖ := by abel_nf
      _ ≤ ‖u + r • θ'‖ + ‖r • θ'‖ := norm_sub_le _ _
      _ = ‖u + r • θ'‖ + |r| * ‖θ'‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ max R_ψ 0 + 1 * ‖θ'‖ := by nlinarith [norm_nonneg θ']
      _ ≤ R_u := by dsimp [R_u]; linarith
  have hf_u_cont : Continuous (fun u : Fin n → ℝ => f (fun i => z_s i - (u i : ℂ))) :=
    hf.continuousOn.comp_continuous
      (continuous_pi fun i =>
        continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
      (fun u => tube_sub_ofReal_mem hzs_mem u)
  rcases ((isCompact_closedBall (0 : Fin n → ℝ) R_u).image hf_u_cont).isBounded.exists_norm_le with
    ⟨M_fu0, hM_fu0⟩
  let M_fu : ℝ := max M_fu0 0
  let d_norm : ℝ × (Fin n → ℝ) → ℝ := fun p => ‖dirDerivIter θ' ψ (m + 1) (p.2 + p.1 • θ')‖
  have hd_cont : Continuous d_norm :=
    continuous_norm.comp ((continuous_dirDerivIter θ' hψ (m + 1)).comp
      (continuous_snd.add (continuous_fst.smul continuous_const)))
  rcases ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod
    (isCompact_closedBall (0 : Fin n → ℝ) R_u) |>.image hd_cont).isBounded.exists_norm_le with
    ⟨M_d0, hM_d0⟩
  let M_d : ℝ := max M_d0 0
  let H : ℝ → (Fin n → ℝ) → ℂ := fun r u =>
    f (fun i => z_s i - (u i : ℂ)) * (dirDerivIter θ' ψ m (u + r • θ') : ℂ)
  let H' : ℝ → (Fin n → ℝ) → ℂ := fun r u =>
    f (fun i => z_s i - (u i : ℂ)) * (dirDerivIter θ' ψ (m + 1) (u + r • θ') : ℂ)
  let bound_u : (Fin n → ℝ) → ℝ := Set.indicator K_u (fun _ => M_fu * M_d)
  have hbu_int : Integrable bound_u volume :=
    (integrableOn_const (hs := hKu_fin.ne) (hC := ENNReal.coe_ne_top)).integrable_indicator hKu_meas
  have hH_meas : ∀ j (r : ℝ), AEStronglyMeasurable
      (fun u => f (fun i => z_s i - (u i : ℂ)) * (dirDerivIter θ' ψ j (u + r • θ') : ℂ)) volume :=
    fun j r => (hf_u_cont.mul (Complex.continuous_ofReal.comp
      ((continuous_dirDerivIter θ' hψ j).comp
        (continuous_id.add continuous_const)))).aestronglyMeasurable
  have hH0_int : Integrable (H 0) volume := by
    have h_eq : H 0 = fun u => f (fun i => z_s i - (u i : ℂ)) * (dirDerivIter θ' ψ m u : ℂ) := by
      ext u; simp [H]
    rw [h_eq]
    exact (hf_u_cont.mul (Complex.continuous_ofReal.comp (continuous_dirDerivIter θ' hψ m))
      ).integrable_of_hasCompactSupport
      (((hasCompactSupport_dirDerivIter θ' hψ_supp m).comp_left Complex.ofReal_zero).mul_left)
  have hd_re2_raw := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := H) (F' := H') (bound := bound_u) (s := Set.Ioo (-1 : ℝ) 1)
    (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1))
    (Filter.Eventually.of_forall fun r => hH_meas m r)
    hH0_int
    (hH_meas (m + 1) 0)
    (Filter.Eventually.of_forall fun u r hr => by
      by_cases hu : u ∈ K_u
      · change ‖H' r u‖ ≤ bound_u u
        simp only [H', bound_u, Set.indicator_of_mem hu, norm_mul, Complex.norm_real]
        have hr_cc : r ∈ Set.Icc (-1 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
        have h1 : ‖f (fun i => z_s i - (u i : ℂ))‖ ≤ M_fu :=
          (hM_fu0 _ ⟨u, hu, rfl⟩).trans (le_max_left _ _)
        have h2 : ‖dirDerivIter θ' ψ (m + 1) (u + r • θ')‖ ≤ M_d :=
          (le_abs_self _).trans ((hM_d0 _ ⟨(r, u), ⟨hr_cc, hu⟩, rfl⟩).trans (le_max_left _ _))
        exact mul_le_mul h1 h2 (norm_nonneg _) (le_max_right _ _)
      · change ‖H' r u‖ ≤ bound_u u
        have h_not : u + r • θ' ∉ tsupport (dirDerivIter θ' ψ (m + 1)) := fun hm =>
          h_supp_u r hr u hu (tsupport_dirDerivIter_subset θ' ψ (m + 1) hm)
        have hd0 : dirDerivIter θ' ψ (m + 1) (u + r • θ') = 0 :=
          image_eq_zero_of_notMem_tsupport h_not
        simp [H', bound_u, hu, hd0])
    hbu_int
    (Filter.Eventually.of_forall fun u r _ => by
      have hd_sh := QFT.hasDerivAt_iteratedFDeriv_shift hψ u (-θ') m r
      have h_fn : (fun t : ℝ => iteratedFDeriv ℝ m ψ (u - t • -θ') (fun _ => - -θ')) =
          fun t => dirDerivIter θ' ψ m (u + t • θ') := by
        ext t
        simp [dirDerivIter, sub_neg_eq_add]
      have h_val : iteratedFDeriv ℝ (m + 1) ψ (u - r • -θ') (fun _ => - -θ') =
          dirDerivIter θ' ψ (m + 1) (u + r • θ') := by
        simp [dirDerivIter, sub_neg_eq_add]
      rw [h_fn, h_val] at hd_sh
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hd_sh).const_mul
        (f (fun i => z_s i - (u i : ℂ))))).2
  have h_H'_zero : (∫ u, H' 0 u) = tubeConv f (dirDerivIter θ' ψ (m + 1)) z_s := by
    simp [H', tubeConv]
  rw [h_H'_zero] at hd_re2_raw
  have h_eq_fn : (fun r : ℝ => G_m (γ_re r)) = fun r => ∫ u, H r u := by
    ext r; exact h_shift_eq r
  rw [h_eq_fn] at hd_re1
  have h_eq_deriv : fderiv ℂ G_m z_s θ_c = tubeConv f (dirDerivIter θ' ψ (m + 1)) z_s :=
    hd_re1.unique hd_re2_raw
  rwa [h_eq_deriv] at hd_im

noncomputable def bumpOfPos (n : ℕ) {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : Fin n → ℝ) :=
  ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩

lemma bumpOfPos_integral_pos (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ u : Fin n → ℝ, (bumpOfPos n hε u : ℝ) := by
  let b := bumpOfPos n hε
  have hb_cd : ContDiff ℝ (⊤ : ℕ∞) (b : (Fin n → ℝ) → ℝ) := b.contDiff
  have hb_int : Integrable (b : (Fin n → ℝ) → ℝ) volume :=
    hb_cd.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have h_ball_sub : Metric.ball (0 : Fin n → ℝ) (ε / 2) ⊆ Metric.closedBall 0 b.rIn :=
    Metric.ball_subset_closedBall
  have h_set_le : ∫ x in Metric.ball (0 : Fin n → ℝ) (ε / 2), (b x : ℝ) ≤ ∫ x, (b x : ℝ) :=
    setIntegral_le_integral hb_int (Filter.Eventually.of_forall fun _ => b.nonneg)
  have h_one : ∀ x ∈ Metric.ball (0 : Fin n → ℝ) (ε / 2), (b x : ℝ) = 1 :=
    fun x hx => b.one_of_mem_closedBall (h_ball_sub hx)
  have h_eq_vol : ∫ x in Metric.ball (0 : Fin n → ℝ) (ε / 2), (b x : ℝ) =
      (volume (Metric.ball (0 : Fin n → ℝ) (ε / 2))).toReal := by
    rw [setIntegral_congr_fun measurableSet_ball h_one, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have h_vol_pos : 0 < (volume (Metric.ball (0 : Fin n → ℝ) (ε / 2))).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume 0 (half_pos hε)).ne'
      measure_ball_lt_top.ne
  linarith

noncomputable def unitMollifier (n : ℕ) {ε : ℝ} (hε : 0 < ε) (t : Fin n → ℝ) : ℝ :=
  (∫ u : Fin n → ℝ, (bumpOfPos n hε u : ℝ))⁻¹ * bumpOfPos n hε t

lemma contDiff_unitMollifier (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (unitMollifier n hε) :=
  contDiff_const.mul (bumpOfPos n hε).contDiff

lemma nonneg_unitMollifier (n : ℕ) {ε : ℝ} (hε : 0 < ε) (t : Fin n → ℝ) :
    0 ≤ unitMollifier n hε t :=
  mul_nonneg (inv_nonneg.mpr (bumpOfPos_integral_pos n hε).le) (bumpOfPos n hε).nonneg

lemma tsupport_unitMollifier_subset (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    tsupport (unitMollifier n hε) ⊆ Metric.closedBall 0 ε := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro t ht
  have hb_ne : (bumpOfPos n hε t : ℝ) ≠ 0 := fun h0 => ht (by simp [unitMollifier, h0])
  have ht_ball : t ∈ Metric.ball (0 : Fin n → ℝ) ε := by
    have : t ∈ Function.support (bumpOfPos n hε : (Fin n → ℝ) → ℝ) := hb_ne
    rwa [(bumpOfPos n hε).support_eq] at this
  exact Metric.ball_subset_closedBall ht_ball

lemma hasCompactSupport_unitMollifier (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    _root_.HasCompactSupport (unitMollifier n hε) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 ε)
    ((subset_tsupport _).trans (tsupport_unitMollifier_subset n hε))

lemma integrable_unitMollifier (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (unitMollifier n hε) volume :=
  (contDiff_unitMollifier n hε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_unitMollifier n hε)

lemma integral_unitMollifier (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫ t : Fin n → ℝ, unitMollifier n hε t = 1 := by
  dsimp [unitMollifier]
  rw [MeasureTheory.integral_const_mul]
  exact inv_mul_cancel₀ (bumpOfPos_integral_pos n hε).ne'

lemma tendsto_tubeConv_unitMollifier {n : ℕ} {V : Set (Fin n → ℝ)} (hV_open : IsOpen V)
    {f : (Fin n → ℂ) → ℂ} (hf_cont : ContinuousOn f (TubeDomain V))
    {z : Fin n → ℂ} (hz : z ∈ TubeDomain V)
    {ε_seq : ℕ → ℝ} (hε_pos : ∀ k, 0 < ε_seq k)
    (hε_lim : Filter.Tendsto ε_seq Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => tubeConv f (unitMollifier n (hε_pos k)) z)
      Filter.atTop (nhds (f z)) := by
  have hTV_open : IsOpen (TubeDomain V) := isOpen_TubeDomain hV_open
  let sh : (Fin n → ℝ) → (Fin n → ℂ) := fun t i => z i - (t i : ℂ)
  have hsh_cont : Continuous sh :=
    continuous_pi fun i =>
      continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i))
  have hsh0 : sh 0 = z := by ext i; simp [sh]
  have hf_at : ContinuousAt (f ∘ sh) 0 := by
    have h1 : ContinuousAt f (sh 0) := by
      rw [hsh0]
      exact hf_cont.continuousAt (hTV_open.mem_nhds hz)
    exact h1.comp hsh_cont.continuousAt
  rw [Metric.tendsto_atTop]
  intro η hη
  rcases Metric.continuousAt_iff.mp hf_at (η / 2) (half_pos hη) with ⟨δ, hδ, h_close⟩
  rcases (Metric.tendsto_atTop.mp hε_lim) (δ / 2) (half_pos hδ) with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  have hε_lt : ε_seq k < δ := by
    have h1 := hK k hk
    rw [Real.dist_eq, sub_zero, abs_of_pos (hε_pos k)] at h1
    linarith
  let χ := unitMollifier n (hε_pos k)
  have hχ_int_c : Integrable (fun t => (χ t : ℂ)) volume :=
    Complex.ofRealCLM.integrable_comp (integrable_unitMollifier n (hε_pos k))
  have h_fz_eq : f z = ∫ t, f z * (χ t : ℂ) := by
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal,
      integral_unitMollifier n (hε_pos k), Complex.ofReal_one, mul_one]
  have hf_int : Integrable (fun t => f (sh t) * (χ t : ℂ)) volume :=
    ((hf_cont.comp_continuous hsh_cont fun t => tube_sub_ofReal_mem hz t).mul
      (Complex.continuous_ofReal.comp (contDiff_unitMollifier n (hε_pos k)).continuous)
      ).integrable_of_hasCompactSupport
      (((hasCompactSupport_unitMollifier n (hε_pos k)).comp_left Complex.ofReal_zero).mul_left)
  rw [dist_eq_norm]
  have h_diff : tubeConv f χ z - f z = ∫ t, (f (sh t) - f z) * (χ t : ℂ) := by
    conv_lhs => rw [h_fz_eq]
    dsimp [tubeConv, sh]
    rw [← MeasureTheory.integral_sub hf_int (hχ_int_c.const_mul (f z))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
  rw [h_diff]
  have h_pt : ∀ t : Fin n → ℝ, ‖(f (sh t) - f z) * (χ t : ℂ)‖ ≤ (η / 2) * χ t := by
    intro t
    by_cases hχt : χ t = 0
    · simp [hχt]
    · have ht_supp : t ∈ Metric.closedBall (0 : Fin n → ℝ) (ε_seq k) :=
        tsupport_unitMollifier_subset n (hε_pos k) (subset_tsupport χ hχt)
      have ht_δ : dist t 0 < δ :=
        lt_of_le_of_lt (Metric.mem_closedBall.mp ht_supp) hε_lt
      have hf_le : ‖f (sh t) - f z‖ ≤ η / 2 := by
        have hc := h_close ht_δ
        dsimp [Function.comp] at hc
        rw [hsh0, dist_eq_norm] at hc
        exact hc.le
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (nonneg_unitMollifier n (hε_pos k) t)]
      exact mul_le_mul_of_nonneg_right hf_le (nonneg_unitMollifier n (hε_pos k) t)
  calc ‖∫ t, (f (sh t) - f z) * (χ t : ℂ)‖
      ≤ ∫ t, ‖(f (sh t) - f z) * (χ t : ℂ)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t, (η / 2) * χ t :=
        MeasureTheory.integral_mono
          ((hf_int.sub (hχ_int_c.const_mul (f z))).congr
            (Filter.Eventually.of_forall fun t => by dsimp; ring)).norm
          ((integrable_unitMollifier n (hε_pos k)).const_mul (η / 2)) h_pt
    _ = η / 2 := by
        rw [MeasureTheory.integral_const_mul, integral_unitMollifier n (hε_pos k), mul_one]
    _ < η := half_lt_self hη

noncomputable def shiftedTestFun {n : ℕ} (Ω_n : Opens (Fin n → ℝ))
    {U : Opens (Fin n → ℝ)} (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {r_ψ : ℝ} (hψ_tsupp : tsupport ψ ⊆ Metric.closedBall 0 r_ψ)
    (x : Fin n → ℝ) (hx : Metric.closedBall x r_ψ ⊆ (U : Set (Fin n → ℝ))) : 𝓓(Ω_n, ℝ) where
  toFun u := ψ (x - u)
  contDiff' := hψ.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x r_ψ) ?_
    intro u hu
    have hxu : x - u ∈ tsupport ψ := subset_tsupport ψ hu
    have hnorm : ‖x - u‖ ≤ r_ψ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hψ_tsupp hxu
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hnorm
  tsupport_subset' := by
    refine (closure_minimal ?_ Metric.isClosed_closedBall).trans (hx.trans hU)
    intro u hu
    have hxu : x - u ∈ tsupport ψ := subset_tsupport ψ hu
    have hnorm : ‖x - u‖ ≤ r_ψ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hψ_tsupp hxu
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hnorm

lemma tsupport_shiftedTestFun_subset {n : ℕ} (Ω_n : Opens (Fin n → ℝ))
    {U : Opens (Fin n → ℝ)} (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {r_ψ : ℝ} (hψ_tsupp : tsupport ψ ⊆ Metric.closedBall 0 r_ψ)
    (x : Fin n → ℝ) (hx : Metric.closedBall x r_ψ ⊆ (U : Set (Fin n → ℝ))) :
    tsupport (fun u => shiftedTestFun Ω_n hU ψ hψ hψ_tsupp x hx u) ⊆ (U : Set (Fin n → ℝ)) := by
  refine (closure_minimal ?_ Metric.isClosed_closedBall).trans hx
  intro u hu
  have hxu : x - u ∈ tsupport ψ := subset_tsupport ψ hu
  have hnorm : ‖x - u‖ ≤ r_ψ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hψ_tsupp hxu
  simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hnorm

lemma boundaryIntegral_shiftedTestFun {n : ℕ} (Ω_n : Opens (Fin n → ℝ))
    {U : Opens (Fin n → ℝ)} (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (f : (Fin n → ℂ) → ℂ) (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {r_ψ : ℝ} (hψ_tsupp : tsupport ψ ⊆ Metric.closedBall 0 r_ψ)
    (x : Fin n → ℝ) (hx : Metric.closedBall x r_ψ ⊆ (U : Set (Fin n → ℝ)))
    (y : Fin n → ℝ) :
    boundaryIntegral Ω_n f (shiftedTestFun Ω_n hU ψ hψ hψ_tsupp x hx) y =
      tubeConv f ψ (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) := by
  change (∫ u : Fin n → ℝ, f (fun i => (u i : ℂ) + (y i : ℂ) * Complex.I) * (ψ (x - u) : ℂ)) =
    ∫ t : Fin n → ℝ, f (fun i => ((x i : ℂ) + (y i : ℂ) * Complex.I) - (t i : ℂ)) * (ψ t : ℂ)
  have h_eq : (fun u : Fin n → ℝ =>
      f (fun i => (u i : ℂ) + (y i : ℂ) * Complex.I) * (ψ (x - u) : ℂ)) =
      fun u => (fun t : Fin n → ℝ =>
        f (fun i => ((x i : ℂ) + (y i : ℂ) * Complex.I) - (t i : ℂ)) * (ψ t : ℂ)) (x - u) := by
    ext u
    congr 2
    ext i
    simp
    ring
  rw [h_eq]
  exact MeasureTheory.integral_sub_left_eq_self
    (fun t : Fin n → ℝ =>
      f (fun i => ((x i : ℂ) + (y i : ℂ) * Complex.I) - (t i : ℂ)) * (ψ t : ℂ)) volume x

noncomputable def shiftedBoundaryEval {n : ℕ} (Ω_n : Opens (Fin n → ℝ))
    {U : Opens (Fin n → ℝ)} (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (T : 𝓓'(Ω_n, ℂ)) (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {r_ψ : ℝ} (hψ_tsupp : tsupport ψ ⊆ Metric.closedBall 0 r_ψ)
    (x : Fin n → ℝ) : ℂ :=
  open Classical in
  if hx : Metric.closedBall x r_ψ ⊆ (U : Set (Fin n → ℝ)) then
    T (shiftedTestFun Ω_n hU ψ hψ hψ_tsupp x hx)
  else 0

lemma shiftedBoundaryEval_eq_of_equalOn {n : ℕ} (Ω_n : Opens (Fin n → ℝ))
    {U : Opens (Fin n → ℝ)} (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    {T₁ T₂ : 𝓓'(Ω_n, ℂ)} (h_match : EqualOn Ω_n T₁ T₂ U hU)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {r_ψ : ℝ} (hψ_tsupp : tsupport ψ ⊆ Metric.closedBall 0 r_ψ)
    (x : Fin n → ℝ) :
    shiftedBoundaryEval Ω_n hU T₁ ψ hψ hψ_tsupp x =
      shiftedBoundaryEval Ω_n hU T₂ ψ hψ hψ_tsupp x := by
  classical
  dsimp [shiftedBoundaryEval]
  split_ifs with hx
  · exact h_match _ (tsupport_shiftedTestFun_subset Ω_n hU ψ hψ hψ_tsupp x hx)
  · rfl

lemma closedBall_shift_subset {n : ℕ} {x₀ x : Fin n → ℝ} {R₀ r_ψ : ℝ}
    (hx : x ∈ Metric.closedBall x₀ R₀)
    {S : Set (Fin n → ℝ)} (hS : Metric.closedBall x₀ (R₀ + r_ψ) ⊆ S) :
    Metric.closedBall x r_ψ ⊆ S := by
  intro u hu
  apply hS
  rw [Metric.mem_closedBall] at hx hu ⊢
  exact (dist_triangle u x x₀).trans (by linarith)

lemma exists_uniform_lipschitz_boundary_tubeConv {n : ℕ}
    (Ω_n : Opens (Fin n → ℝ)) {U : Opens (Fin n → ℝ)} (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    {V : Set (Fin n → ℝ)} (hV_open : IsOpen V)
    (hV_cone : ∀ v ∈ V, ∀ c : ℝ, c > 0 → (fun i => c * v i) ∈ V)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (TubeDomain V))
    (hf_growth : HasPolynomialTubeGrowth V f)
    {T : 𝓓'(Ω_n, ℂ)} (hT : HasBoundaryValue Ω_n f V T)
    {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ_supp : _root_.HasCompactSupport ψ)
    {r_ψ : ℝ} (_hr_ψ : 0 < r_ψ) (hψ_tsupp : tsupport ψ ⊆ Metric.closedBall 0 r_ψ)
    (x₀ : Fin n → ℝ) {R₀ : ℝ} (_hR₀ : 0 < R₀)
    (hR_sub : Metric.closedBall x₀ (R₀ + r_ψ) ⊆ (U : Set (Fin n → ℝ)))
    {L_dir : Set (Fin n → ℝ)} (hL_comp : IsCompact L_dir) (hL_ne : L_dir.Nonempty)
    (hL_sub : L_dir ⊆ V) :
    ∃ L_lip : ℝ, 0 ≤ L_lip ∧
      (∀ x ∈ Metric.closedBall x₀ R₀, ∀ θ' ∈ L_dir, ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2),
        ‖tubeConv f ψ (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I) -
          shiftedBoundaryEval Ω_n hU T ψ hψ hψ_tsupp x‖ ≤ L_lip * s) ∧
      ContinuousOn (shiftedBoundaryEval Ω_n hU T ψ hψ hψ_tsupp) (Metric.closedBall x₀ R₀) := by
  classical
  let K_x : Set (Fin n → ℝ) := Metric.closedBall x₀ (R₀ + r_ψ)
  rcases hf_growth K_x L_dir (isCompact_closedBall _ _) hL_comp hL_sub with ⟨N, C_f, hCf_nn, hCf_bd⟩
  rcases hL_comp.isBounded.exists_norm_le with ⟨M_θ0, hM_θ0⟩
  let M_θ : ℝ := max M_θ0 0
  have hM_θ_nn : 0 ≤ M_θ := le_max_right _ _
  have h_ifd_ex : ∀ j : ℕ, ∃ M_j : ℝ, 0 ≤ M_j ∧
      ∀ t ∈ Metric.closedBall (0 : Fin n → ℝ) r_ψ, ‖iteratedFDeriv ℝ j ψ t‖ ≤ M_j := by
    intro j
    have hc : Continuous (fun t => ‖iteratedFDeriv ℝ j ψ t‖) :=
      continuous_norm.comp
        (hψ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤)))
    rcases ((isCompact_closedBall (0 : Fin n → ℝ) r_ψ).image hc).isBounded.exists_norm_le with
      ⟨Mj0, hMj0⟩
    refine ⟨max Mj0 0, le_max_right _ _, fun t ht => ?_⟩
    exact (le_abs_self _).trans ((hMj0 _ ⟨t, ht, rfl⟩).trans (le_max_left _ _))
  choose M_ψ hM_ψ_nn hM_ψ_bd using h_ifd_ex
  let vol_r : ℝ := (volume (Metric.closedBall (0 : Fin n → ℝ) r_ψ)).toReal
  have hvol_nn : 0 ≤ vol_r := ENNReal.toReal_nonneg
  let C_seq : ℕ → ℝ := fun j => C_f * M_ψ j * M_θ ^ j * vol_r
  have hC_seq_nn : ∀ j, 0 ≤ C_seq j := fun j => by
    dsimp [C_seq]
    have := hM_ψ_nn j
    positivity
  have h_ray_bd : ∀ x ∈ Metric.closedBall x₀ R₀, ∀ θ' ∈ L_dir, ∀ j : ℕ,
      ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2),
        ‖tubeConv f (dirDerivIter θ' ψ j)
          (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I)‖ ≤ C_seq j / s ^ N := by
    intro x hx θ' hθ' j s ⟨hs0, hs12⟩
    let z_s : Fin n → ℂ := fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I
    have hzs_mem : z_s ∈ TubeDomain V := by
      change (fun i => (z_s i).im) ∈ V
      have him : (fun i => (z_s i).im) = fun i => s * θ' i := by ext i; simp [z_s]
      rw [him]
      exact hV_cone θ' (hL_sub hθ') s hs0
    have h_int_fn : Integrable (fun t : Fin n → ℝ =>
        f (fun i => z_s i - (t i : ℂ)) * (dirDerivIter θ' ψ j t : ℂ)) volume :=
      ((hf.continuousOn.comp_continuous
        (continuous_pi fun i =>
          continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
        fun t => tube_sub_ofReal_mem hzs_mem t).mul
        (Complex.continuous_ofReal.comp (continuous_dirDerivIter θ' hψ j))
        ).integrable_of_hasCompactSupport
        (((hasCompactSupport_dirDerivIter θ' hψ_supp j).comp_left Complex.ofReal_zero).mul_left)
    let bound_t : (Fin n → ℝ) → ℝ :=
      Set.indicator (Metric.closedBall 0 r_ψ)
        (fun _ => (C_f / s ^ N) * (M_ψ j * M_θ ^ j))
    have hbt_int : Integrable bound_t volume :=
      (integrableOn_const (hs := measure_closedBall_lt_top.ne)
        (hC := ENNReal.coe_ne_top)).integrable_indicator Metric.isClosed_closedBall.measurableSet
    have h_pt : ∀ t : Fin n → ℝ,
        ‖f (fun i => z_s i - (t i : ℂ)) * (dirDerivIter θ' ψ j t : ℂ)‖ ≤ bound_t t := by
      intro t
      by_cases ht : t ∈ Metric.closedBall (0 : Fin n → ℝ) r_ψ
      · simp only [bound_t, Set.indicator_of_mem ht, norm_mul, Complex.norm_real]
        have hxt : x - t ∈ K_x := by
          rw [Metric.mem_closedBall, dist_eq_norm] at hx ⊢
          rw [Metric.mem_closedBall, dist_zero_right] at ht
          calc ‖x - t - x₀‖ = ‖(x - x₀) - t‖ := by abel_nf
            _ ≤ ‖x - x₀‖ + ‖t‖ := norm_sub_le _ _
            _ ≤ R₀ + r_ψ := add_le_add hx ht
        have hf_eq : (fun i => z_s i - (t i : ℂ)) =
            fun i => (((x - t) i : ℝ) : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I := by
          ext i; simp [z_s]; ring
        rw [hf_eq]
        have h1 : ‖f (fun i => (((x - t) i : ℝ) : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I)‖ ≤
            C_f / s ^ N := hCf_bd (x - t) hxt θ' hθ' s hs0 (by linarith)
        have hθ_le : ‖θ'‖ ≤ M_θ := (hM_θ0 θ' hθ').trans (le_max_left _ _)
        have h2 : ‖dirDerivIter θ' ψ j t‖ ≤ M_ψ j * M_θ ^ j :=
          (norm_dirDerivIter_le θ' ψ j t).trans
            (mul_le_mul (hM_ψ_bd j t ht) (pow_le_pow_left₀ (norm_nonneg θ') hθ_le j)
              (pow_nonneg (norm_nonneg θ') j) (hM_ψ_nn j))
        exact mul_le_mul h1 h2 (norm_nonneg _) (div_nonneg hCf_nn (pow_nonneg hs0.le N))
      · have h_not_supp : t ∉ tsupport (dirDerivIter θ' ψ j) := fun hm =>
          ht (hψ_tsupp (tsupport_dirDerivIter_subset θ' ψ j hm))
        have hd0 : dirDerivIter θ' ψ j t = 0 := image_eq_zero_of_notMem_tsupport h_not_supp
        simp [bound_t, ht, hd0]
    calc ‖tubeConv f (dirDerivIter θ' ψ j) z_s‖
        ≤ ∫ t, ‖f (fun i => z_s i - (t i : ℂ)) * (dirDerivIter θ' ψ j t : ℂ)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ t, bound_t t := MeasureTheory.integral_mono h_int_fn.norm hbt_int h_pt
      _ = C_seq j / s ^ N := by
          dsimp [bound_t, C_seq, vol_r]
          rw [MeasureTheory.integral_indicator Metric.isClosed_closedBall.measurableSet,
            setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]
          ring
  let L_lip : ℝ := odeLipschitzBound N C_seq
  have hL_nn : 0 ≤ L_lip := odeLipschitzBound_nonneg N hC_seq_nn
  have h_lip_pair : ∀ x ∈ Metric.closedBall x₀ R₀, ∀ θ' ∈ L_dir,
      ∀ t₁ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ t₂ ∈ Set.Ioc (0 : ℝ) (1 / 2),
        ‖tubeConv f ψ (fun i => (x i : ℂ) + ((t₁ * θ' i : ℝ) : ℂ) * Complex.I) -
          tubeConv f ψ (fun i => (x i : ℂ) + ((t₂ * θ' i : ℝ) : ℂ) * Complex.I)‖ ≤
          L_lip * |t₁ - t₂| := by
    intro x hx θ' hθ' t₁ ht₁ t₂ ht₂
    let F_ray : ℕ → ℝ → ℂ := fun j t =>
      tubeConv f (dirDerivIter θ' ψ j)
        (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I)
    have hF0 : ∀ t : ℝ, F_ray 0 t =
        tubeConv f ψ (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I) := by
      intro t
      have hdir0 : dirDerivIter θ' ψ 0 = ψ := by ext u; simp [dirDerivIter]
      dsimp [F_ray]
      rw [hdir0]
    rw [← hF0 t₁, ← hF0 t₂]
    exact ode_poly_singularity_lipschitz hC_seq_nn
      (fun j t ht => hasDerivAt_tubeConv_im_ray hV_open hV_cone hf hψ hψ_supp
        x θ' (hL_sub hθ') j ht.1)
      (h_ray_bd x hx θ' hθ') t₁ ht₁ t₂ ht₂
  have h_to_bv : ∀ x ∈ Metric.closedBall x₀ R₀, ∀ θ' ∈ L_dir, ∀ s ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖tubeConv f ψ (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I) -
        shiftedBoundaryEval Ω_n hU T ψ hψ hψ_tsupp x‖ ≤ L_lip * s := by
    intro x hx θ' hθ' s hs
    have hx_sub : Metric.closedBall x r_ψ ⊆ (U : Set (Fin n → ℝ)) :=
      closedBall_shift_subset hx hR_sub
    have hB_eq : shiftedBoundaryEval Ω_n hU T ψ hψ hψ_tsupp x =
        T (shiftedTestFun Ω_n hU ψ hψ hψ_tsupp x hx_sub) := by
      simp [shiftedBoundaryEval, hx_sub]
    rw [hB_eq]
    let φ_x := shiftedTestFun Ω_n hU ψ hψ hψ_tsupp x hx_sub
    have h_ray_tendsto : Filter.Tendsto (fun t : ℝ => t • θ')
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 V) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hc : Continuous (fun t : ℝ => t • θ') := continuous_id.smul continuous_const
        have h0 : (0 : ℝ) • θ' = 0 := zero_smul ℝ θ'
        exact h0 ▸ hc.continuousWithinAt.tendsto
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact hV_cone θ' (hL_sub hθ') t ht
    have h_bv_ray : Filter.Tendsto
        (fun t : ℝ => tubeConv f ψ (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (T φ_x)) := by
      have hc := (hT φ_x).comp h_ray_tendsto
      refine hc.congr fun t => ?_
      dsimp [Function.comp]
      rw [boundaryIntegral_shiftedTestFun Ω_n hU f ψ hψ hψ_tsupp x hx_sub (t • θ')]
      rfl
    haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot :=
      nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
    have h_lhs_lim : Filter.Tendsto
        (fun t : ℝ => ‖tubeConv f ψ (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I) -
          tubeConv f ψ (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I)‖)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ‖tubeConv f ψ (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I) - T φ_x‖) :=
      (tendsto_const_nhds.sub h_bv_ray).norm
    have h_rhs_lim : Filter.Tendsto (fun t : ℝ => L_lip * |s - t|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (L_lip * |s - 0|)) := by
      have hc : Continuous (fun t : ℝ => L_lip * |s - t|) :=
        continuous_const.mul (continuous_abs.comp (continuous_const.sub continuous_id))
      exact hc.continuousWithinAt.tendsto
    have h_ev_le : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
        ‖tubeConv f ψ (fun i => (x i : ℂ) + ((s * θ' i : ℝ) : ℂ) * Complex.I) -
          tubeConv f ψ (fun i => (x i : ℂ) + ((t * θ' i : ℝ) : ℂ) * Complex.I)‖ ≤
          L_lip * |s - t| := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht_pos ht_lt
      exact h_lip_pair x hx θ' hθ' s hs t ⟨ht_pos, le_of_lt ht_lt⟩
    have h_res := le_of_tendsto_of_tendsto h_lhs_lim h_rhs_lim h_ev_le
    rwa [sub_zero, abs_of_pos hs.1] at h_res
  refine ⟨L_lip, hL_nn, h_to_bv, ?_⟩
  rcases hL_ne with ⟨θ₀, hθ₀⟩
  intro x₁ hx₁
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let s₀ : ℝ := min (1 / 4) (ε / (4 * (L_lip + 1)))
  have hs₀_pos : 0 < s₀ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hs₀_mem : s₀ ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
    ⟨hs₀_pos, (min_le_left _ _).trans (by norm_num)⟩
  have hs₀_err : L_lip * s₀ ≤ ε / 4 := by
    have h1 : s₀ ≤ ε / (4 * (L_lip + 1)) := min_le_right _ _
    have hL1_ne : L_lip + 1 ≠ 0 := by linarith
    calc L_lip * s₀ ≤ L_lip * (ε / (4 * (L_lip + 1))) := mul_le_mul_of_nonneg_left h1 hL_nn
      _ = (L_lip / (L_lip + 1)) * (ε / 4) := by field_simp [hL1_ne]
      _ ≤ 1 * (ε / 4) :=
          mul_le_mul_of_nonneg_right
            (div_le_one_of_le₀ (by linarith) (by positivity)) (by positivity)
      _ = ε / 4 := one_mul _
  let h_slice : (Fin n → ℝ) → ℂ := fun x =>
    tubeConv f ψ (fun i => (x i : ℂ) + ((s₀ * θ₀ i : ℝ) : ℂ) * Complex.I)
  have h_slice_cont : Continuous h_slice := by
    have hd := differentiableOn_tubeConv hV_open hf hψ.continuous hψ_supp
    refine hd.continuousOn.comp_continuous
      (continuous_pi fun i =>
        (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const)
      fun x => ?_
    change (fun i => (((x i : ℂ) + ((s₀ * θ₀ i : ℝ) : ℂ) * Complex.I)).im) ∈ V
    have him : (fun i => (((x i : ℂ) + ((s₀ * θ₀ i : ℝ) : ℂ) * Complex.I)).im) =
        fun i => s₀ * θ₀ i := by ext i; simp
    rw [him]
    exact hV_cone θ₀ (hL_sub hθ₀) s₀ hs₀_pos
  rcases Metric.continuousAt_iff.mp (h_slice_cont.continuousAt (x := x₁)) (ε / 4)
    (by positivity) with ⟨δ, hδ, hδ_close⟩
  refine ⟨δ, hδ, fun x₂ hx₂ h_dist => ?_⟩
  rw [dist_eq_norm]
  have hb1 := h_to_bv x₁ hx₁ θ₀ hθ₀ s₀ hs₀_mem
  have hb2 := h_to_bv x₂ hx₂ θ₀ hθ₀ s₀ hs₀_mem
  have hm : ‖h_slice x₂ - h_slice x₁‖ < ε / 4 := by
    simpa [dist_eq_norm] using hδ_close h_dist
  let B := shiftedBoundaryEval Ω_n hU T ψ hψ hψ_tsupp
  calc ‖B x₂ - B x₁‖
      = ‖(B x₂ - h_slice x₂) + (h_slice x₂ - h_slice x₁) + (h_slice x₁ - B x₁)‖ := by abel_nf
    _ ≤ ‖B x₂ - h_slice x₂‖ + ‖h_slice x₂ - h_slice x₁‖ + ‖h_slice x₁ - B x₁‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖h_slice x₂ - B x₂‖ + ‖h_slice x₂ - h_slice x₁‖ + ‖h_slice x₁ - B x₁‖ := by
        rw [norm_sub_rev (B x₂)]
    _ < ε / 4 + ε / 4 + ε / 4 := by dsimp [h_slice, B] at hm ⊢; linarith
    _ < ε := by linarith

def orthantSimplex {n : ℕ} (v : Fin n → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (fun α : Fin n → ℝ => ∑ j : Fin n, (α j) • v j) ''
    {α : Fin n → ℝ | (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1}

lemma isCompact_orthantSimplex {n : ℕ} (v : Fin n → (Fin n → ℝ)) :
    IsCompact (orthantSimplex v) := by
  let S_α : Set (Fin n → ℝ) := {α : Fin n → ℝ | (∀ j, 0 ≤ α j) ∧ ∑ j, α j = 1}
  have hS_eq : S_α =
      (Set.pi Set.univ fun _ : Fin n => Set.Icc (0 : ℝ) 1) ∩ {α | ∑ j, α j = 1} := by
    ext α
    simp only [S_α, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_univ_pi, Set.mem_Icc]
    refine ⟨fun ⟨hnn, hsum⟩ => ⟨fun j => ⟨hnn j, ?_⟩, hsum⟩,
      fun ⟨hIcc, hsum⟩ => ⟨fun j => (hIcc j).1, hsum⟩⟩
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ j)
  have hS_comp : IsCompact S_α := by
    rw [hS_eq]
    exact (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (isClosed_eq (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)
  have h_lin_cont : Continuous (fun α : Fin n → ℝ => ∑ j : Fin n, (α j) • v j) :=
    continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const
  exact hS_comp.image h_lin_cont

lemma orthantSimplex_subset {n : ℕ} {V : Set (Fin n → ℝ)} (hV_conv : Convex ℝ V)
    {v : Fin n → (Fin n → ℝ)} (hv : ∀ j, v j ∈ V) :
    orthantSimplex v ⊆ V := by
  rintro _ ⟨α, ⟨hnn, hsum⟩, rfl⟩
  dsimp only
  have hcm : Finset.univ.centerMass α v = ∑ j : Fin n, α j • v j :=
    Finset.centerMass_eq_of_sum_1 Finset.univ v hsum
  rw [← hcm]
  exact hV_conv.centerMass_mem (fun j _ => hnn j) (by linarith) (fun j _ => hv j)

lemma orthantSimplex_nonempty {n : ℕ} (hn : 0 < n) (v : Fin n → (Fin n → ℝ)) :
    (orthantSimplex v).Nonempty := by
  let α₀ : Fin n → ℝ := Pi.single ⟨0, hn⟩ 1
  refine ⟨∑ j : Fin n, (α₀ j) • v j, ⟨α₀, ⟨?_, ?_⟩, rfl⟩⟩
  · intro j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj; simp [α₀]
    · simp [α₀, hj]
  · simp [α₀]

lemma cAffine_posOrthant_decomp {n : ℕ} (hn : 0 < n)
    (v : Fin n → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    {w : Fin n → ℂ} (hw : w ∈ TubeDomain (PosOrthant n)) :
    let M := Matrix.of fun i j => v j i
    let S : ℝ := ∑ j : Fin n, (w j).im
    let θ' : Fin n → ℝ := ∑ j : Fin n, (S⁻¹ * (w j).im) • v j
    0 < S ∧ θ' ∈ orthantSimplex v ∧
      cAffine M x₀ w = fun i =>
        (((x₀ + M.mulVec fun j => (w j).re) i : ℝ) : ℂ) + ((S * θ' i : ℝ) : ℂ) * Complex.I := by
  intro M S θ'
  have hS_pos : 0 < S :=
    lt_of_lt_of_le (hw ⟨0, hn⟩)
      (Finset.single_le_sum (fun j _ => (hw j).le) (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
  have hθ_mem : θ' ∈ orthantSimplex v := by
    refine ⟨fun j => S⁻¹ * (w j).im, ⟨fun j => mul_nonneg (inv_nonneg.mpr hS_pos.le) (hw j).le, ?_⟩,
      rfl⟩
    dsimp [S]
    rw [← Finset.mul_sum, inv_mul_cancel₀ hS_pos.ne']
  refine ⟨hS_pos, hθ_mem, ?_⟩
  ext i
  have hre := congr_fun (cAffine_re M x₀ w) i
  have him := congr_fun (cAffine_im M x₀ w) i
  apply Complex.ext
  · simpa using hre
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    rw [him]
    dsimp [M, Matrix.mulVec, dotProduct, θ']
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hS_pos.ne']

lemma cAffine_negOrthant_decomp {n : ℕ} (hn : 0 < n)
    (v : Fin n → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    {w : Fin n → ℂ} (hw : w ∈ TubeDomain (NegOrthant n)) :
    let M := Matrix.of fun i j => v j i
    let S : ℝ := ∑ j : Fin n, -(w j).im
    let θ' : Fin n → ℝ := -(∑ j : Fin n, (S⁻¹ * -(w j).im) • v j)
    0 < S ∧ θ' ∈ ((fun u : Fin n → ℝ => -u) '' orthantSimplex v) ∧
      cAffine M x₀ w = fun i =>
        (((x₀ + M.mulVec fun j => (w j).re) i : ℝ) : ℂ) + ((S * θ' i : ℝ) : ℂ) * Complex.I := by
  intro M S θ'
  have hw_neg : ∀ j : Fin n, 0 < -(w j).im := fun j => neg_pos.mpr (hw j)
  have hS_pos : 0 < S :=
    lt_of_lt_of_le (hw_neg ⟨0, hn⟩)
      (Finset.single_le_sum (fun j _ => (hw_neg j).le) (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
  have hθ_pos_mem : (∑ j : Fin n, (S⁻¹ * -(w j).im) • v j) ∈ orthantSimplex v := by
    refine ⟨fun j => S⁻¹ * -(w j).im,
      ⟨fun j => mul_nonneg (inv_nonneg.mpr hS_pos.le) (hw_neg j).le, ?_⟩, rfl⟩
    dsimp [S]
    rw [← Finset.mul_sum, inv_mul_cancel₀ hS_pos.ne']
  refine ⟨hS_pos, ⟨_, hθ_pos_mem, rfl⟩, ?_⟩
  ext i
  have hre := congr_fun (cAffine_re M x₀ w) i
  have him := congr_fun (cAffine_im M x₀ w) i
  apply Complex.ext
  · simpa using hre
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    rw [him]
    dsimp [M, Matrix.mulVec, dotProduct, θ']
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_neg,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hS_pos.ne']

lemma sphere_sq_sub_eq_mul_im {R : ℝ} (_hR : 0 ≤ R) {ζ : ℂ} (hζ : ζ ∈ Metric.sphere (0 : ℂ) R) :
    ζ ^ 2 - (R : ℂ) ^ 2 = ζ * (2 * Complex.I * (ζ.im : ℂ)) := by
  have h_norm : ‖ζ‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
  have h_sq : ζ.re ^ 2 + ζ.im ^ 2 = R ^ 2 := by
    have h1 := Complex.normSq_eq_norm_sq ζ
    rw [h_norm, Complex.normSq_apply] at h1
    nlinarith
  apply Complex.ext <;> simp [sq] <;> nlinarith

lemma one_le_norm_sq_sub_five_fourths {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) (3 / 4)) :
    1 ≤ ‖z ^ 2 - ((5 / 4 : ℝ) : ℂ) ^ 2‖ := by
  have hz_le : ‖z‖ ≤ 3 / 4 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hz2_le : ‖z ^ 2‖ ≤ 9 / 16 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have hR2 : ‖(((5 / 4 : ℝ) : ℂ) ^ 2)‖ = 25 / 16 := by
    rw [norm_pow, Complex.norm_real]
    norm_num
  have h_rev : ‖(((5 / 4 : ℝ) : ℂ) ^ 2)‖ - ‖z ^ 2‖ ≤ ‖z ^ 2 - ((5 / 4 : ℝ) : ℂ) ^ 2‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  linarith

lemma tendsto_orthantSliceCoeff_of_poly_im_bound {n : ℕ}
    (g_seq : ℕ → (Fin n → ℂ) → ℂ) (g_lim : (Fin n → ℂ) → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : ∀ k, OrthantEOWData n (g_seq k) ρ)
    {N : ℕ} {C_sl : ℝ} (hC_nn : 0 ≤ C_sl)
    (h_bd : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ζ.im ≠ 0 →
      ∀ k, ‖orthantSlice (g_seq k) 0 y ζ‖ ≤ C_sl / |ζ.im| ^ N)
    (h_pt : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ζ.im ≠ 0 →
      Filter.Tendsto (fun k => orthantSlice (g_seq k) 0 y ζ)
        Filter.atTop (nhds (orthantSlice g_lim 0 y ζ))) :
    ∃ M_star : ℝ, 0 ≤ M_star ∧
      (∀ y ∈ orthantBox n ρ, ∀ m : ℕ, ∀ k : ℕ,
        ‖orthantSliceCoeff (g_seq k) 0 y m‖ ≤ M_star * (4 / 3 : ℝ) ^ m) ∧
      (∀ y ∈ orthantBox n ρ, ∀ m : ℕ, ∃ c : ℂ,
        Filter.Tendsto (fun k => orthantSliceCoeff (g_seq k) 0 y m) Filter.atTop (nhds c)) := by
  let Q : ℂ → ℂ := fun ζ => (ζ ^ 2 - ((5 / 4 : ℝ) : ℂ) ^ 2) ^ (N + 1)
  have hQ_diff : Differentiable ℂ Q :=
    ((differentiable_id.pow 2).sub (differentiable_const _)).pow (N + 1)
  let M_Q : ℝ := C_sl * (5 / 2 : ℝ) ^ (N + 1) * (5 / 4 : ℝ)
  have hMQ_nn : 0 ≤ M_Q := by dsimp [M_Q]; positivity
  let M_star : ℝ := (5 / 2) * M_Q
  have hMs_nn : 0 ≤ M_star := by dsimp [M_star]; positivity
  have hQ_sphere_norm : ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4),
      ‖Q ζ‖ = ((5 / 2) * |ζ.im|) ^ (N + 1) := by
    intro ζ hζ
    have hζ_norm : ‖ζ‖ = 5 / 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
    dsimp [Q]
    rw [sphere_sq_sub_eq_mul_im (by norm_num) hζ, norm_pow]
    congr 1
    rw [norm_mul, norm_mul, norm_mul, hζ_norm, Complex.norm_ofNat, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs]
    ring
  have hQ_prod_bd : ∀ y ∈ orthantBox n ρ, ∀ k : ℕ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4),
      ‖Q ζ * orthantSlice (g_seq k) 0 y ζ‖ ≤ M_Q := by
    intro y hy k ζ hζ
    rw [norm_mul, hQ_sphere_norm ζ hζ]
    by_cases him : ζ.im = 0
    · simp [him, hMQ_nn]
    · have him_pos : 0 < |ζ.im| := abs_pos.mpr him
      have him_le : |ζ.im| ≤ 5 / 4 := by
        have hζ_norm : ‖ζ‖ = 5 / 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
        exact (Complex.abs_im_le_norm ζ).trans_eq hζ_norm
      have hg_le := h_bd y hy ζ hζ him k
      calc ((5 / 2) * |ζ.im|) ^ (N + 1) * ‖orthantSlice (g_seq k) 0 y ζ‖
          ≤ ((5 / 2) * |ζ.im|) ^ (N + 1) * (C_sl / |ζ.im| ^ N) :=
            mul_le_mul_of_nonneg_left hg_le (by positivity)
        _ = C_sl * (5 / 2 : ℝ) ^ (N + 1) * |ζ.im| := by
            rw [mul_pow, pow_succ |ζ.im| N]
            field_simp [him_pos.ne']
        _ ≤ M_Q := by
            dsimp [M_Q]
            exact mul_le_mul_of_nonneg_left him_le (by positivity)
  have hQ_prod_pt : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4),
      Filter.Tendsto (fun k => Q ζ * orthantSlice (g_seq k) 0 y ζ)
        Filter.atTop (nhds (Q ζ * orthantSlice g_lim 0 y ζ)) := by
    intro y hy ζ hζ
    by_cases him : ζ.im = 0
    · have hQ0 : Q ζ = 0 := by
        rw [← norm_eq_zero, hQ_sphere_norm ζ hζ, him, abs_zero, mul_zero,
          zero_pow (Nat.succ_ne_zero N)]
      simp [hQ0]
    · exact (h_pt y hy ζ hζ him).const_mul (Q ζ)
  have h0_le : ‖(0 : Fin n → ℝ)‖ ≤ ρ / 8 := by rw [norm_zero]; positivity
  have h_disc_conv : ∀ y ∈ orthantBox n ρ,
      (∀ k : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) (3 / 4),
        ‖orthantSlice (g_seq k) 0 y z‖ ≤ M_star) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) (3 / 4), ∃ c : ℂ,
        Filter.Tendsto (fun k => orthantSlice (g_seq k) 0 y z) Filter.atTop (nhds c)) := by
    intro y hy
    have hy_pos := orthantBox_subset_posOrthant n hρ hy
    have hy_norm := orthantBox_norm_le hρ hy
    have h_an : ∀ k, AnalyticOnNhd ℂ (orthantSlice (g_seq k) 0 y) (Metric.ball 0 (3 / 2)) :=
      fun k => orthantSlice_analyticOnNhd n (g_seq k) hρ (hdata k) h0_le hy_pos hy_norm
    have h_cauchy_eq : ∀ k : ℕ, ∀ z ∈ Metric.closedBall (0 : ℂ) (3 / 4),
        Q z * orthantSlice (g_seq k) 0 y z =
          (2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C(0, 5 / 4), (ζ - z)⁻¹ • (Q ζ * orthantSlice (g_seq k) 0 y ζ) := by
      intro k z hz
      have hz_ball : z ∈ Metric.ball (0 : ℂ) (5 / 4) := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      have hd_cb : DifferentiableOn ℂ (fun ζ => Q ζ * orthantSlice (g_seq k) 0 y ζ)
          (Metric.closedBall 0 (5 / 4)) := by
        refine hQ_diff.differentiableOn.mul ((h_an k).differentiableOn.mono fun ζ hζ => ?_)
        rw [Metric.mem_closedBall, dist_zero_right] at hζ
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      exact (((hd_cb.mono closure_ball_subset_closedBall).diffContOnCl
        ).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz_ball).symm
    refine ⟨fun k z hz => ?_, fun z hz => ?_⟩
    · have hQ_ge1 : 1 ≤ ‖Q z‖ := by
        dsimp [Q]; rw [norm_pow]; exact one_le_pow₀ (one_le_norm_sq_sub_five_fourths hz)
      have hz_le : ‖z‖ ≤ 3 / 4 := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have h_int_bd :
          ‖∮ ζ in C(0, 5 / 4), (ζ - z)⁻¹ • (Q ζ * orthantSlice (g_seq k) 0 y ζ)‖ ≤
            2 * Real.pi * (5 / 4) * (2 * M_Q) := by
        refine circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) fun ζ hζ => ?_
        have hζ_norm : ‖ζ‖ = 5 / 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
        have h_sub_ge : (1 / 2 : ℝ) ≤ ‖ζ - z‖ := by
          have h1 := norm_sub_norm_le ζ z
          linarith
        have h_inv_le : ‖(ζ - z)⁻¹‖ ≤ 2 := by
          rw [norm_inv]
          have h2 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
          rw [← h2]
          exact (inv_le_inv₀ (by linarith) (by norm_num)).mpr h_sub_ge
        rw [smul_eq_mul, norm_mul]
        exact mul_le_mul h_inv_le (hQ_prod_bd y hy k ζ hζ) (norm_nonneg _) (by norm_num)
      have hQz_le : ‖Q z * orthantSlice (g_seq k) 0 y z‖ ≤ M_star := by
        rw [h_cauchy_eq k z hz, smul_eq_mul, norm_mul, norm_inv, norm_mul, norm_mul,
          Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
          Complex.norm_I, mul_one]
        have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
        calc (2 * Real.pi)⁻¹ * ‖∮ ζ in C(0, 5 / 4), _‖
            ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (5 / 4) * (2 * M_Q)) :=
              mul_le_mul_of_nonneg_left h_int_bd (inv_nonneg.mpr h2pi.le)
          _ = M_star := by dsimp [M_star]; field_simp [h2pi.ne']; ring
      calc ‖orthantSlice (g_seq k) 0 y z‖
          = 1 * ‖orthantSlice (g_seq k) 0 y z‖ := (one_mul _).symm
        _ ≤ ‖Q z‖ * ‖orthantSlice (g_seq k) 0 y z‖ :=
            mul_le_mul_of_nonneg_right hQ_ge1 (norm_nonneg _)
        _ = ‖Q z * orthantSlice (g_seq k) 0 y z‖ := (norm_mul _ _).symm
        _ ≤ M_star := hQz_le
    · have hz_ball : z ∈ Metric.ball (0 : ℂ) (5 / 4) := by
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      have h_cont_sp : ∀ k : ℕ,
          ContinuousOn (fun ζ => Q ζ * orthantSlice (g_seq k) 0 y ζ)
            (Metric.sphere 0 (5 / 4)) := by
        intro k
        refine hQ_diff.continuous.continuousOn.mul ((h_an k).continuousOn.mono fun ζ hζ => ?_)
        rw [Metric.mem_sphere, dist_zero_right] at hζ
        rw [Metric.mem_ball, dist_zero_right, hζ]
        norm_num
      have h_lim_Q := tendsto_circleIntegral_cauchy_of_dominated (R := 5 / 4) (by norm_num)
        (fun k ζ => Q ζ * orthantSlice (g_seq k) 0 y ζ)
        (fun ζ => Q ζ * orthantSlice g_lim 0 y ζ)
        (Filter.Eventually.of_forall h_cont_sp) M_Q
        (Filter.Eventually.of_forall (hQ_prod_bd y hy))
        (hQ_prod_pt y hy) hz_ball
      have h_lim_Q' : Filter.Tendsto (fun k => Q z * orthantSlice (g_seq k) 0 y z)
          Filter.atTop
          (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C(0, 5 / 4), (ζ - z)⁻¹ • (Q ζ * orthantSlice g_lim 0 y ζ))) :=
        h_lim_Q.congr fun k => (h_cauchy_eq k z hz).symm
      have hQz_ne : Q z ≠ 0 := by
        have h1 : 1 ≤ ‖Q z‖ := by
          dsimp [Q]; rw [norm_pow]; exact one_le_pow₀ (one_le_norm_sq_sub_five_fourths hz)
        exact norm_ne_zero_iff.mp (by linarith)
      refine ⟨(Q z)⁻¹ * ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(0, 5 / 4), (ζ - z)⁻¹ • (Q ζ * orthantSlice g_lim 0 y ζ)), ?_⟩
      exact (h_lim_Q'.const_mul (Q z)⁻¹).congr fun k => inv_mul_cancel_left₀ hQz_ne _
  have h_coeff_34 : ∀ y ∈ orthantBox n ρ, ∀ k m : ℕ,
      orthantSliceCoeff (g_seq k) 0 y m =
        (cauchyPowerSeries (orthantSlice (g_seq k) 0 y) 0 (3 / 4) m) (fun _ => 1) := by
    intro y hy k m
    have hy_pos := orthantBox_subset_posOrthant n hρ hy
    have hy_norm := orthantBox_norm_le hρ hy
    have han := orthantSlice_analyticOnNhd n (g_seq k) hρ (hdata k) h0_le hy_pos hy_norm
    have hP54 := orthantSlice_hasFPowerSeriesOnBall n (g_seq k) hρ (hdata k) h0_le hy_pos hy_norm
    have h_coe34 : ((3 / 4 : NNReal) : ℝ) = 3 / 4 := by norm_num
    have hdiff34 : DifferentiableOn ℂ (orthantSlice (g_seq k) 0 y)
        (Metric.closedBall 0 ((3 / 4 : NNReal) : ℝ)) := by
      refine han.differentiableOn.mono fun ζ hζ => ?_
      rw [Metric.mem_closedBall, dist_zero_right, h_coe34] at hζ
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hP34 := hdiff34.hasFPowerSeriesOnBall (by norm_num : (0 : NNReal) < 3 / 4)
    rw [h_coe34] at hP34
    have heq := hP54.hasFPowerSeriesAt.eq_formalMultilinearSeries hP34.hasFPowerSeriesAt
    dsimp [orthantSliceCoeff]
    rw [heq]
  refine ⟨M_star, hMs_nn, fun y hy m k => ?_, fun y hy m => ?_⟩
  · rw [h_coeff_34 y hy k m, cauchyPowerSeries_apply]
    simp only [sub_zero, smul_eq_mul]
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
    have h_int :
        ‖∮ z in C(0, 3 / 4), (1 / z) ^ m * (z⁻¹ * orthantSlice (g_seq k) 0 y z)‖ ≤
          2 * Real.pi * (3 / 4) * ((4 / 3 : ℝ) ^ m * ((4 / 3) * M_star)) := by
      refine circleIntegral.norm_integral_le_of_norm_le_const (by norm_num) fun z hz => ?_
      have hz_norm : ‖z‖ = 3 / 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
      have hz_cb : z ∈ Metric.closedBall (0 : ℂ) (3 / 4) := Metric.sphere_subset_closedBall hz
      rw [norm_mul, norm_mul, one_div, norm_pow, norm_inv, hz_norm]
      have h_inv : (3 / 4 : ℝ)⁻¹ = 4 / 3 := by norm_num
      rw [h_inv]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((h_disc_conv y hy).1 k z hz_cb) (by norm_num)) (by positivity)
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    calc (2 * Real.pi)⁻¹ * ‖∮ z in C(0, 3 / 4), _‖
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * (3 / 4) * ((4 / 3 : ℝ) ^ m * ((4 / 3) * M_star))) :=
          mul_le_mul_of_nonneg_left h_int (inv_nonneg.mpr h2pi.le)
      _ = M_star * (4 / 3 : ℝ) ^ m := by field_simp [h2pi.ne']
  · choose s_lim hs_lim using (h_disc_conv y hy).2
    have h_cm_mem : ∀ θ : ℝ, circleMap (0 : ℂ) (3 / 4) θ ∈ Metric.closedBall 0 (3 / 4) :=
      fun θ => by rw [Metric.mem_closedBall, dist_zero_right, norm_circleMap_zero]; norm_num
    let I_fn : ℕ → ℝ → ℂ := fun k θ =>
      deriv (circleMap 0 (3 / 4)) θ *
        ((1 / circleMap 0 (3 / 4) θ) ^ m *
          ((circleMap 0 (3 / 4) θ)⁻¹ * orthantSlice (g_seq k) 0 y (circleMap 0 (3 / 4) θ)))
    let I_lim : ℝ → ℂ := fun θ =>
      deriv (circleMap 0 (3 / 4)) θ *
        ((1 / circleMap 0 (3 / 4) θ) ^ m *
          ((circleMap 0 (3 / 4) θ)⁻¹ * s_lim (circleMap 0 (3 / 4) θ) (h_cm_mem θ)))
    have h_int_lim : Filter.Tendsto
        (fun k => ∫ θ in (0 : ℝ)..(2 * Real.pi), I_fn k θ)
        Filter.atTop (nhds (∫ θ in (0 : ℝ)..(2 * Real.pi), I_lim θ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => M_star * (4 / 3 : ℝ) ^ m) ?_ ?_ intervalIntegrable_const ?_
      · refine Filter.Eventually.of_forall fun k => ?_
        have hy_pos := orthantBox_subset_posOrthant n hρ hy
        have hy_norm := orthantBox_norm_le hρ hy
        have han := orthantSlice_analyticOnNhd n (g_seq k) hρ (hdata k) h0_le hy_pos hy_norm
        have h_cm : Continuous (circleMap (0 : ℂ) (3 / 4)) := continuous_circleMap 0 (3 / 4)
        have h_dcm : Continuous (deriv (circleMap (0 : ℂ) (3 / 4))) :=
          continuous_deriv_circleMap' 0 (3 / 4)
        have h_ne : ∀ θ : ℝ, circleMap (0 : ℂ) (3 / 4) θ ≠ 0 := fun θ =>
          norm_ne_zero_iff.mp (by rw [norm_circleMap_zero]; norm_num)
        have h_sl : Continuous (fun θ => orthantSlice (g_seq k) 0 y (circleMap 0 (3 / 4) θ)) :=
          han.continuousOn.comp_continuous h_cm fun θ => by
            rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero]; norm_num
        exact (h_dcm.mul (((continuous_const.div h_cm h_ne).pow m).mul
          ((h_cm.inv₀ h_ne).mul h_sl))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun θ _ => ?_
        dsimp [I_fn]
        rw [deriv_circleMap, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero,
          abs_of_pos (by norm_num), norm_mul, norm_mul, one_div, norm_pow, norm_inv,
          norm_circleMap_zero, abs_of_pos (by norm_num)]
        have h_inv : (3 / 4 : ℝ)⁻¹ = 4 / 3 := by norm_num
        rw [h_inv]
        have hg_le := (h_disc_conv y hy).1 k _ (h_cm_mem θ)
        calc (3 / 4 : ℝ) * ((4 / 3 : ℝ) ^ m *
              ((4 / 3) * ‖orthantSlice (g_seq k) 0 y (circleMap 0 (3 / 4) θ)‖))
            ≤ (3 / 4) * ((4 / 3 : ℝ) ^ m * ((4 / 3) * M_star)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hg_le (by norm_num)) (by positivity)
          _ = M_star * (4 / 3 : ℝ) ^ m := by ring
      · refine Filter.Eventually.of_forall fun θ _ => ?_
        dsimp [I_fn, I_lim]
        exact ((hs_lim (circleMap 0 (3 / 4) θ) (h_cm_mem θ)).const_mul _).const_mul _ |>.const_mul _
    refine ⟨(2 * Real.pi * Complex.I : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi), I_lim θ, ?_⟩
    refine (h_int_lim.const_mul (2 * Real.pi * Complex.I : ℂ)⁻¹).congr fun k => ?_
    rw [h_coeff_34 y hy k m, cauchyPowerSeries_apply, circleIntegral]
    simp [I_fn, sub_zero, smul_eq_mul]

def orthantPosOpen (n : ℕ) (r₁ : ℝ) : Set (Fin n → ℂ) :=
  (fun z : Fin n → ℂ => fun i => (z i).re) ⁻¹' Metric.ball (fun _ => r₁ / 4) (r₁ / 8) ∩
    (fun z : Fin n → ℂ => fun i => (z i).im) ⁻¹' Metric.ball (fun _ => r₁ / 4) (r₁ / 8)

def orthantNegOpen (n : ℕ) (r₁ : ℝ) : Set (Fin n → ℂ) :=
  (fun z : Fin n → ℂ => fun i => (z i).re) ⁻¹' Metric.ball (fun _ => r₁ / 4) (r₁ / 8) ∩
    (fun z : Fin n → ℂ => fun i => -(z i).im) ⁻¹' Metric.ball (fun _ => r₁ / 4) (r₁ / 8)

lemma orthantPosNegOpen_props (n : ℕ) {r₁ : ℝ} (hr₁ : 0 < r₁) :
    IsOpen (orthantPosOpen n r₁) ∧ (orthantPosOpen n r₁).Nonempty ∧
      orthantPosOpen n r₁ ⊆ Metric.ball 0 r₁ ∩ TubeDomain (PosOrthant n) ∧
      (∀ z ∈ orthantPosOpen n r₁, ‖z‖ ≤ 3 * r₁ / 4) ∧
    IsOpen (orthantNegOpen n r₁) ∧ (orthantNegOpen n r₁).Nonempty ∧
      orthantNegOpen n r₁ ⊆ Metric.ball 0 r₁ ∩ TubeDomain (NegOrthant n) ∧
      (∀ z ∈ orthantNegOpen n r₁, ‖z‖ ≤ 3 * r₁ / 4) := by
  let a : ℝ := r₁ / 4
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a / 2 = r₁ / 8 := by dsimp [a]; ring
  have hre_c : Continuous (fun z : Fin n → ℂ => fun i => (z i).re) :=
    continuous_pi fun i => Complex.continuous_re.comp (continuous_apply i)
  have him_c : Continuous (fun z : Fin n → ℂ => fun i => (z i).im) :=
    continuous_pi fun i => Complex.continuous_im.comp (continuous_apply i)
  have hnim_c : Continuous (fun z : Fin n → ℂ => fun i => -(z i).im) :=
    continuous_pi fun i => continuous_neg.comp (Complex.continuous_im.comp (continuous_apply i))
  have h1_open : IsOpen (orthantPosOpen n r₁) :=
    (Metric.isOpen_ball.preimage hre_c).inter (Metric.isOpen_ball.preimage him_c)
  have h2_open : IsOpen (orthantNegOpen n r₁) :=
    (Metric.isOpen_ball.preimage hre_c).inter (Metric.isOpen_ball.preimage hnim_c)
  have h1_ne : (orthantPosOpen n r₁).Nonempty := by
    refine ⟨fun _ => (a : ℂ) + Complex.I * (a : ℂ), ?_, ?_⟩
    · rw [Set.mem_preimage]
      convert Metric.mem_ball_self (by positivity : 0 < r₁ / 8) using 1
      ext i; simp [a]
    · rw [Set.mem_preimage]
      convert Metric.mem_ball_self (by positivity : 0 < r₁ / 8) using 1
      ext i; simp [a]
  have h2_ne : (orthantNegOpen n r₁).Nonempty := by
    refine ⟨fun _ => (a : ℂ) - Complex.I * (a : ℂ), ?_, ?_⟩
    · rw [Set.mem_preimage]
      convert Metric.mem_ball_self (by positivity : 0 < r₁ / 8) using 1
      ext i; simp [a]
    · rw [Set.mem_preimage]
      convert Metric.mem_ball_self (by positivity : 0 < r₁ / 8) using 1
      ext i; simp [a]
  have h1_norm : ∀ z ∈ orthantPosOpen n r₁, ‖z‖ ≤ 3 * r₁ / 4 := by
    rintro z ⟨hz_re, hz_im⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hri : |(z i).re - r₁ / 4| < r₁ / 8 := by
      simpa [Real.dist_eq] using
        (dist_le_pi_dist (fun j => (z j).re) (fun _ => r₁ / 4) i).trans_lt
          (Metric.mem_ball.mp hz_re)
    have hii : |(z i).im - r₁ / 4| < r₁ / 8 := by
      simpa [Real.dist_eq] using
        (dist_le_pi_dist (fun j => (z j).im) (fun _ => r₁ / 4) i).trans_lt
          (Metric.mem_ball.mp hz_im)
    rw [abs_lt] at hri hii
    calc ‖z i‖ ≤ |(z i).re| + |(z i).im| := Complex.norm_le_abs_re_add_abs_im (z i)
      _ ≤ 3 * r₁ / 8 + 3 * r₁ / 8 :=
          add_le_add (abs_le.mpr ⟨by linarith, by linarith⟩)
            (abs_le.mpr ⟨by linarith, by linarith⟩)
      _ = 3 * r₁ / 4 := by ring
  have h2_norm : ∀ z ∈ orthantNegOpen n r₁, ‖z‖ ≤ 3 * r₁ / 4 := by
    rintro z ⟨hz_re, hz_im⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    have hri : |(z i).re - r₁ / 4| < r₁ / 8 := by
      simpa [Real.dist_eq] using
        (dist_le_pi_dist (fun j => (z j).re) (fun _ => r₁ / 4) i).trans_lt
          (Metric.mem_ball.mp hz_re)
    have hii : |-(z i).im - r₁ / 4| < r₁ / 8 := by
      simpa [Real.dist_eq] using
        (dist_le_pi_dist (fun j => -(z j).im) (fun _ => r₁ / 4) i).trans_lt
          (Metric.mem_ball.mp hz_im)
    rw [abs_lt] at hri hii
    calc ‖z i‖ ≤ |(z i).re| + |(z i).im| := Complex.norm_le_abs_re_add_abs_im (z i)
      _ ≤ 3 * r₁ / 8 + 3 * r₁ / 8 :=
          add_le_add (abs_le.mpr ⟨by linarith, by linarith⟩)
            (abs_le.mpr ⟨by linarith, by linarith⟩)
      _ = 3 * r₁ / 4 := by ring
  refine ⟨h1_open, h1_ne, ?_, h1_norm, h2_open, h2_ne, ?_, h2_norm⟩
  · intro z hz
    refine ⟨?_, fun i => ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (h1_norm z hz) (by linarith)
    · have hii : |(z i).im - r₁ / 4| < r₁ / 8 := by
        simpa [Real.dist_eq] using
          (dist_le_pi_dist (fun j => (z j).im) (fun _ => r₁ / 4) i).trans_lt
            (Metric.mem_ball.mp hz.2)
      rw [abs_lt] at hii
      linarith
  · intro z hz
    refine ⟨?_, fun i => ?_⟩
    · rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (h2_norm z hz) (by linarith)
    · have hii : |-(z i).im - r₁ / 4| < r₁ / 8 := by
        simpa [Real.dist_eq] using
          (dist_le_pi_dist (fun j => -(z j).im) (fun _ => r₁ / 4) i).trans_lt
            (Metric.mem_ball.mp hz.2)
      rw [abs_lt] at hii
      linarith

lemma orthantPowerSeries_sum_eqOn_posNegOpen {n : ℕ} (hn : 0 < n) (g : (Fin n → ℂ) → ℂ)
    {ρ r₁ : ℝ} (hρ : 0 < ρ) (hr₁ : 0 < r₁) (hr₁_ρ : r₁ ≤ ρ / 8)
    (hdata : OrthantEOWData n g ρ)
    (h_rad : ENNReal.ofNNReal ⟨r₁, hr₁.le⟩ ≤ (orthantPowerSeries n g ρ).radius) :
    EqOn (orthantPowerSeries n g ρ).sum g (orthantPosOpen n r₁) ∧
      EqOn (orthantPowerSeries n g ρ).sum g (orthantNegOpen n r₁) := by
  let P := orthantPowerSeries n g ρ
  let G := P.sum
  let r₁_nn : NNReal := ⟨r₁, hr₁.le⟩
  have hr₁_enn : (0 : ENNReal) < (r₁_nn : ENNReal) := ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hr₁)
  have hG_series : HasFPowerSeriesOnBall G P 0 r₁_nn :=
    (P.hasFPowerSeriesOnBall (lt_of_lt_of_le hr₁_enn h_rad)).mono hr₁_enn h_rad
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 r₁) := by
    intro z hz
    have hze : z ∈ Metric.eball (0 : Fin n → ℂ) r₁_nn := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      change ‖z‖ < r₁
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hG_series.analyticAt_of_mem hze
  have hG_real_pos : ∀ y : Fin n → ℝ, y ∈ PosOrthant n → ‖y‖ < r₁ →
      G (fun i => (y i : ℂ)) = g (fun i => (y i : ℂ)) := by
    intro y hy_pos hy_lt
    have hy_38 : ‖y‖ ≤ 3 * ρ / 8 := by linarith
    have hye : (fun i => (y i : ℂ)) ∈ Metric.eball (0 : Fin n → ℂ) r₁_nn := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      change ‖fun i => (y i : ℂ)‖ < r₁
      refine (pi_norm_lt_iff hr₁).mpr fun i => ?_
      simpa [Complex.norm_real] using (norm_le_pi_norm y i).trans_lt hy_lt
    have h_sumG := hG_series.hasSum hye
    rw [zero_add] at h_sumG
    have h0_le : ‖(0 : Fin n → ℝ)‖ ≤ ρ / 8 := by rw [norm_zero]; positivity
    have hP_y := orthantSlice_hasFPowerSeriesOnBall n g hρ hdata h0_le hy_pos hy_38
    have h1e : (1 : ℂ) ∈ Metric.eball (0 : ℂ) (5 / 4 : NNReal) := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      change ‖(1 : ℂ)‖ < ((5 / 4 : NNReal) : ℝ)
      have hc : ((5 / 4 : NNReal) : ℝ) = 5 / 4 := by norm_num
      rw [hc, norm_one]; norm_num
    have h_sumg := hP_y.hasSum h1e
    rw [zero_add] at h_sumg
    have hg1 : orthantSlice g 0 y 1 = g (fun i => (y i : ℂ)) := by
      dsimp [orthantSlice]; congr 1; ext i; simp
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
  have h_slice_eq : ∀ x y : Fin n → ℝ,
      x ∈ Metric.ball (fun _ => r₁ / 4) (r₁ / 8) →
      y ∈ Metric.ball (fun _ => r₁ / 4) (r₁ / 8) →
      ∀ ζ ∈ Metric.ball (0 : ℂ) (6 / 5),
        G (fun i => (x i : ℂ) + ζ * (y i : ℂ)) = g (fun i => (x i : ℂ) + ζ * (y i : ℂ)) := by
    intro x y hx_b hy_b
    have hx_bounds : ∀ i : Fin n, r₁ / 8 < x i ∧ |x i| < 3 * r₁ / 8 := by
      intro i
      have hdi : |x i - r₁ / 4| < r₁ / 8 := by
        simpa [Real.dist_eq] using
          (dist_le_pi_dist x (fun _ => r₁ / 4) i).trans_lt (Metric.mem_ball.mp hx_b)
      rw [abs_lt] at hdi ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    have hy_bounds : ∀ i : Fin n, r₁ / 8 < y i ∧ |y i| < 3 * r₁ / 8 := by
      intro i
      have hdi : |y i - r₁ / 4| < r₁ / 8 := by
        simpa [Real.dist_eq] using
          (dist_le_pi_dist y (fun _ => r₁ / 4) i).trans_lt (Metric.mem_ball.mp hy_b)
      rw [abs_lt] at hdi ⊢
      exact ⟨by linarith, by linarith, by linarith⟩
    have hx_norm : ‖x‖ ≤ ρ / 8 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      rw [Real.norm_eq_abs]; linarith [(hx_bounds i).2]
    have hy_pos : y ∈ PosOrthant n := fun i => lt_trans (by positivity) (hy_bounds i).1
    have hy_norm : ‖y‖ ≤ 3 * ρ / 8 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      rw [Real.norm_eq_abs]; linarith [(hy_bounds i).2]
    let γ : ℂ → (Fin n → ℂ) := fun ζ i => (x i : ℂ) + ζ * (y i : ℂ)
    have hγ_an : ∀ ζ : ℂ, AnalyticAt ℂ γ ζ := by
      let L : ℂ →L[ℂ] (Fin n → ℂ) :=
        ContinuousLinearMap.pi fun i =>
          (ContinuousLinearMap.id ℂ ℂ).smulRight (y i : ℂ)
      intro ζ
      have heq : γ = fun w => (fun i => (x i : ℂ)) + L w := by ext w i; simp [γ, L]
      rw [heq]
      exact analyticAt_const.add (L.analyticAt ζ)
    have hγ_r1 : ∀ ζ ∈ Metric.ball (0 : ℂ) (6 / 5), γ ζ ∈ Metric.ball (0 : Fin n → ℂ) r₁ := by
      intro ζ hζ
      have hζ_lt : ‖ζ‖ < 6 / 5 := by simpa using hζ
      rw [Metric.mem_ball, dist_zero_right]
      refine (pi_norm_lt_iff hr₁).mpr fun i => ?_
      calc ‖(x i : ℂ) + ζ * (y i : ℂ)‖
          ≤ |x i| + ‖ζ‖ * |y i| := by
            simpa [Complex.norm_real] using norm_add_le (x i : ℂ) (ζ * (y i : ℂ))
        _ < 3 * r₁ / 8 + (6 / 5) * (3 * r₁ / 8) := by
            nlinarith [(hx_bounds i).2, (hy_bounds i).2, abs_nonneg (y i), norm_nonneg ζ]
        _ < r₁ := by linarith
    have hGγ_an : AnalyticOnNhd ℂ (G ∘ γ) (Metric.ball 0 (6 / 5)) :=
      fun ζ hζ => (hG_an (γ ζ) (hγ_r1 ζ hζ)).comp (hγ_an ζ)
    have hgγ_an : AnalyticOnNhd ℂ (g ∘ γ) (Metric.ball 0 (6 / 5)) :=
      (orthantSlice_analyticOnNhd n g hρ hdata hx_norm hy_pos hy_norm).mono
        (Metric.ball_subset_ball (by norm_num))
    have h_real_ev : ∀ᶠ t : ℝ in nhds 0, (G ∘ γ) (t : ℂ) = (g ∘ γ) (t : ℂ) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Set.Ioo (-1 / 4) (1 / 4) by norm_num)]
        with t ht
      have h_pos_t : (fun i => x i + t * y i) ∈ PosOrthant n := by
        intro i
        have hxi := (hx_bounds i).1
        have hyi := (hy_bounds i).2
        rw [abs_lt] at hyi
        nlinarith [ht.1, ht.2]
      have h_norm_t : ‖fun i => x i + t * y i‖ < r₁ := by
        refine (pi_norm_lt_iff hr₁).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        have hxi := (hx_bounds i).2
        have hyi := (hy_bounds i).2
        have ht_abs : |t| < 1 / 4 := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
        calc |x i + t * y i| ≤ |x i| + |t| * |y i| := by
              simpa [abs_mul] using abs_add_le (x i) (t * y i)
          _ < 3 * r₁ / 8 + (1 / 4) * (3 * r₁ / 8) := by nlinarith [abs_nonneg (y i)]
          _ < r₁ := by linarith
      have hγ_t : γ (t : ℂ) = fun i => ((x i + t * y i : ℝ) : ℂ) := by ext i; simp [γ]
      dsimp [Function.comp]
      rw [hγ_t]
      exact hG_real_pos _ h_pos_t h_norm_t
    have h_ev0 := Analysis.analytic_nhds_eq_of_real_eq_1D (G ∘ γ) (g ∘ γ) 0
      (hGγ_an 0 (by simp)) (hgγ_an 0 (by simp)) h_real_ev
    exact hGγ_an.eqOn_of_preconnected_of_eventuallyEq hgγ_an
      (convex_ball (0 : ℂ) (6 / 5)).isPreconnected (by simp) h_ev0
  refine ⟨fun z ⟨hz_re, hz_im⟩ => ?_, fun z ⟨hz_re, hz_im⟩ => ?_⟩
  · have hz_eq : z = fun i => (((z i).re : ℂ) + Complex.I * ((z i).im : ℂ)) := by
      ext i; exact (Complex.re_add_im (z i)).symm.trans (by ring_nf)
    conv_lhs => rw [hz_eq]
    conv_rhs => rw [hz_eq]
    exact h_slice_eq (fun i => (z i).re) (fun i => (z i).im) hz_re hz_im Complex.I
      (by rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]; norm_num)
  · have hz_eq : z = fun i => (((z i).re : ℂ) + (-Complex.I) * ((-(z i).im : ℝ) : ℂ)) := by
      ext i; push_cast; exact (Complex.re_add_im (z i)).symm.trans (by ring_nf)
    conv_lhs => rw [hz_eq]
    conv_rhs => rw [hz_eq]
    exact h_slice_eq (fun i => (z i).re) (fun i => -(z i).im) hz_re hz_im (-Complex.I)
      (by rw [Metric.mem_ball, dist_zero_right, norm_neg, Complex.norm_I]; norm_num)

lemma norm_orthantPowerSeries_le_of_sliceCoeff_geom {n : ℕ} (_hn : 0 < n) (g : (Fin n → ℂ) → ℂ)
    {ρ M_star : ℝ} (hρ : 0 < ρ) (hMs_nn : 0 ≤ M_star)
    (h_coeff : ∀ y ∈ orthantBox n ρ, ∀ m : ℕ,
      ‖orthantSliceCoeff g 0 y m‖ ≤ M_star * (4 / 3 : ℝ) ^ m) (m : ℕ) :
    ‖orthantPowerSeries n g ρ m‖ ≤ M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m := by
  dsimp [orthantPowerSeries]
  refine (norm_sum_le Finset.univ _).trans ?_
  cases m with
  | zero =>
    simp only [Finset.univ_unique, Finset.sum_singleton, pow_zero, mul_one,
      norm_smul, orthantBasisCoeff]
    have hy0_box : (fun _ : Fin n => ρ / 4) ∈ orthantBox n ρ := fun _ => ⟨by linarith, by linarith⟩
    have hc : ‖orthantSliceCoeff g 0 (fun _ => ρ / 4) 0‖ ≤ M_star := by
      simpa using h_coeff _ hy0_box 0
    exact (mul_le_of_le_one_right (norm_nonneg _) (orthantMonomial_norm_le n 0 _)).trans hc
  | succ m =>
    let k := m + 1
    have hk : 0 < k := Nat.succ_pos m
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have h_fac_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
    let M_k : ℝ := M_star * (4 / 3 : ℝ) ^ k
    have hMk_nn : 0 ≤ M_k := by dsimp [M_k]; positivity
    have h_each : ∀ α : Fin k → Fin n,
        ‖orthantBasisCoeff n g ρ 0 k α • orthantMonomial n k α‖ ≤
          M_k * (16 * Real.exp 1 / ρ) ^ k := by
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
              orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k‖ ≤ (2 : ℝ) ^ k * M_k := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ S : Finset (Fin k), ‖(-1 : ℂ) ^ (k - S.card) *
                orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k‖
            ≤ ∑ _S : Finset (Fin k), M_k := by
              refine Finset.sum_le_sum fun S _ => ?_
              rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
              exact h_coeff _ (orthantYStep_mem_box hρ hk α S) k
          _ = (2 : ℝ) ^ k * M_k := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
                nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      have h_exp : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1) ^ k := by
        have h1 := Real.pow_div_factorial_le_exp (k : ℝ) hk_pos.le k
        have h2 : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
          rw [← mul_one (k : ℝ), Real.exp_nat_mul]
        rwa [h2] at h1
      have h_alg : ((k.factorial : ℝ) * (ρ / (8 * (k : ℝ))) ^ k)⁻¹ * ((2 : ℝ) ^ k * M_k) =
          M_k * (16 / ρ) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by
        have h16 : (16 / ρ) ^ k = (2 : ℝ) ^ k * (8 / ρ) ^ k := by
          rw [← mul_pow]; congr 1; ring
        have h8 : (ρ / (8 * (k : ℝ))) ^ k = ((8 / ρ) ^ k)⁻¹ * ((k : ℝ) ^ k)⁻¹ := by
          rw [← inv_pow, ← inv_pow, ← mul_pow]; congr 1; field_simp [hρ.ne', hk_pos.ne']
        have h8_ne : (8 / ρ) ^ k ≠ 0 := pow_ne_zero k (by positivity)
        have hk_ne : (k : ℝ) ^ k ≠ 0 := pow_ne_zero k hk_pos.ne'
        rw [h16, h8]
        field_simp [h_fac_pos.ne', h8_ne, hk_ne]
      calc ((k.factorial : ℝ) * (ρ / (8 * (k : ℝ))) ^ k)⁻¹ *
            ‖∑ S : Finset (Fin k), (-1 : ℂ) ^ (k - S.card) *
              orthantSliceCoeff g 0 (orthantYStep n ρ k α S) k‖
          ≤ ((k.factorial : ℝ) * (ρ / (8 * (k : ℝ))) ^ k)⁻¹ * ((2 : ℝ) ^ k * M_k) :=
            mul_le_mul_of_nonneg_left h_sum_le (by positivity)
        _ = M_k * (16 / ρ) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := h_alg
        _ ≤ M_k * (16 / ρ) ^ k * (Real.exp 1) ^ k :=
            mul_le_mul_of_nonneg_left h_exp (by positivity)
        _ = M_k * (16 * Real.exp 1 / ρ) ^ k := by
            rw [mul_assoc, ← mul_pow]; congr 2; ring
    have h43_le : (4 / 3 : ℝ) ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) k
    calc ∑ α : Fin k → Fin n, ‖orthantBasisCoeff n g ρ 0 k α • orthantMonomial n k α‖
        ≤ ∑ _α : Fin k → Fin n, (M_k * (16 * Real.exp 1 / ρ) ^ k) :=
          Finset.sum_le_sum fun α _ => h_each α
      _ = ((n : ℝ) ^ k) * (M_k * (16 * Real.exp 1 / ρ) ^ k) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      _ = M_star * ((4 / 3 : ℝ) ^ k * ((16 * Real.exp 1 / ρ) ^ k * (n : ℝ) ^ k)) := by
          dsimp [M_k]; ring
      _ ≤ M_star * ((2 : ℝ) ^ k * ((16 * Real.exp 1 / ρ) ^ k * (n : ℝ) ^ k)) := by
          refine mul_le_mul_of_nonneg_left ?_ hMs_nn
          exact mul_le_mul_of_nonneg_right h43_le (by positivity)
      _ = M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ k := by
          congr 1
          rw [← mul_pow, ← mul_pow]
          congr 1; ring

lemma orthantEOWCore_of_mollified_seq {n : ℕ} (hn : 0 < n)
    (g_seq : ℕ → (Fin n → ℂ) → ℂ) (g_lim : (Fin n → ℂ) → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : ∀ k, OrthantEOWData n (g_seq k) ρ)
    {N : ℕ} {C_sl : ℝ} (hC_nn : 0 ≤ C_sl)
    (h_bd : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ζ.im ≠ 0 →
      ∀ k, ‖orthantSlice (g_seq k) 0 y ζ‖ ≤ C_sl / |ζ.im| ^ N)
    (h_pt_sphere : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ζ.im ≠ 0 →
      Filter.Tendsto (fun k => orthantSlice (g_seq k) 0 y ζ)
        Filter.atTop (nhds (orthantSlice g_lim 0 y ζ)))
    (h_pt_pos : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (ρ / 8) ∩ TubeDomain (PosOrthant n),
      Filter.Tendsto (fun k => g_seq k w) Filter.atTop (nhds (g_lim w)))
    (h_pt_neg : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) (ρ / 8) ∩ TubeDomain (NegOrthant n),
      Filter.Tendsto (fun k => g_seq k w) Filter.atTop (nhds (g_lim w))) :
    OrthantEOWCore n g_lim := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨M_star, hMs_nn, h_coeff_bd, h_coeff_conv⟩ :=
    tendsto_orthantSliceCoeff_of_poly_im_bound g_seq g_lim hρ hdata hC_nn h_bd h_pt_sphere
  have h_basis_conv : ∀ m : ℕ, ∀ α : Fin m → Fin n, ∃ c : ℂ,
      Filter.Tendsto (fun k => orthantBasisCoeff n (g_seq k) ρ 0 m α)
        Filter.atTop (nhds c) := by
    intro m α
    cases m with
    | zero =>
      have hy0_box : (fun _ : Fin n => ρ / 4) ∈ orthantBox n ρ :=
        fun _ => ⟨by linarith, by linarith⟩
      rcases h_coeff_conv _ hy0_box 0 with ⟨c, hc⟩
      exact ⟨c, hc⟩
    | succ m =>
      let m1 := m + 1
      have hm1 : 0 < m1 := Nat.succ_pos m
      have h_each_S : ∀ S : Finset (Fin m1), ∃ c : ℂ,
          Filter.Tendsto
            (fun k => orthantSliceCoeff (g_seq k) 0 (orthantYStep n ρ m1 α S) m1)
            Filter.atTop (nhds c) :=
        fun S => h_coeff_conv _ (orthantYStep_mem_box hρ hm1 α S) m1
      choose cS hcS using h_each_S
      refine ⟨(((m1.factorial : ℂ) * ((ρ / (8 * (m1 : ℝ)) : ℝ) : ℂ) ^ m1)⁻¹ *
        ∑ S : Finset (Fin m1), (-1 : ℂ) ^ (m1 - S.card) * cS S), ?_⟩
      dsimp [orthantBasisCoeff]
      exact (tendsto_finsetSum _ fun S _ => (hcS S).const_mul _).const_mul _
  choose c_lim hc_lim using h_basis_conv
  let P_lim : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ :=
    fun m => ∑ α : Fin m → Fin n, c_lim m α • orthantMonomial n m α
  have hP_seq_norm : ∀ k m : ℕ,
      ‖orthantPowerSeries n (g_seq k) ρ m‖ ≤
        M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m :=
    fun k m => norm_orthantPowerSeries_le_of_sliceCoeff_geom hn (g_seq k) hρ hMs_nn
      (fun y hy q => h_coeff_bd y hy q k) m
  have hP_conv : ∀ m : ℕ,
      Filter.Tendsto (fun k => orthantPowerSeries n (g_seq k) ρ m)
        Filter.atTop (nhds (P_lim m)) := by
    intro m
    dsimp [orthantPowerSeries, P_lim]
    exact tendsto_finsetSum _ fun α _ => (hc_lim m α).smul_const _
  have hP_lim_norm : ∀ m : ℕ,
      ‖P_lim m‖ ≤ M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m := fun m =>
    le_of_tendsto (tendsto_norm.comp (hP_conv m))
      (Filter.Eventually.of_forall fun k => hP_seq_norm k m)
  let r₁ : ℝ := min (ρ / 8) (ρ / (64 * Real.exp 1 * (n : ℝ)))
  have hr₁_pos : 0 < r₁ := lt_min (by positivity) (by positivity)
  have hr₁_ρ8 : r₁ ≤ ρ / 8 := min_le_left _ _
  let r₁_nn : NNReal := ⟨r₁, hr₁_pos.le⟩
  have h_rad_of_bd : ∀ P : FormalMultilinearSeries ℂ (Fin n → ℂ) ℂ,
      (∀ m, ‖P m‖ ≤ M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m) →
      (r₁_nn : ENNReal) ≤ P.radius := by
    intro P hP_bd
    refine FormalMultilinearSeries.le_radius_of_bound P M_star fun m => ?_
    have hr_le : (r₁_nn : ℝ) ≤ ρ / (64 * Real.exp 1 * (n : ℝ)) := min_le_right _ _
    have h_prod : (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m * (r₁_nn : ℝ) ^ m ≤ 1 := by
      rw [← mul_pow]
      refine pow_le_one₀ (by positivity) ?_
      have h1 : (32 * Real.exp 1 * (n : ℝ) / ρ) * (r₁_nn : ℝ) ≤
          (32 * Real.exp 1 * (n : ℝ) / ρ) * (ρ / (64 * Real.exp 1 * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hr_le (by positivity)
      have h2 : (32 * Real.exp 1 * (n : ℝ) / ρ) * (ρ / (64 * Real.exp 1 * (n : ℝ))) = 1 / 2 := by
        have he : (Real.exp 1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
        field_simp [hρ.ne', hn_pos.ne', he]
        ring
      linarith
    calc ‖P m‖ * (r₁_nn : ℝ) ^ m
        ≤ (M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m) * (r₁_nn : ℝ) ^ m :=
          mul_le_mul_of_nonneg_right (hP_bd m) (pow_nonneg hr₁_pos.le m)
      _ = M_star * ((32 * Real.exp 1 * (n : ℝ) / ρ) ^ m * (r₁_nn : ℝ) ^ m) := by ring
      _ ≤ M_star * 1 := mul_le_mul_of_nonneg_left h_prod hMs_nn
      _ = M_star := mul_one _
  have hr₁_enn : (0 : ENNReal) < (r₁_nn : ENNReal) :=
    ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hr₁_pos)
  have hPlim_rad : (r₁_nn : ENNReal) ≤ P_lim.radius := h_rad_of_bd P_lim hP_lim_norm
  let G_lim : (Fin n → ℂ) → ℂ := P_lim.sum
  have hG_series : HasFPowerSeriesOnBall G_lim P_lim 0 r₁_nn :=
    (P_lim.hasFPowerSeriesOnBall (lt_of_lt_of_le hr₁_enn hPlim_rad)).mono hr₁_enn hPlim_rad
  have hG_an : AnalyticOnNhd ℂ G_lim (Metric.ball 0 r₁) := by
    intro z hz
    have hze : z ∈ Metric.eball (0 : Fin n → ℂ) r₁_nn := by
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe]
      change ‖z‖ < r₁
      simpa [Metric.mem_ball, dist_zero_right] using hz
    exact hG_series.analyticAt_of_mem hze
  have h_sum_tendsto : ∀ w : Fin n → ℂ, ‖w‖ ≤ 3 * r₁ / 4 →
      Filter.Tendsto (fun k => (orthantPowerSeries n (g_seq k) ρ).sum w)
        Filter.atTop (nhds (G_lim w)) := by
    intro w hw
    have hw_le : ‖w‖ ≤ ρ / (64 * Real.exp 1 * (n : ℝ)) := by
      have hr_le : r₁ ≤ ρ / (64 * Real.exp 1 * (n : ℝ)) := min_le_right _ _
      linarith [norm_nonneg w]
    change Filter.Tendsto
      (fun k => ∑' m : ℕ, (orthantPowerSeries n (g_seq k) ρ m) (fun _ => w))
      Filter.atTop (nhds (∑' m : ℕ, (P_lim m) (fun _ => w)))
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun m : ℕ => M_star * (1 / 2 : ℝ) ^ m)
      (summable_geometric_two.mul_left M_star)
      (fun m => ?_)
      (Filter.Eventually.of_forall fun k m => ?_)
    · let ev := ContinuousMultilinearMap.apply ℂ (fun _ : Fin m => Fin n → ℂ) ℂ (fun _ => w)
      exact ev.continuous.tendsto _ |>.comp (hP_conv m)
    · have h_op := ContinuousMultilinearMap.le_opNorm
        (orthantPowerSeries n (g_seq k) ρ m) (fun _ : Fin m => w)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h_op
      have h_prod : (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m * ‖w‖ ^ m ≤ (1 / 2 : ℝ) ^ m := by
        rw [← mul_pow]
        refine pow_le_pow_left₀ (by positivity) ?_ m
        have h1 : (32 * Real.exp 1 * (n : ℝ) / ρ) * ‖w‖ ≤
            (32 * Real.exp 1 * (n : ℝ) / ρ) * (ρ / (64 * Real.exp 1 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hw_le (by positivity)
        have h2 : (32 * Real.exp 1 * (n : ℝ) / ρ) * (ρ / (64 * Real.exp 1 * (n : ℝ))) = 1 / 2 := by
          have he : (Real.exp 1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
          field_simp [hρ.ne', hn_pos.ne', he]
          ring
        linarith
      calc ‖(orthantPowerSeries n (g_seq k) ρ m) (fun _ => w)‖
          ≤ ‖orthantPowerSeries n (g_seq k) ρ m‖ * ‖w‖ ^ m := h_op
        _ ≤ (M_star * (32 * Real.exp 1 * (n : ℝ) / ρ) ^ m) * ‖w‖ ^ m :=
            mul_le_mul_of_nonneg_right (hP_seq_norm k m) (pow_nonneg (norm_nonneg w) m)
        _ = M_star * ((32 * Real.exp 1 * (n : ℝ) / ρ) ^ m * ‖w‖ ^ m) := by ring
        _ ≤ M_star * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_left h_prod hMs_nn
  obtain ⟨hW₁_open, hW₁_ne, hW₁_sub, hW₁_norm, hW₂_open, hW₂_ne, hW₂_sub, hW₂_norm⟩ :=
    orthantPosNegOpen_props n hr₁_pos
  have h_eq_k : ∀ k : ℕ,
      EqOn (orthantPowerSeries n (g_seq k) ρ).sum (g_seq k) (orthantPosOpen n r₁) ∧
        EqOn (orthantPowerSeries n (g_seq k) ρ).sum (g_seq k) (orthantNegOpen n r₁) :=
    fun k => orthantPowerSeries_sum_eqOn_posNegOpen hn (g_seq k) hρ hr₁_pos hr₁_ρ8 (hdata k)
      (h_rad_of_bd _ (hP_seq_norm k))
  refine ⟨r₁, hr₁_pos, G_lim, hG_an,
    ⟨orthantPosOpen n r₁, hW₁_open, hW₁_ne, hW₁_sub, fun w hw => ?_⟩,
    ⟨orthantNegOpen n r₁, hW₂_open, hW₂_ne, hW₂_sub, fun w hw => ?_⟩⟩
  · have hw_ρ8 : w ∈ Metric.ball (0 : Fin n → ℂ) (ρ / 8) ∩ TubeDomain (PosOrthant n) :=
      ⟨Metric.ball_subset_ball hr₁_ρ8 (hW₁_sub hw).1, (hW₁_sub hw).2⟩
    have h1 := h_sum_tendsto w (hW₁_norm w hw)
    have h2 : Filter.Tendsto (fun k => (orthantPowerSeries n (g_seq k) ρ).sum w)
        Filter.atTop (nhds (g_lim w)) :=
      (h_pt_pos w hw_ρ8).congr fun k => ((h_eq_k k).1 hw).symm
    exact tendsto_nhds_unique h1 h2
  · have hw_ρ8 : w ∈ Metric.ball (0 : Fin n → ℂ) (ρ / 8) ∩ TubeDomain (NegOrthant n) :=
      ⟨Metric.ball_subset_ball hr₁_ρ8 (hW₂_sub hw).1, (hW₂_sub hw).2⟩
    have h1 := h_sum_tendsto w (hW₂_norm w hw)
    have h2 : Filter.Tendsto (fun k => (orthantPowerSeries n (g_seq k) ρ).sum w)
        Filter.atTop (nhds (g_lim w)) :=
      (h_pt_neg w hw_ρ8).congr fun k => ((h_eq_k k).2 hw).symm
    exact tendsto_nhds_unique h1 h2

theorem local_eow_of_tempered_boundary {n : ℕ}
    (Ω_n : Opens (Fin n → ℝ))
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_minus_open : IsOpen V_minus)
    (h_opposite : V_minus = (fun v => -v) '' V_plus)
    (hV_plus_conv : Convex ℝ V_plus)
    (hV_ne : V_plus.Nonempty)
    (h0_not_mem : (0 : Fin n → ℝ) ∉ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ c : ℝ, c > 0 → (fun i => c * v i) ∈ V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (hf_plus_growth : HasPolynomialTubeGrowth V_plus f_plus)
    (hf_minus_growth : HasPolynomialTubeGrowth V_minus f_minus)
    (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (T_plus : 𝓓'(Ω_n, ℂ)) (hT_plus : HasBoundaryValue Ω_n f_plus V_plus T_plus)
    (T_minus : 𝓓'(Ω_n, ℂ)) (hT_minus : HasBoundaryValue Ω_n f_minus V_minus T_minus)
    (h_match : EqualOn Ω_n T_plus T_minus U hU) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    rcases hV_ne with ⟨v, hv⟩
    exact False.elim (h0_not_mem (Subsingleton.elim v 0 ▸ hv))
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h0_cl : (0 : Fin n → ℝ) ∈ closure V_plus := by
    rcases hV_ne with ⟨v, hv⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    let c : ℝ := ε / (2 * (‖v‖ + 1))
    have hc_pos : 0 < c := by positivity
    refine ⟨fun i => c * v i, hV_plus_cone v hv c hc_pos, ?_⟩
    rw [dist_zero_left]
    have h_norm : ‖fun i : Fin n => c * v i‖ = c * ‖v‖ := by
      change ‖c • v‖ = c * ‖v‖
      rw [norm_smul, Real.norm_of_nonneg hc_pos.le]
    rw [h_norm]
    dsimp [c]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have h_disj : Disjoint V_plus V_minus :=
    disjoint_opposite_of_convex_zero_not_mem h_opposite hV_plus_conv h0_not_mem
  have h0_minus : (0 : Fin n → ℝ) ∉ V_minus := by
    rw [h_opposite]
    rintro ⟨u, hu, hu0⟩
    exact h0_not_mem (neg_eq_zero.mp hu0 ▸ hu)
  have hV_minus_cone : ∀ v ∈ V_minus, ∀ c : ℝ, c > 0 → (fun i => c * v i) ∈ V_minus := by
    intro v hv c hc
    rw [h_opposite] at hv ⊢
    rcases hv with ⟨u, hu, rfl⟩
    refine ⟨fun i => c * u i, hV_plus_cone u hu c hc, ?_⟩
    ext i; simp [mul_neg]
  let fg := glueWedgeFun V_plus f_plus f_minus
  have hfg_plus : DifferentiableOn ℂ fg (TubeDomain V_plus) :=
    hf_plus_holo.congr (fun _ hz => glueWedgeFun_eq_plus hz)
  have hfg_minus : DifferentiableOn ℂ fg (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
    rw [← h_opposite]
    exact hf_minus_holo.congr (fun _ hz => glueWedgeFun_eq_minus h_disj h0_minus hz)
  obtain ⟨v, hli, hv⟩ := exists_linearIndependent_mem_open hV_plus_open hV_ne
  let M_v : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => v j i
  let Δ_plus : Set (Fin n → ℝ) := orthantSimplex v
  let Δ_minus : Set (Fin n → ℝ) := (fun u => -u) '' Δ_plus
  have hΔp_comp : IsCompact Δ_plus := isCompact_orthantSimplex v
  have hΔp_sub : Δ_plus ⊆ V_plus := orthantSimplex_subset hV_plus_conv hv
  have hΔp_ne : Δ_plus.Nonempty := orthantSimplex_nonempty hn v
  have hΔm_comp : IsCompact Δ_minus := hΔp_comp.image continuous_neg
  have hΔm_sub : Δ_minus ⊆ V_minus := by
    rw [h_opposite]
    exact Set.image_mono hΔp_sub
  have hΔm_ne : Δ_minus.Nonempty := hΔp_ne.image _
  let K_v : ℝ := 1 + ∑ j : Fin n, ‖v j‖
  have hKv_pos : 0 < K_v := by
    dsimp [K_v]
    have : 0 ≤ ∑ j : Fin n, ‖v j‖ := Finset.sum_nonneg fun j _ => norm_nonneg (v j)
    linarith
  have hMv_norm : ∀ u : Fin n → ℝ, ‖M_v.mulVec u‖ ≤ K_v * ‖u‖ := by
    intro u
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hKv_pos.le (norm_nonneg u))).mpr fun i => ?_
    dsimp [M_v, Matrix.mulVec, dotProduct]
    calc ‖∑ j : Fin n, v j i * u j‖
        ≤ ∑ j : Fin n, ‖v j i * u j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖v j‖ * ‖u‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm (v j) i) (norm_le_pi_norm u j)
            (norm_nonneg _) (norm_nonneg _)
      _ = (∑ j : Fin n, ‖v j‖) * ‖u‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ K_v * ‖u‖ := mul_le_mul_of_nonneg_right (by dsimp [K_v]; linarith) (norm_nonneg u)
  have h_core_all : ∀ x₀ ∈ (U : Set (Fin n → ℝ)), LocalEOWCore V_plus fg x₀ := by
    intro x₀ hx₀
    rcases (Metric.nhds_basis_closedBall.mem_iff).mp (U.isOpen.mem_nhds hx₀) with
      ⟨r_U, hr_U_pos, hr_U_sub⟩
    let R₀ : ℝ := r_U / 2
    have hR₀_pos : 0 < R₀ := half_pos hr_U_pos
    have h2R₀_sub : Metric.closedBall x₀ (2 * R₀) ⊆ (U : Set (Fin n → ℝ)) := by
      have heq : 2 * R₀ = r_U := by dsimp [R₀]; ring
      rwa [heq]
    let ρ : ℝ := min (1 / (2 * (n : ℝ))) (R₀ / (2 * K_v))
    have hρ_pos : 0 < ρ := lt_min (by positivity) (by positivity)
    have hnρ_le : (n : ℝ) * ρ ≤ 1 / 2 := by
      have h1 : ρ ≤ 1 / (2 * (n : ℝ)) := min_le_left _ _
      calc (n : ℝ) * ρ ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) := mul_le_mul_of_nonneg_left h1 hn_pos.le
        _ = 1 / 2 := by field_simp [hn_pos.ne']
    have hKv_ρ_le : K_v * ρ ≤ R₀ / 2 := by
      have h1 : ρ ≤ R₀ / (2 * K_v) := min_le_right _ _
      calc K_v * ρ ≤ K_v * (R₀ / (2 * K_v)) := mul_le_mul_of_nonneg_left h1 hKv_pos.le
        _ = R₀ / 2 := by field_simp [hKv_pos.ne']
    let ε_seq : ℕ → ℝ := fun k => min (R₀ / 2) (1 / ((k : ℝ) + 1))
    have hε_pos : ∀ k, 0 < ε_seq k := fun k => lt_min (half_pos hR₀_pos) (by positivity)
    have hε_le : ∀ k, ε_seq k ≤ R₀ / 2 := fun k => min_le_left _ _
    have hε_lim : Filter.Tendsto ε_seq Filter.atTop (nhds 0) := by
      have h_inv : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      refine squeeze_zero (fun k => (hε_pos k).le) (fun k => min_le_right _ _) h_inv
    let χ_seq : ℕ → (Fin n → ℝ) → ℝ := fun k => unitMollifier n (hε_pos k)
    have hχ_cd : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (χ_seq k) := fun k => contDiff_unitMollifier n (hε_pos k)
    have hχ_supp : ∀ k, _root_.HasCompactSupport (χ_seq k) :=
      fun k => hasCompactSupport_unitMollifier n (hε_pos k)
    have hχ_tsupp : ∀ k, tsupport (χ_seq k) ⊆ Metric.closedBall 0 (R₀ / 2) := fun k =>
      (tsupport_unitMollifier_subset n (hε_pos k)).trans
        (Metric.closedBall_subset_closedBall (hε_le k))
    have hR_sub : Metric.closedBall x₀ (R₀ + R₀ / 2) ⊆ (U : Set (Fin n → ℝ)) :=
      (Metric.closedBall_subset_closedBall (by linarith)).trans h2R₀_sub
    let g_seq : ℕ → (Fin n → ℂ) → ℂ := fun k w =>
      if w ∈ TubeDomain (PosOrthant n) then
        tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w)
      else if w ∈ TubeDomain (NegOrthant n) then
        tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w)
      else
        shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k)
          (x₀ + M_v.mulVec fun j => (w j).re)
    have h_pos_neg_disj : ∀ w : Fin n → ℂ,
        w ∈ TubeDomain (PosOrthant n) → w ∉ TubeDomain (NegOrthant n) := by
      intro w hwp hwn
      have hp := hwp ⟨0, hn⟩
      have hm := hwn ⟨0, hn⟩
      linarith
    have hre_map_cb : ∀ w : Fin n → ℂ, ‖w‖ ≤ 2 * ρ →
        (x₀ + M_v.mulVec fun j => (w j).re) ∈ Metric.closedBall x₀ R₀ := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      have hre_norm : ‖fun j : Fin n => (w j).re‖ ≤ 2 * ρ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
        rw [Real.norm_eq_abs]
        exact (Complex.abs_re_le_norm (w j)).trans ((norm_le_pi_norm w j).trans hw)
      calc ‖M_v.mulVec fun j => (w j).re‖
          ≤ K_v * ‖fun j : Fin n => (w j).re‖ := hMv_norm _
        _ ≤ K_v * (2 * ρ) := mul_le_mul_of_nonneg_left hre_norm hKv_pos.le
        _ = 2 * (K_v * ρ) := by ring
        _ ≤ R₀ := by linarith
    have hdata_seq : ∀ k, OrthantEOWData n (g_seq k) ρ := by
      intro k
      obtain ⟨L_p, hLp_nn, hLp_bd, hBp_cont⟩ :=
        exists_uniform_lipschitz_boundary_tubeConv Ω_n hU hV_plus_open hV_plus_cone
          hf_plus_holo hf_plus_growth hT_plus (hχ_cd k) (hχ_supp k) (half_pos hR₀_pos)
          (hχ_tsupp k) x₀ hR₀_pos hR_sub hΔp_comp hΔp_ne hΔp_sub
      obtain ⟨L_m, hLm_nn, hLm_bd, _hBm_cont⟩ :=
        exists_uniform_lipschitz_boundary_tubeConv Ω_n hU hV_minus_open hV_minus_cone
          hf_minus_holo hf_minus_growth hT_minus (hχ_cd k) (hχ_supp k) (half_pos hR₀_pos)
          (hχ_tsupp k) x₀ hR₀_pos hR_sub hΔm_comp hΔm_ne hΔm_sub
      have h_holo_p : DifferentiableOn ℂ (tubeConv f_plus (χ_seq k) ∘ cAffine M_v x₀)
          (TubeDomain (PosOrthant n)) :=
        (differentiableOn_tubeConv hV_plus_open hf_plus_holo (hχ_cd k).continuous (hχ_supp k)
          ).comp (differentiable_cAffine M_v x₀).differentiableOn
          (fun w hw => cAffine_mem_tube_plus hn hV_plus_conv hV_plus_cone v hv x₀ w hw)
      have h_holo_m : DifferentiableOn ℂ (tubeConv f_minus (χ_seq k) ∘ cAffine M_v x₀)
          (TubeDomain (NegOrthant n)) := by
        refine (differentiableOn_tubeConv hV_minus_open hf_minus_holo
          (hχ_cd k).continuous (hχ_supp k)).comp
          (differentiable_cAffine M_v x₀).differentiableOn fun w hw => ?_
        rw [h_opposite]
        exact cAffine_mem_tube_minus hn hV_plus_conv hV_plus_cone v hv x₀ w hw
      refine ⟨?_, ?_, ?_⟩
      · exact (h_holo_p.mono Set.inter_subset_right).congr fun w hw => by simp [g_seq, hw.2]
      · refine (h_holo_m.mono Set.inter_subset_right).congr fun w hw => ?_
        have hnp : w ∉ TubeDomain (PosOrthant n) := fun hp => h_pos_neg_disj w hp hw.2
        simp [g_seq, hnp, hw.2]
      · intro w₀ ⟨hw₀_ball, hw₀_cases⟩
        rcases hw₀_cases with (hwp | hwm) | hw_real
        · have h_open : IsOpen (Metric.ball (0 : Fin n → ℂ) ρ ∩ TubeDomain (PosOrthant n)) :=
            Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant n))
          have h_cwa : ContinuousWithinAt (g_seq k)
              (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) w₀ :=
            ((h_holo_p.continuousOn.mono Set.inter_subset_right).congr
              fun w hw => by simp [g_seq, hw.2]) w₀ ⟨hw₀_ball, hwp⟩
          exact (h_cwa.continuousAt (h_open.mem_nhds ⟨hw₀_ball, hwp⟩)).continuousWithinAt
        · have h_open : IsOpen (Metric.ball (0 : Fin n → ℂ) ρ ∩ TubeDomain (NegOrthant n)) :=
            Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant n))
          have h_cwa : ContinuousWithinAt (g_seq k)
              (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) w₀ :=
            ((h_holo_m.continuousOn.mono Set.inter_subset_right).congr fun w hw => by
              have hnp : w ∉ TubeDomain (PosOrthant n) := fun hp => h_pos_neg_disj w hp hw.2
              simp [g_seq, hnp, hw.2]) w₀ ⟨hw₀_ball, hwm⟩
          exact (h_cwa.continuousAt (h_open.mem_nhds ⟨hw₀_ball, hwm⟩)).continuousWithinAt
        · rw [Metric.continuousWithinAt_iff]
          intro ε hε
          let x_re : (Fin n → ℂ) → (Fin n → ℝ) := fun w => x₀ + M_v.mulVec fun j => (w j).re
          have hxre_cont : Continuous x_re :=
            continuous_const.add
              ((Matrix.mulVecLin M_v).toContinuousLinearMap.continuous.comp
                (continuous_pi fun j => Complex.continuous_re.comp (continuous_apply j)))
          have hw₀_cb : x_re w₀ ∈ Metric.closedBall x₀ R₀ := by
            refine hre_map_cb w₀ ?_
            have hlt : ‖w₀‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hw₀_ball
            linarith
          have hB_xre_cont : ContinuousWithinAt
              (fun w => shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w))
              (Metric.ball 0 ρ) w₀ :=
            (hBp_cont (x_re w₀) hw₀_cb).comp hxre_cont.continuousWithinAt fun w hw => by
              refine hre_map_cb w ?_
              have hlt : ‖w‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hw
              linarith
          rcases Metric.continuousWithinAt_iff.mp hB_xre_cont (ε / 2) (half_pos hε) with
            ⟨δ₁, hδ₁, hδ₁_close⟩
          let L_tot : ℝ := L_p + L_m + 1
          have hLt_pos : 0 < L_tot := by dsimp [L_tot]; positivity
          let δ : ℝ := min δ₁ (min (1 / (2 * (n : ℝ))) (ε / (2 * (n : ℝ) * L_tot)))
          have hδ_pos : 0 < δ := lt_min hδ₁ (lt_min (by positivity) (by positivity))
          have hgw₀ : g_seq k w₀ =
              shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w₀) := by
            have hnp : w₀ ∉ TubeDomain (PosOrthant n) := fun hp => by
              have h0 : 0 < (w₀ ⟨0, hn⟩).im := hp ⟨0, hn⟩
              rw [hw_real ⟨0, hn⟩] at h0
              exact lt_irrefl 0 h0
            have hnm : w₀ ∉ TubeDomain (NegOrthant n) := fun hm => by
              have h0 : (w₀ ⟨0, hn⟩).im < 0 := hm ⟨0, hn⟩
              rw [hw_real ⟨0, hn⟩] at h0
              exact lt_irrefl 0 h0
            simp [g_seq, hnp, hnm, x_re]
          refine ⟨δ, hδ_pos, fun w ⟨hw_ball, hw_c⟩ hw_dist => ?_⟩
          have hw_δ₁ : dist w w₀ < δ₁ := lt_of_lt_of_le hw_dist (min_le_left _ _)
          have hB_diff : ‖shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k)
              (x_re w) - g_seq k w₀‖ < ε / 2 := by
            rw [hgw₀, ← dist_eq_norm]
            exact hδ₁_close hw_ball hw_δ₁
          have hw_cb : x_re w ∈ Metric.closedBall x₀ R₀ := by
            refine hre_map_cb w ?_
            have hlt : ‖w‖ < ρ := by simpa [Metric.mem_ball, dist_zero_right] using hw_ball
            linarith
          have him_sum_lt : ∀ sgn : ℝ, |sgn| = 1 →
              ∑ j : Fin n, sgn * (w j).im ≤ (n : ℝ) * dist w w₀ := by
            intro sgn hsgn
            calc ∑ j : Fin n, sgn * (w j).im
                ≤ ∑ j : Fin n, |sgn * (w j).im| := Finset.sum_le_sum fun j _ => le_abs_self _
              _ ≤ ∑ _j : Fin n, dist w w₀ := by
                  refine Finset.sum_le_sum fun j _ => ?_
                  rw [abs_mul, hsgn, one_mul]
                  have h0 : (w j).im = (w j - w₀ j).im := by simp [hw_real j]
                  have hdist_j : ‖w j - w₀ j‖ ≤ dist w w₀ := by
                    simpa [dist_eq_norm] using dist_le_pi_dist w w₀ j
                  rw [h0]
                  exact (Complex.abs_im_le_norm _).trans hdist_j
              _ = (n : ℝ) * dist w w₀ := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rcases hw_c with (hwp | hwm) | hwr
          · obtain ⟨hS_pos, hθ_mem, hc_eq⟩ := cAffine_posOrthant_decomp hn v x₀ hwp
            let S : ℝ := ∑ j : Fin n, (w j).im
            have hS_le_dist : S ≤ (n : ℝ) * dist w w₀ := by
              simpa [S] using him_sum_lt 1 (by norm_num)
            have hS_lt_δ : S < (n : ℝ) * δ :=
              lt_of_le_of_lt hS_le_dist (mul_lt_mul_of_pos_left hw_dist hn_pos)
            have hS_12 : S ≤ 1 / 2 := by
              have h1 : δ ≤ 1 / (2 * (n : ℝ)) := (min_le_right _ _).trans (min_le_left _ _)
              have h2 : (n : ℝ) * δ ≤ 1 / 2 := by
                calc (n : ℝ) * δ ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) :=
                      mul_le_mul_of_nonneg_left h1 hn_pos.le
                  _ = 1 / 2 := by field_simp [hn_pos.ne']
              linarith
            have hgw : g_seq k w = tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w) := by
              simp [g_seq, hwp]
            have h_lip := hLp_bd (x_re w) hw_cb _ hθ_mem S ⟨hS_pos, hS_12⟩
            rw [← hc_eq] at h_lip
            have hLp_lt : L_p * S < ε / 2 := by
              have h1 : δ ≤ ε / (2 * (n : ℝ) * L_tot) :=
                (min_le_right _ _).trans (min_le_right _ _)
              have h2 : (n : ℝ) * δ ≤ ε / (2 * L_tot) := by
                calc (n : ℝ) * δ ≤ (n : ℝ) * (ε / (2 * (n : ℝ) * L_tot)) :=
                      mul_le_mul_of_nonneg_left h1 hn_pos.le
                  _ = ε / (2 * L_tot) := by field_simp [hn_pos.ne', hLt_pos.ne']
              calc L_p * S ≤ L_p * ((n : ℝ) * δ) := mul_le_mul_of_nonneg_left hS_lt_δ.le hLp_nn
                _ ≤ L_p * (ε / (2 * L_tot)) := mul_le_mul_of_nonneg_left h2 hLp_nn
                _ = (L_p / L_tot) * (ε / 2) := by ring_nf
                _ < 1 * (ε / 2) := by
                    refine mul_lt_mul_of_pos_right ?_ (half_pos hε)
                    rw [div_lt_one hLt_pos]
                    dsimp [L_tot]; linarith
                _ = ε / 2 := one_mul _
            rw [dist_eq_norm, hgw]
            calc ‖tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w) - g_seq k w₀‖
                ≤ ‖tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w) -
                    shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w)‖ +
                  ‖shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w) -
                    g_seq k w₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add (lt_of_le_of_lt h_lip hLp_lt) hB_diff
              _ = ε := add_halves ε
          · obtain ⟨hS_pos, hθ_mem, hc_eq⟩ := cAffine_negOrthant_decomp hn v x₀ hwm
            let S : ℝ := ∑ j : Fin n, -(w j).im
            have hS_le_dist : S ≤ (n : ℝ) * dist w w₀ := by
              simpa [S] using him_sum_lt (-1) (by norm_num)
            have hS_lt_δ : S < (n : ℝ) * δ :=
              lt_of_le_of_lt hS_le_dist (mul_lt_mul_of_pos_left hw_dist hn_pos)
            have hS_12 : S ≤ 1 / 2 := by
              have h1 : δ ≤ 1 / (2 * (n : ℝ)) := (min_le_right _ _).trans (min_le_left _ _)
              have h2 : (n : ℝ) * δ ≤ 1 / 2 := by
                calc (n : ℝ) * δ ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) :=
                      mul_le_mul_of_nonneg_left h1 hn_pos.le
                  _ = 1 / 2 := by field_simp [hn_pos.ne']
              linarith
            have hnp : w ∉ TubeDomain (PosOrthant n) := fun hp => h_pos_neg_disj w hp hwm
            have hgw : g_seq k w = tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w) := by
              simp [g_seq, hnp, hwm]
            have h_lip := hLm_bd (x_re w) hw_cb _ hθ_mem S ⟨hS_pos, hS_12⟩
            rw [← hc_eq, ← shiftedBoundaryEval_eq_of_equalOn Ω_n hU h_match] at h_lip
            have hLm_lt : L_m * S < ε / 2 := by
              have h1 : δ ≤ ε / (2 * (n : ℝ) * L_tot) :=
                (min_le_right _ _).trans (min_le_right _ _)
              have h2 : (n : ℝ) * δ ≤ ε / (2 * L_tot) := by
                calc (n : ℝ) * δ ≤ (n : ℝ) * (ε / (2 * (n : ℝ) * L_tot)) :=
                      mul_le_mul_of_nonneg_left h1 hn_pos.le
                  _ = ε / (2 * L_tot) := by field_simp [hn_pos.ne', hLt_pos.ne']
              calc L_m * S ≤ L_m * ((n : ℝ) * δ) := mul_le_mul_of_nonneg_left hS_lt_δ.le hLm_nn
                _ ≤ L_m * (ε / (2 * L_tot)) := mul_le_mul_of_nonneg_left h2 hLm_nn
                _ = (L_m / L_tot) * (ε / 2) := by ring_nf
                _ < 1 * (ε / 2) := by
                    refine mul_lt_mul_of_pos_right ?_ (half_pos hε)
                    rw [div_lt_one hLt_pos]
                    dsimp [L_tot]; linarith
                _ = ε / 2 := one_mul _
            rw [dist_eq_norm, hgw]
            calc ‖tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w) - g_seq k w₀‖
                ≤ ‖tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w) -
                    shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w)‖ +
                  ‖shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w) -
                    g_seq k w₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add (lt_of_le_of_lt h_lip hLm_lt) hB_diff
              _ = ε := add_halves ε
          · have hnp : w ∉ TubeDomain (PosOrthant n) := fun hp => by
              have h0 : 0 < (w ⟨0, hn⟩).im := hp ⟨0, hn⟩
              rw [hwr ⟨0, hn⟩] at h0
              exact lt_irrefl 0 h0
            have hnm : w ∉ TubeDomain (NegOrthant n) := fun hm => by
              have h0 : (w ⟨0, hn⟩).im < 0 := hm ⟨0, hn⟩
              rw [hwr ⟨0, hn⟩] at h0
              exact lt_irrefl 0 h0
            have hgw : g_seq k w =
                shiftedBoundaryEval Ω_n hU T_plus (χ_seq k) (hχ_cd k) (hχ_tsupp k) (x_re w) := by
              simp [g_seq, hnp, hnm, x_re]
            rw [dist_eq_norm, hgw]
            exact hB_diff.trans (half_lt_self hε)
    rcases hf_plus_growth (Metric.closedBall x₀ (2 * R₀)) Δ_plus
      (isCompact_closedBall _ _) hΔp_comp hΔp_sub with ⟨N_p, C_p, hCp_nn, hCp_bd⟩
    rcases hf_minus_growth (Metric.closedBall x₀ (2 * R₀)) Δ_minus
      (isCompact_closedBall _ _) hΔm_comp hΔm_sub with ⟨N_m, C_m, hCm_nn, hCm_bd⟩
    let N_max : ℕ := max N_p N_m
    let C_sl : ℝ := (C_p + C_m) * (8 / ρ) ^ N_max
    have hCsl_nn : 0 ≤ C_sl := by dsimp [C_sl]; positivity
    have h_sphere_bd : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ζ.im ≠ 0 →
        ∀ k, ‖orthantSlice (g_seq k) 0 y ζ‖ ≤ C_sl / |ζ.im| ^ N_max := by
      intro y hy ζ hζ him_ne k
      have hy_pos := orthantBox_subset_posOrthant n hρ_pos hy
      have hy_norm := orthantBox_norm_le hρ_pos hy
      let w : Fin n → ℂ := fun i => (0 : ℂ) + ζ * (y i : ℂ)
      have hζ_norm : ‖ζ‖ = 5 / 4 := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
      have hw_norm : ‖w‖ ≤ 2 * ρ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
        have hyi : |y i| ≤ 3 * ρ / 8 := (norm_le_pi_norm y i).trans hy_norm
        calc ‖(0 : ℂ) + ζ * (y i : ℂ)‖ = ‖ζ‖ * |y i| := by
              rw [zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ (5 / 4) * (3 * ρ / 8) := by rw [hζ_norm]; linarith
          _ ≤ 2 * ρ := by linarith
      have hx_cb : (x₀ + M_v.mulVec fun j => (w j).re) ∈ Metric.closedBall x₀ R₀ :=
        hre_map_cb w hw_norm
      have him_abs_le : |ζ.im| ≤ 5 / 4 := (Complex.abs_im_le_norm ζ).trans_eq hζ_norm
      have him_abs_pos : 0 < |ζ.im| := abs_pos.mpr him_ne
      have h_y_sum_ge : ρ / 8 ≤ ∑ j : Fin n, y j :=
        le_trans (hy ⟨0, hn⟩).1
          (Finset.single_le_sum (fun j _ => (hy_pos j).le) (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
      have h_y_sum_le : ∑ j : Fin n, y j ≤ (n : ℝ) * (3 * ρ / 8) := by
        calc ∑ j : Fin n, y j ≤ ∑ _j : Fin n, (3 * ρ / 8) :=
              Finset.sum_le_sum fun j _ => (hy j).2
          _ = (n : ℝ) * (3 * ρ / 8) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
      · have hwm : w ∈ TubeDomain (NegOrthant n) := fun i => by
          dsimp [w]; simp [Complex.mul_im, mul_neg_of_neg_of_pos him_neg (hy_pos i)]
        have hnp : w ∉ TubeDomain (PosOrthant n) := fun hp => h_pos_neg_disj w hp hwm
        obtain ⟨hS_pos, hθ_mem, hc_eq⟩ := cAffine_negOrthant_decomp hn v x₀ hwm
        let S : ℝ := ∑ j : Fin n, -(w j).im
        have hS_eq : S = |ζ.im| * ∑ j : Fin n, y j := by
          dsimp [S, w]
          rw [abs_of_neg him_neg, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by simp [Complex.mul_im]
        have hS_le1 : S ≤ 1 := by
          rw [hS_eq]
          calc |ζ.im| * ∑ j : Fin n, y j
              ≤ (5 / 4) * ((n : ℝ) * (3 * ρ / 8)) :=
                mul_le_mul him_abs_le h_y_sum_le
                  (Finset.sum_nonneg fun j _ => (hy_pos j).le) (by norm_num)
            _ = (15 / 32) * ((n : ℝ) * ρ) := by ring
            _ ≤ (15 / 32) * (1 / 2) := mul_le_mul_of_nonneg_left hnρ_le (by norm_num)
            _ ≤ 1 := by norm_num
        have hS_ge : (ρ / 8) * |ζ.im| ≤ S := by
          rw [hS_eq, mul_comm]
          exact mul_le_mul_of_nonneg_left h_y_sum_ge him_abs_pos.le
        have hS_le_ρ8 : S ≤ 1 := hS_le1
        have h_slice_eq : orthantSlice (g_seq k) 0 y ζ =
            tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w) := by
          dsimp [orthantSlice]
          change g_seq k w = _
          simp [g_seq, hnp, hwm]
        rw [h_slice_eq]
        have hzs_mem : cAffine M_v x₀ w ∈ TubeDomain V_minus := by
          rw [h_opposite]
          exact cAffine_mem_tube_minus hn hV_plus_conv hV_plus_cone v hv x₀ w hwm
        have hf_int : Integrable (fun t =>
            f_minus (fun i => cAffine M_v x₀ w i - (t i : ℂ)) * (χ_seq k t : ℂ)) volume :=
          ((hf_minus_holo.continuousOn.comp_continuous
            (continuous_pi fun i =>
              continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
            fun t => tube_sub_ofReal_mem hzs_mem t).mul
            (Complex.continuous_ofReal.comp (hχ_cd k).continuous)
            ).integrable_of_hasCompactSupport
            (((hχ_supp k).comp_left Complex.ofReal_zero).mul_left)
        have h_pt_t : ∀ t : Fin n → ℝ,
            ‖f_minus (fun i => cAffine M_v x₀ w i - (t i : ℂ)) * (χ_seq k t : ℂ)‖ ≤
              (C_m / S ^ N_m) * χ_seq k t := by
          intro t
          by_cases hχt : χ_seq k t = 0
          · simp [hχt]
          · have ht_cb : t ∈ Metric.closedBall (0 : Fin n → ℝ) (R₀ / 2) :=
              hχ_tsupp k (subset_tsupport (χ_seq k) hχt)
            have hxt_cb :
                (x₀ + M_v.mulVec fun j => (w j).re) - t ∈ Metric.closedBall x₀ (2 * R₀) := by
              rw [Metric.mem_closedBall, dist_eq_norm] at hx_cb ⊢
              rw [Metric.mem_closedBall, dist_zero_right] at ht_cb
              calc ‖(x₀ + M_v.mulVec fun j => (w j).re) - t - x₀‖
                  = ‖((x₀ + M_v.mulVec fun j => (w j).re) - x₀) - t‖ := by abel_nf
                _ ≤ ‖(x₀ + M_v.mulVec fun j => (w j).re) - x₀‖ + ‖t‖ := norm_sub_le _ _
                _ ≤ R₀ + R₀ / 2 := add_le_add hx_cb ht_cb
                _ ≤ 2 * R₀ := by linarith
            have hc_sub : (fun i => cAffine M_v x₀ w i - (t i : ℂ)) =
                fun i => ((((x₀ + M_v.mulVec fun j => (w j).re) - t) i : ℝ) : ℂ) +
                  ((S * (-(∑ j : Fin n, (S⁻¹ * -(w j).im) • v j)) i : ℝ) : ℂ) * Complex.I := by
              change cAffine M_v x₀ w = _ at hc_eq
              rw [hc_eq]
              dsimp [M_v, S]
              ext i; simp; ring_nf
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (nonneg_unitMollifier n (hε_pos k) t), hc_sub]
            exact mul_le_mul_of_nonneg_right
              (hCm_bd _ hxt_cb _ hθ_mem S hS_pos hS_le1) (nonneg_unitMollifier n (hε_pos k) t)
        have h_tc_le : ‖tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w)‖ ≤ C_m / S ^ N_m := by
          calc ‖tubeConv f_minus (χ_seq k) (cAffine M_v x₀ w)‖
              ≤ ∫ t, ‖f_minus (fun i => cAffine M_v x₀ w i - (t i : ℂ)) * (χ_seq k t : ℂ)‖ :=
                MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ t, (C_m / S ^ N_m) * χ_seq k t :=
                MeasureTheory.integral_mono hf_int.norm
                  ((integrable_unitMollifier n (hε_pos k)).const_mul _) h_pt_t
            _ = C_m / S ^ N_m := by
                rw [MeasureTheory.integral_const_mul, integral_unitMollifier n (hε_pos k), mul_one]
        have hS_pow : S ^ N_max ≤ S ^ N_m :=
          pow_le_pow_of_le_one hS_pos.le hS_le1 (le_max_right N_p N_m)
        have h1 : C_m / S ^ N_m ≤ C_m / S ^ N_max :=
          div_le_div_of_nonneg_left hCm_nn (pow_pos hS_pos N_max) hS_pow
        have h2 : C_m / S ^ N_max ≤ C_sl / |ζ.im| ^ N_max := by
          have h_ge_pow : ((ρ / 8) * |ζ.im|) ^ N_max ≤ S ^ N_max :=
            pow_le_pow_left₀ (by positivity) hS_ge N_max
          have h_div1 : C_m / S ^ N_max ≤ C_m / ((ρ / 8) * |ζ.im|) ^ N_max :=
            div_le_div_of_nonneg_left hCm_nn (by positivity) h_ge_pow
          have h_alg : C_m / ((ρ / 8) * |ζ.im|) ^ N_max =
              (C_m * (8 / ρ) ^ N_max) / |ζ.im| ^ N_max := by
            rw [mul_pow]
            have hρ8 : (ρ / 8) ^ N_max = ((8 / ρ) ^ N_max)⁻¹ := by
              rw [← inv_pow]; congr 1; field_simp [hρ_pos.ne']
            rw [hρ8]
            have h8_ne : (8 / ρ) ^ N_max ≠ 0 := pow_ne_zero _ (by positivity)
            have him_ne' : |ζ.im| ^ N_max ≠ 0 := pow_ne_zero _ him_abs_pos.ne'
            field_simp [h8_ne, him_ne']
          refine h_div1.trans ?_
          rw [h_alg]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [hCp_nn]) (by positivity)) (by positivity)
        exact h_tc_le.trans (h1.trans h2)
      · have hwp : w ∈ TubeDomain (PosOrthant n) := fun i => by
          dsimp [w]; simp [Complex.mul_im, mul_pos him_pos (hy_pos i)]
        obtain ⟨hS_pos, hθ_mem, hc_eq⟩ := cAffine_posOrthant_decomp hn v x₀ hwp
        let S : ℝ := ∑ j : Fin n, (w j).im
        have hS_eq : S = |ζ.im| * ∑ j : Fin n, y j := by
          dsimp [S, w]
          rw [abs_of_pos him_pos, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by simp [Complex.mul_im]
        have hS_le1 : S ≤ 1 := by
          rw [hS_eq]
          calc |ζ.im| * ∑ j : Fin n, y j
              ≤ (5 / 4) * ((n : ℝ) * (3 * ρ / 8)) :=
                mul_le_mul him_abs_le h_y_sum_le
                  (Finset.sum_nonneg fun j _ => (hy_pos j).le) (by norm_num)
            _ = (15 / 32) * ((n : ℝ) * ρ) := by ring
            _ ≤ (15 / 32) * (1 / 2) := mul_le_mul_of_nonneg_left hnρ_le (by norm_num)
            _ ≤ 1 := by norm_num
        have hS_ge : (ρ / 8) * |ζ.im| ≤ S := by
          rw [hS_eq, mul_comm]
          exact mul_le_mul_of_nonneg_left h_y_sum_ge him_abs_pos.le
        have h_slice_eq : orthantSlice (g_seq k) 0 y ζ =
            tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w) := by
          dsimp [orthantSlice]
          change g_seq k w = _
          simp [g_seq, hwp]
        rw [h_slice_eq]
        have hzs_mem : cAffine M_v x₀ w ∈ TubeDomain V_plus :=
          cAffine_mem_tube_plus hn hV_plus_conv hV_plus_cone v hv x₀ w hwp
        have hf_int : Integrable (fun t =>
            f_plus (fun i => cAffine M_v x₀ w i - (t i : ℂ)) * (χ_seq k t : ℂ)) volume :=
          ((hf_plus_holo.continuousOn.comp_continuous
            (continuous_pi fun i =>
              continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply i)))
            fun t => tube_sub_ofReal_mem hzs_mem t).mul
            (Complex.continuous_ofReal.comp (hχ_cd k).continuous)
            ).integrable_of_hasCompactSupport
            (((hχ_supp k).comp_left Complex.ofReal_zero).mul_left)
        have h_pt_t : ∀ t : Fin n → ℝ,
            ‖f_plus (fun i => cAffine M_v x₀ w i - (t i : ℂ)) * (χ_seq k t : ℂ)‖ ≤
              (C_p / S ^ N_p) * χ_seq k t := by
          intro t
          by_cases hχt : χ_seq k t = 0
          · simp [hχt]
          · have ht_cb : t ∈ Metric.closedBall (0 : Fin n → ℝ) (R₀ / 2) :=
              hχ_tsupp k (subset_tsupport (χ_seq k) hχt)
            have hxt_cb :
                (x₀ + M_v.mulVec fun j => (w j).re) - t ∈ Metric.closedBall x₀ (2 * R₀) := by
              rw [Metric.mem_closedBall, dist_eq_norm] at hx_cb ⊢
              rw [Metric.mem_closedBall, dist_zero_right] at ht_cb
              calc ‖(x₀ + M_v.mulVec fun j => (w j).re) - t - x₀‖
                  = ‖((x₀ + M_v.mulVec fun j => (w j).re) - x₀) - t‖ := by abel_nf
                _ ≤ ‖(x₀ + M_v.mulVec fun j => (w j).re) - x₀‖ + ‖t‖ := norm_sub_le _ _
                _ ≤ R₀ + R₀ / 2 := add_le_add hx_cb ht_cb
                _ ≤ 2 * R₀ := by linarith
            have hc_sub : (fun i => cAffine M_v x₀ w i - (t i : ℂ)) =
                fun i => ((((x₀ + M_v.mulVec fun j => (w j).re) - t) i : ℝ) : ℂ) +
                  ((S * (∑ j : Fin n, (S⁻¹ * (w j).im) • v j) i : ℝ) : ℂ) * Complex.I := by
              change cAffine M_v x₀ w = _ at hc_eq
              rw [hc_eq]
              dsimp [M_v, S]
              ext i; simp; ring_nf
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (nonneg_unitMollifier n (hε_pos k) t), hc_sub]
            exact mul_le_mul_of_nonneg_right
              (hCp_bd _ hxt_cb _ hθ_mem S hS_pos hS_le1) (nonneg_unitMollifier n (hε_pos k) t)
        have h_tc_le : ‖tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w)‖ ≤ C_p / S ^ N_p := by
          calc ‖tubeConv f_plus (χ_seq k) (cAffine M_v x₀ w)‖
              ≤ ∫ t, ‖f_plus (fun i => cAffine M_v x₀ w i - (t i : ℂ)) * (χ_seq k t : ℂ)‖ :=
                MeasureTheory.norm_integral_le_integral_norm _
            _ ≤ ∫ t, (C_p / S ^ N_p) * χ_seq k t :=
                MeasureTheory.integral_mono hf_int.norm
                  ((integrable_unitMollifier n (hε_pos k)).const_mul _) h_pt_t
            _ = C_p / S ^ N_p := by
                rw [MeasureTheory.integral_const_mul, integral_unitMollifier n (hε_pos k), mul_one]
        have hS_pow : S ^ N_max ≤ S ^ N_p :=
          pow_le_pow_of_le_one hS_pos.le hS_le1 (le_max_left N_p N_m)
        have h1 : C_p / S ^ N_p ≤ C_p / S ^ N_max :=
          div_le_div_of_nonneg_left hCp_nn (pow_pos hS_pos N_max) hS_pow
        have h2 : C_p / S ^ N_max ≤ C_sl / |ζ.im| ^ N_max := by
          have h_ge_pow : ((ρ / 8) * |ζ.im|) ^ N_max ≤ S ^ N_max :=
            pow_le_pow_left₀ (by positivity) hS_ge N_max
          have h_div1 : C_p / S ^ N_max ≤ C_p / ((ρ / 8) * |ζ.im|) ^ N_max :=
            div_le_div_of_nonneg_left hCp_nn (by positivity) h_ge_pow
          have h_alg : C_p / ((ρ / 8) * |ζ.im|) ^ N_max =
              (C_p * (8 / ρ) ^ N_max) / |ζ.im| ^ N_max := by
            rw [mul_pow]
            have hρ8 : (ρ / 8) ^ N_max = ((8 / ρ) ^ N_max)⁻¹ := by
              rw [← inv_pow]; congr 1; field_simp [hρ_pos.ne']
            rw [hρ8]
            have h8_ne : (8 / ρ) ^ N_max ≠ 0 := pow_ne_zero _ (by positivity)
            have him_ne' : |ζ.im| ^ N_max ≠ 0 := pow_ne_zero _ him_abs_pos.ne'
            field_simp [h8_ne, him_ne']
          refine h_div1.trans ?_
          rw [h_alg]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [hCm_nn]) (by positivity)) (by positivity)
        exact h_tc_le.trans (h1.trans h2)
    have h_pt_pos : ∀ w ∈ TubeDomain (PosOrthant n),
        Filter.Tendsto (fun k => g_seq k w) Filter.atTop
          (nhds ((fg ∘ cAffine M_v x₀) w)) := by
      intro w hwp
      have hz_p : cAffine M_v x₀ w ∈ TubeDomain V_plus :=
        cAffine_mem_tube_plus hn hV_plus_conv hV_plus_cone v hv x₀ w hwp
      have h_fg_eq : (fg ∘ cAffine M_v x₀) w = f_plus (cAffine M_v x₀ w) :=
        glueWedgeFun_eq_plus hz_p
      rw [h_fg_eq]
      exact (tendsto_tubeConv_unitMollifier hV_plus_open hf_plus_holo.continuousOn hz_p
        hε_pos hε_lim).congr fun k => by simp [g_seq, χ_seq, hwp]
    have h_pt_neg : ∀ w ∈ TubeDomain (NegOrthant n),
        Filter.Tendsto (fun k => g_seq k w) Filter.atTop
          (nhds ((fg ∘ cAffine M_v x₀) w)) := by
      intro w hwm
      have hnp : w ∉ TubeDomain (PosOrthant n) := fun hp => h_pos_neg_disj w hp hwm
      have hz_m : cAffine M_v x₀ w ∈ TubeDomain V_minus := by
        rw [h_opposite]
        exact cAffine_mem_tube_minus hn hV_plus_conv hV_plus_cone v hv x₀ w hwm
      have h_fg_eq : (fg ∘ cAffine M_v x₀) w = f_minus (cAffine M_v x₀ w) :=
        glueWedgeFun_eq_minus h_disj h0_minus hz_m
      rw [h_fg_eq]
      exact (tendsto_tubeConv_unitMollifier hV_minus_open hf_minus_holo.continuousOn hz_m
        hε_pos hε_lim).congr fun k => by simp [g_seq, χ_seq, hnp, hwm]
    have h_pt_sphere : ∀ y ∈ orthantBox n ρ, ∀ ζ ∈ Metric.sphere (0 : ℂ) (5 / 4), ζ.im ≠ 0 →
        Filter.Tendsto (fun k => orthantSlice (g_seq k) 0 y ζ)
          Filter.atTop (nhds (orthantSlice (fg ∘ cAffine M_v x₀) 0 y ζ)) := by
      intro y hy ζ _ him_ne
      have hy_pos := orthantBox_subset_posOrthant n hρ_pos hy
      rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
      · exact h_pt_neg (fun i => (0 : ℂ) + ζ * (y i : ℂ)) fun i => by
          simp [Complex.mul_im, mul_neg_of_neg_of_pos him_neg (hy_pos i)]
      · exact h_pt_pos (fun i => (0 : ℂ) + ζ * (y i : ℂ)) fun i => by
          simp [Complex.mul_im, mul_pos him_pos (hy_pos i)]
    have h_orth := orthantEOWCore_of_mollified_seq hn g_seq (fg ∘ cAffine M_v x₀) hρ_pos
      hdata_seq hCsl_nn h_sphere_bd h_pt_sphere
      (fun w hw => h_pt_pos w hw.2) (fun w hw => h_pt_neg w hw.2)
    exact eow_local_core_of_orthant hn V_plus hV_plus_open hV_plus_conv hV_plus_cone fg
      hfg_plus hfg_minus x₀ v hli hv h_orth
  obtain ⟨W, F, hU_W, hF_diff, hF_p, hF_m⟩ :=
    local_eow_epstein_of_core_family V_plus hV_plus_open hV_plus_conv h0_cl fg
      hfg_plus hfg_minus U h_core_all
  refine ⟨W, F, hU_W, hF_diff, ?_, ?_⟩
  · intro z hz
    rw [hF_p hz]
    exact glueWedgeFun_eq_plus hz.2
  · intro z hz
    have hz_opp : z ∈ (W : Set (Fin n → ℂ)) ∩ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) := by
      rwa [← h_opposite]
    rw [hF_m hz_opp]
    exact glueWedgeFun_eq_minus h_disj h0_minus hz.2

end TemperedEOW

end Distribution
