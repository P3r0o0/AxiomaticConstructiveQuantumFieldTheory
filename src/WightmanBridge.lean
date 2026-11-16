import VacuumTheory
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Calculus.ContDiff.Convolution

namespace QFT

open Geometry Geometry.MatrixAnalysis Geometry.PolarDecomposition
  MeasureTheory Filter Topology Matrix
open scoped ComplexOrder FourierTransform RealInnerProductSpace
  Interval ContDiff InnerProductSpace Convolution

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def compactSchwartzZero (n : ℕ) : CompactSchwartz n :=
  ⟨0, HasCompactSupport.zero⟩

def compactSchwartzAdd (n : ℕ) (f g : CompactSchwartz n) : CompactSchwartz n :=
  ⟨f.val + g.val, f.property.add g.property⟩

def compactSchwartzSMul (n : ℕ) (c : ℂ) (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨c • f.val, f.property.smul_left⟩

@[simp]
lemma compactSchwartzZero_val (n : ℕ) :
    (compactSchwartzZero n).val = 0 := rfl

@[simp]
lemma compactSchwartzAdd_val (n : ℕ) (f g : CompactSchwartz n) :
    (compactSchwartzAdd n f g).val = f.val + g.val := rfl

@[simp]
lemma compactSchwartzSMul_val (n : ℕ) (c : ℂ) (f : CompactSchwartz n) :
    (compactSchwartzSMul n c f).val = c • f.val := rfl

lemma hasCompactSupport_sum_compactSchwartz {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → CompactSchwartz n) :
    HasCompactSupport ((∑ a ∈ s, (f a).val : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
      (Fin n → Fin 4 → ℝ) → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (f a).property.add ih

def compactSchwartzSum {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → CompactSchwartz n) : CompactSchwartz n :=
  ⟨∑ a ∈ s, (f a).val, hasCompactSupport_sum_compactSchwartz n s f⟩

@[simp]
lemma compactSchwartzSum_val {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → CompactSchwartz n) :
    (compactSchwartzSum n s f).val = ∑ a ∈ s, (f a).val := rfl

lemma schwartzMap_sum_apply {α : Type*} (n : ℕ)
    (s : Finset α) (f : α → SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    (∑ a ∈ s, f a) x = ∑ a ∈ s, f a x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

@[simp]
lemma wightmanConcatSchwartz_zero_left (j k : ℕ) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzZero j) g = 0 := by
  ext x
  simp [wightmanConcatSchwartz_apply]

@[simp]
lemma wightmanConcatSchwartz_zero_right (j k : ℕ) (f : CompactSchwartz j) :
    wightmanConcatSchwartz j k f (compactSchwartzZero k) = 0 := by
  ext x
  simp [wightmanConcatSchwartz_apply]

lemma wightmanConcatSchwartz_add_left (j k : ℕ)
    (f₁ f₂ : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzAdd j f₁ f₂) g =
      wightmanConcatSchwartz j k f₁ g + wightmanConcatSchwartz j k f₂ g := by
  ext x
  change (starRingEnd ℂ)
      ((f₁.val (fun i => x (Fin.castAdd k (Fin.rev i))) +
        f₂.val (fun i => x (Fin.castAdd k (Fin.rev i))))) *
      g.val (fun i => x (Fin.natAdd j i)) =
    wightmanConcatSchwartz j k f₁ g x + wightmanConcatSchwartz j k f₂ g x
  rw [map_add, add_mul]
  rfl

lemma wightmanConcatSchwartz_add_right (j k : ℕ)
    (f : CompactSchwartz j) (g₁ g₂ : CompactSchwartz k) :
    wightmanConcatSchwartz j k f (compactSchwartzAdd k g₁ g₂) =
      wightmanConcatSchwartz j k f g₁ + wightmanConcatSchwartz j k f g₂ := by
  ext x
  change (starRingEnd ℂ) (f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
      (g₁.val (fun i => x (Fin.natAdd j i)) + g₂.val (fun i => x (Fin.natAdd j i))) =
    wightmanConcatSchwartz j k f g₁ x + wightmanConcatSchwartz j k f g₂ x
  rw [mul_add]
  rfl

lemma wightmanConcatSchwartz_smul_left (j k : ℕ) (c : ℂ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzSMul j c f) g =
      star c • wightmanConcatSchwartz j k f g := by
  ext x
  change (starRingEnd ℂ) (c * f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
      g.val (fun i => x (Fin.natAdd j i)) =
    star c * wightmanConcatSchwartz j k f g x
  rw [map_mul, ← Complex.star_def, mul_assoc]
  rfl

lemma wightmanConcatSchwartz_smul_right (j k : ℕ) (c : ℂ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k f (compactSchwartzSMul k c g) =
      c • wightmanConcatSchwartz j k f g := by
  ext x
  change (starRingEnd ℂ) (f.val (fun i => x (Fin.castAdd k (Fin.rev i)))) *
      (c * g.val (fun i => x (Fin.natAdd j i))) =
    c * wightmanConcatSchwartz j k f g x
  rw [mul_left_comm]
  rfl

lemma wightmanConcatSchwartz_smul_smul (j k : ℕ) (cA cB : ℂ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzSMul j cA f) (compactSchwartzSMul k cB g) =
      (star cA * cB) • wightmanConcatSchwartz j k f g := by
  rw [wightmanConcatSchwartz_smul_left, wightmanConcatSchwartz_smul_right, smul_smul]

lemma wightmanConcatSchwartz_sum_sum {α β : Type*}
    (j k : ℕ) (s : Finset α) (t : Finset β)
    (f : α → CompactSchwartz j) (g : β → CompactSchwartz k) :
    wightmanConcatSchwartz j k (compactSchwartzSum j s f) (compactSchwartzSum k t g) =
      ∑ a ∈ s, ∑ b ∈ t, wightmanConcatSchwartz j k (f a) (g b) := by
  ext x
  rw [wightmanConcatSchwartz_apply, compactSchwartzSum_val, compactSchwartzSum_val,
      schwartzMap_sum_apply, schwartzMap_sum_apply,
      schwartzMap_sum_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [schwartzMap_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rfl

lemma sum_comm_finset_double {γ δ₁ δ₂ : Type*} (u : Finset γ) (s : Finset δ₁) (t : Finset δ₂)
    (f : γ → δ₁ → δ₂ → ℂ) :
    (∑ x ∈ u, ∑ a ∈ s, ∑ b ∈ t, f x a b) =
      ∑ a ∈ s, ∑ b ∈ t, ∑ x ∈ u, f x a b := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

def wightmanSingleDelta (A : WightmanConfig ι) (c : ℂ)
    (j : ℕ) (α : Fin j → ι) : CompactSchwartz j :=
  if h : j = A.1 then
    if h ▸ α = A.2.1 then
      h ▸ compactSchwartzSMul A.1 c A.2.2
    else
      compactSchwartzZero j
  else
    compactSchwartzZero j

omit [Fintype ι] in
@[simp]
lemma wightmanSingleDelta_eq_deg (j : ℕ) (α₀ α : Fin j → ι)
    (f₀ : CompactSchwartz j) (c : ℂ) :
    wightmanSingleDelta ⟨j, (α₀, f₀)⟩ c j α =
      if α = α₀ then compactSchwartzSMul j c f₀ else compactSchwartzZero j := by
  simp [wightmanSingleDelta]

omit [Fintype ι] in
lemma wightmanSingleDelta_ne_deg (A : WightmanConfig ι) (c : ℂ) {j : ℕ}
    (hj : j ≠ A.1) (α : Fin j → ι) :
    wightmanSingleDelta A c j α = compactSchwartzZero j := by
  simp [wightmanSingleDelta, hj]

lemma wightmanKernel_mk
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanKernel S W ⟨j, (α, f)⟩ ⟨k, (α', g)⟩ =
      ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k f g) := rfl

lemma inner_sum_wightmanSingleDelta
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (A B : WightmanConfig ι) (cA cB : ℂ) (j k : ℕ) :
    (∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanSingleDelta A cA j α)
            (wightmanSingleDelta B cB k α'))) =
      if j = A.1 then
        if k = B.1 then
          star cA * cB * wightmanKernel S W A B
        else 0
      else 0 := by
  rcases A with ⟨j₀, α₀, f₀⟩
  rcases B with ⟨k₀, α₀', g₀⟩
  change (∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanSingleDelta ⟨j₀, (α₀, f₀)⟩ cA j α)
            (wightmanSingleDelta ⟨k₀, (α₀', g₀)⟩ cB k α'))) =
      if j = j₀ then
        if k = k₀ then
          star cA * cB * wightmanKernel S W ⟨j₀, (α₀, f₀)⟩ ⟨k₀, (α₀', g₀)⟩
        else 0
      else 0
  by_cases hj : j = j₀
  · subst hj
    rw [if_pos rfl]
    by_cases hk : k = k₀
    · subst hk
      rw [if_pos rfl]
      have h_term : ∀ (α : Fin j → ι) (α' : Fin k → ι),
          (∑ β : Fin j → ι,
            (∏ i : Fin j, S.C (α i) (β i)) *
              W (j + k) (Fin.append (β ∘ Fin.rev) α')
                (wightmanConcatSchwartz j k
                  (wightmanSingleDelta ⟨j, (α₀, f₀)⟩ cA j α)
                  (wightmanSingleDelta ⟨k, (α₀', g₀)⟩ cB k α'))) =
            if α = α₀ then
              if α' = α₀' then
                star cA * cB * wightmanKernel S W ⟨j, (α₀, f₀)⟩ ⟨k, (α₀', g₀)⟩
              else 0
            else 0 := by
        intro α α'
        rw [wightmanSingleDelta_eq_deg, wightmanSingleDelta_eq_deg]
        by_cases hα : α = α₀
        · subst hα
          rw [if_pos rfl]
          by_cases hα' : α' = α₀'
          · subst hα'
            rw [if_pos rfl, if_pos rfl, if_pos rfl, wightmanKernel_mk, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun β _ => ?_)
            rw [wightmanConcatSchwartz_smul_smul, map_smul, smul_eq_mul]
            ring
          · rw [if_neg hα', if_pos rfl, if_neg hα']
            refine Finset.sum_eq_zero (fun β _ => ?_)
            rw [wightmanConcatSchwartz_zero_right, map_zero, mul_zero]
        · rw [if_neg hα, if_neg hα]
          refine Finset.sum_eq_zero (fun β _ => ?_)
          rw [wightmanConcatSchwartz_zero_left, map_zero, mul_zero]
      simp_rw [h_term]
      have h_sum_k : ∀ α : Fin j → ι,
          (∑ α' : Fin k → ι,
            if α = α₀ then
              if α' = α₀' then
                star cA * cB * wightmanKernel S W ⟨j, (α₀, f₀)⟩ ⟨k, (α₀', g₀)⟩
              else 0
            else 0) =
          if α = α₀ then
            star cA * cB * wightmanKernel S W ⟨j, (α₀, f₀)⟩ ⟨k, (α₀', g₀)⟩
          else 0 := by
        intro α
        by_cases hα : α = α₀ <;> simp [hα]
      simp_rw [h_sum_k]
      simp
    · rw [if_neg hk]
      refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun α' _ => ?_))
      refine Finset.sum_eq_zero (fun β _ => ?_)
      rw [wightmanSingleDelta_ne_deg ⟨k₀, (α₀', g₀)⟩ cB hk,
          wightmanConcatSchwartz_zero_right, map_zero, mul_zero]
  · rw [if_neg hj]
    refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun α' _ => ?_))
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [wightmanSingleDelta_ne_deg ⟨j₀, (α₀, f₀)⟩ cA hj,
        wightmanConcatSchwartz_zero_left, map_zero, mul_zero]

lemma sum_range_ite_ite
    {N j₀ k₀ : ℕ} (hj : j₀ ≤ N) (hk : k₀ ≤ N) (v : ℂ) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      if j = j₀ then if k = k₀ then v else 0 else 0) = v := by
  have h_sum_k : ∀ j : ℕ,
      (∑ k ∈ Finset.range (N + 1),
        if j = j₀ then if k = k₀ then v else 0 else 0) =
      if j = j₀ then v else 0 := by
    intro j
    by_cases hj' : j = j₀
    · rw [if_pos hj']
      simp_rw [if_pos hj']
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
    · rw [if_neg hj']
      simp_rw [if_neg hj']
      exact Finset.sum_const_zero
  simp_rw [h_sum_k]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]

theorem sum_wightmanSingleDelta_borchers
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    {N : ℕ} {A B : WightmanConfig ι} (hA : A.1 ≤ N) (hB : B.1 ≤ N) (cA cB : ℂ) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A cA j α)
              (wightmanSingleDelta B cB k α'))) =
      star cA * cB * wightmanKernel S W A B := by
  simp_rw [inner_sum_wightmanSingleDelta]
  exact sum_range_ite_ite hA hB (star cA * cB * wightmanKernel S W A B)

def wightmanCollapsedCompact (Ψ : WightmanConfig ι →₀ ℂ)
    (j : ℕ) (α : Fin j → ι) : CompactSchwartz j :=
  compactSchwartzSum j Ψ.support (fun A => wightmanSingleDelta A (Ψ A) j α)

def wightmanCollapsedSchwartz (Ψ : WightmanConfig ι →₀ ℂ)
    (j : ℕ) (α : Fin j → ι) : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
  (wightmanCollapsedCompact Ψ j α).val

def wightmanSupportMaxDeg (Ψ : WightmanConfig ι →₀ ℂ) : ℕ :=
  Ψ.support.sup Sigma.fst

omit [Fintype ι] [DecidableEq ι] in
lemma deg_le_wightmanSupportMaxDeg {Ψ : WightmanConfig ι →₀ ℂ} {A : WightmanConfig ι}
    (hA : A ∈ Ψ.support) :
    A.1 ≤ wightmanSupportMaxDeg Ψ :=
  Finset.le_sup (f := Sigma.fst) hA

lemma inner_sum_wightmanCollapsedCompact
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Ψ Φ : WightmanConfig ι →₀ ℂ) (j k : ℕ) :
    (∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanCollapsedCompact Ψ j α)
            (wightmanCollapsedCompact Φ k α'))) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        if j = A.1 then
          if k = B.1 then
            star (Ψ A) * Φ B * wightmanKernel S W A B
          else 0
        else 0 := by
  have h_expand : ∀ (α : Fin j → ι) (α' : Fin k → ι) (β : Fin j → ι),
      (∏ i : Fin j, S.C (α i) (β i)) *
        W (j + k) (Fin.append (β ∘ Fin.rev) α')
          (wightmanConcatSchwartz j k
            (wightmanCollapsedCompact Ψ j α)
            (wightmanCollapsedCompact Φ k α')) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α')) := by
    intro α α' β
    unfold wightmanCollapsedCompact
    rw [wightmanConcatSchwartz_sum_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_sum, Finset.mul_sum]
  simp_rw [h_expand]
  have h_comm_β : ∀ (α : Fin j → ι) (α' : Fin k → ι),
      (∑ β : Fin j → ι, ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α'))) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α')) :=
    fun _ _ => sum_comm_finset_double _ _ _ _
  simp_rw [h_comm_β]
  have h_comm_α' : ∀ (α : Fin j → ι),
      (∑ α' : Fin k → ι, ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α'))) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanSingleDelta A (Ψ A) j α)
              (wightmanSingleDelta B (Φ B) k α')) :=
    fun _ => sum_comm_finset_double _ _ _ _
  simp_rw [h_comm_α']
  rw [sum_comm_finset_double]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  refine Finset.sum_congr rfl (fun B _ => ?_)
  exact inner_sum_wightmanSingleDelta S W A B (Ψ A) (Φ B) j k

theorem wightmanPreInner_eq_borchersSum
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Ψ Φ : WightmanConfig ι →₀ ℂ) {N : ℕ}
    (hΨ : wightmanSupportMaxDeg Ψ ≤ N) (hΦ : wightmanSupportMaxDeg Φ ≤ N) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (wightmanCollapsedCompact Ψ j α)
              (wightmanCollapsedCompact Φ k α'))) =
      wightmanPreInner S W Ψ Φ := by
  simp_rw [inner_sum_wightmanCollapsedCompact]
  have h_comm_k : ∀ j : ℕ,
      (∑ k ∈ Finset.range (N + 1), ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support,
        if j = A.1 then
          if k = B.1 then
            star (Ψ A) * Φ B * wightmanKernel S W A B
          else 0
        else 0) =
      ∑ A ∈ Ψ.support, ∑ B ∈ Φ.support, ∑ k ∈ Finset.range (N + 1),
        if j = A.1 then
          if k = B.1 then
            star (Ψ A) * Φ B * wightmanKernel S W A B
          else 0
        else 0 :=
    fun _ => sum_comm_finset_double _ _ _ _
  simp_rw [h_comm_k]
  rw [sum_comm_finset_double]
  unfold wightmanPreInner Finsupp.sum
  refine Finset.sum_congr rfl (fun A hA => ?_)
  refine Finset.sum_congr rfl (fun B hB => ?_)
  exact sum_range_ite_ite
    ((deg_le_wightmanSupportMaxDeg hA).trans hΨ)
    ((deg_le_wightmanSupportMaxDeg hB).trans hΦ)
    (star (Ψ A) * Φ B * wightmanKernel S W A B)

def CompactPositivity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) : Prop :=
  ∀ (N : ℕ) (F : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j),
    0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k (F j α) (F k α'))

theorem compactPositivity_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) :
    CompactPositivity S W := by
  intro N F
  exact hpos N (fun j α => (F j α).val)
    (fun j k α α' => wightmanConcatSchwartz j k (F j α) (F k α'))
    (fun _ _ _ _ _ => rfl)

theorem wightmanPreInner_self_nonneg_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    0 ≤ wightmanPreInner S W Ψ Ψ := by
  rw [← wightmanPreInner_eq_borchersSum S W Ψ Ψ le_rfl le_rfl]
  exact hpos (wightmanSupportMaxDeg Ψ) (wightmanCollapsedCompact Ψ)

theorem wightmanPreInner_self_nonneg_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    0 ≤ wightmanPreInner S W Ψ Ψ :=
  wightmanPreInner_self_nonneg_of_compactPositivity (compactPositivity_of_positivity hpos) Ψ

theorem wightmanKernelPositive_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) :
    WightmanKernelPositive S W :=
  fun Ψ => (Complex.nonneg_iff.mp (wightmanPreInner_self_nonneg_of_compactPositivity hpos Ψ)).1

theorem wightmanKernelPositive_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) :
    WightmanKernelPositive S W :=
  wightmanKernelPositive_of_compactPositivity (compactPositivity_of_positivity hpos)

theorem star_wightmanPreInner_self_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    star (wightmanPreInner S W Ψ Ψ) = wightmanPreInner S W Ψ Ψ := by
  rw [Complex.star_def, Complex.conj_eq_iff_im]
  exact (Complex.nonneg_iff.mp (wightmanPreInner_self_nonneg_of_compactPositivity hpos Ψ)).2.symm

theorem star_wightmanPreInner_self_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) (Ψ : WightmanConfig ι →₀ ℂ) :
    star (wightmanPreInner S W Ψ Ψ) = wightmanPreInner S W Ψ Ψ :=
  star_wightmanPreInner_self_of_compactPositivity (compactPositivity_of_positivity hpos) Ψ

@[simp]
lemma wightmanPreInner_zero_left {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W 0 Φ = 0 := by
  simp [wightmanPreInner]

@[simp]
lemma wightmanPreInner_zero_right {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ 0 = 0 := by
  simp [wightmanPreInner]

lemma wightmanPreInner_add_left_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ₁ Ψ₂ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W (Ψ₁ + Ψ₂) Φ =
      wightmanPreInner S W Ψ₁ Φ + wightmanPreInner S W Ψ₂ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.sum_add_index']
  · intro A
    simp
  · intro A c₁ c₂
    simp [add_mul, Finsupp.sum_add]

lemma wightmanPreInner_add_right_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (Ψ Φ₁ Φ₂ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ (Φ₁ + Φ₂) =
      wightmanPreInner S W Ψ Φ₁ + wightmanPreInner S W Ψ Φ₂ := by
  unfold wightmanPreInner
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_add_index']
  · intro B
    simp
  · intro B c₁ c₂
    ring

lemma wightmanPreInner_smul_left_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (c : ℂ) (Ψ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W (c • Ψ) Φ =
      star c * wightmanPreInner S W Ψ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.sum_smul_index]
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun B _ => ?_)
    rw [star_mul']
    ring
  · intro A
    simp

lemma wightmanPreInner_smul_right_raw {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (c : ℂ) (Ψ Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ (c • Φ) =
      c * wightmanPreInner S W Ψ Φ := by
  unfold wightmanPreInner
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_smul_index, Finsupp.mul_sum]
  · refine Finsupp.sum_congr (fun B _ => ?_)
    ring
  · intro B
    simp

@[simp]
lemma wightmanPreInner_single_single {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (A B : WightmanConfig ι) :
    wightmanPreInner S W (Finsupp.single A 1) (Finsupp.single B 1) =
      wightmanKernel S W A B := by
  unfold wightmanPreInner
  simp

lemma wightmanPreInner_sum_left {α : Type*}
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (s : Finset α) (Ψ : α → WightmanConfig ι →₀ ℂ) (Φ : WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W (∑ a ∈ s, Ψ a) Φ =
      ∑ a ∈ s, wightmanPreInner S W (Ψ a) Φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, wightmanPreInner_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, wightmanPreInner_add_left_raw, ih]

lemma wightmanPreInner_sum_right {α : Type*}
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Ψ : WightmanConfig ι →₀ ℂ) (s : Finset α) (Φ : α → WightmanConfig ι →₀ ℂ) :
    wightmanPreInner S W Ψ (∑ a ∈ s, Φ a) =
      ∑ a ∈ s, wightmanPreInner S W Ψ (Φ a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, wightmanPreInner_zero_right]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, wightmanPreInner_add_right_raw, ih]

lemma wightmanPreInner_single_add_smul_single
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (A B : WightmanConfig ι) (c : ℂ) :
    wightmanPreInner S W
      (Finsupp.single A 1 + c • Finsupp.single B 1)
      (Finsupp.single A 1 + c • Finsupp.single B 1) =
      wightmanKernel S W A A +
        c * wightmanKernel S W A B +
        star c * wightmanKernel S W B A +
        (star c * c) * wightmanKernel S W B B := by
  rw [wightmanPreInner_add_left_raw, wightmanPreInner_add_right_raw,
      wightmanPreInner_add_right_raw, wightmanPreInner_smul_left_raw,
      wightmanPreInner_smul_left_raw, wightmanPreInner_smul_right_raw,
      wightmanPreInner_smul_right_raw, wightmanPreInner_single_single,
      wightmanPreInner_single_single, wightmanPreInner_single_single,
      wightmanPreInner_single_single]
  ring

theorem wightmanKernelHermiticity_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : CompactPositivity S W) :
    WightmanKernelHermiticity S W := by
  intro A B
  have hAA : star (wightmanKernel S W A A) = wightmanKernel S W A A := by
    simpa using star_wightmanPreInner_self_of_compactPositivity hpos (Finsupp.single A 1)
  have hBB : star (wightmanKernel S W B B) = wightmanKernel S W B B := by
    simpa using star_wightmanPreInner_self_of_compactPositivity hpos (Finsupp.single B 1)
  have h_one := star_wightmanPreInner_self_of_compactPositivity hpos
    (Finsupp.single A 1 + (1 : ℂ) • Finsupp.single B 1)
  rw [wightmanPreInner_single_add_smul_single] at h_one
  simp only [star_one, one_mul, star_add, hAA, hBB] at h_one
  have h1 : star (wightmanKernel S W A B) + star (wightmanKernel S W B A) =
      wightmanKernel S W A B + wightmanKernel S W B A := by
    linear_combination h_one
  have h_I := star_wightmanPreInner_self_of_compactPositivity hpos
    (Finsupp.single A 1 + Complex.I • Finsupp.single B 1)
  rw [wightmanPreInner_single_add_smul_single] at h_I
  have h_star_I : star Complex.I = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  have h_I_norm : star Complex.I * Complex.I = 1 := by
    rw [h_star_I, neg_mul, Complex.I_mul_I, neg_neg]
  rw [h_I_norm, one_mul, h_star_I] at h_I
  simp only [star_add, star_mul', star_neg, h_star_I, neg_neg, hAA, hBB] at h_I
  have h2_I : Complex.I * (-Complex.I * star (wightmanKernel S W A B) +
      Complex.I * star (wightmanKernel S W B A)) =
      Complex.I * (Complex.I * wightmanKernel S W A B +
        -Complex.I * wightmanKernel S W B A) := by
    linear_combination Complex.I * h_I
  have h2 : star (wightmanKernel S W A B) - star (wightmanKernel S W B A) =
      -wightmanKernel S W A B + wightmanKernel S W B A := by
    calc star (wightmanKernel S W A B) - star (wightmanKernel S W B A)
      _ = -(Complex.I * Complex.I) * star (wightmanKernel S W A B) +
            (Complex.I * Complex.I) * star (wightmanKernel S W B A) := by
            rw [Complex.I_mul_I]
            ring
      _ = Complex.I * (-Complex.I * star (wightmanKernel S W A B) +
            Complex.I * star (wightmanKernel S W B A)) := by ring
      _ = Complex.I * (Complex.I * wightmanKernel S W A B +
            -Complex.I * wightmanKernel S W B A) := h2_I
      _ = (Complex.I * Complex.I) * wightmanKernel S W A B -
            (Complex.I * Complex.I) * wightmanKernel S W B A := by ring
      _ = -wightmanKernel S W A B + wightmanKernel S W B A := by
            rw [Complex.I_mul_I]
            ring
  linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2

theorem wightmanKernelHermiticity_of_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hpos : Positivity S W) :
    WightmanKernelHermiticity S W :=
  wightmanKernelHermiticity_of_compactPositivity (compactPositivity_of_positivity hpos)

def wightmanPositiveDataOfCompactPositivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (hpos : CompactPositivity S W) :
    WightmanPositiveData R S where
  W := W
  hermiticity := wightmanKernelHermiticity_of_compactPositivity hpos
  positivity := wightmanKernelPositive_of_compactPositivity hpos

def wightmanPositiveDataOfPositivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (hpos : Positivity S W) :
    WightmanPositiveData R S where
  W := W
  hermiticity := wightmanKernelHermiticity_of_positivity hpos
  positivity := wightmanKernelPositive_of_positivity hpos

@[simp]
lemma wightmanPositiveDataOfPositivity_W
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (hpos : Positivity S W) :
    (wightmanPositiveDataOfPositivity S W hpos).W = W := rfl

@[ext]
lemma wightmanPositiveData_ext {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {WData₁ WData₂ : WightmanPositiveData R S} (hW : WData₁.W = WData₂.W) :
    WData₁ = WData₂ := by
  cases WData₁
  cases WData₂
  congr

lemma wightmanPositiveDataOfPositivity_eq_wightmanPositiveDataOfOSData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hpos : Positivity S W) (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    wightmanPositiveDataOfPositivity S W hpos =
      wightmanPositiveDataOfOSData D W hspec h_schw :=
  rfl

def wightmanCompactBorchersFinsupp (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j) :
    WightmanConfig ι →₀ ℂ :=
  ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
    Finsupp.single ⟨j, (α, F j α)⟩ 1

theorem wightmanPreInner_wightmanCompactBorchersFinsupp
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (N : ℕ) (F F' : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j) :
    wightmanPreInner S W
      (wightmanCompactBorchersFinsupp N F)
      (wightmanCompactBorchersFinsupp N F') =
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i : Fin j, S.C (α i) (β i)) *
            W (j + k) (Fin.append (β ∘ Fin.rev) α')
              (wightmanConcatSchwartz j k (F j α) (F' k α')) := by
  unfold wightmanCompactBorchersFinsupp
  rw [wightmanPreInner_sum_left]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [wightmanPreInner_sum_left]
  have h_comm :
      (∑ α : Fin j → ι,
        wightmanPreInner S W (Finsupp.single ⟨j, (α, F j α)⟩ 1)
          (∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            Finsupp.single ⟨k, (α', F' k α')⟩ 1)) =
      ∑ k ∈ Finset.range (N + 1), ∑ α : Fin j → ι, ∑ α' : Fin k → ι,
        wightmanKernel S W ⟨j, (α, F j α)⟩ ⟨k, (α', F' k α')⟩ := by
    have h_inner : ∀ α : Fin j → ι,
        wightmanPreInner S W (Finsupp.single ⟨j, (α, F j α)⟩ 1)
          (∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            Finsupp.single ⟨k, (α', F' k α')⟩ 1) =
        ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
          wightmanKernel S W ⟨j, (α, F j α)⟩ ⟨k, (α', F' k α')⟩ := by
      intro α
      rw [wightmanPreInner_sum_right]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [wightmanPreInner_sum_right]
      refine Finset.sum_congr rfl (fun α' _ => ?_)
      exact wightmanPreInner_single_single S W _ _
    simp_rw [h_inner]
    exact Finset.sum_comm
  rw [h_comm]
  rfl

theorem wightmanPreInner_self_nonneg_of_wightmanPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ : WightmanConfig ι →₀ ℂ) :
    0 ≤ wightmanPreInner S WData.W Ψ Ψ := by
  rw [Complex.nonneg_iff]
  refine ⟨WData.positivity Ψ, ?_⟩
  have h_conj := wightmanPreInner_conj_symm WData Ψ Ψ
  rw [Complex.star_def, Complex.conj_eq_iff_im] at h_conj
  exact h_conj.symm

theorem compactPositivity_of_wightmanPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    CompactPositivity S WData.W := by
  intro N F
  rw [← wightmanPreInner_wightmanCompactBorchersFinsupp S WData.W N F F]
  exact wightmanPreInner_self_nonneg_of_wightmanPositiveData WData
    (wightmanCompactBorchersFinsupp N F)

theorem compactPositivity_iff_wightmanKernelPositive_and_hermiticity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    CompactPositivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W) :=
  ⟨fun hpos =>
    ⟨wightmanKernelPositive_of_compactPositivity hpos,
     wightmanKernelHermiticity_of_compactPositivity hpos⟩,
   fun ⟨hpos, hherm⟩ =>
    compactPositivity_of_wightmanPositiveData
      { W := W, hermiticity := hherm, positivity := hpos }⟩

theorem positivity_of_compactPositivity_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W) (hcpos : CompactPositivity S W) :
    Positivity S W := by
  intro N F G hG
  let Fc : ∀ j : ℕ, (Fin j → ι) → CompactSchwartz j := fun j α =>
    compactSchwartzSMul j (∫ y : Fin j → Fin 4 → ℝ, F j α y)
      (momentumWavepacketCompactSchwartz j 0)
  have h_int : ∀ (j : ℕ) (α : Fin j → ι),
      (∫ y : Fin j → Fin 4 → ℝ, (Fc j α).val y) =
        ∫ y : Fin j → Fin 4 → ℝ, F j α y := by
    intro j α
    change (∫ y : Fin j → Fin 4 → ℝ,
        (∫ z : Fin j → Fin 4 → ℝ, F j α z) * momentumWavepacketSchwartz j 0 y) =
      ∫ y : Fin j → Fin 4 → ℝ, F j α y
    rw [MeasureTheory.integral_const_mul, integral_momentumWavepacketSchwartz_zero, mul_one]
  have h_eq1 := wightmanSesquilinear_eq_vladimirovSesquilinear S W hspec N F F G hG
  have h_eq2 := wightmanSesquilinear_eq_vladimirovSesquilinear S W hspec N
    (fun j α => (Fc j α).val) (fun k α' => (Fc k α').val)
    (fun j k α α' => wightmanConcatSchwartz j k (Fc j α) (Fc k α'))
    (fun _ _ _ _ _ => rfl)
  simp_rw [h_int] at h_eq2
  rw [h_eq1, ← h_eq2]
  exact hcpos N Fc

theorem positivity_iff_compactPositivity_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W) :
    Positivity S W ↔ CompactPositivity S W :=
  ⟨compactPositivity_of_positivity,
   positivity_of_compactPositivity_of_zeroMomentumSpectrumCondition hspec⟩

theorem positivity_iff_wightmanKernelPositive_and_hermiticity_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W) :
    Positivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W) :=
  (positivity_iff_compactPositivity_of_zeroMomentumSpectrumCondition S hspec).trans
    (compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W)

namespace OSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (B : OSEuclideanTubeBridge R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S B.W B.positivity

@[simp]
lemma toWightmanPositiveData_W (B : OSEuclideanTubeBridge R S η 𝒮) :
    B.toWightmanPositiveData.W = B.W := rfl

abbrev WightmanHilbertSpace (B : OSEuclideanTubeBridge R S η 𝒮) : Type _ :=
  WightmanHilbert B.toWightmanPositiveData

def wightmanVacuumVec (B : OSEuclideanTubeBridge R S η 𝒮) : B.WightmanHilbertSpace :=
  wightmanVacuum B.toWightmanPositiveData

def wightmanBasisVec (B : OSEuclideanTubeBridge R S η 𝒮) (A : WightmanConfig ι) :
    B.WightmanHilbertSpace :=
  wightmanBasis B.toWightmanPositiveData A

end OSEuclideanTubeBridge

namespace ForwardConeOSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S B.W B.positivity

@[simp]
lemma toWightmanPositiveData_W (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    B.toWightmanPositiveData.W = B.W := rfl

abbrev WightmanHilbertSpace (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) : Type _ :=
  WightmanHilbert B.toWightmanPositiveData

def wightmanVacuumVec (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    B.WightmanHilbertSpace :=
  wightmanVacuum B.toWightmanPositiveData

def wightmanBasisVec (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) (A : WightmanConfig ι) :
    B.WightmanHilbertSpace :=
  wightmanBasis B.toWightmanPositiveData A

end ForwardConeOSEuclideanTubeBridge

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (P : OSReconstructedWightman R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S P.W P.positivity

@[simp]
lemma toWightmanPositiveData_W (P : OSReconstructedWightman R S η 𝒮) :
    P.toWightmanPositiveData.W = P.W := rfl

abbrev WightmanHilbertSpace (P : OSReconstructedWightman R S η 𝒮) : Type _ :=
  WightmanHilbert P.toWightmanPositiveData

def wightmanVacuumVec (P : OSReconstructedWightman R S η 𝒮) : P.WightmanHilbertSpace :=
  wightmanVacuum P.toWightmanPositiveData

def wightmanBasisVec (P : OSReconstructedWightman R S η 𝒮) (A : WightmanConfig ι) :
    P.WightmanHilbertSpace :=
  wightmanBasis P.toWightmanPositiveData A

def osWightmanLinearIsometryEquiv (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    P.Hilbert ≃ₗᵢ[ℂ] P.WightmanHilbertSpace :=
  vladimirovOSWightmanLinearIsometryEquiv P.osData P.W P.spectrum h_schw

@[simp]
theorem osWightmanLinearIsometryEquiv_vacuum (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    P.osWightmanLinearIsometryEquiv h_schw P.vacuum = P.wightmanVacuumVec :=
  vladimirovOSWightmanLinearIsometryEquiv_osVacuum P.osData P.W P.spectrum h_schw

@[simp]
theorem osWightmanLinearIsometryEquiv_symm_wightmanVacuum
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    (P.osWightmanLinearIsometryEquiv h_schw).symm P.wightmanVacuumVec = P.vacuum :=
  vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum P.osData P.W P.spectrum h_schw

end OSReconstructedWightman

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def toWightmanPositiveData (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S P.W P.positivity

@[simp]
lemma toWightmanPositiveData_W (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.toWightmanPositiveData.W = P.W := rfl

abbrev WightmanHilbertSpace (P : ForwardConeOSReconstructedWightman R S η 𝒮) : Type _ :=
  WightmanHilbert P.toWightmanPositiveData

def wightmanVacuumVec (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.WightmanHilbertSpace :=
  wightmanVacuum P.toWightmanPositiveData

def wightmanBasisVec (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A : WightmanConfig ι) :
    P.WightmanHilbertSpace :=
  wightmanBasis P.toWightmanPositiveData A

end ForwardConeOSReconstructedWightman

namespace ForwardConeSpectralFamily

def toWightmanPositiveData (F : ForwardConeSpectralFamily ι)
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (hpos : Positivity S F.toWightmanFamily) :
    WightmanPositiveData R S :=
  wightmanPositiveDataOfPositivity S F.toWightmanFamily hpos

@[simp]
lemma toWightmanPositiveData_W (F : ForwardConeSpectralFamily ι)
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (hpos : Positivity S F.toWightmanFamily) :
    (F.toWightmanPositiveData S hpos).W = F.toWightmanFamily := rfl

end ForwardConeSpectralFamily

theorem phase1_wightman_positivity_bridge_master
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    (CompactPositivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W)) ∧
    (Positivity S W → CompactPositivity S W) ∧
    (Positivity S W → WightmanKernelPositive S W) ∧
    (Positivity S W → WightmanKernelHermiticity S W) ∧
    (ZeroMomentumSpectrumCondition W →
      (Positivity S W ↔
        (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W))) :=
  ⟨compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W,
   compactPositivity_of_positivity,
   wightmanKernelPositive_of_positivity,
   wightmanKernelHermiticity_of_positivity,
   positivity_iff_wightmanKernelPositive_and_hermiticity_of_zeroMomentumSpectrumCondition S⟩

omit [Fintype ι] [DecidableEq ι] in
noncomputable def schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (hasTemperateGrowth_sub_const_n n (fun _ => a))
    (antilipschitzWith_sub_const_n n (fun _ => a))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_apply (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (x : Fin n → Fin 4 → ℝ) :
    schwartzDiagTranslateN n a f x = f (fun i => x i - a) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_shift (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (x : Fin n → Fin 4 → ℝ) :
    schwartzDiagTranslateN n a f (fun i => x i + a) = f x := by
  rw [schwartzDiagTranslateN_apply]
  have h_sub : (fun i : Fin n => x i + a - a) = x := by
    ext i μ
    simp
  rw [h_sub]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_zero (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN n 0 f = f := by
  ext x
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzDiagTranslateN_add (n : ℕ) (a b : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN n (a + b) f =
      schwartzDiagTranslateN n a (schwartzDiagTranslateN n b f) := by
  ext x
  simp only [schwartzDiagTranslateN_apply]
  congr 1
  ext i μ
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma schwartzDiagTranslateN_fin0 (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    schwartzDiagTranslateN 0 a f = f := by
  ext x
  rw [schwartzDiagTranslateN_apply]
  congr 1
  ext i
  exact Fin.elim0 i

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, schwartzDiagTranslateN n a f x) =
      ∫ x : Fin n → Fin 4 → ℝ, f x :=
  MeasureTheory.integral_sub_right_eq_self (fun x => f x) (fun _ : Fin n => a)

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :
    HasCompactSupport (schwartzDiagTranslateN n a f : (Fin n → Fin 4 → ℝ) → ℂ) := by
  let v0 : Fin n → Fin 4 → ℝ := fun _ => a
  have hK : IsCompact
      ((fun y : Fin n → Fin 4 → ℝ => y + v0) ''
        tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :=
    hf.isCompact.image (continuous_id.add continuous_const)
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨x - v0, subset_tsupport _ (Function.mem_support.mpr hx), ?_⟩
  ext i μ
  simp [v0]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzTranslate (n : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨schwartzDiagTranslateN n a f.val,
   hasCompactSupport_schwartzDiagTranslateN n a f.val f.property⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTranslate_val (n : ℕ) (a : Fin 4 → ℝ) (f : CompactSchwartz n) :
    (compactSchwartzTranslate n a f).val = schwartzDiagTranslateN n a f.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTranslate_zero (n : ℕ) (f : CompactSchwartz n) :
    compactSchwartzTranslate n 0 f = f := by
  ext x
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzTranslate_add (n : ℕ) (a b : Fin 4 → ℝ)
    (f : CompactSchwartz n) :
    compactSchwartzTranslate n (a + b) f =
      compactSchwartzTranslate n a (compactSchwartzTranslate n b f) := by
  apply Subtype.ext
  exact schwartzDiagTranslateN_add n a b f.val

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTranslate_fin0 (a : Fin 4 → ℝ) (f : CompactSchwartz 0) :
    compactSchwartzTranslate 0 a f = f := by
  apply Subtype.ext
  exact schwartzDiagTranslateN_fin0 a f.val

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConcatSchwartz_translate_shift (j k : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    wightmanConcatSchwartz j k
      (compactSchwartzTranslate j a f) (compactSchwartzTranslate k a g)
      (fun i => x i + a) =
    wightmanConcatSchwartz j k f g x := by
  simp only [wightmanConcatSchwartz_apply, compactSchwartzTranslate_val,
    schwartzDiagTranslateN_apply, add_sub_cancel_right]

omit [Fintype ι] [DecidableEq ι] in
lemma sum_minkowskiInner_left {n : ℕ} (p : Fin n → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    (∑ k : Fin n, minkowskiInner (p k) a) =
      minkowskiInner (∑ k : Fin n, p k) a := by
  simp only [minkowskiInner_explicit, Finset.sum_apply, Finset.sum_mul,
    Finset.sum_sub_distrib]

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_shift_n {n : ℕ}
    (h h' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (a : Fin 4 → ℝ)
    (h_shift : ∀ x, h' (fun i => x i + a) = h x)
    (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier h' p =
      Complex.exp
        (-(Complex.I * ((minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ))) *
        minkowskiFourier h p := by
  dsimp [minkowskiFourier]
  let v0 : Fin n → Fin 4 → ℝ := fun _ => a
  have h_int := MeasureTheory.integral_add_right_eq_self
    (μ := (MeasureTheory.MeasureSpace.volume :
      MeasureTheory.Measure (Fin n → Fin 4 → ℝ)))
    (fun y : Fin n → Fin 4 → ℝ =>
      h' y * Complex.exp
        (-(Complex.I * ((∑ k, minkowskiInner (p k) (y k) : ℝ) : ℂ)))) v0
  rw [← h_int, ← MeasureTheory.integral_const_mul]
  congr 1
  ext x
  have hx_add : x + v0 = fun i => x i + a := rfl
  have h_h' : h' (x + v0) = h x := by
    rw [hx_add]
    exact h_shift x
  dsimp
  rw [h_h']
  have h_sum : (∑ k : Fin n, minkowskiInner (p k) (x k + v0 k)) =
      (∑ k : Fin n, minkowskiInner (p k) (x k)) +
        minkowskiInner (∑ k : Fin n, p k) a := by
    have h_add := (minkowskiPhaseLM n p).map_add x v0
    change (∑ k : Fin n, minkowskiInner (p k) (x k + v0 k)) =
      (∑ k : Fin n, minkowskiInner (p k) (x k)) +
        (∑ k : Fin n, minkowskiInner (p k) a) at h_add
    rw [h_add, sum_minkowskiInner_left]
  have h_exp :
      -(Complex.I * (((∑ k : Fin n, minkowskiInner (p k) (x k)) +
        minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ)) =
      (-(Complex.I * ((minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ))) +
        (-(Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (x k) : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [h_sum, h_exp, Complex.exp_add]
  ring

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma minkowskiFourier_schwartzDiagTranslateN (n : ℕ) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (schwartzDiagTranslateN n a f) p =
      Complex.exp
        (-(Complex.I * ((minkowskiInner (∑ k : Fin n, p k) a : ℝ) : ℂ))) *
        minkowskiFourier f p :=
  minkowskiFourier_shift_n f (schwartzDiagTranslateN n a f) a
    (schwartzDiagTranslateN_shift n a f) p

omit [Fintype ι] [DecidableEq ι] in
def WightmanTranslationInvariant (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) →
    W n α f' = W n α f

theorem wightmanTranslationInvariant_of_poincare
    (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (hP : PoincareCovariant R W) :
    WightmanTranslationInvariant W :=
  fun n α a f f' hf' => translationInvariant_of_poincare R W hP n a α f f' hf'

omit [Fintype ι] [DecidableEq ι] in
theorem wightmanTranslationInvariant_of_tubeTranslationInvariant
    {W : WightmanFamily ι} (E : TubeExtension W)
    (htrans : TubeTranslationInvariant E) :
    WightmanTranslationInvariant W :=
  wightman_translationInvariant_of_tubeTranslationInvariant E htrans

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanConfigTranslate (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) : WightmanConfig ι :=
  ⟨A.1, (A.2.1, compactSchwartzTranslate A.1 a A.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_zero_apply (A : WightmanConfig ι) :
    wightmanConfigTranslate 0 A = A := by
  rcases A with ⟨n, α, f⟩
  dsimp [wightmanConfigTranslate]
  rw [compactSchwartzTranslate_zero]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_zero :
    wightmanConfigTranslate (ι := ι) 0 = id := by
  ext A : 1
  exact wightmanConfigTranslate_zero_apply A

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigTranslate_add_apply (a b : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    wightmanConfigTranslate (a + b) A =
      wightmanConfigTranslate a (wightmanConfigTranslate b A) := by
  rcases A with ⟨n, α, f⟩
  dsimp [wightmanConfigTranslate]
  rw [compactSchwartzTranslate_add]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigTranslate_add (a b : Fin 4 → ℝ) :
    wightmanConfigTranslate (ι := ι) (a + b) =
      wightmanConfigTranslate a ∘ wightmanConfigTranslate b := by
  ext A : 1
  exact wightmanConfigTranslate_add_apply a b A

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_vacuum (a : Fin 4 → ℝ) :
    wightmanConfigTranslate a (wightmanVacuumConfig ι) =
      wightmanVacuumConfig ι := by
  dsimp [wightmanConfigTranslate, wightmanVacuumConfig, wightmanBaseConfig]
  rw [compactSchwartzTranslate_fin0]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_wightmanConfigTranslate (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    (∫ y : Fin (wightmanConfigTranslate a A).1 → Fin 4 → ℝ,
      (wightmanConfigTranslate a A).2.2.val y) =
      ∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y :=
  integral_schwartzDiagTranslateN A.1 a A.2.2.val

theorem wightmanKernel_translate_invariant
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (htrans : WightmanTranslationInvariant W)
    (a : Fin 4 → ℝ) (A B : WightmanConfig ι) :
    wightmanKernel S W
      (wightmanConfigTranslate a A) (wightmanConfigTranslate a B) =
    wightmanKernel S W A B := by
  rcases A with ⟨j, α, f⟩
  rcases B with ⟨k, α', g⟩
  dsimp [wightmanKernel, wightmanConfigTranslate]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  exact htrans (j + k) (osConcatIdx j k β α') a
    (wightmanConcatSchwartz j k f g)
    (wightmanConcatSchwartz j k
      (compactSchwartzTranslate j a f) (compactSchwartzTranslate k a g))
    (wightmanConcatSchwartz_translate_shift j k a f g)

theorem wightmanKernel_translate_symm
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (htrans : WightmanTranslationInvariant W)
    (a : Fin 4 → ℝ) (A B : WightmanConfig ι) :
    wightmanKernel S W (wightmanConfigTranslate a A) B =
      wightmanKernel S W A (wightmanConfigTranslate (-a) B) := by
  have h := wightmanKernel_translate_invariant S htrans (-a)
    (wightmanConfigTranslate a A) B
  rw [← wightmanConfigTranslate_add_apply, neg_add_cancel,
      wightmanConfigTranslate_zero_apply] at h
  exact h.symm

noncomputable def wightmanLiftConfigMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g : WightmanConfig ι → WightmanConfig ι) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  (WightmanPreHilbertSpace.equivFinsupp WData).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℂ g).comp
      (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap)

@[simp]
lemma toFinsupp_wightmanLiftConfigMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g : WightmanConfig ι → WightmanConfig ι)
    (Ψ : WightmanPreHilbertSpace WData) :
    (wightmanLiftConfigMap WData g Ψ).toFinsupp =
      Finsupp.mapDomain g Ψ.toFinsupp := rfl

@[simp]
lemma wightmanLiftConfigMap_id
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanLiftConfigMap WData id = LinearMap.id := by
  ext Ψ : 1
  apply WightmanPreHilbertSpace.ext
  simp

lemma wightmanLiftConfigMap_comp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g₁ g₂ : WightmanConfig ι → WightmanConfig ι) :
    wightmanLiftConfigMap WData (g₁ ∘ g₂) =
      (wightmanLiftConfigMap WData g₁).comp
        (wightmanLiftConfigMap WData g₂) := by
  ext Ψ : 1
  apply WightmanPreHilbertSpace.ext
  simp [Finsupp.mapDomain_comp]

@[simp]
lemma wightmanLiftConfigMap_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g : WightmanConfig ι → WightmanConfig ι) (A : WightmanConfig ι) :
    wightmanLiftConfigMap WData g (wightmanBasisPre WData A) =
      wightmanBasisPre WData (g A) := by
  apply WightmanPreHilbertSpace.ext
  simp [wightmanBasisPre]

lemma inner_wightmanLiftConfigMap
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (g₁ g₂ : WightmanConfig ι → WightmanConfig ι)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanLiftConfigMap WData g₁ Ψ,
      wightmanLiftConfigMap WData g₂ Φ⟫_ℂ =
      Ψ.toFinsupp.sum fun A cA =>
        Φ.toFinsupp.sum fun B cB =>
          star cA * cB * wightmanKernel S WData.W (g₁ A) (g₂ B) := by
  rw [WightmanPreHilbertSpace.inner_def, toFinsupp_wightmanLiftConfigMap,
      toFinsupp_wightmanLiftConfigMap]
  unfold wightmanPreInner
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by ring)]

noncomputable def wightmanTranslateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanLiftConfigMap WData (wightmanConfigTranslate a)

@[simp]
lemma wightmanTranslateLM_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanTranslateLM WData 0 = LinearMap.id := by
  unfold wightmanTranslateLM
  rw [wightmanConfigTranslate_zero, wightmanLiftConfigMap_id]

lemma wightmanTranslateLM_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a b : Fin 4 → ℝ) :
    wightmanTranslateLM WData (a + b) =
      (wightmanTranslateLM WData a).comp (wightmanTranslateLM WData b) := by
  unfold wightmanTranslateLM
  rw [wightmanConfigTranslate_add, wightmanLiftConfigMap_comp]

@[simp]
lemma wightmanTranslateLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    wightmanTranslateLM WData a (wightmanBasisPre WData A) =
      wightmanBasisPre WData (wightmanConfigTranslate a A) :=
  wightmanLiftConfigMap_wightmanBasisPre WData (wightmanConfigTranslate a) A

@[simp]
lemma wightmanTranslateLM_vacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) :
    wightmanTranslateLM WData a (wightmanVacuumPre WData) =
      wightmanVacuumPre WData := by
  unfold wightmanVacuumPre
  rw [wightmanTranslateLM_wightmanBasisPre, wightmanConfigTranslate_vacuum]

theorem inner_wightmanTranslateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 4 → ℝ) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanTranslateLM WData a Ψ, wightmanTranslateLM WData a Φ⟫_ℂ =
      ⟪Ψ, Φ⟫_ℂ := by
  unfold wightmanTranslateLM
  rw [inner_wightmanLiftConfigMap WData
      (wightmanConfigTranslate a) (wightmanConfigTranslate a) Ψ Φ,
      WightmanPreHilbertSpace.inner_def]
  unfold wightmanPreInner
  refine Finsupp.sum_congr (fun A _ => Finsupp.sum_congr (fun B _ => ?_))
  rw [wightmanKernel_translate_invariant S htrans a A B]

theorem norm_wightmanTranslateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 4 → ℝ) (Ψ : WightmanPreHilbertSpace WData) :
    ‖wightmanTranslateLM WData a Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanTranslateLM WData htrans a Ψ Ψ]

noncomputable def wightmanTranslatePreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    WightmanPreHilbertSpace WData →L[ℂ] WightmanPreHilbertSpace WData :=
  (wightmanTranslateLM WData a).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wightmanTranslateLM WData htrans a Ψ])

noncomputable def wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  (wightmanTranslatePreCLM WData htrans a).completion

@[simp]
lemma wightmanTranslate_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData (wightmanTranslateLM WData a Ψ) :=
  ContinuousLinearMap.completion_apply_coe
    (wightmanTranslatePreCLM WData htrans a) Ψ

@[simp]
theorem wightmanTranslate_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) :
    wightmanTranslate WData htrans a (wightmanBasis WData A) =
      wightmanBasis WData (wightmanConfigTranslate a A) := by
  dsimp [wightmanBasis]
  rw [wightmanTranslate_toWightmanHilbert,
      wightmanTranslateLM_wightmanBasisPre]

@[simp]
theorem wightmanTranslate_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a (wightmanVacuum WData) =
      wightmanVacuum WData := by
  dsimp [wightmanVacuum]
  rw [wightmanTranslate_toWightmanHilbert, wightmanTranslateLM_vacuumPre]

@[simp]
theorem wightmanTranslate_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) :
    wightmanTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanTranslate WData htrans 0 (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData Ψ
    rw [wightmanTranslate_toWightmanHilbert, wightmanTranslateLM_zero,
        LinearMap.id_apply]

theorem wightmanTranslate_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a b : Fin 4 → ℝ) :
    wightmanTranslate WData htrans (a + b) =
      (wightmanTranslate WData htrans a).comp
        (wightmanTranslate WData htrans b) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanTranslate WData htrans (a + b)
        (toWightmanHilbert WData Ψ) =
      wightmanTranslate WData htrans a
        (wightmanTranslate WData htrans b (toWightmanHilbert WData Ψ))
    rw [wightmanTranslate_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert,
        wightmanTranslateLM_add, LinearMap.comp_apply]

theorem wightmanTranslate_neg_comp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    (wightmanTranslate WData htrans (-a)).comp
      (wightmanTranslate WData htrans a) =
    ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  rw [← wightmanTranslate_add, neg_add_cancel, wightmanTranslate_zero]

theorem wightmanTranslate_comp_neg
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    (wightmanTranslate WData htrans a).comp
      (wightmanTranslate WData htrans (-a)) =
    ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  rw [← wightmanTranslate_add, add_neg_cancel, wightmanTranslate_zero]

theorem inner_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (x y : WightmanHilbert WData) :
    ⟪wightmanTranslate WData htrans a x,
      wightmanTranslate WData htrans a y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ),
        wightmanTranslate WData htrans a (toWightmanHilbert WData Φ)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ
    rw [wightmanTranslate_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert,
        inner_toWightmanHilbert, inner_toWightmanHilbert,
        inner_wightmanTranslateLM WData htrans a Ψ Φ]

@[simp]
theorem norm_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (x : WightmanHilbert WData) :
    ‖wightmanTranslate WData htrans a x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanTranslate WData htrans a x x]

theorem inner_wightmanTranslate_adjoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ)
    (x y : WightmanHilbert WData) :
    ⟪wightmanTranslate WData htrans a x, y⟫_ℂ =
      ⟪x, wightmanTranslate WData htrans (-a) y⟫_ℂ := by
  rw [← inner_wightmanTranslate WData htrans (-a)
      (wightmanTranslate WData htrans a x) y]
  change ⟪((wightmanTranslate WData htrans (-a)).comp
      (wightmanTranslate WData htrans a)) x,
    wightmanTranslate WData htrans (-a) y⟫_ℂ = _
  rw [wightmanTranslate_neg_comp, ContinuousLinearMap.id_apply]

noncomputable def wightmanTranslateLinearIsometryEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    WightmanHilbert WData ≃ₗᵢ[ℂ] WightmanHilbert WData where
  toFun := wightmanTranslate WData htrans a
  map_add' := (wightmanTranslate WData htrans a).map_add
  map_smul' := (wightmanTranslate WData htrans a).map_smul
  invFun := wightmanTranslate WData htrans (-a)
  left_inv x := by
    change ((wightmanTranslate WData htrans (-a)).comp
      (wightmanTranslate WData htrans a)) x = x
    rw [wightmanTranslate_neg_comp, ContinuousLinearMap.id_apply]
  right_inv x := by
    change ((wightmanTranslate WData htrans a).comp
      (wightmanTranslate WData htrans (-a))) x = x
    rw [wightmanTranslate_comp_neg, ContinuousLinearMap.id_apply]
  norm_map' := norm_wightmanTranslate WData htrans a

noncomputable def wightmanSpatialTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 3 → ℝ) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  wightmanTranslate WData htrans (euclidSpatialVec a)

noncomputable def wightmanTimeTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (t : ℝ) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  wightmanTranslate WData htrans (euclidTimeVec t)

@[simp]
theorem wightmanSpatialTranslate_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) :
    wightmanSpatialTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  unfold wightmanSpatialTranslate
  rw [euclidSpatialVec_zero, wightmanTranslate_zero]

theorem wightmanSpatialTranslate_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a b : Fin 3 → ℝ) :
    wightmanSpatialTranslate WData htrans (a + b) =
      (wightmanSpatialTranslate WData htrans a).comp
        (wightmanSpatialTranslate WData htrans b) := by
  unfold wightmanSpatialTranslate
  rw [euclidSpatialVec_add, wightmanTranslate_add]

@[simp]
theorem wightmanSpatialTranslate_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 3 → ℝ) :
    wightmanSpatialTranslate WData htrans a (wightmanVacuum WData) =
      wightmanVacuum WData :=
  wightmanTranslate_vacuum WData htrans (euclidSpatialVec a)

@[simp]
theorem wightmanTimeTranslate_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) :
    wightmanTimeTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  unfold wightmanTimeTranslate
  rw [euclidTimeVec_zero, wightmanTranslate_zero]

theorem wightmanTimeTranslate_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (t₁ t₂ : ℝ) :
    wightmanTimeTranslate WData htrans (t₁ + t₂) =
      (wightmanTimeTranslate WData htrans t₁).comp
        (wightmanTimeTranslate WData htrans t₂) := by
  unfold wightmanTimeTranslate
  rw [euclidTimeVec_add, wightmanTranslate_add]

@[simp]
theorem wightmanTimeTranslate_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (t : ℝ) :
    wightmanTimeTranslate WData htrans t (wightmanVacuum WData) =
      wightmanVacuum WData :=
  wightmanTranslate_vacuum WData htrans (euclidTimeVec t)

omit [Fintype ι] [DecidableEq ι] in
lemma euclidTimeVec_add_euclidSpatialVec (a : Fin 4 → ℝ) :
    euclidTimeVec (a 0) + euclidSpatialVec (spatialPart a) = a := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidTimeVec, euclidSpatialVec]
  · intro i
    simp [euclidTimeVec, euclidSpatialVec, spatialPart]

theorem wightmanTranslate_eq_time_comp_spatial
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a =
      (wightmanTimeTranslate WData htrans (a 0)).comp
        (wightmanSpatialTranslate WData htrans (spatialPart a)) := by
  unfold wightmanTimeTranslate wightmanSpatialTranslate
  rw [← wightmanTranslate_add, euclidTimeVec_add_euclidSpatialVec]

theorem wightmanSpatialTranslate_comm_wightmanTimeTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 3 → ℝ) (t : ℝ) :
    (wightmanSpatialTranslate WData htrans a).comp
      (wightmanTimeTranslate WData htrans t) =
    (wightmanTimeTranslate WData htrans t).comp
      (wightmanSpatialTranslate WData htrans a) := by
  unfold wightmanSpatialTranslate wightmanTimeTranslate
  rw [← wightmanTranslate_add, ← wightmanTranslate_add,
      add_comm (euclidSpatialVec a) (euclidTimeVec t)]

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_schwartzLorentzCLM (n : ℕ) (A : SL2C)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :
    HasCompactSupport (schwartzLorentzCLM n A f : (Fin n → Fin 4 → ℝ) → ℂ) := by
  have hK : IsCompact
      ((lorentzEquiv n A⁻¹) ''
        tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :=
    hf.isCompact.image (lorentzEquiv n A⁻¹).continuous
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  rw [Function.mem_support] at hx
  refine ⟨lorentzEquiv n A x, subset_tsupport _ (Function.mem_support.mpr hx), ?_⟩
  change lorentzActLM n A⁻¹ (lorentzActLM n A x) = x
  rw [lorentzActLM_mul, inv_mul_cancel, lorentzActLM_one]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzLorentz (n : ℕ) (A : SL2C)
    (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨schwartzLorentzCLM n A⁻¹ f.val,
   hasCompactSupport_schwartzLorentzCLM n A⁻¹ f.val f.property⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzLorentz_val (n : ℕ) (A : SL2C) (f : CompactSchwartz n) :
    (compactSchwartzLorentz n A f).val = schwartzLorentzCLM n A⁻¹ f.val := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzLorentz_one (n : ℕ) (f : CompactSchwartz n) :
    compactSchwartzLorentz n 1 f = f := by
  ext x
  change f.val (lorentzActLM n (1 : SL2C)⁻¹ x) = f.val x
  rw [inv_one, lorentzActLM_one]

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzLorentz_mul (n : ℕ) (A B : SL2C) (f : CompactSchwartz n) :
    compactSchwartzLorentz n (A * B) f =
      compactSchwartzLorentz n A (compactSchwartzLorentz n B f) := by
  ext x
  change f.val (lorentzActLM n (A * B)⁻¹ x) =
    f.val (lorentzActLM n B⁻¹ (lorentzActLM n A⁻¹ x))
  rw [lorentzActLM_mul, _root_.mul_inv_rev]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzLorentz_fin0 (A : SL2C) (f : CompactSchwartz 0) :
    compactSchwartzLorentz 0 A f = f := by
  ext x
  change f.val (fun i => (lorentzOfSL2C A⁻¹).mulVec (x i)) = f.val x
  congr 1
  ext i
  exact Fin.elim0 i

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzLorentz_translate (n : ℕ) (A : SL2C) (a : Fin 4 → ℝ)
    (f : CompactSchwartz n) :
    compactSchwartzLorentz n A (compactSchwartzTranslate n a f) =
      compactSchwartzTranslate n ((lorentzOfSL2C A).mulVec a)
        (compactSchwartzLorentz n A f) := by
  ext x
  change f.val (fun i => (lorentzOfSL2C A⁻¹).mulVec (x i) - a) =
    f.val (fun i =>
      (lorentzOfSL2C A⁻¹).mulVec (x i - (lorentzOfSL2C A).mulVec a))
  congr 1
  ext i μ
  have h_sub : (lorentzOfSL2C A⁻¹).mulVec (x i - (lorentzOfSL2C A).mulVec a) =
      (lorentzOfSL2C A⁻¹).mulVec (x i) -
        (lorentzOfSL2C A⁻¹).mulVec ((lorentzOfSL2C A).mulVec a) :=
    Matrix.mulVec_sub (lorentzOfSL2C A⁻¹) (x i) ((lorentzOfSL2C A).mulVec a)
  have h_inv : (lorentzOfSL2C A⁻¹).mulVec ((lorentzOfSL2C A).mulVec a) = a := by
    rw [Matrix.mulVec_mulVec, ← lorentzOfSL2C_mul, inv_mul_cancel,
        lorentzOfSL2C_one, Matrix.one_mulVec]
  rw [h_sub, h_inv]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConcatSchwartz_lorentz_rel (j k : ℕ) (A : SL2C)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    wightmanConcatSchwartz j k
      (compactSchwartzLorentz j A f) (compactSchwartzLorentz k A g)
      (fun i => (lorentzOfSL2C A).mulVec (x i)) =
    wightmanConcatSchwartz j k f g x := by
  simp only [wightmanConcatSchwartz_apply, compactSchwartzLorentz_val]
  rw [schwartzLorentz_rel j A f.val (fun i => x (Fin.castAdd k (Fin.rev i))),
      schwartzLorentz_rel k A g.val (fun i => x (Fin.natAdd j i))]

omit [Fintype ι] [DecidableEq ι] in
def WightmanScalarLorentzInvariant (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (A : SL2C)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ,
      f' (fun i => (lorentzOfSL2C A).mulVec (x i)) = f x) →
    W n α f' = W n α f

theorem wightmanScalarLorentzInvariant_of_poincare_rep_eq_one
    (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (hP : PoincareCovariant R W) (hrep : ∀ A : SL2C, R.rep A = 1) :
    WightmanScalarLorentzInvariant W := by
  intro n α A f f' hf'
  have h_poinc : ∀ x : Fin n → Fin 4 → ℝ,
      f' (fun i => poincareAct 0 A (x i)) = f x := by
    intro x
    dsimp [poincareAct]
    simp only [add_zero]
    exact hf' x
  have h := hP n 0 A f f' h_poinc α
  have h_prod : ∀ β : Fin n → ι,
      (∏ i : Fin n, R.rep A (α i) (β i)) = if α = β then 1 else 0 := by
    intro β
    simp_rw [hrep A]
    by_cases hαβ : α = β
    · subst hαβ
      simp
    · rw [if_neg hαβ]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact hαβ (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [Matrix.one_apply_ne hi])
  simp_rw [h_prod, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true] at h
  exact h

theorem wightmanScalarLorentzInvariant_of_poincare_trivialRep
    {W : WightmanFamily Unit} (hP : PoincareCovariant trivialRep W) :
    WightmanScalarLorentzInvariant W :=
  wightmanScalarLorentzInvariant_of_poincare_rep_eq_one
    trivialRep hP (fun _ => rfl)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanConfigLorentz (A : SL2C)
    (C : WightmanConfig ι) : WightmanConfig ι :=
  ⟨C.1, (C.2.1, compactSchwartzLorentz C.1 A C.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_one_apply (C : WightmanConfig ι) :
    wightmanConfigLorentz 1 C = C := by
  rcases C with ⟨n, α, f⟩
  dsimp [wightmanConfigLorentz]
  rw [compactSchwartzLorentz_one]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_one :
    wightmanConfigLorentz (ι := ι) 1 = id := by
  ext C : 1
  exact wightmanConfigLorentz_one_apply C

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigLorentz_mul_apply (A B : SL2C) (C : WightmanConfig ι) :
    wightmanConfigLorentz (A * B) C =
      wightmanConfigLorentz A (wightmanConfigLorentz B C) := by
  rcases C with ⟨n, α, f⟩
  dsimp [wightmanConfigLorentz]
  rw [compactSchwartzLorentz_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigLorentz_mul (A B : SL2C) :
    wightmanConfigLorentz (ι := ι) (A * B) =
      wightmanConfigLorentz A ∘ wightmanConfigLorentz B := by
  ext C : 1
  exact wightmanConfigLorentz_mul_apply A B C

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_vacuum (A : SL2C) :
    wightmanConfigLorentz A (wightmanVacuumConfig ι) =
      wightmanVacuumConfig ι := by
  dsimp [wightmanConfigLorentz, wightmanVacuumConfig, wightmanBaseConfig]
  rw [compactSchwartzLorentz_fin0]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConfigLorentz_translate (A : SL2C) (a : Fin 4 → ℝ) :
    wightmanConfigLorentz (ι := ι) A ∘ wightmanConfigTranslate a =
      wightmanConfigTranslate ((lorentzOfSL2C A).mulVec a) ∘
        wightmanConfigLorentz A := by
  ext C : 1
  rcases C with ⟨n, α, f⟩
  dsimp [wightmanConfigLorentz, wightmanConfigTranslate]
  rw [compactSchwartzLorentz_translate]

theorem wightmanKernel_scalarLorentz_invariant
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (hlor : WightmanScalarLorentzInvariant W)
    (A : SL2C) (C₁ C₂ : WightmanConfig ι) :
    wightmanKernel S W
      (wightmanConfigLorentz A C₁) (wightmanConfigLorentz A C₂) =
    wightmanKernel S W C₁ C₂ := by
  rcases C₁ with ⟨j, α, f⟩
  rcases C₂ with ⟨k, α', g⟩
  dsimp [wightmanKernel, wightmanConfigLorentz]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  exact hlor (j + k) (osConcatIdx j k β α') A
    (wightmanConcatSchwartz j k f g)
    (wightmanConcatSchwartz j k
      (compactSchwartzLorentz j A f) (compactSchwartzLorentz k A g))
    (wightmanConcatSchwartz_lorentz_rel j k A f g)

noncomputable def wightmanScalarLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanLiftConfigMap WData (wightmanConfigLorentz A)

@[simp]
lemma wightmanScalarLorentzLM_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanScalarLorentzLM WData 1 = LinearMap.id := by
  unfold wightmanScalarLorentzLM
  rw [wightmanConfigLorentz_one, wightmanLiftConfigMap_id]

lemma wightmanScalarLorentzLM_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : SL2C) :
    wightmanScalarLorentzLM WData (A * B) =
      (wightmanScalarLorentzLM WData A).comp
        (wightmanScalarLorentzLM WData B) := by
  unfold wightmanScalarLorentzLM
  rw [wightmanConfigLorentz_mul, wightmanLiftConfigMap_comp]

@[simp]
lemma wightmanScalarLorentzLM_vacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) :
    wightmanScalarLorentzLM WData A (wightmanVacuumPre WData) =
      wightmanVacuumPre WData := by
  dsimp [wightmanScalarLorentzLM, wightmanVacuumPre]
  rw [wightmanLiftConfigMap_wightmanBasisPre, wightmanConfigLorentz_vacuum]

theorem inner_wightmanScalarLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W)
    (A : SL2C) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanScalarLorentzLM WData A Ψ,
      wightmanScalarLorentzLM WData A Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  unfold wightmanScalarLorentzLM
  rw [inner_wightmanLiftConfigMap WData
      (wightmanConfigLorentz A) (wightmanConfigLorentz A) Ψ Φ,
      WightmanPreHilbertSpace.inner_def]
  unfold wightmanPreInner
  refine Finsupp.sum_congr (fun C₁ _ => Finsupp.sum_congr (fun C₂ _ => ?_))
  rw [wightmanKernel_scalarLorentz_invariant S hlor A C₁ C₂]

theorem norm_wightmanScalarLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W)
    (A : SL2C) (Ψ : WightmanPreHilbertSpace WData) :
    ‖wightmanScalarLorentzLM WData A Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanScalarLorentzLM WData hlor A Ψ Ψ]

noncomputable def wightmanScalarLorentzPreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C) :
    WightmanPreHilbertSpace WData →L[ℂ] WightmanPreHilbertSpace WData :=
  (wightmanScalarLorentzLM WData A).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wightmanScalarLorentzLM WData hlor A Ψ])

noncomputable def wightmanScalarLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  (wightmanScalarLorentzPreCLM WData hlor A).completion

@[simp]
lemma wightmanScalarLorentz_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData (wightmanScalarLorentzLM WData A Ψ) :=
  ContinuousLinearMap.completion_apply_coe
    (wightmanScalarLorentzPreCLM WData hlor A) Ψ

@[simp]
theorem wightmanScalarLorentz_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) :
    wightmanScalarLorentz WData hlor 1 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanScalarLorentz WData hlor 1
      (toWightmanHilbert WData Ψ) = toWightmanHilbert WData Ψ
    rw [wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentzLM_one, LinearMap.id_apply]

theorem wightmanScalarLorentz_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A B : SL2C) :
    wightmanScalarLorentz WData hlor (A * B) =
      (wightmanScalarLorentz WData hlor A).comp
        (wightmanScalarLorentz WData hlor B) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanScalarLorentz WData hlor (A * B)
        (toWightmanHilbert WData Ψ) =
      wightmanScalarLorentz WData hlor A
        (wightmanScalarLorentz WData hlor B (toWightmanHilbert WData Ψ))
    rw [wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentzLM_mul, LinearMap.comp_apply]

@[simp]
theorem wightmanScalarLorentz_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C) :
    wightmanScalarLorentz WData hlor A (wightmanVacuum WData) =
      wightmanVacuum WData := by
  dsimp [wightmanVacuum]
  rw [wightmanScalarLorentz_toWightmanHilbert,
      wightmanScalarLorentzLM_vacuumPre]

theorem inner_wightmanScalarLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C)
    (x y : WightmanHilbert WData) :
    ⟪wightmanScalarLorentz WData hlor A x,
      wightmanScalarLorentz WData hlor A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Ψ),
        wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Φ)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ
    rw [wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        inner_toWightmanHilbert, inner_toWightmanHilbert,
        inner_wightmanScalarLorentzLM WData hlor A Ψ Φ]

@[simp]
theorem norm_wightmanScalarLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hlor : WightmanScalarLorentzInvariant WData.W) (A : SL2C)
    (x : WightmanHilbert WData) :
    ‖wightmanScalarLorentz WData hlor A x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanScalarLorentz WData hlor A x x]

theorem wightmanScalarLorentz_comp_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hlor : WightmanScalarLorentzInvariant WData.W)
    (A : SL2C) (a : Fin 4 → ℝ) :
    (wightmanScalarLorentz WData hlor A).comp
      (wightmanTranslate WData htrans a) =
    (wightmanTranslate WData htrans ((lorentzOfSL2C A).mulVec a)).comp
      (wightmanScalarLorentz WData hlor A) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanScalarLorentz WData hlor A
        (wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ)) =
      wightmanTranslate WData htrans ((lorentzOfSL2C A).mulVec a)
        (wightmanScalarLorentz WData hlor A (toWightmanHilbert WData Ψ))
    rw [wightmanTranslate_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanScalarLorentz_toWightmanHilbert,
        wightmanTranslate_toWightmanHilbert]
    congr 1
    dsimp [wightmanScalarLorentzLM, wightmanTranslateLM]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← wightmanLiftConfigMap_comp, ← wightmanLiftConfigMap_comp,
        wightmanConfigLorentz_translate]

@[simp]
theorem wightmanBasis_translate_eq_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (a : Fin 4 → ℝ) (A : WightmanConfig ι) :
    wightmanBasis WData (wightmanConfigTranslate a A) =
      wightmanBasis WData A := by
  have h_eq :
      toWightmanHilbert WData
        (wightmanBasisPre WData (wightmanConfigTranslate a A)) =
      toWightmanHilbert WData (wightmanBasisPre WData A) := by
    refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
    · rw [inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          integral_wightmanConfigTranslate]
      rfl
    · rw [inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          integral_wightmanConfigTranslate]
      rfl
    · rw [inner_wightmanBasisPre, inner_wightmanBasisPre,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          wightmanKernel_eq_vladimirovKernel_mul_integral S hspec,
          integral_wightmanConfigTranslate]
      rfl
  exact h_eq

@[simp]
theorem wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W) (a : Fin 4 → ℝ) :
    wightmanTranslate WData htrans a =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData Ψ
    have h_expand : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    rw [h_expand, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul, wightmanTranslate_wightmanBasis,
        wightmanBasis_translate_eq_of_zeroMomentumSpectrumCondition WData hspec a A]

@[simp]
theorem osSpatialTranslate_eq_id_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (htrans : OSTranslationInvariant D.𝒮) (b : Fin 3 → ℝ) :
    osSpatialTranslate D htrans b = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans b (toOSHilbert D Ψ) = toOSHilbert D Ψ
    have h_expand : toOSHilbert D Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis D A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert D).map_smul _ _)
    rw [h_expand, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul]
    congr 1
    dsimp [osBasis]
    rw [osSpatialTranslate_toOSHilbert]
    unfold osSpatialTranslateLM
    rw [osLiftConfigMap_osBasisPre]
    change osBasis D (osConfigSpatialShift b A) = osBasis D A
    rw [osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw (osConfigSpatialShift b A),
        osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw A]
    rfl

@[simp]
theorem osContractionSemigroup_eq_id_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hcontr : OSContractionCondition D) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ) =
      toOSHilbert D Ψ
    have h_expand : toOSHilbert D Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis D A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert D).map_smul _ _)
    rw [h_expand, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul]
    congr 1
    dsimp [osBasis]
    rw [osContractionSemigroup_toOSHilbert]
    unfold osTimeShiftLM
    rw [osLiftConfigMap_osBasisPre]
    change osBasis D (osConfigTimeShift τ hτ A) = osBasis D A
    rw [osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw (osConfigTimeShift τ hτ A),
        osBasis_eq_osIndexedBaseConfig_of_vladimirov D hspec h_schw A]
    rfl

theorem vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (htrans_os : OSTranslationInvariant D.𝒮)
    (htrans_W : WightmanTranslationInvariant
      (wightmanPositiveDataOfOSData D W hspec h_schw).W)
    (b : Fin 3 → ℝ) (x : OSHilbert D) :
    vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
      (osSpatialTranslate D htrans_os b x) =
    wightmanSpatialTranslate (wightmanPositiveDataOfOSData D W hspec h_schw)
      htrans_W b
      (vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw x) := by
  unfold wightmanSpatialTranslate
  rw [osSpatialTranslate_eq_id_of_vladimirov D hspec h_schw htrans_os b,
      wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        (wightmanPositiveDataOfOSData D W hspec h_schw) hspec htrans_W
        (euclidSpatialVec b),
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

theorem vladimirovOSWightmanLinearIsometryEquiv_intertwines_contraction_timeTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hcontr : OSContractionCondition D)
    (htrans_W : WightmanTranslationInvariant
      (wightmanPositiveDataOfOSData D W hspec h_schw).W)
    (τ : ℝ) (hτ : 0 ≤ τ) (x : OSHilbert D) :
    vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
      (osContractionSemigroup D hcontr τ hτ x) =
    wightmanTimeTranslate (wightmanPositiveDataOfOSData D W hspec h_schw)
      htrans_W τ
      (vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw x) := by
  unfold wightmanTimeTranslate
  rw [osContractionSemigroup_eq_id_of_vladimirov D hspec h_schw hcontr τ hτ,
      wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        (wightmanPositiveDataOfOSData D W hspec h_schw) hspec htrans_W
        (euclidTimeVec τ),
      ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]

theorem fourMomentumW_wightmanTranslationInvariant (q : Fin 4 → ℝ) :
    WightmanTranslationInvariant (fourMomentumW q) :=
  wightmanTranslationInvariant_of_tubeTranslationInvariant
    (fourMomentumTubeExtension q) (fourMomentumTubeTranslationInvariant q)

@[simp]
theorem fourMomentumEvenWightmanTerm_translate (q a : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumEvenWightmanTerm q (wightmanConfigTranslate a A) =
      fourMomentumEvenWightmanTerm q A := by
  unfold fourMomentumEvenWightmanTerm wightmanConfigTranslate
  dsimp only [compactSchwartzTranslate_val]
  by_cases hn : A.1 % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_alternatingMomentum_of_even A.1 hn q]
    have h0 : minkowskiInner 0 a = 0 := by
      simp [minkowskiInner_explicit]
    rw [h0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  · rw [if_neg hn, if_neg hn]

@[simp]
theorem fourMomentumOddWightmanTerm_translate (q a : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumOddWightmanTerm q (wightmanConfigTranslate a A) =
      Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
        fourMomentumOddWightmanTerm q A := by
  unfold fourMomentumOddWightmanTerm wightmanConfigTranslate
  dsimp only [compactSchwartzTranslate_val]
  by_cases hn : A.1 % 2 = 1
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_neg_alternatingMomentum_of_odd A.1 hn q]
    congr 2
    have h_neg : minkowskiInner (-q) a = -minkowskiInner q a := by
      simp [minkowskiInner_explicit]
      ring
    rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg]
  · rw [if_neg hn, if_neg hn, mul_zero]

theorem wightmanBasis_fourMomentumWightmanData_translate
    (q a : Fin 4 → ℝ) (A : WightmanConfig Unit) :
    wightmanBasis (fourMomentumWightmanData q)
      (wightmanConfigTranslate a A) =
      fourMomentumEvenWightmanTerm q A •
        wightmanVacuum (fourMomentumWightmanData q) +
      (Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
        fourMomentumOddWightmanTerm q A) •
        fourMomentumWightmanOneParticle q := by
  rw [wightmanBasis_fourMomentumWightmanData_eq,
      fourMomentumEvenWightmanTerm_translate,
      fourMomentumOddWightmanTerm_translate]

@[simp]
theorem wightmanTranslate_fourMomentumWightmanOneParticle
    (q a : Fin 4 → ℝ) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a
      (fourMomentumWightmanOneParticle q) =
    Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) •
      fourMomentumWightmanOneParticle q := by
  change wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a
      (wightmanBasis (fourMomentumWightmanData q)
        (fourMomentumWightmanOneParticleConfig q)) = _
  rw [wightmanTranslate_wightmanBasis,
      wightmanBasis_fourMomentumWightmanData_translate,
      fourMomentumEvenWightmanTerm_oneParticleConfig,
      fourMomentumOddWightmanTerm_oneParticleConfig,
      zero_smul, zero_add, mul_one]

theorem wightmanTranslate_fourMomentumWightmanData_apply
    (q a : Fin 4 → ℝ) (Φ : WightmanHilbert (fourMomentumWightmanData q)) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a Φ =
    ⟪wightmanVacuum (fourMomentumWightmanData q), Φ⟫_ℂ •
      wightmanVacuum (fourMomentumWightmanData q) +
    Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) •
      (⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ •
        fourMomentumWightmanOneParticle q) := by
  conv_lhs => rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, wightmanTranslate_vacuum,
      wightmanTranslate_fourMomentumWightmanOneParticle,
      smul_smul, mul_comm ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ, ← smul_smul]

lemma fourMomentumSpatialPhase_eq_exp_minkowskiInner
    (q : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    fourMomentumSpatialPhase q b =
      Complex.exp
        (Complex.I * ((minkowskiInner q (euclidSpatialVec b) : ℝ) : ℂ)) := by
  unfold fourMomentumSpatialPhase
  rw [minkowskiInner_explicit]
  congr 1
  simp [minkowskiInnerC, wickEmbed, euclidSpatialVec]
  ring

@[simp]
theorem wightmanSpatialTranslate_fourMomentumWightmanOneParticle
    (q : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    wightmanSpatialTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) b
      (fourMomentumWightmanOneParticle q) =
    fourMomentumSpatialPhase q b • fourMomentumWightmanOneParticle q := by
  unfold wightmanSpatialTranslate
  rw [wightmanTranslate_fourMomentumWightmanOneParticle,
      fourMomentumSpatialPhase_eq_exp_minkowskiInner]

theorem fourMomentumOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    (q : Fin 4 → ℝ)
    (htrans : OSTranslationInvariant (fourMomentumOSData q).𝒮)
    (b : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)) :
    fourMomentumOSWightmanLinearIsometryEquiv q
      (osSpatialTranslate (fourMomentumOSData q) htrans b Φ) =
    wightmanSpatialTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) b
      (fourMomentumOSWightmanLinearIsometryEquiv q Φ) := by
  conv_lhs => rw [osSpatialTranslate_fourMomentumOSData_apply q htrans b Φ]
  conv_rhs =>
    rw [fourMomentumHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, map_smul,
      map_add, map_smul, map_smul,
      fourMomentumOSWightmanLinearIsometryEquiv_osVacuum,
      fourMomentumOSWightmanLinearIsometryEquiv_oneParticle,
      map_add, map_smul, map_smul,
      wightmanSpatialTranslate_vacuum,
      wightmanSpatialTranslate_fourMomentumWightmanOneParticle,
      smul_smul, smul_smul, mul_comm]

lemma laplaceExp_mul_I_neg_eq_exp_minkowskiInner_euclidTimeVec
    (q : Fin 4 → ℝ) (t : ℝ) :
    laplaceExp (q 0) (Complex.I * ((-t : ℝ) : ℂ)) =
      Complex.exp
        (Complex.I * ((minkowskiInner q (euclidTimeVec t) : ℝ) : ℂ)) := by
  unfold laplaceExp
  rw [minkowskiInner_explicit]
  congr 1
  dsimp [euclidTimeVec]
  push_cast
  ring

theorem fourMomentumOSHolomorphicSemigroup_realTimeUnitary_apply
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (t : ℝ)
    (Φ : OSHilbert (fourMomentumOSData q)) :
    (fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ =
      ⟪osVacuum (fourMomentumOSData q), Φ⟫_ℂ •
        osVacuum (fourMomentumOSData q) +
      Complex.exp
        (Complex.I * ((minkowskiInner q (euclidTimeVec t) : ℝ) : ℂ)) •
        (⟪fourMomentumOneParticle q, Φ⟫_ℂ • fourMomentumOneParticle q) := by
  change (fourMomentumOSSpectralDecomposition hq0).entireZ
      (Complex.I * ((-t : ℝ) : ℂ)) Φ = _
  rw [OSSpectralDecomposition.entireZ_apply, Fin.sum_univ_two]
  dsimp [fourMomentumOSSpectralDecomposition]
  rw [laplaceExp_zero_left, one_smul,
      laplaceExp_mul_I_neg_eq_exp_minkowskiInner_euclidTimeVec]

theorem fourMomentumOSWightmanLinearIsometryEquiv_intertwines_realTimeUnitary
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) (t : ℝ)
    (Φ : OSHilbert (fourMomentumOSData q)) :
    fourMomentumOSWightmanLinearIsometryEquiv q
      ((fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ) =
    wightmanTimeTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) t
      (fourMomentumOSWightmanLinearIsometryEquiv q Φ) := by
  rw [fourMomentumOSHolomorphicSemigroup_realTimeUnitary_apply hq0 t Φ]
  conv_rhs =>
    rw [fourMomentumHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [map_add, map_smul, map_smul, map_smul,
      map_add, map_smul, map_smul,
      fourMomentumOSWightmanLinearIsometryEquiv_osVacuum,
      fourMomentumOSWightmanLinearIsometryEquiv_oneParticle,
      wightmanTimeTranslate,
      wightmanTranslate_fourMomentumWightmanData_apply]
  simp [inner_wightmanVacuum_fourMomentumWightmanOneParticle,
    inner_fourMomentumWightmanOneParticle_wightmanVacuum]

namespace OSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant (B : OSEuclideanTubeBridge R S η 𝒮) :
    WightmanTranslationInvariant B.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R B.poincare

noncomputable def wightmanTranslateOp (B : OSEuclideanTubeBridge R S η 𝒮)
    (a : Fin 4 → ℝ) :
    B.WightmanHilbertSpace →L[ℂ] B.WightmanHilbertSpace :=
  wightmanTranslate B.toWightmanPositiveData B.wightmanTranslationInvariant a

end OSEuclideanTubeBridge

namespace ForwardConeOSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant
    (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    WightmanTranslationInvariant B.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R B.poincare

noncomputable def wightmanTranslateOp
    (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) (a : Fin 4 → ℝ) :
    B.WightmanHilbertSpace →L[ℂ] B.WightmanHilbertSpace :=
  wightmanTranslate B.toWightmanPositiveData B.wightmanTranslationInvariant a

end ForwardConeOSEuclideanTubeBridge

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant (P : OSReconstructedWightman R S η 𝒮) :
    WightmanTranslationInvariant P.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R P.poincare

noncomputable def wightmanTranslateOp (P : OSReconstructedWightman R S η 𝒮)
    (a : Fin 4 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTranslate P.toWightmanPositiveData P.wightmanTranslationInvariant a

noncomputable def wightmanSpatialTranslateOp
    (P : OSReconstructedWightman R S η 𝒮) (a : Fin 3 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanSpatialTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant a

noncomputable def wightmanTimeTranslateOp
    (P : OSReconstructedWightman R S η 𝒮) (t : ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTimeTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant t

theorem osWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (a : Fin 3 → ℝ) (x : P.Hilbert) :
    P.osWightmanLinearIsometryEquiv h_schw
      (osSpatialTranslate P.osData P.osAxioms.os1_translation a x) =
    P.wightmanSpatialTranslateOp a
      (P.osWightmanLinearIsometryEquiv h_schw x) :=
  vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
    P.osData P.W P.spectrum h_schw P.osAxioms.os1_translation
    P.wightmanTranslationInvariant a x

theorem osWightmanLinearIsometryEquiv_intertwines_contraction_timeTranslate
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (τ : ℝ) (hτ : 0 ≤ τ) (x : P.Hilbert) :
    P.osWightmanLinearIsometryEquiv h_schw
      (osContractionSemigroup P.osData P.contraction τ hτ x) =
    P.wightmanTimeTranslateOp τ
      (P.osWightmanLinearIsometryEquiv h_schw x) :=
  vladimirovOSWightmanLinearIsometryEquiv_intertwines_contraction_timeTranslate
    P.osData P.W P.spectrum h_schw P.contraction
    P.wightmanTranslationInvariant τ hτ x

end OSReconstructedWightman

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanTranslationInvariant
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    WightmanTranslationInvariant P.toWightmanPositiveData.W :=
  wightmanTranslationInvariant_of_poincare R P.poincare

noncomputable def wightmanTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 4 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTranslate P.toWightmanPositiveData P.wightmanTranslationInvariant a

noncomputable def wightmanSpatialTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 3 → ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanSpatialTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant a

noncomputable def wightmanTimeTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (t : ℝ) :
    P.WightmanHilbertSpace →L[ℂ] P.WightmanHilbertSpace :=
  wightmanTimeTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant t

@[simp]
theorem wightmanTranslateOp_vacuum
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 4 → ℝ) :
    P.wightmanTranslateOp a P.wightmanVacuumVec = P.wightmanVacuumVec :=
  wightmanTranslate_vacuum P.toWightmanPositiveData
    P.wightmanTranslationInvariant a

theorem wightmanTranslateOp_add
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a b : Fin 4 → ℝ) :
    P.wightmanTranslateOp (a + b) =
      (P.wightmanTranslateOp a).comp (P.wightmanTranslateOp b) :=
  wightmanTranslate_add P.toWightmanPositiveData
    P.wightmanTranslationInvariant a b

theorem inner_wightmanTranslateOp
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (a : Fin 4 → ℝ)
    (x y : P.WightmanHilbertSpace) :
    ⟪P.wightmanTranslateOp a x, P.wightmanTranslateOp a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  inner_wightmanTranslate P.toWightmanPositiveData
    P.wightmanTranslationInvariant a x y

end ForwardConeOSReconstructedWightman

namespace ForwardConeSpectralFamily

omit [Fintype ι] [DecidableEq ι] in
theorem wightmanTranslationInvariant (F : ForwardConeSpectralFamily ι) :
    WightmanTranslationInvariant F.toWightmanFamily :=
  wightmanTranslationInvariant_of_tubeTranslationInvariant
    F.toTubeExtension F.tubeTranslationInvariant

noncomputable def wightmanTranslateOp (F : ForwardConeSpectralFamily ι)
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (hpos : Positivity S F.toWightmanFamily) (a : Fin 4 → ℝ) :
    WightmanHilbert (F.toWightmanPositiveData S hpos) →L[ℂ]
      WightmanHilbert (F.toWightmanPositiveData S hpos) :=
  wightmanTranslate (F.toWightmanPositiveData S hpos)
    F.wightmanTranslationInvariant a

end ForwardConeSpectralFamily

theorem phase2_wightman_symmetry_bridge_master
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    (wightmanTranslate WData htrans 0 =
      ContinuousLinearMap.id ℂ (WightmanHilbert WData)) ∧
    (∀ a b : Fin 4 → ℝ,
      wightmanTranslate WData htrans (a + b) =
        (wightmanTranslate WData htrans a).comp
          (wightmanTranslate WData htrans b)) ∧
    (∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a (wightmanVacuum WData) =
        wightmanVacuum WData) ∧
    (∀ (a : Fin 4 → ℝ) (x y : WightmanHilbert WData),
      ⟪wightmanTranslate WData htrans a x,
        wightmanTranslate WData htrans a y⟫_ℂ = ⟪x, y⟫_ℂ) ∧
    (∀ a : Fin 4 → ℝ,
      wightmanTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) a
        (fourMomentumWightmanOneParticle q) =
      Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) •
        fourMomentumWightmanOneParticle q) ∧
    (∀ (b : Fin 3 → ℝ) (Φ : OSHilbert (fourMomentumOSData q)),
      fourMomentumOSWightmanLinearIsometryEquiv q
        (osSpatialTranslate (fourMomentumOSData q)
          (fourMomentumOSTranslationInvariant q) b Φ) =
      wightmanSpatialTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) b
        (fourMomentumOSWightmanLinearIsometryEquiv q Φ)) ∧
    (∀ (t : ℝ) (Φ : OSHilbert (fourMomentumOSData q)),
      fourMomentumOSWightmanLinearIsometryEquiv q
        ((fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ) =
      wightmanTimeTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) t
        (fourMomentumOSWightmanLinearIsometryEquiv q Φ)) :=
  ⟨wightmanTranslate_zero WData htrans,
   wightmanTranslate_add WData htrans,
   wightmanTranslate_vacuum WData htrans,
   inner_wightmanTranslate WData htrans,
   wightmanTranslate_fourMomentumWightmanOneParticle q,
   fourMomentumOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
     q (fourMomentumOSTranslationInvariant q),
   fourMomentumOSWightmanLinearIsometryEquiv_intertwines_realTimeUnitary hq0⟩

@[simp]
lemma inner_wightmanVacuumPre_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanVacuumPre WData, wightmanBasisPre WData A⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι) A :=
  inner_wightmanBasisPre WData (wightmanVacuumConfig ι) A

@[simp]
lemma inner_wightmanBasisPre_wightmanVacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanBasisPre WData A, wightmanVacuumPre WData⟫_ℂ =
      wightmanKernel S WData.W A (wightmanVacuumConfig ι) :=
  inner_wightmanBasisPre WData A (wightmanVacuumConfig ι)

@[simp]
lemma inner_wightmanVacuumPre_self
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    ⟪wightmanVacuumPre WData, wightmanVacuumPre WData⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι)
        (wightmanVacuumConfig ι) :=
  inner_wightmanBasisPre WData (wightmanVacuumConfig ι)
    (wightmanVacuumConfig ι)

@[simp]
theorem inner_wightmanVacuum_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanVacuum WData, wightmanBasis WData A⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι) A := by
  dsimp [wightmanVacuum, wightmanBasis]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_wightmanBasisPre]

@[simp]
theorem inner_wightmanBasis_wightmanVacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    ⟪wightmanBasis WData A, wightmanVacuum WData⟫_ℂ =
      wightmanKernel S WData.W A (wightmanVacuumConfig ι) := by
  dsimp [wightmanVacuum, wightmanBasis]
  rw [inner_toWightmanHilbert, inner_wightmanBasisPre_wightmanVacuumPre]

@[simp]
theorem inner_wightmanVacuum_self
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    ⟪wightmanVacuum WData, wightmanVacuum WData⟫_ℂ =
      wightmanKernel S WData.W (wightmanVacuumConfig ι)
        (wightmanVacuumConfig ι) := by
  dsimp [wightmanVacuum]
  rw [inner_toWightmanHilbert, inner_wightmanVacuumPre_self]

def WightmanVacuumNormalized {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (W : WightmanFamily ι) : Prop :=
  wightmanKernel S W (wightmanVacuumConfig ι) (wightmanVacuumConfig ι) = 1

theorem inner_wightmanVacuum_self_of_normalized
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hvac : WightmanVacuumNormalized S WData.W) :
    ⟪wightmanVacuum WData, wightmanVacuum WData⟫_ℂ = 1 := by
  rw [inner_wightmanVacuum_self, hvac]

theorem norm_wightmanVacuum_of_normalized
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hvac : WightmanVacuumNormalized S WData.W) :
    ‖wightmanVacuum WData‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanVacuum_self_of_normalized WData hvac]
  simp

lemma inner_wightmanPreHilbert_wightmanVacuumPre_left
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanVacuumPre WData, Φ⟫_ℂ =
      Φ.toFinsupp.sum (fun B cB =>
        cB * wightmanKernel S WData.W (wightmanVacuumConfig ι) B) := by
  change wightmanPreInner S WData.W
    (Finsupp.single (wightmanVacuumConfig ι) 1) Φ.toFinsupp = _
  unfold wightmanPreInner
  simp

lemma inner_wightmanPreHilbert_wightmanVacuumPre_right
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Ψ : WightmanPreHilbertSpace WData) :
    ⟪Ψ, wightmanVacuumPre WData⟫_ℂ =
      Ψ.toFinsupp.sum (fun A cA =>
        star cA * wightmanKernel S WData.W A (wightmanVacuumConfig ι)) := by
  change wightmanPreInner S WData.W Ψ.toFinsupp
    (Finsupp.single (wightmanVacuumConfig ι) 1) = _
  unfold wightmanPreInner
  refine Finsupp.sum_congr (fun A _ => ?_)
  simp

lemma inner_wightmanVacuumPre_mul_inner_eq_finsupp_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪Ψ, wightmanVacuumPre WData⟫_ℂ * ⟪wightmanVacuumPre WData, Φ⟫_ℂ =
      Ψ.toFinsupp.sum (fun A cA =>
        Φ.toFinsupp.sum (fun B cB =>
          star cA * cB *
            (wightmanKernel S WData.W A (wightmanVacuumConfig ι) *
              wightmanKernel S WData.W (wightmanVacuumConfig ι) B))) := by
  rw [inner_wightmanPreHilbert_wightmanVacuumPre_right,
      inner_wightmanPreHilbert_wightmanVacuumPre_left, Finsupp.sum_mul]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun B _ => ?_)
  ring

def WightmanClusterAlong {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) : Prop :=
  ∀ A B : WightmanConfig ι,
    Tendsto
      (fun t : ℝ =>
        wightmanKernel S WData.W A (wightmanConfigTranslate (t • a) B))
      atTop
      (𝓝 (wightmanKernel S WData.W A (wightmanVacuumConfig ι) *
        wightmanKernel S WData.W (wightmanVacuumConfig ι) B))

def WightmanSpatialClusterAlong {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S)
    (a : Fin 3 → ℝ) : Prop :=
  WightmanClusterAlong WData (euclidSpatialVec a)

def WightmanSpatialClusterDecomposition {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S) : Prop :=
  ∀ a : Fin 3 → ℝ, a ≠ 0 → WightmanSpatialClusterAlong WData a

def WightmanSpacelikeClusterDecomposition {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S) : Prop :=
  ∀ a : Fin 4 → ℝ, minkowskiInner a a < 0 → WightmanClusterAlong WData a

def WightmanTimeClusterDecomposition {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S) : Prop :=
  WightmanClusterAlong WData (euclidTimeVec 1)

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_euclidSpatialVec_self (a : Fin 3 → ℝ) :
    minkowskiInner (euclidSpatialVec a) (euclidSpatialVec a) =
      -(a 0 * a 0 + a 1 * a 1 + a 2 * a 2) := by
  rw [minkowskiInner_explicit]
  change (0 : ℝ) * 0 - a 0 * a 0 - a 1 * a 1 - a 2 * a 2 =
    -(a 0 * a 0 + a 1 * a 1 + a 2 * a 2)
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_euclidSpatialVec_self_lt_zero
    {a : Fin 3 → ℝ} (ha : a ≠ 0) :
    minkowskiInner (euclidSpatialVec a) (euclidSpatialVec a) < 0 := by
  rw [minkowskiInner_euclidSpatialVec_self]
  have h_nonneg : 0 ≤ a 0 * a 0 + a 1 * a 1 + a 2 * a 2 :=
    add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (mul_self_nonneg _)
  have h_ne : a 0 * a 0 + a 1 * a 1 + a 2 * a 2 ≠ 0 := by
    intro h0
    apply ha
    ext i
    have h0' : a 0 * a 0 = 0 := by
      nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1),
        mul_self_nonneg (a 2)]
    have h1' : a 1 * a 1 = 0 := by
      nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1),
        mul_self_nonneg (a 2)]
    have h2' : a 2 * a 2 = 0 := by
      nlinarith [mul_self_nonneg (a 0), mul_self_nonneg (a 1),
        mul_self_nonneg (a 2)]
    fin_cases i
    · exact mul_self_eq_zero.mp h0'
    · exact mul_self_eq_zero.mp h1'
    · exact mul_self_eq_zero.mp h2'
  linarith [lt_of_le_of_ne h_nonneg h_ne.symm]

theorem wightmanSpatialClusterDecomposition_of_spacelike
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {WData : WightmanPositiveData R S}
    (h : WightmanSpacelikeClusterDecomposition WData) :
    WightmanSpatialClusterDecomposition WData :=
  fun a ha => h (euclidSpatialVec a)
    (minkowskiInner_euclidSpatialVec_self_lt_zero ha)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma smul_euclidSpatialVec (t : ℝ) (a : Fin 3 → ℝ) :
    t • euclidSpatialVec a = euclidSpatialVec (t • a) := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidSpatialVec]
  · intro i
    simp [euclidSpatialVec]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma smul_euclidTimeVec_one (t : ℝ) :
    t • euclidTimeVec 1 = euclidTimeVec t := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidTimeVec]
  · intro i
    simp [euclidTimeVec]

theorem tendsto_inner_wightmanTranslateLM_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {a : Fin 4 → ℝ}
    (hcluster : WightmanClusterAlong WData a)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    Tendsto
      (fun t : ℝ => ⟪Ψ, wightmanTranslateLM WData (t • a) Φ⟫_ℂ)
      atTop
      (𝓝 (⟪Ψ, wightmanVacuumPre WData⟫_ℂ *
        ⟪wightmanVacuumPre WData, Φ⟫_ℂ)) := by
  have h_eq : (fun t : ℝ => ⟪Ψ, wightmanTranslateLM WData (t • a) Φ⟫_ℂ) =
      fun t : ℝ =>
        Ψ.toFinsupp.sum (fun A cA =>
          Φ.toFinsupp.sum (fun B cB =>
            star cA * cB *
              wightmanKernel S WData.W A
                (wightmanConfigTranslate (t • a) B))) := by
    ext t
    unfold wightmanTranslateLM
    have hR := inner_wightmanLiftConfigMap WData id
      (wightmanConfigTranslate (t • a)) Ψ Φ
    rw [wightmanLiftConfigMap_id, LinearMap.id_apply] at hR
    exact hR
  rw [h_eq, inner_wightmanVacuumPre_mul_inner_eq_finsupp_sum]
  unfold Finsupp.sum
  refine tendsto_finsetSum _ (fun A _ => ?_)
  refine tendsto_finsetSum _ (fun B _ => ?_)
  exact Tendsto.const_mul
    (star (Ψ.toFinsupp A) * Φ.toFinsupp B) (hcluster A B)

theorem tendsto_inner_wightmanCompletion_of_norm_le_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (T : ℝ → WightmanHilbert WData →L[ℂ] WightmanHilbert WData)
    (hT_norm : ∀ (t : ℝ) (z : WightmanHilbert WData), ‖T t z‖ ≤ ‖z‖)
    (hT_dense : ∀ Ψ Φ : WightmanPreHilbertSpace WData,
      Tendsto
        (fun t : ℝ =>
          ⟪toWightmanHilbert WData Ψ, T t (toWightmanHilbert WData Φ)⟫_ℂ)
        atTop
        (𝓝 (⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, toWightmanHilbert WData Φ⟫_ℂ)))
    (x y : WightmanHilbert WData) :
    Tendsto (fun t : ℝ => ⟪x, T t y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  have h_dense : DenseRange (toWightmanHilbert WData) :=
    UniformSpace.Completion.denseRange_coe
  have h_step1 : ∀ Ψ : WightmanPreHilbertSpace WData,
      Tendsto (fun t : ℝ => ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ)
        atTop
        (𝓝 (⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, y⟫_ℂ)) := by
    intro Ψ
    apply tendsto_of_forall_pos_exists_approx
    intro δ hδ
    let M : ℝ :=
      max (‖toWightmanHilbert WData Ψ‖)
        (‖toWightmanHilbert WData Ψ‖ *
          ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) + 1
    have hM_pos : 0 < M := by positivity
    obtain ⟨_, ⟨Φ, rfl⟩, hΦ⟩ :=
      Metric.mem_closure_iff.mp (h_dense y) (δ / M) (div_pos hδ hM_pos)
    rw [dist_eq_norm] at hΦ
    refine ⟨fun t =>
        ⟪toWightmanHilbert WData Ψ, T t (toWightmanHilbert WData Φ)⟫_ℂ,
      ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
        ⟪wightmanVacuum WData, toWightmanHilbert WData Φ⟫_ℂ,
      hT_dense Ψ Φ, fun t => ?_, ?_⟩
    · have h_sub :
          ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ -
            ⟪toWightmanHilbert WData Ψ, T t (toWightmanHilbert WData Φ)⟫_ℂ =
          ⟪toWightmanHilbert WData Ψ,
            T t (y - toWightmanHilbert WData Φ)⟫_ℂ := by
        rw [← inner_sub_right, map_sub]
      rw [h_sub]
      have h1 :
          ‖⟪toWightmanHilbert WData Ψ,
              T t (y - toWightmanHilbert WData Φ)⟫_ℂ‖ ≤
            ‖toWightmanHilbert WData Ψ‖ *
              ‖y - toWightmanHilbert WData Φ‖ := by
        refine le_trans (norm_inner_le_norm _ _) ?_
        exact mul_le_mul_of_nonneg_left
          (hT_norm t (y - toWightmanHilbert WData Φ)) (norm_nonneg _)
      have h2 : ‖toWightmanHilbert WData Ψ‖ ≤ M := by
        dsimp [M]
        linarith [le_max_left (‖toWightmanHilbert WData Ψ‖)
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖)]
      have h3 :
          ‖toWightmanHilbert WData Ψ‖ * ‖y - toWightmanHilbert WData Φ‖ ≤
            M * (δ / M) :=
        mul_le_mul h2 hΦ.le (norm_nonneg _) hM_pos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hM_pos)] at h3
      exact le_trans h1 h3
    · have h_sub :
          ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
            ⟪wightmanVacuum WData, toWightmanHilbert WData Φ⟫_ℂ -
          ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
            ⟪wightmanVacuum WData, y⟫_ℂ =
          ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
            ⟪wightmanVacuum WData, toWightmanHilbert WData Φ - y⟫_ℂ := by
        rw [← mul_sub, inner_sub_right]
      rw [h_sub, norm_mul]
      have ha := norm_inner_le_norm (𝕜 := ℂ)
        (toWightmanHilbert WData Ψ) (wightmanVacuum WData)
      have hb := norm_inner_le_norm (𝕜 := ℂ)
        (wightmanVacuum WData) (toWightmanHilbert WData Φ - y)
      rw [norm_sub_rev] at hb
      have h1 :
          ‖⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ‖ *
            ‖⟪wightmanVacuum WData, toWightmanHilbert WData Φ - y⟫_ℂ‖ ≤
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) *
            ‖y - toWightmanHilbert WData Φ‖ := by
        calc ‖⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ‖ *
            ‖⟪wightmanVacuum WData, toWightmanHilbert WData Φ - y⟫_ℂ‖
          _ ≤ (‖toWightmanHilbert WData Ψ‖ * ‖wightmanVacuum WData‖) *
              (‖wightmanVacuum WData‖ * ‖y - toWightmanHilbert WData Φ‖) :=
            mul_le_mul ha hb (norm_nonneg _) (by positivity)
          _ = (‖toWightmanHilbert WData Ψ‖ *
              ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) *
              ‖y - toWightmanHilbert WData Φ‖ := by
            ring
      have h2 :
          ‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ ≤ M := by
        dsimp [M]
        linarith [le_max_right (‖toWightmanHilbert WData Ψ‖)
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖)]
      have h3 :
          (‖toWightmanHilbert WData Ψ‖ *
            ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖) *
            ‖y - toWightmanHilbert WData Φ‖ ≤ M * (δ / M) :=
        mul_le_mul h2 hΦ.le (norm_nonneg _) hM_pos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hM_pos)] at h3
      exact le_trans h1 h3
  apply tendsto_of_forall_pos_exists_approx
  intro δ hδ
  let M : ℝ :=
    max (‖y‖) (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) + 1
  have hM_pos : 0 < M := by positivity
  obtain ⟨_, ⟨Ψ, rfl⟩, hΨ⟩ :=
    Metric.mem_closure_iff.mp (h_dense x) (δ / M) (div_pos hδ hM_pos)
  rw [dist_eq_norm] at hΨ
  refine ⟨fun t => ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ,
    ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
      ⟪wightmanVacuum WData, y⟫_ℂ,
    h_step1 Ψ, fun t => ?_, ?_⟩
  · have h_sub :
        ⟪x, T t y⟫_ℂ - ⟪toWightmanHilbert WData Ψ, T t y⟫_ℂ =
        ⟪x - toWightmanHilbert WData Ψ, T t y⟫_ℂ :=
      (inner_sub_left _ _ _).symm
    rw [h_sub]
    have h1 :
        ‖⟪x - toWightmanHilbert WData Ψ, T t y⟫_ℂ‖ ≤
          ‖x - toWightmanHilbert WData Ψ‖ * ‖y‖ := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_left (hT_norm t y) (norm_nonneg _)
    have h2 : ‖y‖ ≤ M := by
      dsimp [M]
      linarith [le_max_left (‖y‖)
        (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖)]
    have h3 : ‖x - toWightmanHilbert WData Ψ‖ * ‖y‖ ≤ (δ / M) * M :=
      mul_le_mul hΨ.le h2 (norm_nonneg _) (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)] at h3
    exact le_trans h1 h3
  · have h_sub :
        ⟪toWightmanHilbert WData Ψ, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, y⟫_ℂ -
        ⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ =
        ⟪toWightmanHilbert WData Ψ - x, wightmanVacuum WData⟫_ℂ *
          ⟪wightmanVacuum WData, y⟫_ℂ := by
      rw [← sub_mul, inner_sub_left]
    rw [h_sub, norm_mul]
    have ha := norm_inner_le_norm (𝕜 := ℂ)
      (toWightmanHilbert WData Ψ - x) (wightmanVacuum WData)
    rw [norm_sub_rev] at ha
    have hb := norm_inner_le_norm (𝕜 := ℂ) (wightmanVacuum WData) y
    have h1 :
        ‖⟪toWightmanHilbert WData Ψ - x, wightmanVacuum WData⟫_ℂ‖ *
          ‖⟪wightmanVacuum WData, y⟫_ℂ‖ ≤
        ‖x - toWightmanHilbert WData Ψ‖ *
          (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) := by
      calc ‖⟪toWightmanHilbert WData Ψ - x, wightmanVacuum WData⟫_ℂ‖ *
          ‖⟪wightmanVacuum WData, y⟫_ℂ‖
        _ ≤ (‖x - toWightmanHilbert WData Ψ‖ * ‖wightmanVacuum WData‖) *
            (‖wightmanVacuum WData‖ * ‖y‖) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
        _ = ‖x - toWightmanHilbert WData Ψ‖ *
            (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) := by
          ring
    have h2 : ‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖ ≤ M := by
      dsimp [M]
      linarith [le_max_right (‖y‖)
        (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖)]
    have h3 :
        ‖x - toWightmanHilbert WData Ψ‖ *
          (‖wightmanVacuum WData‖ * ‖wightmanVacuum WData‖ * ‖y‖) ≤
        (δ / M) * M :=
      mul_le_mul hΨ.le h2 (by positivity) (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)] at h3
    exact le_trans h1 h3

theorem tendsto_inner_wightmanTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    (x y : WightmanHilbert WData) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanTranslate WData htrans (t • a) y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  refine tendsto_inner_wightmanCompletion_of_norm_le_one WData
    (fun t => wightmanTranslate WData htrans (t • a))
    (fun t z => (norm_wightmanTranslate WData htrans (t • a) z).le)
    (fun Ψ Φ => ?_) x y
  dsimp [wightmanVacuum]
  rw [inner_toWightmanHilbert, inner_toWightmanHilbert]
  have h_eq : (fun t : ℝ =>
      ⟪toWightmanHilbert WData Ψ,
        wightmanTranslate WData htrans (t • a)
          (toWightmanHilbert WData Φ)⟫_ℂ) =
      fun t : ℝ => ⟪Ψ, wightmanTranslateLM WData (t • a) Φ⟫_ℂ := by
    ext t
    rw [wightmanTranslate_toWightmanHilbert, inner_toWightmanHilbert]
  rw [h_eq]
  exact tendsto_inner_wightmanTranslateLM_atTop WData hcluster Ψ Φ

theorem tendsto_inner_wightmanSpatialTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a)
    (x y : WightmanHilbert WData) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanSpatialTranslate WData htrans (t • a) y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  have h := tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x y
  have h_eq :
      (fun t : ℝ =>
        ⟪x, wightmanTranslate WData htrans (t • euclidSpatialVec a) y⟫_ℂ) =
      fun t : ℝ => ⟪x, wightmanSpatialTranslate WData htrans (t • a) y⟫_ℂ := by
    ext t
    rw [smul_euclidSpatialVec]
    rfl
  rwa [h_eq] at h

theorem tendsto_inner_wightmanTimeTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData)
    (x y : WightmanHilbert WData) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanTimeTranslate WData htrans t y⟫_ℂ)
      atTop
      (𝓝 (⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, y⟫_ℂ)) := by
  have h := tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x y
  have h_eq :
      (fun t : ℝ =>
        ⟪x, wightmanTranslate WData htrans (t • euclidTimeVec 1) y⟫_ℂ) =
      fun t : ℝ => ⟪x, wightmanTimeTranslate WData htrans t y⟫_ℂ := by
    ext t
    rw [smul_euclidTimeVec_one]
    rfl
  rwa [h_eq] at h

theorem tendsto_inner_wightmanTranslate_eq_zero_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    (x : WightmanHilbert WData) {y : WightmanHilbert WData}
    (horth : ⟪wightmanVacuum WData, y⟫_ℂ = 0) :
    Tendsto
      (fun t : ℝ => ⟪x, wightmanTranslate WData htrans (t • a) y⟫_ℂ)
      atTop (𝓝 0) := by
  have h := tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x y
  rwa [horth, mul_zero] at h

theorem eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTranslate WData htrans (t • a) Ψ = Ψ) :
    Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData := by
  have h_inner_eq : ∀ x : WightmanHilbert WData,
      ⟪x, Ψ⟫_ℂ = ⟪x, ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData⟫_ℂ := by
    intro x
    have h_tendsto :=
      tendsto_inner_wightmanTranslate_atTop WData htrans hcluster x Ψ
    have h_const_fn :
        (fun t : ℝ => ⟪x, wightmanTranslate WData htrans (t • a) Ψ⟫_ℂ) =
        fun _ : ℝ => ⟪x, Ψ⟫_ℂ := by
      ext t
      rw [hfixed t]
    rw [h_const_fn] at h_tendsto
    have h_lim :
        ⟪x, Ψ⟫_ℂ =
          ⟪x, wightmanVacuum WData⟫_ℂ * ⟪wightmanVacuum WData, Ψ⟫_ℂ :=
      tendsto_nhds_unique tendsto_const_nhds h_tendsto
    rw [h_lim, inner_smul_right, mul_comm]
  have h_diff :
      ⟪Ψ - ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData,
        Ψ - ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData⟫_ℂ = 0 := by
    rw [inner_sub_right,
        h_inner_eq (Ψ - ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData),
        sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h_diff)

theorem eq_zero_of_wightmanTranslate_ray_fixed_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTranslate WData htrans (t • a) Ψ = Ψ)
    (horth : ⟪wightmanVacuum WData, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
      WData htrans hcluster hfixed, horth, zero_smul]

theorem eq_smul_wightmanVacuum_of_wightmanSpatialTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanSpatialTranslate WData htrans (t • a) Ψ = Ψ) :
    Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData := by
  refine eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
    WData htrans hcluster (fun t => ?_)
  rw [smul_euclidSpatialVec]
  exact hfixed t

theorem eq_zero_of_wightmanSpatialTranslate_fixed_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanSpatialTranslate WData htrans (t • a) Ψ = Ψ)
    (horth : ⟪wightmanVacuum WData, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_wightmanVacuum_of_wightmanSpatialTranslate_fixed
      WData htrans hcluster hfixed, horth, zero_smul]

theorem eq_smul_wightmanVacuum_of_wightmanTimeTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTimeTranslate WData htrans t Ψ = Ψ) :
    Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData := by
  refine eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
    WData htrans hcluster (fun t => ?_)
  rw [smul_euclidTimeVec_one]
  exact hfixed t

theorem eq_zero_of_wightmanTimeTranslate_fixed_of_inner_wightmanVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData)
    {Ψ : WightmanHilbert WData}
    (hfixed : ∀ t : ℝ, wightmanTimeTranslate WData htrans t Ψ = Ψ)
    (horth : ⟪wightmanVacuum WData, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_wightmanVacuum_of_wightmanTimeTranslate_fixed
      WData htrans hcluster hfixed, horth, zero_smul]

def WightmanVacuumUnique {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ Ψ : WightmanHilbert WData,
    (∀ a : Fin 4 → ℝ, wightmanTranslate WData htrans a Ψ = Ψ) →
      Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData

def WightmanSpatialVacuumUnique {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ Ψ : WightmanHilbert WData,
    (∀ a : Fin 3 → ℝ, wightmanSpatialTranslate WData htrans a Ψ = Ψ) →
      Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData

def WightmanTimeVacuumUnique {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ Ψ : WightmanHilbert WData,
    (∀ t : ℝ, wightmanTimeTranslate WData htrans t Ψ = Ψ) →
      Ψ = ⟪wightmanVacuum WData, Ψ⟫_ℂ • wightmanVacuum WData

def OSVacuumUnique {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (hcontr : OSContractionCondition D) : Prop :=
  ∀ Ψ : OSHilbert D,
    (∀ (τ : ℝ) (hτ : 0 ≤ τ), osContractionSemigroup D hcontr τ hτ Ψ = Ψ) →
      Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D

def OSSpatialVacuumUnique {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (htrans : OSTranslationInvariant D.𝒮) : Prop :=
  ∀ Ψ : OSHilbert D,
    (∀ a : Fin 3 → ℝ, osSpatialTranslate D htrans a Ψ = Ψ) →
      Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D

theorem wightmanVacuumUnique_of_clusterAlong
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 4 → ℝ} (hcluster : WightmanClusterAlong WData a) :
    WightmanVacuumUnique WData htrans :=
  fun _ hfixed =>
    eq_smul_wightmanVacuum_of_wightmanTranslate_ray_fixed
      WData htrans hcluster (fun t => hfixed (t • a))

theorem wightmanSpatialVacuumUnique_of_spatialClusterAlong
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {a : Fin 3 → ℝ} (hcluster : WightmanSpatialClusterAlong WData a) :
    WightmanSpatialVacuumUnique WData htrans :=
  fun _ hfixed =>
    eq_smul_wightmanVacuum_of_wightmanSpatialTranslate_fixed
      WData htrans hcluster (fun t => hfixed (t • a))

theorem wightmanTimeVacuumUnique_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hcluster : WightmanTimeClusterDecomposition WData) :
    WightmanTimeVacuumUnique WData htrans :=
  fun _ hfixed =>
    eq_smul_wightmanVacuum_of_wightmanTimeTranslate_fixed
      WData htrans hcluster hfixed

theorem wightmanVacuumUnique_of_wightmanSpatialVacuumUnique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (huniq : WightmanSpatialVacuumUnique WData htrans) :
    WightmanVacuumUnique WData htrans :=
  fun Ψ hfixed => huniq Ψ (fun a => hfixed (euclidSpatialVec a))

theorem wightmanVacuumUnique_of_wightmanTimeVacuumUnique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (huniq : WightmanTimeVacuumUnique WData htrans) :
    WightmanVacuumUnique WData htrans :=
  fun Ψ hfixed => huniq Ψ (fun t => hfixed (euclidTimeVec t))

theorem osVacuumUnique_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (hcontr : OSContractionCondition D)
    (hcluster : OSTimeClusterDecomposition D) :
    OSVacuumUnique D hcontr :=
  fun _ hfixed =>
    eq_smul_osVacuum_of_osContractionSemigroup_fixed D hcontr hcluster hfixed

theorem osSpatialVacuumUnique_of_spatialClusterAlong
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (htrans : OSTranslationInvariant D.𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong D a) :
    OSSpatialVacuumUnique D htrans :=
  fun _ hfixed =>
    eq_smul_osVacuum_of_osSpatialTranslate_fixed
      D htrans hcluster (fun t => hfixed (t • a))

theorem wightmanVacuumNormalized_iff_osVacuumNormalized_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanVacuumNormalized S W ↔ OSVacuumNormalized D.𝒮 := by
  unfold WightmanVacuumNormalized OSVacuumNormalized
  rw [← osConfigToWightmanConfig_osVacuumConfig,
      wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw,
      ← inner_osBasis D (osVacuumConfig ι) (osVacuumConfig ι)]
  change ⟪osVacuum D, osVacuum D⟫_ℂ = 1 ↔
    D.𝒮 0 Fin.elim0 (euclidOrderedBasePoint 0) = 1
  rw [inner_osVacuum_self]

theorem wightmanKernel_translate_right_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (hspec : ZeroMomentumSpectrumCondition W)
    (a : Fin 4 → ℝ) (A B : WightmanConfig ι) :
    wightmanKernel S W A (wightmanConfigTranslate a B) =
      wightmanKernel S W A B := by
  rw [wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A
        (wightmanConfigTranslate a B),
      wightmanKernel_eq_vladimirovKernel_mul_integral S hspec A B,
      integral_wightmanConfigTranslate]
  rfl

theorem osKernel_spatialShift_right_of_vladimirov
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (a : Fin 3 → ℝ) (A B : OSConfig ι) :
    osKernel S 𝒮 A (osConfigSpatialShift a B) = osKernel S 𝒮 A B := by
  rw [osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A
        (osConfigSpatialShift a B),
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A B]
  rfl

theorem osKernel_timeShift_right_of_vladimirov
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (τ : ℝ) (hτ : 0 ≤ τ) (A B : OSConfig ι) :
    osKernel S 𝒮 A (osConfigTimeShift τ hτ B) = osKernel S 𝒮 A B := by
  rw [osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A
        (osConfigTimeShift τ hτ B),
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw A B]
  rfl

theorem wightmanClusterAlong_iff_osSpatialClusterAlong_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (a : Fin 4 → ℝ) (b : Fin 3 → ℝ) :
    WightmanClusterAlong (wightmanPositiveDataOfOSData D W hspec h_schw) a ↔
      OSSpatialClusterAlong D b := by
  refine ⟨fun hW A B => ?_, fun hOS A B => ?_⟩
  · have h_spec :=
      hW (osConfigToWightmanConfig A) (osConfigToWightmanConfig B)
    have h_lhs :
        (fun t : ℝ =>
          wightmanKernel S W (osConfigToWightmanConfig A)
            (wightmanConfigTranslate (t • a) (osConfigToWightmanConfig B))) =
        fun t : ℝ =>
          osKernel S D.𝒮 A (osConfigSpatialShift (t • b) B) := by
      ext t
      rw [wightmanKernel_translate_right_of_zeroMomentumSpectrumCondition
            S hspec,
          wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw,
          osKernel_spatialShift_right_of_vladimirov S hspec h_schw]
    have h_rhs :
        wightmanKernel S W (osConfigToWightmanConfig A)
          (wightmanVacuumConfig ι) *
        wightmanKernel S W (wightmanVacuumConfig ι)
          (osConfigToWightmanConfig B) =
        osKernel S D.𝒮 A (osVacuumConfig ι) *
          osKernel S D.𝒮 (osVacuumConfig ι) B := by
      rw [← osConfigToWightmanConfig_osVacuumConfig,
          wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw,
          wightmanKernel_osConfigToWightmanConfig_eq_osKernel S hspec h_schw]
    rwa [wightmanPositiveDataOfOSData_W, h_lhs, h_rhs] at h_spec
  · have h_base :=
      hOS (osIndexedBaseConfig A.1 A.2.1) (osIndexedBaseConfig B.1 B.2.1)
    have h_const_os :
        (fun t : ℝ =>
          osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1)
            (osConfigSpatialShift (t • b) (osIndexedBaseConfig B.1 B.2.1))) =
        fun _ : ℝ =>
          osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1)
            (osIndexedBaseConfig B.1 B.2.1) := by
      ext t
      exact osKernel_spatialShift_right_of_vladimirov S hspec h_schw (t • b)
        (osIndexedBaseConfig A.1 A.2.1) (osIndexedBaseConfig B.1 B.2.1)
    rw [h_const_os] at h_base
    have h_os_fac :
        osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1)
          (osIndexedBaseConfig B.1 B.2.1) =
        osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1) (osVacuumConfig ι) *
          osKernel S D.𝒮 (osVacuumConfig ι)
            (osIndexedBaseConfig B.1 B.2.1) :=
      tendsto_nhds_unique tendsto_const_nhds h_base
    have h_w_fac :
        (fun t : ℝ =>
          wightmanKernel S (wightmanPositiveDataOfOSData D W hspec h_schw).W A
            (wightmanConfigTranslate (t • a) B)) =
        fun _ : ℝ =>
          wightmanKernel S (wightmanPositiveDataOfOSData D W hspec h_schw).W A
            (wightmanVacuumConfig ι) *
          wightmanKernel S (wightmanPositiveDataOfOSData D W hspec h_schw).W
            (wightmanVacuumConfig ι) B := by
      ext t
      rw [wightmanPositiveDataOfOSData_W,
          wightmanKernel_translate_right_of_zeroMomentumSpectrumCondition
            S hspec,
          wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A B,
          wightmanKernel_eq_osKernel_mul_integral S hspec h_schw A
            (wightmanVacuumConfig ι),
          wightmanKernel_eq_osKernel_mul_integral S hspec h_schw
            (wightmanVacuumConfig ι) B,
          integral_wightmanVacuumConfig, star_one, one_mul, mul_one, h_os_fac]
      change star (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
          (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) *
          (osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1) (osVacuumConfig ι) *
            osKernel S D.𝒮 (osVacuumConfig ι)
              (osIndexedBaseConfig B.1 B.2.1)) =
        star (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
          osKernel S D.𝒮 (osIndexedBaseConfig A.1 A.2.1) (osVacuumConfig ι) *
          ((∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) *
            osKernel S D.𝒮 (osVacuumConfig ι)
              (osIndexedBaseConfig B.1 B.2.1))
      ring
    rw [h_w_fac]
    exact tendsto_const_nhds

theorem wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (a : Fin 4 → ℝ) :
    WightmanClusterAlong (wightmanPositiveDataOfOSData D W hspec h_schw) a ↔
      OSTimeClusterDecomposition D := by
  rw [wightmanClusterAlong_iff_osSpatialClusterAlong_of_vladimirov
    D W hspec h_schw a 0]
  refine ⟨fun hOS A B => ?_, fun hT A B => ?_⟩
  · have h_spec := hOS A B
    have h_eq :
        (fun τ : ℝ =>
          osKernel S D.𝒮 A
            (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
        fun t : ℝ => osKernel S D.𝒮 A (osConfigSpatialShift (t • 0) B) := by
      ext τ
      rw [osKernel_timeShift_right_of_vladimirov S hspec h_schw,
          osKernel_spatialShift_right_of_vladimirov S hspec h_schw]
    rwa [h_eq]
  · have h_spec := hT A B
    have h_eq :
        (fun t : ℝ => osKernel S D.𝒮 A (osConfigSpatialShift (t • 0) B)) =
        fun τ : ℝ =>
          osKernel S D.𝒮 A
            (osConfigTimeShift (max τ 0) (le_max_right τ 0) B) := by
      ext t
      rw [osKernel_spatialShift_right_of_vladimirov S hspec h_schw,
          osKernel_timeShift_right_of_vladimirov S hspec h_schw]
    rwa [h_eq]

theorem wightmanTimeCluster_iff_osTimeCluster_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    WightmanTimeClusterDecomposition
        (wightmanPositiveDataOfOSData D W hspec h_schw) ↔
      OSTimeClusterDecomposition D :=
  wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    D W hspec h_schw (euclidTimeVec 1)

theorem wightmanVacuumUnique_iff_osVacuumUnique_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hcontr : OSContractionCondition D)
    (htrans : WightmanTranslationInvariant W) :
    WightmanVacuumUnique
        (wightmanPositiveDataOfOSData D W hspec h_schw) htrans ↔
      OSVacuumUnique D hcontr := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  let e := vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
  refine ⟨fun hW Ψ hfixed => ?_, fun hOS Ψ hfixed => ?_⟩
  · have h_wfixed : ∀ a : Fin 4 → ℝ,
        wightmanTranslate WData htrans a (e Ψ) = e Ψ := by
      intro a
      rw [wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
          WData hspec htrans a, ContinuousLinearMap.id_apply]
    have h_eq := hW (e Ψ) h_wfixed
    have h_symm := congrArg e.symm h_eq
    rw [e.symm_apply_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_osVacuum D W hspec h_schw,
        e.inner_map_map] at h_symm
    exact h_symm
  · have h_osfixed : ∀ (τ : ℝ) (hτ : 0 ≤ τ),
        osContractionSemigroup D hcontr τ hτ (e.symm Ψ) = e.symm Ψ := by
      intro τ hτ
      rw [osContractionSemigroup_eq_id_of_vladimirov D hspec h_schw hcontr τ hτ,
          ContinuousLinearMap.id_apply]
    have h_eq := hOS (e.symm Ψ) h_osfixed
    have h_map := congrArg e h_eq
    rw [e.apply_symm_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_osVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum
          D W hspec h_schw,
        e.symm.inner_map_map] at h_map
    exact h_map

theorem wightmanSpatialVacuumUnique_iff_osSpatialVacuumUnique_of_vladimirov
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (hOS : OSTranslationInvariant D.𝒮)
    (hW : WightmanTranslationInvariant W) :
    WightmanSpatialVacuumUnique
        (wightmanPositiveDataOfOSData D W hspec h_schw) hW ↔
      OSSpatialVacuumUnique D hOS := by
  let WData := wightmanPositiveDataOfOSData D W hspec h_schw
  let e := vladimirovOSWightmanLinearIsometryEquiv D W hspec h_schw
  refine ⟨fun hW_uniq Ψ hfixed => ?_, fun hOS_uniq Ψ hfixed => ?_⟩
  · have h_wfixed : ∀ a : Fin 3 → ℝ,
        wightmanSpatialTranslate WData hW a (e Ψ) = e Ψ := by
      intro a
      rw [← vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
            D W hspec h_schw hOS hW a Ψ, hfixed a]
    have h_eq := hW_uniq (e Ψ) h_wfixed
    have h_symm := congrArg e.symm h_eq
    rw [e.symm_apply_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_osVacuum D W hspec h_schw,
        e.inner_map_map] at h_symm
    exact h_symm
  · have h_osfixed : ∀ a : Fin 3 → ℝ,
        osSpatialTranslate D hOS a (e.symm Ψ) = e.symm Ψ := by
      intro a
      apply e.injective
      rw [vladimirovOSWightmanLinearIsometryEquiv_intertwines_spatialTranslate
            D W hspec h_schw hOS hW a (e.symm Ψ),
          e.apply_symm_apply, hfixed a]
    have h_eq := hOS_uniq (e.symm Ψ) h_osfixed
    have h_map := congrArg e h_eq
    rw [e.apply_symm_apply, map_smul,
        vladimirovOSWightmanLinearIsometryEquiv_osVacuum,
        ← vladimirovOSWightmanLinearIsometryEquiv_symm_wightmanVacuum
          D W hspec h_schw,
        e.symm.inner_map_map] at h_map
    exact h_map

theorem vacWightman_vacuumNormalized
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    WightmanVacuumNormalized S (vacWightmanData R S).W := by
  dsimp [vacWightmanData]
  rw [wightmanVacuumNormalized_iff_osVacuumNormalized_of_vladimirov
    (vacOSData R S) vacW vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)]
  exact vacS_vacuumNormalized

@[simp]
theorem inner_wightmanVacuum_vacWightmanData_self
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    ⟪wightmanVacuum (vacWightmanData R S),
      wightmanVacuum (vacWightmanData R S)⟫_ℂ = 1 :=
  inner_wightmanVacuum_self_of_normalized (vacWightmanData R S)
    (vacWightman_vacuumNormalized R S)

@[simp]
theorem norm_wightmanVacuum_vacWightmanData
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    ‖wightmanVacuum (vacWightmanData R S)‖ = 1 :=
  norm_wightmanVacuum_of_normalized (vacWightmanData R S)
    (vacWightman_vacuumNormalized R S)

theorem vacWightmanHilbert_eq_smul_wightmanVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (Φ : WightmanHilbert (vacWightmanData R S)) :
    Φ = ⟪wightmanVacuum (vacWightmanData R S), Φ⟫_ℂ •
      wightmanVacuum (vacWightmanData R S) := by
  let e := vacOSWightmanLinearIsometryEquiv R S
  have h_os := vacHilbert_eq_smul_osVacuum R S (e.symm Φ)
  have h_map := congrArg e h_os
  rw [e.apply_symm_apply, map_smul,
      ← e.inner_map_map (osVacuum (vacOSData R S)) (e.symm Φ),
      e.apply_symm_apply, vacOSWightmanLinearIsometryEquiv_osVacuum R S] at h_map
  exact h_map

theorem vacWightmanClusterAlong
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (a : Fin 4 → ℝ) :
    WightmanClusterAlong (vacWightmanData R S) a := by
  dsimp [vacWightmanData]
  rw [wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    (vacOSData R S) vacW vacZeroMomentumSpectrumCondition
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl) a]
  exact vacOSTimeCluster R S

theorem vacWightmanVacuumUnique
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : WightmanTranslationInvariant (vacWightmanData R S).W) :
    WightmanVacuumUnique (vacWightmanData R S) htrans :=
  fun Φ _ => vacWightmanHilbert_eq_smul_wightmanVacuum R S Φ

theorem fourMomentumWightman_vacuumNormalized (q : Fin 4 → ℝ) :
    WightmanVacuumNormalized trivialStarStructure
      (fourMomentumWightmanData q).W := by
  unfold WightmanVacuumNormalized
  rw [← inner_wightmanVacuum_self (fourMomentumWightmanData q),
      inner_wightmanVacuum_fourMomentumWightmanData_self]

theorem fourMomentumWightmanOneParticle_ne_zero (q : Fin 4 → ℝ) :
    fourMomentumWightmanOneParticle q ≠ 0 := by
  intro h
  have hn := norm_fourMomentumWightmanOneParticle q
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem wightmanTranslate_fourMomentumWightmanData_fixed_iff
    (q a : Fin 4 → ℝ) (Φ : WightmanHilbert (fourMomentumWightmanData q)) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a Φ = Φ ↔
      (Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) - 1) *
        ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ = 0 := by
  have h_diff :
      wightmanTranslate (fourMomentumWightmanData q)
          (fourMomentumW_wightmanTranslationInvariant q) a Φ - Φ =
        ((Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) - 1) *
          ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ) •
          fourMomentumWightmanOneParticle q := by
    rw [wightmanTranslate_fourMomentumWightmanData_apply q a Φ]
    conv_lhs =>
      arg 2
      rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
    rw [smul_smul, add_sub_add_left_eq_sub, ← sub_smul, sub_mul, one_mul]
  rw [← sub_eq_zero, h_diff,
      smul_eq_zero_iff_left (fourMomentumWightmanOneParticle_ne_zero q)]

omit [Fintype ι] [DecidableEq ι] in
def minkowskiDualVec (q : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![q 0, -q 1, -q 2, -q 3]

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_minkowskiDualVec (q : Fin 4 → ℝ) :
    minkowskiInner q (minkowskiDualVec q) =
      q 0 * q 0 + q 1 * q 1 + q 2 * q 2 + q 3 * q 3 := by
  rw [minkowskiInner_explicit]
  change q 0 * q 0 - q 1 * (-q 1) - q 2 * (-q 2) - q 3 * (-q 3) =
    q 0 * q 0 + q 1 * q 1 + q 2 * q 2 + q 3 * q 3
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_minkowskiDualVec_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    minkowskiInner q (minkowskiDualVec q) ≠ 0 := by
  rw [minkowskiInner_minkowskiDualVec]
  intro h0
  apply hq
  ext μ
  have h0' : q 0 * q 0 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  have h1' : q 1 * q 1 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  have h2' : q 2 * q 2 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  have h3' : q 3 * q 3 = 0 := by
    nlinarith [mul_self_nonneg (q 0), mul_self_nonneg (q 1),
      mul_self_nonneg (q 2), mul_self_nonneg (q 3)]
  fin_cases μ
  · exact mul_self_eq_zero.mp h0'
  · exact mul_self_eq_zero.mp h1'
  · exact mul_self_eq_zero.mp h2'
  · exact mul_self_eq_zero.mp h3'

omit [Fintype ι] [DecidableEq ι] in
lemma exists_minkowskiInner_eq_pi_of_ne_zero {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    ∃ a : Fin 4 → ℝ, minkowskiInner q a = Real.pi := by
  refine ⟨(Real.pi / minkowskiInner q (minkowskiDualVec q)) •
    minkowskiDualVec q, ?_⟩
  rw [minkowskiInner_smul_right,
      div_mul_cancel₀ _ (minkowskiInner_minkowskiDualVec_ne_zero hq)]

omit [Fintype ι] [DecidableEq ι] in
lemma exp_I_mul_pi_sub_one_ne_zero :
    Complex.exp (Complex.I * (Real.pi : ℂ)) - 1 ≠ 0 := by
  rw [mul_comm, Complex.exp_pi_mul_I]
  norm_num

theorem wightmanVacuumUnique_fourMomentumWightmanData_of_ne_zero
    {q : Fin 4 → ℝ} (hq : q ≠ 0) :
    WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) := by
  intro Φ hfixed
  obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero hq
  have ha_fixed :=
    (wightmanTranslate_fourMomentumWightmanData_fixed_iff q a Φ).mp (hfixed a)
  rw [ha] at ha_fixed
  have h_orth : ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ = 0 :=
    (mul_eq_zero.mp ha_fixed).resolve_left exp_I_mul_pi_sub_one_ne_zero
  conv_lhs =>
    rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
  rw [h_orth, zero_smul, add_zero]

theorem not_wightmanVacuumUnique_fourMomentumWightmanData_zero :
    ¬ WightmanVacuumUnique (fourMomentumWightmanData 0)
      (fourMomentumW_wightmanTranslationInvariant 0) := by
  intro huniq
  have hfixed : ∀ a : Fin 4 → ℝ,
      wightmanTranslate (fourMomentumWightmanData 0)
        (fourMomentumW_wightmanTranslationInvariant 0) a
        (fourMomentumWightmanOneParticle 0) =
      fourMomentumWightmanOneParticle 0 := by
    intro a
    rw [wightmanTranslate_fourMomentumWightmanOneParticle]
    have h0 : minkowskiInner (0 : Fin 4 → ℝ) a = 0 := by
      simp [minkowskiInner_explicit]
    rw [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  have h_eq := huniq (fourMomentumWightmanOneParticle 0) hfixed
  rw [inner_wightmanVacuum_fourMomentumWightmanOneParticle, zero_smul] at h_eq
  exact fourMomentumWightmanOneParticle_ne_zero 0 h_eq

theorem wightmanVacuumUnique_fourMomentumWightmanData_iff (q : Fin 4 → ℝ) :
    WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q ≠ 0 := by
  refine ⟨fun huniq hq0 => ?_, wightmanVacuumUnique_fourMomentumWightmanData_of_ne_zero⟩
  subst hq0
  exact not_wightmanVacuumUnique_fourMomentumWightmanData_zero huniq

theorem wightmanTimeVacuumUnique_fourMomentumWightmanData_iff (q : Fin 4 → ℝ) :
    WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q 0 ≠ 0 := by
  refine ⟨fun huniq hq0 => ?_, fun hq0 Φ hfixed => ?_⟩
  · have hfixed : ∀ t : ℝ,
        wightmanTimeTranslate (fourMomentumWightmanData q)
          (fourMomentumW_wightmanTranslationInvariant q) t
          (fourMomentumWightmanOneParticle q) =
        fourMomentumWightmanOneParticle q := by
      intro t
      unfold wightmanTimeTranslate
      rw [wightmanTranslate_fourMomentumWightmanOneParticle]
      have h0 : minkowskiInner q (euclidTimeVec t) = 0 := by
        simp [minkowskiInner_explicit, euclidTimeVec, hq0]
      rw [h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
    have h_eq := huniq (fourMomentumWightmanOneParticle q) hfixed
    rw [inner_wightmanVacuum_fourMomentumWightmanOneParticle, zero_smul] at h_eq
    exact fourMomentumWightmanOneParticle_ne_zero q h_eq
  · have ht := hfixed (Real.pi / q 0)
    unfold wightmanTimeTranslate at ht
    have h_iff :=
      (wightmanTranslate_fourMomentumWightmanData_fixed_iff
        q (euclidTimeVec (Real.pi / q 0)) Φ).mp ht
    have h_inner :
        minkowskiInner q (euclidTimeVec (Real.pi / q 0)) = Real.pi := by
      rw [minkowskiInner_explicit]
      dsimp [euclidTimeVec]
      have h_mul : q 0 * (Real.pi / q 0) = Real.pi :=
        mul_div_cancel₀ Real.pi hq0
      linarith
    rw [h_inner] at h_iff
    have h_orth : ⟪fourMomentumWightmanOneParticle q, Φ⟫_ℂ = 0 :=
      (mul_eq_zero.mp h_iff).resolve_left exp_I_mul_pi_sub_one_ne_zero
    conv_lhs =>
      rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Φ]
    rw [h_orth, zero_smul, add_zero]

theorem wightmanTimeVacuumUnique_fourMomentumWightmanData_iff_osTimeCluster
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      OSTimeClusterDecomposition (fourMomentumOSData q) := by
  rw [wightmanTimeVacuumUnique_fourMomentumWightmanData_iff,
      osTimeClusterDecomposition_fourMomentumOSData_iff]
  exact ⟨fun hne => lt_of_le_of_ne hq0 hne.symm, ne_of_gt⟩

theorem wightmanVacuumUnique_fourMomentum_iff_osTimeCluster_of_mem_closure_forward_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      OSTimeClusterDecomposition (fourMomentumOSData q) := by
  rw [wightmanVacuumUnique_fourMomentumWightmanData_iff,
      osTimeClusterDecomposition_fourMomentumOSData_iff]
  refine ⟨zero_apply_pos_of_mem_closure_forward_light_cone hq, ?_⟩
  intro hpos h0
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

noncomputable def z2FreeWightmanOneParticle :
    WightmanHilbert z2FreeWightmanData :=
  z2FreeOSWightmanLinearIsometryEquiv z2FreeOneParticle

@[simp]
theorem z2FreeOSWightmanLinearIsometryEquiv_osVacuum :
    z2FreeOSWightmanLinearIsometryEquiv (osVacuum z2FreeOSData) =
      wightmanVacuum z2FreeWightmanData :=
  vladimirovOSWightmanLinearIsometryEquiv_osVacuum z2FreeOSData z2FreeW
    (momentZeroMomentumSpectrumCondition z2FreeCoeff)
    (fun n α x _ => by
      change z2FreeS n α x = vladimirovSchwinger (momentW z2FreeCoeff) n α x
      rw [vladimirovSchwinger_momentW]
      rfl)

@[simp]
theorem inner_wightmanVacuum_z2FreeWightmanOneParticle :
    ⟪wightmanVacuum z2FreeWightmanData, z2FreeWightmanOneParticle⟫_ℂ = 0 := by
  dsimp [z2FreeWightmanOneParticle]
  rw [← z2FreeOSWightmanLinearIsometryEquiv_osVacuum,
      z2FreeOSWightmanLinearIsometryEquiv.inner_map_map,
      inner_osVacuum_z2FreeOneParticle]

@[simp]
theorem norm_z2FreeWightmanOneParticle :
    ‖z2FreeWightmanOneParticle‖ = 1 := by
  dsimp [z2FreeWightmanOneParticle]
  rw [z2FreeOSWightmanLinearIsometryEquiv.norm_map, norm_z2FreeOneParticle]

theorem z2FreeWightmanOneParticle_ne_zero :
    z2FreeWightmanOneParticle ≠ 0 := by
  intro h
  have hn := norm_z2FreeWightmanOneParticle
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

theorem not_wightmanVacuumUnique_z2FreeWightmanData
    (htrans : WightmanTranslationInvariant z2FreeWightmanData.W) :
    ¬ WightmanVacuumUnique z2FreeWightmanData htrans := by
  intro huniq
  have hfixed : ∀ a : Fin 4 → ℝ,
      wightmanTranslate z2FreeWightmanData htrans a
        z2FreeWightmanOneParticle = z2FreeWightmanOneParticle := by
    intro a
    rw [wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        z2FreeWightmanData
        (momentZeroMomentumSpectrumCondition z2FreeCoeff) htrans a,
        ContinuousLinearMap.id_apply]
  have h_eq := huniq z2FreeWightmanOneParticle hfixed
  rw [inner_wightmanVacuum_z2FreeWightmanOneParticle, zero_smul] at h_eq
  exact z2FreeWightmanOneParticle_ne_zero h_eq

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightmanClusterAlong_iff_osTimeCluster
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (a : Fin 4 → ℝ) :
    WightmanClusterAlong P.toWightmanPositiveData a ↔
      OSTimeClusterDecomposition P.osData :=
  wightmanClusterAlong_iff_osTimeCluster_of_vladimirov
    P.osData P.W P.spectrum h_schw a

theorem wightmanVacuumUnique_iff_osVacuumUnique
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x) :
    WightmanVacuumUnique P.toWightmanPositiveData
        P.wightmanTranslationInvariant ↔
      OSVacuumUnique P.osData P.contraction :=
  wightmanVacuumUnique_iff_osVacuumUnique_of_vladimirov
    P.osData P.W P.spectrum h_schw P.contraction
    P.wightmanTranslationInvariant

end OSReconstructedWightman

theorem phase3_wightman_cluster_vacuum_bridge_master
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (q : Fin 4 → ℝ) :
    (∀ Φ : WightmanHilbert (vacWightmanData R S),
      Φ = ⟪wightmanVacuum (vacWightmanData R S), Φ⟫_ℂ •
        wightmanVacuum (vacWightmanData R S)) ∧
    (∀ a : Fin 4 → ℝ, WightmanClusterAlong (vacWightmanData R S) a) ∧
    (WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q ≠ 0) ∧
    (WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q 0 ≠ 0) ∧
    (¬ WightmanVacuumUnique z2FreeWightmanData
      (wightmanTranslationInvariant_of_poincare
        trivialRep (momentPoincareCovariant z2FreeCoeff))) :=
  ⟨vacWightmanHilbert_eq_smul_wightmanVacuum R S,
   vacWightmanClusterAlong R S,
   wightmanVacuumUnique_fourMomentumWightmanData_iff q,
   wightmanTimeVacuumUnique_fourMomentumWightmanData_iff q,
   not_wightmanVacuumUnique_z2FreeWightmanData
     (wightmanTranslationInvariant_of_poincare
       trivialRep (momentPoincareCovariant z2FreeCoeff))⟩

noncomputable def vladimirovSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    WightmanHilbert WData :=
  (∫ x : Fin n → Fin 4 → ℝ, f x) •
    wightmanBasis WData (wightmanBaseConfig n α)

@[simp]
lemma vladimirovSchwartzVec_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι) :
    vladimirovSchwartzVec WData n α 0 = 0 := by
  unfold vladimirovSchwartzVec
  change (∫ x : Fin n → Fin 4 → ℝ, (0 : ℂ)) •
      wightmanBasis WData (wightmanBaseConfig n α) = 0
  rw [MeasureTheory.integral_zero, zero_smul]

lemma vladimirovSchwartzVec_add
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovSchwartzVec WData n α (f + g) =
      vladimirovSchwartzVec WData n α f +
        vladimirovSchwartzVec WData n α g := by
  unfold vladimirovSchwartzVec
  change (∫ x : Fin n → Fin 4 → ℝ, f x + g x) •
      wightmanBasis WData (wightmanBaseConfig n α) = _
  rw [MeasureTheory.integral_add f.integrable g.integrable, add_smul]

lemma vladimirovSchwartzVec_smul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovSchwartzVec WData n α (c • f) =
      c • vladimirovSchwartzVec WData n α f := by
  unfold vladimirovSchwartzVec
  change (∫ x : Fin n → Fin 4 → ℝ, c * f x) •
      wightmanBasis WData (wightmanBaseConfig n α) = _
  rw [MeasureTheory.integral_const_mul, mul_smul]

@[simp]
lemma vladimirovSchwartzVec_schwartzDiagTranslateN
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (n : ℕ) (α : Fin n → ι)
    (a : Fin 4 → ℝ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovSchwartzVec WData n α (schwartzDiagTranslateN n a f) =
      vladimirovSchwartzVec WData n α f := by
  unfold vladimirovSchwartzVec
  rw [integral_schwartzDiagTranslateN]

theorem wightmanTranslate_vladimirovSchwartzVec_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W)
    (n : ℕ) (α : Fin n → ι) (a : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wightmanTranslate WData htrans a (vladimirovSchwartzVec WData n α f) =
      vladimirovSchwartzVec WData n α (schwartzDiagTranslateN n a f) := by
  rw [vladimirovSchwartzVec_schwartzDiagTranslateN,
      wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
        WData hspec htrans a,
      ContinuousLinearMap.id_apply]

theorem vladimirovSchwartzVec_eq_wightmanBasis_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    vladimirovSchwartzVec (wightmanPositiveDataOfOSData D W hspec h_schw)
        A.1 A.2.1 A.2.2.val =
      wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw) A :=
  (wightmanBasis_eq_integral_smul_wightmanBaseConfig D W hspec h_schw A).symm

theorem inner_vladimirovSchwartzVec_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ⟪vladimirovSchwartzVec WData j α f,
      vladimirovSchwartzVec WData k α' g⟫_ℂ =
    star (∫ y : Fin j → Fin 4 → ℝ, f y) *
      (∫ z : Fin k → Fin 4 → ℝ, g z) *
      vladimirovKernel S WData.W j k α α' := by
  unfold vladimirovSchwartzVec
  rw [inner_smul_left, inner_smul_right, inner_wightmanBasis,
      wightmanKernel_eq_vladimirovKernel_mul_integral S hspec
        (wightmanBaseConfig j α) (wightmanBaseConfig k α'),
      integral_wightmanBaseConfig, integral_wightmanBaseConfig,
      star_one, one_mul, one_mul, ← Complex.star_def, mul_assoc]
  rfl

theorem inner_vladimirovSchwartzVec_eq_wightman_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (h : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hh : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      h x = (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun i => x (Fin.natAdd j i))) :
    ⟪vladimirovSchwartzVec WData j α f,
      vladimirovSchwartzVec WData k α' g⟫_ℂ =
    ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        WData.W (j + k) (Fin.append (β ∘ Fin.rev) α') h := by
  rw [inner_vladimirovSchwartzVec_of_zeroMomentumSpectrumCondition
      WData hspec j k α α' f g]
  unfold vladimirovKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  have hh_eq :
      (fun x : Fin (j + k) → Fin 4 → ℝ => h x) =
      fun x =>
        ((fun y => (starRingEnd ℂ) (f y))
          (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        ((fun z => g z) (fun i => x (Fin.natAdd j i))) := by
    ext x
    exact hh x
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec (j + k)
      (Fin.append (β ∘ Fin.rev) α') h,
      hh_eq,
      integral_split_rev_mul j k
        (fun y => (starRingEnd ℂ) (f y)) (fun z => g z),
      integral_conj, ← Complex.star_def]
  change (star (∫ y : Fin j → Fin 4 → ℝ, f y) *
      ∫ z : Fin k → Fin 4 → ℝ, g z) *
      ((∏ i : Fin j, S.C (α i) (β i)) *
        vladimirov_H WData.W (j + k) (osConcatIdx j k β α') 0) =
    (∏ i : Fin j, S.C (α i) (β i)) *
      (vladimirov_H WData.W (j + k) (osConcatIdx j k β α') 0 *
        (star (∫ y : Fin j → Fin 4 → ℝ, f y) *
          ∫ z : Fin k → Fin 4 → ℝ, g z))
  ring

noncomputable def vladimirovBorchersSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    WightmanHilbert WData :=
  ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
    vladimirovSchwartzVec WData j α (F j α)

theorem inner_vladimirovBorchersSchwartzVec_eq_wightmanSesquilinear
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (N : ℕ)
    (F F' : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
      (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F' k α' (fun i => x (Fin.natAdd j i))) :
    ⟪vladimirovBorchersSchwartzVec WData N F,
      vladimirovBorchersSchwartzVec WData N F'⟫_ℂ =
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          WData.W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α') := by
  unfold vladimirovBorchersSchwartzVec
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_inner]
  have h_comm :
      (∑ α : Fin j → ι,
        ⟪vladimirovSchwartzVec WData j α (F j α),
          ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ) =
      ∑ k ∈ Finset.range (N + 1), ∑ α : Fin j → ι, ∑ α' : Fin k → ι,
        ⟪vladimirovSchwartzVec WData j α (F j α),
          vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ := by
    have h_inner : ∀ α : Fin j → ι,
        ⟪vladimirovSchwartzVec WData j α (F j α),
          ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
            vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ =
        ∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
          ⟪vladimirovSchwartzVec WData j α (F j α),
            vladimirovSchwartzVec WData k α' (F' k α')⟫_ℂ := by
      intro α
      rw [inner_sum]
      refine Finset.sum_congr rfl (fun k _ => inner_sum _ _ _)
    simp_rw [h_inner]
    exact Finset.sum_comm
  rw [h_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun α _ => ?_)
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  exact inner_vladimirovSchwartzVec_eq_wightman_of_zeroMomentumSpectrumCondition
    WData hspec j k α α' (F j α) (F' k α') (G j k α α') (hG j k α α')

noncomputable def fourMomentumEvenSchwartzTerm (q : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) : ℂ :=
  if n % 2 = 0 then minkowskiFourier f (alternatingMomentum n q) else 0

noncomputable def fourMomentumOddSchwartzTerm (q : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) : ℂ :=
  if n % 2 = 1 then minkowskiFourier f (-alternatingMomentum n q) else 0

@[simp]
lemma fourMomentumEvenSchwartzTerm_compact (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumEvenSchwartzTerm q A.1 A.2.2.val =
      fourMomentumEvenWightmanTerm q A := rfl

@[simp]
lemma fourMomentumOddSchwartzTerm_compact (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumOddSchwartzTerm q A.1 A.2.2.val =
      fourMomentumOddWightmanTerm q A := rfl

lemma minkowskiFourier_add_n (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (f + g) p =
      minkowskiFourier f p + minkowskiFourier g p := by
  rw [← minkowskiFourierEvalTD_apply, ← minkowskiFourierEvalTD_apply,
      ← minkowskiFourierEvalTD_apply, map_add]

lemma minkowskiFourier_smul_n (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (c • f) p = c * minkowskiFourier f p := by
  rw [← minkowskiFourierEvalTD_apply, ← minkowskiFourierEvalTD_apply,
      map_smul, smul_eq_mul]

@[simp]
lemma minkowskiFourier_zero_n (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (0 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) p = 0 := by
  rw [← minkowskiFourierEvalTD_apply, map_zero]

lemma fourMomentumEvenSchwartzTerm_add (q : Fin 4 → ℝ) (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumEvenSchwartzTerm q n (f + g) =
      fourMomentumEvenSchwartzTerm q n f +
        fourMomentumEvenSchwartzTerm q n g := by
  unfold fourMomentumEvenSchwartzTerm
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, if_pos hn, minkowskiFourier_add_n]
  · simp [hn]

lemma fourMomentumOddSchwartzTerm_add (q : Fin 4 → ℝ) (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumOddSchwartzTerm q n (f + g) =
      fourMomentumOddSchwartzTerm q n f +
        fourMomentumOddSchwartzTerm q n g := by
  unfold fourMomentumOddSchwartzTerm
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, if_pos hn, minkowskiFourier_add_n]
  · simp [hn]

lemma fourMomentumEvenSchwartzTerm_smul (q : Fin 4 → ℝ) (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumEvenSchwartzTerm q n (c • f) =
      c * fourMomentumEvenSchwartzTerm q n f := by
  unfold fourMomentumEvenSchwartzTerm
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_smul_n]
  · simp [hn]

lemma fourMomentumOddSchwartzTerm_smul (q : Fin 4 → ℝ) (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumOddSchwartzTerm q n (c • f) =
      c * fourMomentumOddSchwartzTerm q n f := by
  unfold fourMomentumOddSchwartzTerm
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, minkowskiFourier_smul_n]
  · simp [hn]

@[simp]
lemma fourMomentumEvenSchwartzTerm_translate (q a : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumEvenSchwartzTerm q n (schwartzDiagTranslateN n a f) =
      fourMomentumEvenSchwartzTerm q n f := by
  unfold fourMomentumEvenSchwartzTerm
  by_cases hn : n % 2 = 0
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_alternatingMomentum_of_even n hn q]
    have h0 : minkowskiInner 0 a = 0 := by
      simp [minkowskiInner_explicit]
    rw [h0, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  · rw [if_neg hn, if_neg hn]

@[simp]
lemma fourMomentumOddSchwartzTerm_translate (q a : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumOddSchwartzTerm q n (schwartzDiagTranslateN n a f) =
      Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
        fourMomentumOddSchwartzTerm q n f := by
  unfold fourMomentumOddSchwartzTerm
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, if_pos hn, minkowskiFourier_schwartzDiagTranslateN,
        sum_neg_alternatingMomentum_of_odd n hn q]
    congr 2
    have h_neg : minkowskiInner (-q) a = -minkowskiInner q a := by
      simp [minkowskiInner_explicit]
      ring
    rw [h_neg, Complex.ofReal_neg, mul_neg, neg_neg]
  · rw [if_neg hn, if_neg hn, mul_zero]

noncomputable def fourMomentumSchwartzVec (q : Fin 4 → ℝ) (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    WightmanHilbert (fourMomentumWightmanData q) :=
  fourMomentumEvenSchwartzTerm q n f •
    wightmanVacuum (fourMomentumWightmanData q) +
  fourMomentumOddSchwartzTerm q n f •
    fourMomentumWightmanOneParticle q

@[simp]
theorem fourMomentumSchwartzVec_compact (q : Fin 4 → ℝ)
    (A : WightmanConfig Unit) :
    fourMomentumSchwartzVec q A.1 A.2.2.val =
      wightmanBasis (fourMomentumWightmanData q) A :=
  (wightmanBasis_fourMomentumWightmanData_eq q A).symm

theorem fourMomentumSchwartzVec_add (q : Fin 4 → ℝ) (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumSchwartzVec q n (f + g) =
      fourMomentumSchwartzVec q n f + fourMomentumSchwartzVec q n g := by
  unfold fourMomentumSchwartzVec
  rw [fourMomentumEvenSchwartzTerm_add, fourMomentumOddSchwartzTerm_add,
      add_smul, add_smul]
  abel

theorem fourMomentumSchwartzVec_smul (q : Fin 4 → ℝ) (n : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    fourMomentumSchwartzVec q n (c • f) =
      c • fourMomentumSchwartzVec q n f := by
  unfold fourMomentumSchwartzVec
  rw [fourMomentumEvenSchwartzTerm_smul, fourMomentumOddSchwartzTerm_smul,
      smul_add, mul_smul, mul_smul]

@[simp]
theorem inner_wightmanVacuum_fourMomentumSchwartzVec (q : Fin 4 → ℝ)
    (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ⟪wightmanVacuum (fourMomentumWightmanData q),
      fourMomentumSchwartzVec q n f⟫_ℂ =
    fourMomentumW q n α f := by
  unfold fourMomentumSchwartzVec
  rw [inner_add_right, inner_smul_right, inner_smul_right,
      inner_wightmanVacuum_fourMomentumWightmanData_self,
      inner_wightmanVacuum_fourMomentumWightmanOneParticle,
      mul_one, mul_zero, add_zero, fourMomentumW_apply]
  rfl

@[simp]
theorem inner_fourMomentumWightmanOneParticle_fourMomentumSchwartzVec
    (q : Fin 4 → ℝ) (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ⟪fourMomentumWightmanOneParticle q,
      fourMomentumSchwartzVec q n f⟫_ℂ =
    fourMomentumOddSchwartzTerm q n f := by
  unfold fourMomentumSchwartzVec
  rw [inner_add_right, inner_smul_right, inner_smul_right,
      inner_fourMomentumWightmanOneParticle_wightmanVacuum,
      inner_fourMomentumWightmanOneParticle_self,
      mul_zero, mul_one, zero_add]

theorem inner_fourMomentumSchwartzVec_eq (q : Fin 4 → ℝ) (j k : ℕ)
    (fj : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (fk : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ⟪fourMomentumSchwartzVec q j fj, fourMomentumSchwartzVec q k fk⟫_ℂ =
      star (fourMomentumEvenSchwartzTerm q j fj) *
        fourMomentumEvenSchwartzTerm q k fk +
      star (fourMomentumOddSchwartzTerm q j fj) *
        fourMomentumOddSchwartzTerm q k fk := by
  unfold fourMomentumSchwartzVec
  rw [inner_add_left, inner_add_right, inner_add_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_wightmanVacuum_fourMomentumWightmanData_self,
      inner_wightmanVacuum_fourMomentumWightmanOneParticle,
      inner_fourMomentumWightmanOneParticle_wightmanVacuum,
      inner_fourMomentumWightmanOneParticle_self, ← Complex.star_def]
  simp only [mul_one, mul_zero, add_zero, zero_add]

theorem inner_fourMomentumSchwartzVec_eq_fourMomentumW (q : Fin 4 → ℝ)
    (j k : ℕ)
    (fj : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (fk : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hg : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      g x = (starRingEnd ℂ) (fj (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        fk (fun i => x (Fin.natAdd j i)))
    (α : Fin (j + k) → Unit) :
    ⟪fourMomentumSchwartzVec q j fj, fourMomentumSchwartzVec q k fk⟫_ℂ =
      fourMomentumW q (j + k) α g := by
  rw [inner_fourMomentumSchwartzVec_eq,
      fourMomentumW_apply_split_rev_mul q j k fj fk g hg α]
  unfold fourMomentumEvenSchwartzTerm fourMomentumOddSchwartzTerm
  by_cases hj0 : j % 2 = 0 <;> by_cases hk0 : k % 2 = 0
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · simp [hj0, hk0]
  · have hj1 : j % 2 = 1 := by omega
    have hk1 : k % 2 = 1 := by omega
    simp [hj1, hk1]

theorem wightmanTranslate_fourMomentumSchwartzVec (q a : Fin 4 → ℝ)
    (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    wightmanTranslate (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) a
      (fourMomentumSchwartzVec q n f) =
    fourMomentumSchwartzVec q n (schwartzDiagTranslateN n a f) := by
  unfold fourMomentumSchwartzVec
  rw [map_add, map_smul, map_smul, wightmanTranslate_vacuum,
      wightmanTranslate_fourMomentumWightmanOneParticle,
      fourMomentumEvenSchwartzTerm_translate,
      fourMomentumOddSchwartzTerm_translate,
      smul_smul, mul_comm]

omit [Fintype ι] [DecidableEq ι] in
def compactSchwartzStarFun (j : ℕ) (f : CompactSchwartz j)
    (x : Fin j → Fin 4 → ℝ) : ℂ :=
  (starRingEnd ℂ) (f.val (fun i => x (Fin.rev i)))

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzStarFun_contDiff (j : ℕ) (f : CompactSchwartz j) :
    ContDiff ℝ (⊤ : ℕ∞) (compactSchwartzStarFun j f) := by
  have h_rev : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin j → Fin 4 → ℝ => (fun i : Fin j => x (Fin.rev i))) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.rev i))
  exact Complex.conjCLE.contDiff.comp (f.val.smooth'.comp h_rev)

omit [Fintype ι] [DecidableEq ι] in
lemma compactSchwartzStarFun_hasCompactSupport (j : ℕ)
    (f : CompactSchwartz j) :
    HasCompactSupport (compactSchwartzStarFun j f) := by
  have h_cont : Continuous
      (fun y : Fin j → Fin 4 → ℝ => (fun i : Fin j => y (Fin.rev i))) :=
    continuous_pi (fun i => continuous_apply (Fin.rev i))
  refine HasCompactSupport.of_support_subset_isCompact
    (f.property.isCompact.image h_cont) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h_ne : f.val (fun i => x (Fin.rev i)) ≠ 0 := by
    intro h0
    apply hx
    simp [compactSchwartzStarFun, h0]
  refine ⟨fun i => x (Fin.rev i), subset_tsupport _ h_ne, ?_⟩
  ext i μ
  change x (Fin.rev (Fin.rev i)) μ = x i μ
  rw [Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzStar (j : ℕ) (f : CompactSchwartz j) :
    CompactSchwartz j :=
  ⟨(compactSchwartzStarFun_hasCompactSupport j f).toSchwartzMap
      (compactSchwartzStarFun_contDiff j f),
   compactSchwartzStarFun_hasCompactSupport j f⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_apply (j : ℕ) (f : CompactSchwartz j)
    (x : Fin j → Fin 4 → ℝ) :
    (compactSchwartzStar j f).val x =
      (starRingEnd ℂ) (f.val (fun i => x (Fin.rev i))) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_star (j : ℕ) (f : CompactSchwartz j) :
    compactSchwartzStar j (compactSchwartzStar j f) = f := by
  apply Subtype.ext
  ext x
  simp only [compactSchwartzStar_apply, RingHomCompTriple.comp_apply,
    RingHom.id_apply, Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_translate (j : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz j) :
    compactSchwartzStar j (compactSchwartzTranslate j a f) =
      compactSchwartzTranslate j a (compactSchwartzStar j f) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzStar_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzStar_lorentz (j : ℕ) (L : SL2C)
    (f : CompactSchwartz j) :
    compactSchwartzStar j (compactSchwartzLorentz j L f) =
      compactSchwartzLorentz j L (compactSchwartzStar j f) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzStar_apply, schwartzLorentzCLM_apply]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def compactSchwartzTensor (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    CompactSchwartz (j + k) :=
  ⟨wightmanConcatSchwartz j k (compactSchwartzStar j f) g,
   wightmanConcatFun_hasCompactSupport j k (compactSchwartzStar j f) g⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTensor_apply (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    (compactSchwartzTensor j k f g).val x =
      f.val (fun i => x (Fin.castAdd k i)) *
        g.val (fun i => x (Fin.natAdd j i)) := by
  change wightmanConcatSchwartz j k (compactSchwartzStar j f) g x = _
  simp only [wightmanConcatSchwartz_apply, compactSchwartzStar_apply,
    RingHomCompTriple.comp_apply, RingHom.id_apply, Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
lemma wightmanConcatSchwartz_eq_compactSchwartzTensor_star (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    wightmanConcatSchwartz j k f g =
      (compactSchwartzTensor j k (compactSchwartzStar j f) g).val := by
  ext x
  simp [wightmanConcatSchwartz_apply, compactSchwartzTensor_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma integral_compactSchwartzStar (j : ℕ) (f : CompactSchwartz j) :
    (∫ x : Fin j → Fin 4 → ℝ, (compactSchwartzStar j f).val x) =
      star (∫ x : Fin j → Fin 4 → ℝ, f.val x) := by
  change (∫ x : Fin j → Fin 4 → ℝ,
      (starRingEnd ℂ) (f.val (fun i => x (Fin.rev i)))) = _
  rw [integral_conj, integral_comp_rev, ← Complex.star_def]

omit [Fintype ι] [DecidableEq ι] in
lemma integral_compactSchwartzTensor (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    (∫ x : Fin (j + k) → Fin 4 → ℝ, (compactSchwartzTensor j k f g).val x) =
      (∫ y : Fin j → Fin 4 → ℝ, f.val y) *
        (∫ z : Fin k → Fin 4 → ℝ, g.val z) := by
  change (∫ x : Fin (j + k) → Fin 4 → ℝ,
      wightmanConcatSchwartz j k (compactSchwartzStar j f) g x) = _
  rw [integral_wightmanConcatSchwartz, integral_compactSchwartzStar, star_star]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTensor_translate (j k : ℕ) (a : Fin 4 → ℝ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    compactSchwartzTensor j k
      (compactSchwartzTranslate j a f) (compactSchwartzTranslate k a g) =
      compactSchwartzTranslate (j + k) a (compactSchwartzTensor j k f g) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzTensor_apply]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzTensor_lorentz (j k : ℕ) (L : SL2C)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    compactSchwartzTensor j k
      (compactSchwartzLorentz j L f) (compactSchwartzLorentz k L g) =
      compactSchwartzLorentz (j + k) L (compactSchwartzTensor j k f g) := by
  apply Subtype.ext
  ext x
  simp [compactSchwartzTensor_apply, schwartzLorentzCLM_apply]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanConfigMul (A B : WightmanConfig ι) :
    WightmanConfig ι :=
  ⟨A.1 + B.1, (Fin.append A.2.1 B.2.1,
    compactSchwartzTensor A.1 B.1 A.2.2 B.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigMul_fst (A B : WightmanConfig ι) :
    (wightmanConfigMul A B).1 = A.1 + B.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigMul_snd_fst (A B : WightmanConfig ι) :
    (wightmanConfigMul A B).2.1 = Fin.append A.2.1 B.2.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigMul_snd_snd (A B : WightmanConfig ι) :
    (wightmanConfigMul A B).2.2 =
      compactSchwartzTensor A.1 B.1 A.2.2 B.2.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma integral_wightmanConfigMul (A B : WightmanConfig ι) :
    (∫ x : Fin (wightmanConfigMul A B).1 → Fin 4 → ℝ,
      (wightmanConfigMul A B).2.2.val x) =
    (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
      (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z) :=
  integral_compactSchwartzTensor A.1 B.1 A.2.2 B.2.2

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigTranslate_wightmanConfigMul (a : Fin 4 → ℝ)
    (A B : WightmanConfig ι) :
    wightmanConfigTranslate a (wightmanConfigMul A B) =
      wightmanConfigMul (wightmanConfigTranslate a A)
        (wightmanConfigTranslate a B) := by
  unfold wightmanConfigTranslate wightmanConfigMul
  dsimp only
  rw [compactSchwartzTensor_translate]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanConfigLorentz_wightmanConfigMul (L : SL2C)
    (A B : WightmanConfig ι) :
    wightmanConfigLorentz L (wightmanConfigMul A B) =
      wightmanConfigMul (wightmanConfigLorentz L A)
        (wightmanConfigLorentz L B) := by
  unfold wightmanConfigLorentz wightmanConfigMul
  dsimp only
  rw [compactSchwartzTensor_lorentz]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanSingleFieldConfig (α : ι)
    (f : CompactSchwartz 1) : WightmanConfig ι :=
  ⟨1, (fun _ => α, f)⟩

noncomputable def wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanLiftConfigMap WData (wightmanConfigMul A)

noncomputable def wightmanSingleFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (α : ι) (f : CompactSchwartz 1) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  wightmanFieldLM WData (wightmanSingleFieldConfig α f)

@[simp]
lemma wightmanFieldLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : WightmanConfig ι) :
    wightmanFieldLM WData A (wightmanBasisPre WData B) =
      wightmanBasisPre WData (wightmanConfigMul A B) :=
  wightmanLiftConfigMap_wightmanBasisPre WData (wightmanConfigMul A) B

@[simp]
lemma wightmanFieldLM_wightmanVacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    wightmanFieldLM WData A (wightmanVacuumPre WData) =
      wightmanBasisPre WData (wightmanConfigMul A (wightmanVacuumConfig ι)) :=
  wightmanFieldLM_wightmanBasisPre WData A (wightmanVacuumConfig ι)

@[simp]
lemma wightmanSingleFieldLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (α : ι) (f : CompactSchwartz 1)
    (B : WightmanConfig ι) :
    wightmanSingleFieldLM WData α f (wightmanBasisPre WData B) =
      wightmanBasisPre WData
        (wightmanConfigMul (wightmanSingleFieldConfig α f) B) :=
  wightmanFieldLM_wightmanBasisPre WData (wightmanSingleFieldConfig α f) B

theorem wightmanTranslateLM_wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ)
    (A : WightmanConfig ι) (Ψ : WightmanPreHilbertSpace WData) :
    wightmanTranslateLM WData a (wightmanFieldLM WData A Ψ) =
      wightmanFieldLM WData (wightmanConfigTranslate a A)
        (wightmanTranslateLM WData a Ψ) := by
  unfold wightmanTranslateLM wightmanFieldLM
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← wightmanLiftConfigMap_comp, ← wightmanLiftConfigMap_comp]
  congr 2

theorem wightmanScalarLorentzLM_wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (L : SL2C)
    (A : WightmanConfig ι) (Ψ : WightmanPreHilbertSpace WData) :
    wightmanScalarLorentzLM WData L (wightmanFieldLM WData A Ψ) =
      wightmanFieldLM WData (wightmanConfigLorentz L A)
        (wightmanScalarLorentzLM WData L Ψ) := by
  unfold wightmanScalarLorentzLM wightmanFieldLM
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← wightmanLiftConfigMap_comp, ← wightmanLiftConfigMap_comp]
  congr 2

theorem wightmanTranslateLM_wightmanScalarLorentzLM_wightmanFieldLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (a : Fin 4 → ℝ) (L : SL2C)
    (A : WightmanConfig ι) (Ψ : WightmanPreHilbertSpace WData) :
    wightmanTranslateLM WData a
      (wightmanScalarLorentzLM WData L (wightmanFieldLM WData A Ψ)) =
    wightmanFieldLM WData
      (wightmanConfigTranslate a (wightmanConfigLorentz L A))
      (wightmanTranslateLM WData a
        (wightmanScalarLorentzLM WData L Ψ)) := by
  rw [wightmanScalarLorentzLM_wightmanFieldLM,
      wightmanTranslateLM_wightmanFieldLM]

theorem wightmanBasis_wightmanConfigMul_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A B : WightmanConfig ι) :
    wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
        (wightmanConfigMul A B) =
      ((∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) *
        (∫ z : Fin B.1 → Fin 4 → ℝ, B.2.2.val z)) •
        wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
          (wightmanBaseConfig (A.1 + B.1) (Fin.append A.2.1 B.2.1)) := by
  rw [wightmanBasis_eq_integral_smul_wightmanBaseConfig,
      integral_wightmanConfigMul]
  rfl

theorem toWightmanHilbert_wightmanFieldLM_wightmanVacuumPre_of_osData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (A : WightmanConfig ι) :
    toWightmanHilbert (wightmanPositiveDataOfOSData D W hspec h_schw)
        (wightmanFieldLM (wightmanPositiveDataOfOSData D W hspec h_schw) A
          (wightmanVacuumPre (wightmanPositiveDataOfOSData D W hspec h_schw))) =
      (∫ y : Fin A.1 → Fin 4 → ℝ, A.2.2.val y) •
        wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
          (wightmanBaseConfig (A.1 + 0)
            (Fin.append A.2.1 (wightmanVacuumConfig ι).2.1)) := by
  rw [wightmanFieldLM_wightmanVacuumPre]
  change wightmanBasis (wightmanPositiveDataOfOSData D W hspec h_schw)
      (wightmanConfigMul A (wightmanVacuumConfig ι)) = _
  rw [wightmanBasis_wightmanConfigMul_of_osData,
      integral_wightmanVacuumConfig, mul_one]
  rfl

noncomputable def wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    Submodule ℂ (WightmanHilbert WData) :=
  Submodule.span ℂ (Set.range (wightmanBasis WData))

def WightmanVacuumCyclic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) : Prop :=
  Dense (wightmanCyclicSubmodule WData : Set (WightmanHilbert WData))

lemma wightmanBasis_mem_wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : WightmanConfig ι) :
    wightmanBasis WData A ∈ wightmanCyclicSubmodule WData :=
  Submodule.subset_span (Set.mem_range_self A)

lemma wightmanVacuum_mem_wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanVacuum WData ∈ wightmanCyclicSubmodule WData :=
  wightmanBasis_mem_wightmanCyclicSubmodule WData (wightmanVacuumConfig ι)

lemma toWightmanHilbert_mem_wightmanCyclicSubmodule
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (Ψ : WightmanPreHilbertSpace WData) :
    toWightmanHilbert WData Ψ ∈ wightmanCyclicSubmodule WData := by
  have h_expand : toWightmanHilbert WData Ψ =
      ∑ A ∈ Ψ.toFinsupp.support,
        Ψ.toFinsupp A • wightmanBasis WData A := by
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
  rw [h_expand]
  exact Submodule.sum_mem (wightmanCyclicSubmodule WData) (fun A _ =>
    Submodule.smul_mem (wightmanCyclicSubmodule WData) (Ψ.toFinsupp A)
      (wightmanBasis_mem_wightmanCyclicSubmodule WData A))

theorem wightmanVacuumCyclic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    WightmanVacuumCyclic WData := by
  unfold WightmanVacuumCyclic
  have h_dense : DenseRange (toWightmanHilbert WData) :=
    UniformSpace.Completion.denseRange_coe
  refine Dense.mono ?_ h_dense
  rintro x ⟨Ψ, rfl⟩
  exact toWightmanHilbert_mem_wightmanCyclicSubmodule WData Ψ

theorem eq_zero_of_inner_wightmanBasis_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    {Φ : WightmanHilbert WData}
    (horth : ∀ A : WightmanConfig ι, ⟪wightmanBasis WData A, Φ⟫_ℂ = 0) :
    Φ = 0 := by
  have h_pre : ∀ Ψ : WightmanPreHilbertSpace WData,
      ⟪toWightmanHilbert WData Ψ, Φ⟫_ℂ = 0 := by
    intro Ψ
    have h_expand : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support,
          Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    rw [h_expand, sum_inner]
    refine Finset.sum_eq_zero (fun A _ => ?_)
    rw [inner_smul_left, horth A, mul_zero]
  have h_all : ∀ x : WightmanHilbert WData, ⟪x, Φ⟫_ℂ = 0 := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih Ψ => exact h_pre Ψ
  exact inner_self_eq_zero.mp (h_all Φ)

theorem eq_of_inner_wightmanBasis_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    {Φ₁ Φ₂ : WightmanHilbert WData}
    (h : ∀ A : WightmanConfig ι,
      ⟪wightmanBasis WData A, Φ₁⟫_ℂ = ⟪wightmanBasis WData A, Φ₂⟫_ℂ) :
    Φ₁ = Φ₂ := by
  rw [← sub_eq_zero]
  refine eq_zero_of_inner_wightmanBasis_eq_zero WData (fun A => ?_)
  rw [inner_sub_right, h A, sub_self]

theorem phase4_wightman_field_cyclicity_master
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (q : Fin 4 → ℝ) :
    WightmanVacuumCyclic WData ∧
    (∀ (Φ : WightmanHilbert WData),
      (∀ A : WightmanConfig ι, ⟪wightmanBasis WData A, Φ⟫_ℂ = 0) → Φ = 0) ∧
    (∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι)
      (Ψ : WightmanPreHilbertSpace WData),
      wightmanTranslateLM WData a (wightmanFieldLM WData A Ψ) =
        wightmanFieldLM WData (wightmanConfigTranslate a A)
          (wightmanTranslateLM WData a Ψ)) ∧
    (∀ (L : SL2C) (A : WightmanConfig ι)
      (Ψ : WightmanPreHilbertSpace WData),
      wightmanScalarLorentzLM WData L (wightmanFieldLM WData A Ψ) =
        wightmanFieldLM WData (wightmanConfigLorentz L A)
          (wightmanScalarLorentzLM WData L Ψ)) ∧
    (∀ (n : ℕ) (α : Fin n → Unit) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      ⟪wightmanVacuum (fourMomentumWightmanData q),
        fourMomentumSchwartzVec q n f⟫_ℂ =
      fourMomentumW q n α f) ∧
    (∀ (a : Fin 4 → ℝ) (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      wightmanTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) a
        (fourMomentumSchwartzVec q n f) =
      fourMomentumSchwartzVec q n (schwartzDiagTranslateN n a f)) :=
  ⟨wightmanVacuumCyclic WData,
   fun _ => eq_zero_of_inner_wightmanBasis_eq_zero WData,
   wightmanTranslateLM_wightmanFieldLM WData,
   wightmanScalarLorentzLM_wightmanFieldLM WData,
   inner_wightmanVacuum_fourMomentumSchwartzVec q,
   fun a n f => wightmanTranslate_fourMomentumSchwartzVec q a n f⟩

omit [Fintype ι] [DecidableEq ι] in
theorem minkowskiInner_nonneg_of_mem_closure_forward_light_cone
    {q v : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (hv : v ∈ forward_light_cone) :
    0 ≤ minkowskiInner q v := by
  have h_bound := minkowskiInner_ge_coneGap_closure v q hq
  have h_gap := coneGap_pos v hv
  have hq0 : 0 ≤ q 0 := (closure_forward_light_cone_subset hq).1
  have h_prod : 0 ≤ coneGap v * q 0 := mul_nonneg (le_of_lt h_gap) hq0
  exact h_prod.trans h_bound

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wightmanComplexTranslatePhase
    (q a v : Fin 4 → ℝ) : ℂ :=
  Complex.exp
    (Complex.I * ((minkowskiInner q a : ℝ) : ℂ) -
      ((minkowskiInner q v : ℝ) : ℂ))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma norm_wightmanComplexTranslatePhase (q a v : Fin 4 → ℝ) :
    ‖wightmanComplexTranslatePhase q a v‖ =
      Real.exp (-minkowskiInner q v) := by
  unfold wightmanComplexTranslatePhase
  rw [Complex.norm_exp]
  congr 1
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem norm_wightmanComplexTranslatePhase_le_one_iff
    (q a v : Fin 4 → ℝ) :
    ‖wightmanComplexTranslatePhase q a v‖ ≤ 1 ↔
      0 ≤ minkowskiInner q v := by
  rw [norm_wightmanComplexTranslatePhase, Real.exp_le_one_iff]
  constructor <;> intro h <;> linarith

omit [Fintype ι] [DecidableEq ι] in
theorem norm_wightmanComplexTranslatePhase_le_one_of_mem_closure_forward_light_cone
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone)
    (a : Fin 4 → ℝ) {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) :
    ‖wightmanComplexTranslatePhase q a v‖ ≤ 1 := by
  rw [norm_wightmanComplexTranslatePhase_le_one_iff]
  exact minkowskiInner_nonneg_of_mem_closure_forward_light_cone hq hv

def WightmanEigenstatePositiveEnergy
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W) : Prop :=
  ∀ (p : Fin 4 → ℝ) (Ψ : WightmanHilbert WData),
    Ψ ≠ 0 →
    (∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a Ψ =
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) →
    ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner p v

theorem wightmanEigenstate_timeEnergy_nonneg
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (hposE : WightmanEigenstatePositiveEnergy WData htrans)
    {p : Fin 4 → ℝ} {Ψ : WightmanHilbert WData} (hΨ : Ψ ≠ 0)
    (heig : ∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a Ψ =
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) :
    0 ≤ p 0 := by
  have h1 := hposE p Ψ hΨ heig (euclidTimeVec 1)
    timeUnitVec_mem_forward_light_cone
  have h_inner : minkowskiInner p (euclidTimeVec 1) = p 0 := by
    simp [minkowskiInner_explicit, euclidTimeVec]
  rwa [h_inner] at h1

theorem wightmanEigenstate_eq_zero_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W)
    {p : Fin 4 → ℝ} {Ψ : WightmanHilbert WData} (hΨ : Ψ ≠ 0)
    (heig : ∀ a : Fin 4 → ℝ,
      wightmanTranslate WData htrans a Ψ =
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) :
    p = 0 := by
  by_contra hp
  obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero hp
  have h1 := heig a
  rw [wightmanTranslate_eq_id_of_zeroMomentumSpectrumCondition
      WData hspec htrans a,
      ContinuousLinearMap.id_apply, ha] at h1
  have h_sub :
      (Complex.exp (Complex.I * (Real.pi : ℂ)) - 1) • Ψ = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  exact hΨ ((smul_eq_zero.mp h_sub).resolve_left exp_I_mul_pi_sub_one_ne_zero)

theorem wightmanEigenstatePositiveEnergy_of_zeroMomentumSpectrumCondition
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (hspec : ZeroMomentumSpectrumCondition WData.W)
    (htrans : WightmanTranslationInvariant WData.W) :
    WightmanEigenstatePositiveEnergy WData htrans := by
  intro p Ψ hΨ heig v _hv
  have hp0 :=
    wightmanEigenstate_eq_zero_of_zeroMomentumSpectrumCondition
      WData hspec htrans hΨ heig
  subst hp0
  simp [minkowskiInner_explicit]

theorem fourMomentumWightman_eigenstate_momentum_eq_zero_or_eq
    (q p : Fin 4 → ℝ) {Ψ : WightmanHilbert (fourMomentumWightmanData q)}
    (hΨ : Ψ ≠ 0)
    (heig : ∀ a : Fin 4 → ℝ,
      wightmanTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) a Ψ =
      Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ) :
    p = 0 ∨ p = q := by
  by_cases hc0 : ⟪wightmanVacuum (fourMomentumWightmanData q), Ψ⟫_ℂ = 0
  · have hc1 : ⟪fourMomentumWightmanOneParticle q, Ψ⟫_ℂ ≠ 0 := by
      intro hc1_zero
      apply hΨ
      rw [fourMomentumWightmanHilbert_eq_vacuum_add_oneParticle q Ψ,
          hc0, hc1_zero, zero_smul, zero_smul, add_zero]
    refine Or.inr ?_
    by_contra hpq
    have h_sub_ne : p - q ≠ 0 := sub_ne_zero.mpr hpq
    obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero h_sub_ne
    have h_act :
        ⟪fourMomentumWightmanOneParticle q,
          wightmanTranslate (fourMomentumWightmanData q)
            (fourMomentumW_wightmanTranslationInvariant q) a Ψ⟫_ℂ =
        ⟪fourMomentumWightmanOneParticle q,
          Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ⟫_ℂ :=
      congrArg (fun x => ⟪fourMomentumWightmanOneParticle q, x⟫_ℂ) (heig a)
    rw [wightmanTranslate_fourMomentumWightmanData_apply,
        inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right,
        inner_fourMomentumWightmanOneParticle_wightmanVacuum,
        inner_fourMomentumWightmanOneParticle_self,
        mul_zero, mul_one, zero_add] at h_act
    have h_exp_q_ne :
        Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    have h_diff_inner :
        minkowskiInner p a = Real.pi + minkowskiInner q a := by
      have h_sub_inner :
          minkowskiInner (p - q) a =
            minkowskiInner p a - minkowskiInner q a := by
        simp [minkowskiInner_explicit]
        ring
      linarith
    have h_exp_p :
        Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) =
        Complex.exp (Complex.I * (Real.pi : ℂ)) *
          Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) := by
      rw [h_diff_inner, Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [h_exp_p, inner_smul_right] at h_act
    have h_zero :
        (Complex.exp (Complex.I * (Real.pi : ℂ)) - 1) *
          (Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
            ⟪fourMomentumWightmanOneParticle q, Ψ⟫_ℂ) = 0 := by
      linear_combination -h_act
    have h_prod_ne :
        Complex.exp (Complex.I * ((minkowskiInner q a : ℝ) : ℂ)) *
          ⟪fourMomentumWightmanOneParticle q, Ψ⟫_ℂ ≠ 0 :=
      mul_ne_zero h_exp_q_ne hc1
    exact h_prod_ne
      ((mul_eq_zero.mp h_zero).resolve_left exp_I_mul_pi_sub_one_ne_zero)
  · refine Or.inl ?_
    by_contra hp
    obtain ⟨a, ha⟩ := exists_minkowskiInner_eq_pi_of_ne_zero hp
    have h_act :
        ⟪wightmanVacuum (fourMomentumWightmanData q),
          wightmanTranslate (fourMomentumWightmanData q)
            (fourMomentumW_wightmanTranslationInvariant q) a Ψ⟫_ℂ =
        ⟪wightmanVacuum (fourMomentumWightmanData q),
          Complex.exp (Complex.I * ((minkowskiInner p a : ℝ) : ℂ)) • Ψ⟫_ℂ :=
      congrArg
        (fun x => ⟪wightmanVacuum (fourMomentumWightmanData q), x⟫_ℂ) (heig a)
    rw [wightmanTranslate_fourMomentumWightmanData_apply,
        inner_add_right, inner_smul_right, inner_smul_right,
        inner_smul_right,
        inner_wightmanVacuum_fourMomentumWightmanData_self,
        inner_wightmanVacuum_fourMomentumWightmanOneParticle,
        mul_one, mul_zero, mul_zero, add_zero, ha,
        inner_smul_right] at h_act
    have h_zero :
        (Complex.exp (Complex.I * (Real.pi : ℂ)) - 1) *
          ⟪wightmanVacuum (fourMomentumWightmanData q), Ψ⟫_ℂ = 0 := by
      linear_combination -h_act
    exact hc0
      ((mul_eq_zero.mp h_zero).resolve_left exp_I_mul_pi_sub_one_ne_zero)

theorem wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff
    (q : Fin 4 → ℝ) :
    WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner q v := by
  refine ⟨fun hpos v hv => ?_, fun hq p Ψ hΨ heig v hv => ?_⟩
  · exact hpos q (fourMomentumWightmanOneParticle q)
      (fourMomentumWightmanOneParticle_ne_zero q)
      (wightmanTranslate_fourMomentumWightmanOneParticle q) v hv
  · rcases fourMomentumWightman_eigenstate_momentum_eq_zero_or_eq
      q p hΨ heig with rfl | rfl
    · simp [minkowskiInner_explicit]
    · exact hq v hv

theorem wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_of_mem_closure
    {q : Fin 4 → ℝ} (hq : q ∈ closure forward_light_cone) :
    WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) := by
  rw [wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff]
  intro v hv
  exact minkowskiInner_nonneg_of_mem_closure_forward_light_cone hq hv

structure WightmanAxioms (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) where
  WData : WightmanPositiveData R S
  E : TubeExtension WData.W
  positivity : Positivity S WData.W
  poincare : PoincareCovariant R WData.W
  spectrum : ForwardConeSpectrumCondition WData.W
  weakLocality : WeakLocality η WData.W
  tube_covariant : TubeCovariant R E
  tube_pct : TubePCT η R E
  cyclic : WightmanVacuumCyclic WData

namespace WightmanAxioms

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ}

abbrev Hilbert (A : WightmanAxioms R S η) : Type _ :=
  WightmanHilbert A.WData

noncomputable def vacuum (A : WightmanAxioms R S η) : A.Hilbert :=
  wightmanVacuum A.WData

noncomputable def basis (A : WightmanAxioms R S η)
    (cfg : WightmanConfig ι) : A.Hilbert :=
  wightmanBasis A.WData cfg

theorem translationInvariant (A : WightmanAxioms R S η) :
    WightmanTranslationInvariant A.WData.W :=
  wightmanTranslationInvariant_of_poincare R A.poincare

noncomputable def translate (A : WightmanAxioms R S η) (a : Fin 4 → ℝ) :
    A.Hilbert →L[ℂ] A.Hilbert :=
  wightmanTranslate A.WData A.translationInvariant a

noncomputable def spatialTranslate (A : WightmanAxioms R S η)
    (a : Fin 3 → ℝ) : A.Hilbert →L[ℂ] A.Hilbert :=
  wightmanSpatialTranslate A.WData A.translationInvariant a

noncomputable def timeTranslate (A : WightmanAxioms R S η) (t : ℝ) :
    A.Hilbert →L[ℂ] A.Hilbert :=
  wightmanTimeTranslate A.WData A.translationInvariant t

@[simp]
theorem translate_zero (A : WightmanAxioms R S η) :
    A.translate 0 = ContinuousLinearMap.id ℂ A.Hilbert :=
  wightmanTranslate_zero A.WData A.translationInvariant

theorem translate_add (A : WightmanAxioms R S η) (a b : Fin 4 → ℝ) :
    A.translate (a + b) = (A.translate a).comp (A.translate b) :=
  wightmanTranslate_add A.WData A.translationInvariant a b

@[simp]
theorem translate_vacuum (A : WightmanAxioms R S η) (a : Fin 4 → ℝ) :
    A.translate a A.vacuum = A.vacuum :=
  wightmanTranslate_vacuum A.WData A.translationInvariant a

theorem inner_translate (A : WightmanAxioms R S η) (a : Fin 4 → ℝ)
    (x y : A.Hilbert) :
    ⟪A.translate a x, A.translate a y⟫_ℂ = ⟪x, y⟫_ℂ :=
  inner_wightmanTranslate A.WData A.translationInvariant a x y

theorem norm_translate (A : WightmanAxioms R S η) (a : Fin 4 → ℝ)
    (x : A.Hilbert) :
    ‖A.translate a x‖ = ‖x‖ :=
  norm_wightmanTranslate A.WData A.translationInvariant a x

theorem complexCovariant (A : WightmanAxioms R S η) :
    ComplexCovariant R A.E :=
  complex_covariance_of_real R A.WData.W A.E A.tube_covariant

noncomputable def H_ext (A : WightmanAxioms R S η) :
    ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ :=
  spinor_H_ext R A.WData.W A.E

theorem H_ext_analytic (A : WightmanAxioms R S η) (n : ℕ) (α : Fin n → ι) :
    AnalyticOn ℂ (A.H_ext n α) (extended_tube_n n) :=
  spinor_H_ext_analytic R A.WData.W A.E A.tube_covariant n α

theorem extendedTubeWeakLocality (A : WightmanAxioms R S η) :
    ExtendedTubeWeakLocality η A.H_ext :=
  extendedTubeWeakLocality_of_weakLocality R A.WData.W A.E
    A.tube_covariant A.weakLocality

theorem wightman_pct (A : WightmanAxioms R S η) :
    WightmanPCT η R A.WData.W :=
  wightman_pct_of_spectrumCondition R A.WData.W A.spectrum A.poincare A.weakLocality

theorem wrong_statistics_twoPoint_eq_zero (A : WightmanAxioms R S η)
    {ε : ℂ} (hε : R.HasSpinParity ε) (h_wrong : η ≠ ε)
    (β : Fin 2 → ι) :
    A.WData.W 2 β = 0 :=
  wrong_statistics_wightman_two_eq_zero S A.WData.W A.spectrum A.poincare
    A.positivity hε A.weakLocality h_wrong β

theorem spin_statistics (A : WightmanAxioms R S η)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (h_nondeg : ∃ β : Fin 2 → ι, A.WData.W 2 β ≠ 0) :
    η = ε :=
  spin_statistics_of_spectrumCondition S A.WData.W A.spectrum A.poincare
    A.positivity hε A.weakLocality h_nondeg

theorem eq_zero_of_inner_basis_eq_zero (A : WightmanAxioms R S η)
    {Φ : A.Hilbert} (horth : ∀ cfg : WightmanConfig ι, ⟪A.basis cfg, Φ⟫_ℂ = 0) :
    Φ = 0 :=
  eq_zero_of_inner_wightmanBasis_eq_zero A.WData horth

theorem euclidExtendedTubePermLocality (A : WightmanAxioms R S η)
    (hloc : LocalCommutativity η A.WData.W) :
    EuclidExtendedTubePermLocality η A.H_ext :=
  euclidExtendedTubePermLocality_of_localCommutativity R A.WData.W A.E
    A.tube_covariant hloc

noncomputable def permutedSchwinger (A : WightmanAxioms R S η) : SchwingerFamily ι :=
  schwingerFromPermutedTube R A.WData.W η A.E

theorem permutedSchwinger_eq_schwingerFromTube_on_orderedEuclidN
    (A : WightmanAxioms R S η) (hη : η = 1 ∨ η = -1)
    (hloc : LocalCommutativity η A.WData.W)
    (n : ℕ) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    A.permutedSchwinger n α x = schwingerFromTube A.E n α x :=
  schwingerFromPermutedTube_eq_schwingerFromTube_on_orderedEuclidN_of_localCommutativity
    R A.WData.W hη A.E A.tube_covariant hloc n α hx

theorem toFullEuclidOSAxioms (A : WightmanAxioms R S η)
    (hη : η = 1 ∨ η = -1) (htrans : TubeTranslationInvariant A.E)
    (hherm : TubeWickHermiticity S A.E)
    (hpos : OSReflectionPositive S (schwingerFromTube A.E))
    (hloc : LocalCommutativity η A.WData.W) :
    FullEuclidOSAxioms R S η A.permutedSchwinger :=
  schwingerFromPermutedTube_fullEuclidOSAxioms_of_localCommutativity
    R S A.WData.W hη A.E A.tube_covariant htrans hherm hpos hloc

end WightmanAxioms

theorem scalar_wightmanAxioms_spin_statistics {η : ℂ}
    (A : WightmanAxioms trivialRep trivialStarStructure η)
    (h_nondeg : ∃ β : Fin 2 → Unit, A.WData.W 2 β ≠ 0) :
    η = 1 :=
  A.spin_statistics trivialRep_spinParity h_nondeg

theorem vector_wightmanAxioms_spin_statistics {η : ℂ}
    (A : WightmanAxioms stdRep stdStarStructure η)
    (h_nondeg : ∃ β : Fin 2 → Fin 4, A.WData.W 2 β ≠ 0) :
    η = 1 :=
  A.spin_statistics stdRep_spinParity h_nondeg

theorem dirac_wightmanAxioms_spin_statistics {η : ℂ}
    (A : WightmanAxioms diracRep diracStarStructure η)
    (h_nondeg : ∃ β : Fin 2 → Fin 2 ⊕ Fin 2, A.WData.W 2 β ≠ 0) :
    η = -1 :=
  A.spin_statistics diracRep_spinParity h_nondeg

theorem spinorTensorBispinor_wightmanAxioms_spin_statistics (m₁ m₂ : ℕ) {η : ℂ}
    (A : WightmanAxioms
      (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
      (spinorTensorBispinorStarStructure m₁ m₂) η)
    (h_nondeg : ∃ β : Fin 2 → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)), A.WData.W 2 β ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) :=
  A.spin_statistics
    (directSumRep_spinParity (spinorTensorRep_spinParity m₁ m₂)
      (chiralSwapRep_spinParity (spinorTensorRep_spinParity m₁ m₂)))
    h_nondeg

structure WightmanAxiomsWithUniqueVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) extends
    WightmanAxioms R S η where
  vacuumNormalized : WightmanVacuumNormalized S WData.W
  cluster : ∀ a : Fin 4 → ℝ, a ≠ 0 → WightmanClusterAlong WData a
  vacuumUnique :
    WightmanVacuumUnique WData
      (wightmanTranslationInvariant_of_poincare R poincare)

namespace WightmanAxiomsWithUniqueVacuum

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ}

@[simp]
theorem inner_vacuum_self (A : WightmanAxiomsWithUniqueVacuum R S η) :
    ⟪A.toWightmanAxioms.vacuum, A.toWightmanAxioms.vacuum⟫_ℂ = 1 :=
  inner_wightmanVacuum_self_of_normalized A.WData A.vacuumNormalized

@[simp]
theorem norm_vacuum (A : WightmanAxiomsWithUniqueVacuum R S η) :
    ‖A.toWightmanAxioms.vacuum‖ = 1 :=
  norm_wightmanVacuum_of_normalized A.WData A.vacuumNormalized

theorem eq_smul_vacuum_of_translate_fixed
    (A : WightmanAxiomsWithUniqueVacuum R S η)
    {Ψ : A.toWightmanAxioms.Hilbert}
    (hfixed : ∀ a : Fin 4 → ℝ, A.toWightmanAxioms.translate a Ψ = Ψ) :
    Ψ = ⟪A.toWightmanAxioms.vacuum, Ψ⟫_ℂ • A.toWightmanAxioms.vacuum :=
  A.vacuumUnique Ψ hfixed

end WightmanAxiomsWithUniqueVacuum

namespace ForwardConeOSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms
    (B : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    WightmanAxioms R S η where
  WData := B.toWightmanPositiveData
  E := B.E
  positivity := B.positivity
  poincare := B.poincare
  spectrum := B.spectrum
  weakLocality := B.weakLocality
  tube_covariant := B.tube_covariant
  tube_pct := B.tube_pct
  cyclic := wightmanVacuumCyclic B.toWightmanPositiveData

end ForwardConeOSEuclideanTubeBridge

namespace OSEuclideanTubeBridge

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms (B : OSEuclideanTubeBridge R S η 𝒮) :
    WightmanAxioms R S η :=
  B.toForwardConeOSEuclideanTubeBridge.toWightmanAxioms

end OSEuclideanTubeBridge

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    WightmanAxioms R S η where
  WData := P.toWightmanPositiveData
  E := P.E
  positivity := P.positivity
  poincare := P.poincare
  spectrum := P.spectrum
  weakLocality := P.weakLocality
  tube_covariant := P.tube_covariant
  tube_pct := P.tube_pct
  cyclic := wightmanVacuumCyclic P.toWightmanPositiveData

end ForwardConeOSReconstructedWightman

namespace OSReconstructionData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}
  {hOS : OSAxioms R S η 𝒮}
  {hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData}

noncomputable def toWightmanAxioms
    (G : OSReconstructionData hOS hcluster) :
    WightmanAxioms R S η :=
  G.toForwardConeOSReconstructedWightman.toWightmanAxioms

@[simp]
theorem toWightmanAxioms_W
    (G : OSReconstructionData hOS hcluster) :
    G.toWightmanAxioms.WData.W = G.F.toWightmanFamily := rfl

@[simp]
theorem toWightmanAxioms_E
    (G : OSReconstructionData hOS hcluster) :
    G.toWightmanAxioms.E = G.F.toTubeExtension := rfl

end OSReconstructionData

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def toWightmanAxioms
    (P : OSReconstructedWightman R S η 𝒮) :
    WightmanAxioms R S η :=
  P.toForwardConeOSReconstructedWightman.toWightmanAxioms

noncomputable def toWightmanAxiomsWithUniqueVacuum
    (P : OSReconstructedWightman R S η 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger P.W n α x)
    (hnorm : OSVacuumNormalized 𝒮)
    (hcluster : OSTimeClusterDecomposition P.osData) :
    WightmanAxiomsWithUniqueVacuum R S η where
  toWightmanAxioms := P.toWightmanAxioms
  vacuumNormalized :=
    (wightmanVacuumNormalized_iff_osVacuumNormalized_of_vladimirov
      P.osData P.W P.spectrum h_schw).mpr hnorm
  cluster a _ha :=
    (P.wightmanClusterAlong_iff_osTimeCluster h_schw a).mpr hcluster
  vacuumUnique :=
    (P.wightmanVacuumUnique_iff_osVacuumUnique h_schw).mpr
      (osVacuumUnique_of_timeCluster P.osData P.contraction hcluster)

end OSReconstructedWightman

noncomputable def vacWightmanAxioms
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    WightmanAxioms R S η :=
  (vacOSReconstructedWightman R S η).toWightmanAxioms

noncomputable def vacWightmanAxiomsWithUniqueVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    WightmanAxiomsWithUniqueVacuum R S η :=
  (vacOSReconstructedWightman R S η).toWightmanAxiomsWithUniqueVacuum
    (fun n α x _ => by
      change vacS n α x = vladimirovSchwinger vacW n α x
      rw [vladimirovSchwinger_vacW])
    vacS_vacuumNormalized
    (vacOSTimeCluster R S)

noncomputable def z2FreeWightmanAxioms :
    WightmanAxioms trivialRep trivialStarStructure 1 :=
  z2FreeOSReconstructedWightman.toWightmanAxioms

noncomputable def coherentWightmanAxiomsWithUniqueVacuum (r : ℝ) :
    WightmanAxiomsWithUniqueVacuum trivialRep trivialStarStructure 1 :=
  (coherentOSReconstructedWightman r).toWightmanAxiomsWithUniqueVacuum
    (fun n α x _ => by
      change coherentS r n α x = vladimirovSchwinger (coherentW r) n α x
      rw [coherentS, coherentW, vladimirovSchwinger_momentW])
    (by
      unfold OSVacuumNormalized coherentS momentS
      simp [coherentCoeff_apply])
    (coherentOSTimeCluster r)

theorem phase5_wightman_axioms_reconstruction_master
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ)
    (q : Fin 4 → ℝ) :
    (WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner q v) ∧
    (q ∈ closure forward_light_cone →
      WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) ∧
      ForwardConeSpectrumCondition (fourMomentumW q)) ∧
    WightmanVacuumCyclic (vacWightmanAxioms R S η).WData ∧
    WightmanVacuumUnique (vacWightmanAxiomsWithUniqueVacuum R S η).WData
      (vacWightmanAxiomsWithUniqueVacuum R S η).toWightmanAxioms.translationInvariant ∧
    WightmanVacuumCyclic z2FreeWightmanAxioms.WData :=
  ⟨wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff q,
   fun hq =>
     ⟨wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_of_mem_closure hq,
      fourMomentumW_forwardConeSpectrumCondition hq⟩,
   (vacWightmanAxioms R S η).cyclic,
   (vacWightmanAxiomsWithUniqueVacuum R S η).vacuumUnique,
   z2FreeWightmanAxioms.cyclic⟩

theorem wightman_bridge_grand_master
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ)
    (W : WightmanFamily ι)
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    {q : Fin 4 → ℝ} (hq0 : 0 ≤ q 0) :
    ((CompactPositivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W)) ∧
     (ZeroMomentumSpectrumCondition W →
      (Positivity S W ↔
        (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W)))) ∧
    ((∀ a b : Fin 4 → ℝ,
      wightmanTranslate WData htrans (a + b) =
        (wightmanTranslate WData htrans a).comp
          (wightmanTranslate WData htrans b)) ∧
     (∀ (t : ℝ) (Φ : OSHilbert (fourMomentumOSData q)),
      fourMomentumOSWightmanLinearIsometryEquiv q
        ((fourMomentumOSHolomorphicSemigroup hq0).realTimeUnitary (-t) Φ) =
      wightmanTimeTranslate (fourMomentumWightmanData q)
        (fourMomentumW_wightmanTranslationInvariant q) t
        (fourMomentumOSWightmanLinearIsometryEquiv q Φ))) ∧
    ((WightmanVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q ≠ 0) ∧
     (WightmanTimeVacuumUnique (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔ q 0 ≠ 0)) ∧
    (WightmanVacuumCyclic WData ∧
     (∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι)
       (Ψ : WightmanPreHilbertSpace WData),
       wightmanTranslateLM WData a (wightmanFieldLM WData A Ψ) =
         wightmanFieldLM WData (wightmanConfigTranslate a A)
           (wightmanTranslateLM WData a Ψ))) ∧
    ((WightmanEigenstatePositiveEnergy (fourMomentumWightmanData q)
      (fourMomentumW_wightmanTranslationInvariant q) ↔
      ∀ v ∈ forward_light_cone, 0 ≤ minkowskiInner q v) ∧
     WightmanVacuumUnique (vacWightmanAxiomsWithUniqueVacuum R S η).WData
       (vacWightmanAxiomsWithUniqueVacuum R S η).toWightmanAxioms.translationInvariant) :=
  ⟨⟨compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W,
    positivity_iff_wightmanKernelPositive_and_hermiticity_of_zeroMomentumSpectrumCondition S⟩,
   ⟨wightmanTranslate_add WData htrans,
    fourMomentumOSWightmanLinearIsometryEquiv_intertwines_realTimeUnitary hq0⟩,
   ⟨wightmanVacuumUnique_fourMomentumWightmanData_iff q,
    wightmanTimeVacuumUnique_fourMomentumWightmanData_iff q⟩,
   ⟨wightmanVacuumCyclic WData,
    wightmanTranslateLM_wightmanFieldLM WData⟩,
   ⟨wightmanEigenstatePositiveEnergy_fourMomentumWightmanData_iff q,
    (vacWightmanAxiomsWithUniqueVacuum R S η).vacuumUnique⟩⟩

def compactCutoff (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (m : ℕ) :
    CompactSchwartz n :=
  ⟨schwartzCutoffSeq n f m, schwartzCutoffSeq_hasCompactSupport n f m⟩

@[simp]
lemma compactCutoff_val (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (m : ℕ) :
    (compactCutoff n f m).val = schwartzCutoffSeq n f m := rfl

def concatProjLeftCLM (j k : ℕ) :
    (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin j → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => x (Fin.castAdd k (Fin.rev i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

def concatProjRightCLM (j k : ℕ) :
    (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i => x (Fin.natAdd j i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp]
lemma concatProjLeftCLM_apply (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) (i : Fin j) :
    concatProjLeftCLM j k x i = x (Fin.castAdd k (Fin.rev i)) := rfl

@[simp]
lemma concatProjRightCLM_apply (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) (i : Fin k) :
    concatProjRightCLM j k x i = x (Fin.natAdd j i) := rfl

lemma norm_concatProjLeftCLM_apply_le (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖concatProjLeftCLM j k x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i =>
    norm_le_pi_norm x (Fin.castAdd k (Fin.rev i)))

lemma norm_concatProjRightCLM_apply_le (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖concatProjRightCLM j k x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i =>
    norm_le_pi_norm x (Fin.natAdd j i))

lemma opNorm_concatProjLeftCLM_le_one (j k : ℕ) :
    ‖concatProjLeftCLM j k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa [one_mul] using norm_concatProjLeftCLM_apply_le j k x)

lemma opNorm_concatProjRightCLM_le_one (j k : ℕ) :
    ‖concatProjRightCLM j k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa [one_mul] using norm_concatProjRightCLM_apply_le j k x)

lemma starRingEnd_vladimirov_cutoff_bump_schwartz (n : ℕ) (y : Fin n → Fin 4 → ℝ) :
    (starRingEnd ℂ) (vladimirov_cutoff_bump_schwartz n y) =
      vladimirov_cutoff_bump_schwartz n y := by
  change (starRingEnd ℂ) ((vladimirovCutoffBump n 1 Real.zero_lt_one y : ℝ) : ℂ) =
    ((vladimirovCutoffBump n 1 Real.zero_lt_one y : ℝ) : ℂ)
  exact Complex.conj_ofReal _

lemma norm_iteratedFDeriv_bump_comp_clm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (n : ℕ)
    (L : E →L[ℝ] (Fin n → Fin 4 → ℝ)) (hL : ‖L‖ ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (q : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ q
      (fun y : E => vladimirov_cutoff_bump_schwartz n (r • L y)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz n) := by
  let M : E →L[ℝ] (Fin n → Fin 4 → ℝ) := r • L
  have hM_norm : ‖M‖ ≤ 1 := by
    dsimp [M]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
    nlinarith [norm_nonneg L]
  have h_smooth : ContDiff ℝ (q : ℕ∞)
      (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) :=
    ((vladimirov_cutoff_bump_schwartz n).smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
  have h_fn : (fun y : E => vladimirov_cutoff_bump_schwartz n (r • L y)) =
      (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) ∘ M := rfl
  rw [h_fn, M.iteratedFDeriv_comp_right h_smooth x (le_refl _)]
  have h_comp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ q (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) (M x))
    (fun _ : Fin q => M)
  have h_prod : (∏ _ : Fin q, ‖M‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg M) (fun _ _ => hM_norm)
  have h_sem := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
    (vladimirov_cutoff_bump_schwartz n) q (M x)
  calc ‖(iteratedFDeriv ℝ q (vladimirov_cutoff_bump_schwartz n) (M x)).compContinuousLinearMap
        (fun _ => M)‖
      ≤ ‖iteratedFDeriv ℝ q (vladimirov_cutoff_bump_schwartz n) (M x)‖ *
          ∏ _ : Fin q, ‖M‖ := h_comp
    _ ≤ SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz n) * 1 :=
        mul_le_mul h_sem h_prod (Finset.prod_nonneg (fun _ _ => norm_nonneg M))
          (apply_nonneg _ _)
    _ = SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz n) := mul_one _

lemma norm_iteratedFDeriv_concatBumpDiff_le (j k m i : ℕ)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i
      (fun y : Fin (j + k) → Fin 4 → ℝ =>
        vladimirov_cutoff_bump_schwartz j
          ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) *
        vladimirov_cutoff_bump_schwartz k
          ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) - 1) x‖ ≤
      (∑ q ∈ Finset.range (i + 1),
        (i.choose q : ℝ) *
          SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
          SchwartzMap.seminorm ℝ 0 (i - q) (vladimirov_cutoff_bump_schwartz k)) + 1 := by
  let r : ℝ := ((m : ℝ) + 1)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
  let b₁ : (Fin (j + k) → Fin 4 → ℝ) → ℂ :=
    fun y => vladimirov_cutoff_bump_schwartz j (r • concatProjLeftCLM j k y)
  let b₂ : (Fin (j + k) → Fin 4 → ℝ) → ℂ :=
    fun y => vladimirov_cutoff_bump_schwartz k (r • concatProjRightCLM j k y)
  have hb₁_smooth : ContDiff ℝ (⊤ : ℕ∞) b₁ :=
    ((vladimirov_cutoff_bump_schwartz j).smooth ⊤).comp
      ((r • concatProjLeftCLM j k).contDiff)
  have hb₂_smooth : ContDiff ℝ (⊤ : ℕ∞) b₂ :=
    ((vladimirov_cutoff_bump_schwartz k).smooth ⊤).comp
      ((r • concatProjRightCLM j k).contDiff)
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have h1 := norm_iteratedFDeriv_bump_comp_clm_le j (concatProjLeftCLM j k)
      (opNorm_concatProjLeftCLM_le_one j k) hr0 hr1 0 x
    have h2 := norm_iteratedFDeriv_bump_comp_clm_le k (concatProjRightCLM j k)
      (opNorm_concatProjRightCLM_le_one j k) hr0 hr1 0 x
    rw [norm_iteratedFDeriv_zero] at h1 h2
    have h_mul : ‖b₁ x * b₂ x‖ ≤
        SchwartzMap.seminorm ℝ 0 0 (vladimirov_cutoff_bump_schwartz j) *
          SchwartzMap.seminorm ℝ 0 0 (vladimirov_cutoff_bump_schwartz k) := by
      rw [norm_mul]
      exact mul_le_mul h1 h2 (norm_nonneg _) (apply_nonneg _ _)
    calc ‖b₁ x * b₂ x - 1‖
        ≤ ‖b₁ x * b₂ x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖b₁ x * b₂ x‖ + 1 := by simp
      _ ≤ (∑ q ∈ Finset.range 1,
            ((0 : ℕ).choose q : ℝ) *
              SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
              SchwartzMap.seminorm ℝ 0 (0 - q) (vladimirov_cutoff_bump_schwartz k)) + 1 := by
          simp only [Finset.range_one, Finset.sum_singleton, Nat.choose_self,
            Nat.cast_one, one_mul, Nat.sub_self]
          linarith
  | succ p =>
    have h_prod_smooth : ContDiff ℝ (p + 1 : ℕ) (fun y => b₁ y * b₂ y) :=
      (hb₁_smooth.mul hb₂_smooth).of_le (WithTop.coe_le_coe.mpr le_top)
    have h_const_smooth : ContDiff ℝ (p + 1 : ℕ)
        (fun _ : Fin (j + k) → Fin 4 → ℝ => (1 : ℂ)) := contDiff_const
    change ‖iteratedFDeriv ℝ (p + 1)
      ((fun y => b₁ y * b₂ y) - fun _ => (1 : ℂ)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply h_prod_smooth.contDiffAt h_const_smooth.contDiffAt,
        iteratedFDeriv_const_of_ne (Nat.succ_ne_zero p) (1 : ℂ), Pi.zero_apply, sub_zero]
    have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := b₁) (g := b₂)
      (n := p + 1) (N := (⊤ : ℕ∞)) hb₁_smooth hb₂_smooth x (WithTop.coe_le_coe.mpr le_top)
    have h_sum_le :
        (∑ q ∈ Finset.range (p + 1 + 1),
          ((p + 1).choose q : ℝ) * ‖iteratedFDeriv ℝ q b₁ x‖ *
            ‖iteratedFDeriv ℝ (p + 1 - q) b₂ x‖) ≤
        ∑ q ∈ Finset.range (p + 1 + 1),
          ((p + 1).choose q : ℝ) *
            SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
            SchwartzMap.seminorm ℝ 0 (p + 1 - q) (vladimirov_cutoff_bump_schwartz k) := by
      refine Finset.sum_le_sum (fun q _ => ?_)
      have hq1 := norm_iteratedFDeriv_bump_comp_clm_le j (concatProjLeftCLM j k)
        (opNorm_concatProjLeftCLM_le_one j k) hr0 hr1 q x
      have hq2 := norm_iteratedFDeriv_bump_comp_clm_le k (concatProjRightCLM j k)
        (opNorm_concatProjRightCLM_le_one j k) hr0 hr1 (p + 1 - q) x
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg _))
        hq2 (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
    linarith

theorem tendsto_wightmanConcatSchwartz_compactCutoff (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ x : Fin (j + k) → Fin 4 → ℝ,
      G x = (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun i => x (Fin.natAdd j i))) :
    Tendsto
      (fun m : ℕ =>
        wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m))
      Filter.atTop (𝓝 G) := by
  let H_seq : ℕ → SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ :=
    fun m => wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m)
  have h_sub : Tendsto (fun m => H_seq m - G) Filter.atTop (𝓝 0) := by
    rw [(schwartz_withSeminorms ℝ (Fin (j + k) → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0]
    rintro ⟨l, n_der⟩ ε hε
    let K_bump : ℕ → ℝ := fun i =>
      (∑ q ∈ Finset.range (i + 1),
        (i.choose q : ℝ) *
          SchwartzMap.seminorm ℝ 0 q (vladimirov_cutoff_bump_schwartz j) *
          SchwartzMap.seminorm ℝ 0 (i - q) (vladimirov_cutoff_bump_schwartz k)) + 1
    let C : ℝ := ∑ i ∈ Finset.range (n_der + 1),
      (n_der.choose i : ℝ) * K_bump i * SchwartzMap.seminorm ℝ (l + 1) (n_der - i) G
    have hK_nonneg : ∀ i, 0 ≤ K_bump i := fun i =>
      add_nonneg (Finset.sum_nonneg (fun q _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
          (apply_nonneg _ _))) zero_le_one
    have hC_nonneg : 0 ≤ C :=
      Finset.sum_nonneg (fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK_nonneg i)) (apply_nonneg _ _))
    have h_bound_m : ∀ m : ℕ,
        SchwartzMap.seminorm ℝ l n_der (H_seq m - G) ≤ C * (((m : ℝ) + 1)⁻¹) := by
      intro m
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      refine SchwartzMap.seminorm_le_bound ℝ l n_der (H_seq m - G)
        (mul_nonneg hC_nonneg (inv_nonneg.mpr hm_pos.le)) (fun x => ?_)
      let d : (Fin (j + k) → Fin 4 → ℝ) → ℂ := fun y =>
        vladimirov_cutoff_bump_schwartz j
          ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) *
        vladimirov_cutoff_bump_schwartz k
          ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) - 1
      have h_fn_eq :
          ((H_seq m - G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ) :
            (Fin (j + k) → Fin 4 → ℝ) → ℂ) =
          fun y => d y * G y := by
        ext y
        change wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m) y - G y =
          d y * G y
        rw [wightmanConcatSchwartz_apply, compactCutoff_val, compactCutoff_val,
            schwartzCutoffSeq_apply, schwartzCutoffSeq_apply, map_mul,
            starRingEnd_vladimirov_cutoff_bump_schwartz, hG y]
        dsimp [d, concatProjLeftCLM, concatProjRightCLM]
        ring
      by_cases hx : ‖x‖ < (m : ℝ) + 1
      · have h_ev :
            ((H_seq m - G : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ) :
              (Fin (j + k) → Fin 4 → ℝ) → ℂ) =ᶠ[𝓝 x]
              (fun _ => (0 : ℂ)) := by
          have hx_ball : x ∈ Metric.ball (0 : Fin (j + k) → Fin 4 → ℝ) ((m : ℝ) + 1) := by
            simpa [Metric.mem_ball, dist_zero_right] using hx
          filter_upwards [Metric.isOpen_ball.mem_nhds hx_ball] with y hy
          rw [Metric.mem_ball, dist_zero_right] at hy
          have hy_left :
              (((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y ∈
                Metric.ball (0 : Fin j → Fin 4 → ℝ) 1 := by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hm_pos), inv_mul_lt_iff₀ hm_pos, mul_one]
            exact (norm_concatProjLeftCLM_apply_le j k y).trans_lt hy
          have hy_right :
              (((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y ∈
                Metric.ball (0 : Fin k → Fin 4 → ℝ) 1 := by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hm_pos), inv_mul_lt_iff₀ hm_pos, mul_one]
            exact (norm_concatProjRightCLM_apply_le j k y).trans_lt hy
          have h_one₁ :
              vladimirov_cutoff_bump_schwartz j
                ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) = 1 := by
            change ((vladimirovCutoffBump j 1 Real.zero_lt_one
              ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y) : ℝ) : ℂ) = 1
            rw [vladimirov_cutoff_bump_one_of_mem_ball_gen j 1 le_rfl _ hy_left]
            simp
          have h_one₂ :
              vladimirov_cutoff_bump_schwartz k
                ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) = 1 := by
            change ((vladimirovCutoffBump k 1 Real.zero_lt_one
              ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y) : ℝ) : ℂ) = 1
            rw [vladimirov_cutoff_bump_one_of_mem_ball_gen k 1 le_rfl _ hy_right]
            simp
          have h_pt := congrFun h_fn_eq y
          dsimp [d] at h_pt
          rw [h_one₁, h_one₂, one_mul, sub_self, zero_mul] at h_pt
          exact h_pt
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_ev n_der).eq_of_nhds,
            iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
        exact mul_nonneg hC_nonneg (inv_nonneg.mpr hm_pos.le)
      · push Not at hx
        have hd_smooth : ContDiff ℝ (⊤ : ℕ∞) d := by
          have hb₁ : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
              vladimirov_cutoff_bump_schwartz j
                ((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k y)) :=
            ((vladimirov_cutoff_bump_schwartz j).smooth ⊤).comp
              (((((m : ℝ) + 1)⁻¹) • concatProjLeftCLM j k).contDiff)
          have hb₂ : ContDiff ℝ (⊤ : ℕ∞) (fun y =>
              vladimirov_cutoff_bump_schwartz k
                ((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k y)) :=
            ((vladimirov_cutoff_bump_schwartz k).smooth ⊤).comp
              (((((m : ℝ) + 1)⁻¹) • concatProjRightCLM j k).contDiff)
          exact (hb₁.mul hb₂).sub contDiff_const
        rw [h_fn_eq]
        have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
          (f := d) (g := (G : (Fin (j + k) → Fin 4 → ℝ) → ℂ))
          (n := n_der) (N := (⊤ : ℕ∞))
          hd_smooth (G.smooth ⊤) x (WithTop.coe_le_coe.mpr le_top)
        have h_norm_pow : ‖x‖ ^ l ≤ (((m : ℝ) + 1)⁻¹) * ‖x‖ ^ (l + 1) := by
          rw [le_inv_mul_iff₀ hm_pos]
          have h_mul : ((m : ℝ) + 1) * ‖x‖ ^ l ≤ ‖x‖ * ‖x‖ ^ l :=
            mul_le_mul_of_nonneg_right hx (pow_nonneg (norm_nonneg x) l)
          rwa [pow_succ']
        calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ n_der (fun y => d y * G y) x‖
            ≤ ((((m : ℝ) + 1)⁻¹) * ‖x‖ ^ (l + 1)) *
                ∑ i ∈ Finset.range (n_der + 1),
                  (n_der.choose i : ℝ) * ‖iteratedFDeriv ℝ i d x‖ *
                    ‖iteratedFDeriv ℝ (n_der - i)
                      (G : (Fin (j + k) → Fin 4 → ℝ) → ℂ) x‖ :=
              mul_le_mul h_norm_pow h_leib (norm_nonneg _)
                (mul_nonneg (inv_nonneg.mpr hm_pos.le) (pow_nonneg (norm_nonneg x) (l + 1)))
          _ = (((m : ℝ) + 1)⁻¹) *
                ∑ i ∈ Finset.range (n_der + 1),
                  (n_der.choose i : ℝ) * ‖iteratedFDeriv ℝ i d x‖ *
                    (‖x‖ ^ (l + 1) *
                      ‖iteratedFDeriv ℝ (n_der - i)
                        (G : (Fin (j + k) → Fin 4 → ℝ) → ℂ) x‖) := by
              rw [mul_assoc, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl (fun i _ => by ring)
          _ ≤ (((m : ℝ) + 1)⁻¹) * C := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_))
                (inv_nonneg.mpr hm_pos.le)
              have h_di := norm_iteratedFDeriv_concatBumpDiff_le j k m i x
              have h_Gi := SchwartzMap.le_seminorm ℝ (l + 1) (n_der - i) G x
              have h1 : (n_der.choose i : ℝ) * ‖iteratedFDeriv ℝ i d x‖ ≤
                  (n_der.choose i : ℝ) * K_bump i :=
                mul_le_mul_of_nonneg_left h_di (Nat.cast_nonneg _)
              exact mul_le_mul h1 h_Gi
                (mul_nonneg (pow_nonneg (norm_nonneg x) (l + 1)) (norm_nonneg _))
                (mul_nonneg (Nat.cast_nonneg _) (hK_nonneg i))
          _ = C * (((m : ℝ) + 1)⁻¹) := mul_comm _ _
    have h_lim : Tendsto (fun m : ℕ => C * (((m : ℝ) + 1)⁻¹)) Filter.atTop (𝓝 0) := by
      have h_inv : Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      simpa [mul_zero] using (tendsto_const_nhds (x := C)).mul h_inv
    filter_upwards [(tendsto_order.mp h_lim).2 ε hε] with m hm
    rw [SchwartzMap.schwartzSeminormFamily_apply, sub_zero]
    exact (h_bound_m m).trans_lt hm
  simpa using h_sub.add (tendsto_const_nhds (x := G))

theorem positivity_of_compactPositivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {W : WightmanFamily ι}
    (hcpos : CompactPositivity S W) :
    Positivity S W := by
  intro N F G hG
  let seq : ℕ → ℂ := fun m =>
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (compactCutoff j (F j α) m) (compactCutoff k (F k α') m))
  let limVal : ℂ :=
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')
  have h_tendsto : Tendsto seq Filter.atTop (𝓝 limVal) := by
    refine tendsto_finsetSum _ (fun j _ =>
      tendsto_finsetSum _ (fun k _ =>
        tendsto_finsetSum _ (fun α _ =>
          tendsto_finsetSum _ (fun α' _ =>
            tendsto_finsetSum _ (fun β _ => ?_)))))
    have h_cat := tendsto_wightmanConcatSchwartz_compactCutoff j k
      (F j α) (F k α') (G j k α α') (hG j k α α')
    have h_W := (W (j + k) (Fin.append (β ∘ Fin.rev) α')).continuous.tendsto
      (G j k α α') |>.comp h_cat
    exact tendsto_const_nhds.mul h_W
  have h_nonneg : ∀ m : ℕ, 0 ≤ seq m := fun m =>
    hcpos N (fun j α => compactCutoff j (F j α) m)
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · exact ge_of_tendsto (Complex.continuous_re.tendsto limVal |>.comp h_tendsto)
      (Filter.Eventually.of_forall (fun m => (Complex.nonneg_iff.mp (h_nonneg m)).1))
  · have h_im_seq : Complex.im ∘ seq = fun _ => (0 : ℝ) :=
      funext (fun m => ((Complex.nonneg_iff.mp (h_nonneg m)).2).symm)
    have h_im_lim := Complex.continuous_im.tendsto limVal |>.comp h_tendsto
    rw [h_im_seq] at h_im_lim
    exact tendsto_nhds_unique tendsto_const_nhds h_im_lim

theorem positivity_iff_compactPositivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    Positivity S W ↔ CompactPositivity S W :=
  ⟨compactPositivity_of_positivity, positivity_of_compactPositivity⟩

theorem positivity_iff_wightmanKernelPositive_and_hermiticity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    Positivity S W ↔
      (WightmanKernelPositive S W ∧ WightmanKernelHermiticity S W) :=
  (positivity_iff_compactPositivity S W).trans
    (compactPositivity_iff_wightmanKernelPositive_and_hermiticity S W)

theorem positivity_of_wightmanPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    Positivity S WData.W :=
  positivity_of_compactPositivity (compactPositivity_of_wightmanPositiveData WData)

omit [Fintype ι] [DecidableEq ι] in
theorem wightmanZeroPoint_eq_schwingerFromTube_mul_integral
    {W : WightmanFamily ι} (E : TubeExtension W)
    (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    W 0 Fin.elim0 f =
      schwingerFromTube E 0 Fin.elim0 (euclidOrderedBasePoint 0) *
        ∫ x : Fin 0 → Fin 4 → ℝ, f x := by
  have h_bd := E.boundary 0 Fin.elim0 f (euclidTimeVec 1) timeUnitVec_mem_forward_light_cone
  have h_const :
      (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
        E.H 0 Fin.elim0
          (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * (euclidTimeVec 1) k : ℝ) : ℂ)) * f x) =
      fun _ : ℝ =>
        schwingerFromTube E 0 Fin.elim0 (euclidOrderedBasePoint 0) *
          ∫ x : Fin 0 → Fin 4 → ℝ, f x := by
    ext t
    have h_arg : ∀ x : Fin 0 → Fin 4 → ℝ,
        (fun (i : Fin 0) (k : Fin 4) => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * (euclidTimeVec 1) k : ℝ) : ℂ)) =
        wickEmbedN 0 (euclidOrderedBasePoint 0) :=
      fun _ => Subsingleton.elim _ _
    simp_rw [h_arg]
    exact MeasureTheory.integral_const_mul _ _
  rw [h_const] at h_bd
  exact tendsto_nhds_unique h_bd tendsto_const_nhds

theorem wightmanKernel_vacuum_eq_schwingerFromTube
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (E : TubeExtension W) :
    wightmanKernel S W (wightmanVacuumConfig ι) (wightmanVacuumConfig ι) =
      schwingerFromTube E 0 Fin.elim0 (euclidOrderedBasePoint 0) := by
  dsimp only [wightmanVacuumConfig, wightmanBaseConfig]
  rw [wightmanKernel_mk, Finset.univ_unique, Finset.sum_singleton]
  have h_prod : (∏ i : Fin 0, S.C (Fin.elim0 i)
      ((default : Fin 0 → ι) i)) = 1 := Finset.prod_empty
  have h_idx : Fin.append ((default : Fin 0 → ι) ∘ Fin.rev) Fin.elim0 =
      Fin.elim0 := funext (fun i => Fin.elim0 i)
  have h_int_cat :
      (∫ x : Fin 0 → Fin 4 → ℝ,
        (wightmanConcatSchwartz 0 0
          (momentumWavepacketCompactSchwartz 0 0)
          (momentumWavepacketCompactSchwartz 0 0)) x) = 1 := by
    have hc := integral_wightmanConcatSchwartz 0 0
      (momentumWavepacketCompactSchwartz 0 0)
      (momentumWavepacketCompactSchwartz 0 0)
    change (∫ x : Fin 0 → Fin 4 → ℝ,
        (wightmanConcatSchwartz 0 0
          (momentumWavepacketCompactSchwartz 0 0)
          (momentumWavepacketCompactSchwartz 0 0)) x) = _ at hc
    have hm : (∫ y : Fin 0 → Fin 4 → ℝ,
        (momentumWavepacketCompactSchwartz 0 0 :
          SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) y) = 1 :=
      integral_momentumWavepacketSchwartz_zero 0
    rw [hc, hm, star_one, one_mul]
  change (∏ i : Fin 0, S.C (Fin.elim0 i) ((default : Fin 0 → ι) i)) *
      W 0 (Fin.append ((default : Fin 0 → ι) ∘ Fin.rev) Fin.elim0)
        (wightmanConcatSchwartz 0 0
          (momentumWavepacketCompactSchwartz 0 0)
          (momentumWavepacketCompactSchwartz 0 0)) = _
  rw [h_prod, one_mul, h_idx, wightmanZeroPoint_eq_schwingerFromTube_mul_integral E,
      h_int_cat, mul_one]

theorem wightmanVacuumNormalized_iff_osVacuumNormalized_of_schwinger_eq
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (E : TubeExtension W) (𝒮 : SchwingerFamily ι)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x) :
    WightmanVacuumNormalized S W ↔ OSVacuumNormalized 𝒮 := by
  unfold WightmanVacuumNormalized OSVacuumNormalized
  rw [wightmanKernel_vacuum_eq_schwingerFromTube S E,
      ← h_schw 0 Fin.elim0 (euclidOrderedBasePoint 0)
          (euclidOrderedBasePoint_mem_orderedEuclidN 0)]

def wightmanPositiveDataOfWavepacket
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S W A B) :
    WightmanPositiveData R S where
  W := W
  hermiticity A B := by
    rw [← h_ker B A, ← h_ker A B, Complex.star_def, inner_conj_symm]
  positivity Ψ := by
    let v : H := Ψ.sum (fun A c => c • Φ A)
    have h_inner : ⟪v, v⟫_ℂ = wightmanPreInner S W Ψ Ψ := by
      dsimp [v]
      unfold wightmanPreInner
      simp only [Finsupp.sum]
      rw [sum_inner (𝕜 := ℂ)]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      rw [inner_smul_left, inner_sum (𝕜 := ℂ), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun B _ => ?_)
      rw [inner_smul_right, h_ker A B, ← Complex.star_def]
      ring
    rw [← h_inner]
    exact inner_self_nonneg (𝕜 := ℂ)

theorem positivity_of_hilbertWavepacketConfig
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S W A B) :
    Positivity S W :=
  positivity_of_wightmanPositiveData (wightmanPositiveDataOfWavepacket S W Φ h_ker)

noncomputable def wavepacketWightmanPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] H :=
  (Finsupp.lsum ℂ (fun A => LinearMap.toSpanSingleton ℂ H (Φ A))).comp
    (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap

@[simp]
lemma wavepacketWightmanPreLM_wightmanBasisPre
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (A : WightmanConfig ι) :
    wavepacketWightmanPreLM WData Φ (wightmanBasisPre WData A) = Φ A := by
  dsimp [wavepacketWightmanPreLM, wightmanBasisPre, WightmanPreHilbertSpace.equivFinsupp]
  simp

theorem inner_wavepacketWightmanPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (Ψ₁ Ψ₂ : WightmanPreHilbertSpace WData) :
    ⟪wavepacketWightmanPreLM WData Φ Ψ₁, wavepacketWightmanPreLM WData Φ Ψ₂⟫_ℂ =
      ⟪Ψ₁, Ψ₂⟫_ℂ := by
  let L := wavepacketWightmanPreLM WData Φ
  have hL : ∀ X : WightmanPreHilbertSpace WData,
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • Φ A := by
    intro X
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => ?_)
    dsimp only
    rw [L.map_smul, wavepacketWightmanPreLM_wightmanBasisPre]
  have hX : ∀ X : WightmanPreHilbertSpace WData,
      X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • wightmanBasisPre WData A := by
    intro X
    conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData X]
    rfl
  rw [hL Ψ₁, hL Ψ₂]
  conv_rhs => rw [hX Ψ₁, hX Ψ₂]
  rw [sum_inner (𝕜 := ℂ), sum_inner (𝕜 := ℂ)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum (𝕜 := ℂ), inner_sum (𝕜 := ℂ)]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, h_ker A B, inner_wightmanBasisPre]

theorem norm_wavepacketWightmanPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (Ψ : WightmanPreHilbertSpace WData) :
    ‖wavepacketWightmanPreLM WData Φ Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketWightmanPreLM WData Φ h_ker Ψ Ψ]

noncomputable def wavepacketWightmanPreCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    WightmanPreHilbertSpace WData →L[ℂ] H :=
  (wavepacketWightmanPreLM WData Φ).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wavepacketWightmanPreLM WData Φ h_ker Ψ])

noncomputable def wavepacketWightmanCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    WightmanHilbert WData →L[ℂ] H :=
  (wavepacketWightmanPreCLM WData Φ h_ker).extend (toWightmanHilbert WData)

@[simp]
lemma wavepacketWightmanCLM_toWightmanHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (Ψ : WightmanPreHilbertSpace WData) :
    wavepacketWightmanCLM WData Φ h_ker (toWightmanHilbert WData Ψ) =
      wavepacketWightmanPreLM WData Φ Ψ :=
  (wavepacketWightmanPreCLM WData Φ h_ker).extend_eq
    UniformSpace.Completion.isDenseInducing_coe.dense
    (UniformSpace.Completion.isUniformInducing_coe _) Ψ

@[simp]
theorem wavepacketWightmanCLM_wightmanBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (A : WightmanConfig ι) :
    wavepacketWightmanCLM WData Φ h_ker (wightmanBasis WData A) = Φ A := by
  dsimp [wightmanBasis]
  rw [wavepacketWightmanCLM_toWightmanHilbert, wavepacketWightmanPreLM_wightmanBasisPre]

@[simp]
theorem wavepacketWightmanCLM_wightmanVacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    wavepacketWightmanCLM WData Φ h_ker (wightmanVacuum WData) =
      Φ (wightmanVacuumConfig ι) :=
  wavepacketWightmanCLM_wightmanBasis WData Φ h_ker (wightmanVacuumConfig ι)

theorem inner_wavepacketWightmanCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (x y : WightmanHilbert WData) :
    ⟪wavepacketWightmanCLM WData Φ h_ker x,
      wavepacketWightmanCLM WData Φ h_ker y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ₁ Ψ₂ =>
    change ⟪wavepacketWightmanCLM WData Φ h_ker (toWightmanHilbert WData Ψ₁),
        wavepacketWightmanCLM WData Φ h_ker (toWightmanHilbert WData Ψ₂)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ₁, toWightmanHilbert WData Ψ₂⟫_ℂ
    rw [wavepacketWightmanCLM_toWightmanHilbert,
        wavepacketWightmanCLM_toWightmanHilbert,
        inner_toWightmanHilbert,
        inner_wavepacketWightmanPreLM WData Φ h_ker Ψ₁ Ψ₂]

theorem norm_wavepacketWightmanCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (x : WightmanHilbert WData) :
    ‖wavepacketWightmanCLM WData Φ h_ker x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketWightmanCLM WData Φ h_ker x x]

noncomputable def wavepacketWightmanLinearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    WightmanHilbert WData →ₗᵢ[ℂ] H where
  toLinearMap := (wavepacketWightmanCLM WData Φ h_ker).toLinearMap
  norm_map' := norm_wavepacketWightmanCLM WData Φ h_ker

@[simp]
theorem wavepacketWightmanLinearIsometry_wightmanBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (A : WightmanConfig ι) :
    wavepacketWightmanLinearIsometry WData Φ h_ker (wightmanBasis WData A) = Φ A :=
  wavepacketWightmanCLM_wightmanBasis WData Φ h_ker A

@[simp]
theorem wavepacketWightmanLinearIsometry_wightmanVacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B) :
    wavepacketWightmanLinearIsometry WData Φ h_ker (wightmanVacuum WData) =
      Φ (wightmanVacuumConfig ι) :=
  wavepacketWightmanCLM_wightmanVacuum WData Φ h_ker

theorem wavepacketWightmanLinearIsometry_intertwines_translate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (U : (Fin 4 → ℝ) → (H →L[ℂ] H))
    (h_U : ∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι),
      Φ (wightmanConfigTranslate a A) = U a (Φ A))
    (a : Fin 4 → ℝ) (x : WightmanHilbert WData) :
    wavepacketWightmanLinearIsometry WData Φ h_ker
        (wightmanTranslate WData htrans a x) =
      U a (wavepacketWightmanLinearIsometry WData Φ h_ker x) := by
  let J := wavepacketWightmanCLM WData Φ h_ker
  change J (wightmanTranslate WData htrans a x) = U a (J x)
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    have h_exp : toWightmanHilbert WData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • wightmanBasis WData A := by
      conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toWightmanHilbert WData).map_smul _ _)
    change J (wightmanTranslate WData htrans a (toWightmanHilbert WData Ψ)) =
      U a (J (toWightmanHilbert WData Ψ))
    rw [h_exp, map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [map_smul, map_smul, map_smul, map_smul, wightmanTranslate_wightmanBasis]
    dsimp [J]
    rw [wavepacketWightmanCLM_wightmanBasis, wavepacketWightmanCLM_wightmanBasis, h_U]

theorem linearIsometry_surjective_of_denseRange
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι_W : E →ₗᵢ[ℂ] H) (hdense : DenseRange ι_W) :
    Function.Surjective ι_W := by
  intro y
  have h_closed : IsClosed (Set.range ι_W) :=
    ι_W.isometry.isUniformInducing.isComplete_range.isClosed
  have h_univ : Set.range ι_W = Set.univ := by
    rw [← h_closed.closure_eq]
    exact hdense.closure_eq
  have hy : y ∈ Set.range ι_W := by
    rw [h_univ]
    trivial
  exact hy

noncomputable def wavepacketWightmanLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (Φ : WightmanConfig ι → H)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S WData.W A B)
    (hdense : Dense (↑(Submodule.span ℂ (Set.range Φ)) : Set H)) :
    WightmanHilbert WData ≃ₗᵢ[ℂ] H := by
  let ι_W := wavepacketWightmanLinearIsometry WData Φ h_ker
  have h_sub : (Submodule.span ℂ (Set.range Φ) : Set H) ⊆ Set.range ι_W := by
    have h_le : Submodule.span ℂ (Set.range Φ) ≤ LinearMap.range ι_W.toLinearMap :=
      Submodule.span_le.mpr (by
        rintro _ ⟨A, rfl⟩
        exact ⟨wightmanBasis WData A,
          wavepacketWightmanLinearIsometry_wightmanBasis WData Φ h_ker A⟩)
    exact h_le
  have h_dr : DenseRange ι_W := Dense.mono h_sub hdense
  exact LinearIsometryEquiv.ofSurjective ι_W
    (linearIsometry_surjective_of_denseRange ι_W h_dr)

theorem wightmanVacuumNormalized_of_linearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (ι_W : WightmanHilbert WData →ₗᵢ[ℂ] H)
    {Ω : H} (hvac : ι_W (wightmanVacuum WData) = Ω)
    (hnorm : ⟪Ω, Ω⟫_ℂ = 1) :
    WightmanVacuumNormalized S WData.W := by
  unfold WightmanVacuumNormalized
  rw [← inner_wightmanVacuum_self WData, ← ι_W.inner_map_map, hvac, hnorm]

theorem wightmanClusterAlong_of_linearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (ι_W : WightmanHilbert WData →ₗᵢ[ℂ] H)
    {Ω : H} (hvac : ι_W (wightmanVacuum WData) = Ω)
    (U : (Fin 4 → ℝ) → (H →L[ℂ] H))
    (h_inter : ∀ (a : Fin 4 → ℝ) (x : WightmanHilbert WData),
      ι_W (wightmanTranslate WData htrans a x) = U a (ι_W x))
    {a : Fin 4 → ℝ}
    (h_cluster : ∀ x y : H,
      Tendsto (fun t : ℝ => ⟪x, U (t • a) y⟫_ℂ) Filter.atTop
        (𝓝 (⟪x, Ω⟫_ℂ * ⟪Ω, y⟫_ℂ))) :
    WightmanClusterAlong WData a := by
  intro A B
  have h_eq : (fun t : ℝ =>
      wightmanKernel S WData.W A (wightmanConfigTranslate (t • a) B)) =
      fun t : ℝ => ⟪ι_W (wightmanBasis WData A), U (t • a) (ι_W (wightmanBasis WData B))⟫_ℂ := by
    ext t
    rw [← inner_wightmanBasis WData A (wightmanConfigTranslate (t • a) B),
        ← wightmanTranslate_wightmanBasis WData htrans (t • a) B,
        ← ι_W.inner_map_map, h_inter]
  have h_lim_eq :
      wightmanKernel S WData.W A (wightmanVacuumConfig ι) *
        wightmanKernel S WData.W (wightmanVacuumConfig ι) B =
      ⟪ι_W (wightmanBasis WData A), Ω⟫_ℂ * ⟪Ω, ι_W (wightmanBasis WData B)⟫_ℂ := by
    rw [← inner_wightmanBasis_wightmanVacuum WData A,
        ← inner_wightmanVacuum_wightmanBasis WData B,
        ← hvac, ι_W.inner_map_map, ι_W.inner_map_map]
  rw [h_eq, h_lim_eq]
  exact h_cluster (ι_W (wightmanBasis WData A)) (ι_W (wightmanBasis WData B))

theorem wightmanVacuumUnique_of_linearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (ι_W : WightmanHilbert WData →ₗᵢ[ℂ] H)
    {Ω : H} (hvac : ι_W (wightmanVacuum WData) = Ω)
    (U : (Fin 4 → ℝ) → (H →L[ℂ] H))
    (h_inter : ∀ (a : Fin 4 → ℝ) (x : WightmanHilbert WData),
      ι_W (wightmanTranslate WData htrans a x) = U a (ι_W x))
    (h_uniq : ∀ v : H, (∀ a : Fin 4 → ℝ, U a v = v) → v = ⟪Ω, v⟫_ℂ • Ω) :
    WightmanVacuumUnique WData htrans := by
  intro Ψ hfixed
  apply ι_W.injective
  have hU_fixed : ∀ a : Fin 4 → ℝ, U a (ι_W Ψ) = ι_W Ψ := fun a => by
    rw [← h_inter a Ψ, hfixed a]
  have h_eq := h_uniq (ι_W Ψ) hU_fixed
  rw [← hvac, ι_W.inner_map_map, ← ι_W.map_smul] at h_eq
  exact h_eq

theorem eq_zero_on_rightHalfPlane_of_imag_zero {g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hg_cont : ContinuousOn g rightHalfPlane)
    (hg_imag : ∀ t : ℝ, g (Complex.I * (t : ℂ)) = 0) :
    ∀ z ∈ rightHalfPlane, g z = 0 := by
  let f : ℂ → ℂ := fun w => if 0 ≤ w.im then g (-Complex.I * w) else 0
  have h_slit : Analysis.slitDomain (Set.univ : Set ℝ) = Set.univ := by
    ext w
    simp [Analysis.slitDomain]
  have h_rot_mem : ∀ {w : ℂ}, 0 ≤ w.im → -Complex.I * w ∈ rightHalfPlane := by
    intro w hw
    change 0 ≤ (-Complex.I * w).re
    simpa [Complex.mul_re] using hw
  have h_rot_real : ∀ w : ℂ, w.im = 0 → g (-Complex.I * w) = 0 := by
    intro w hw
    have hw_eq : -Complex.I * w = Complex.I * ((-w.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hw]
    rw [hw_eq]
    exact hg_imag (-w.re)
  have hf_cont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro w₀
    by_cases hpos : 0 < w₀.im
    · have h_ev : f =ᶠ[𝓝 w₀] fun w => g (-Complex.I * w) := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos]
          with w hw
        exact if_pos (le_of_lt hw)
      have h_re_pos : (0 : ℝ) < (-Complex.I * w₀).re := by
        simp [Complex.mul_re, hpos]
      have h_nhds : rightHalfPlane ∈ 𝓝 (-Complex.I * w₀) :=
        Filter.mem_of_superset
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h_re_pos)
          (fun z (hz : 0 < z.re) => (le_of_lt hz : z ∈ rightHalfPlane))
      have hg_at : ContinuousAt g (-Complex.I * w₀) :=
        hg_cont.continuousAt h_nhds
      exact (hg_at.comp (continuous_const.mul continuous_id).continuousAt).congr h_ev.symm
    · by_cases hneg : w₀.im < 0
      · have h_ev : f =ᶠ[𝓝 w₀] fun _ => (0 : ℂ) := by
          filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg]
            with w hw
          exact if_neg (not_le_of_gt hw)
        exact continuousAt_const.congr h_ev.symm
      · have hw0 : w₀.im = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
        have hfw0 : f w₀ = 0 := by
          dsimp [f]
          rw [if_pos (le_of_eq hw0.symm)]
          exact h_rot_real w₀ hw0
        rw [Metric.continuousAt_iff]
        intro ε hε
        have hg_within : ContinuousWithinAt (fun w : ℂ => g (-Complex.I * w))
            {w : ℂ | 0 ≤ w.im} w₀ :=
          (hg_cont.comp (continuous_const.mul continuous_id).continuousOn
            (fun _ hw => h_rot_mem hw)).continuousWithinAt (le_of_eq hw0.symm)
        rw [Metric.continuousWithinAt_iff] at hg_within
        rcases hg_within ε hε with ⟨δ, hδ_pos, hδ⟩
        refine ⟨δ, hδ_pos, fun w hw_dist => ?_⟩
        rw [hfw0]
        dsimp [f]
        split_ifs with hw_im
        · have h_step := hδ hw_im hw_dist
          rwa [h_rot_real w₀ hw0] at h_step
        · simpa using hε
  have hf_ana_pos : AnalyticOn ℂ f Analysis.upperHalfPlane := by
    have h_open_uhp : IsOpen Analysis.upperHalfPlane :=
      isOpen_lt continuous_const Complex.continuous_im
    refine DifferentiableOn.analyticOn ?_ h_open_uhp
    have h_diff_comp : DifferentiableOn ℂ (fun w : ℂ => g (-Complex.I * w))
        Analysis.upperHalfPlane :=
      hg_holo.comp (differentiable_const (-Complex.I) |>.mul differentiable_id).differentiableOn
        (fun w hw => by
          have hw' : 0 < w.im := hw
          change 0 < (-Complex.I * w).re
          simpa [Complex.mul_re] using hw')
    exact h_diff_comp.congr (fun w hw => if_pos (le_of_lt hw))
  have hf_ana_neg : AnalyticOn ℂ f Analysis.lowerHalfPlane := by
    have h_open_lhp : IsOpen Analysis.lowerHalfPlane :=
      isOpen_lt Complex.continuous_im continuous_const
    refine DifferentiableOn.analyticOn ?_ h_open_lhp
    exact (differentiableOn_const (0 : ℂ)).congr
      (fun w hw => if_neg (not_le_of_gt hw))
  have hf_ana_univ : AnalyticOnNhd ℂ f Set.univ := by
    have h_on : AnalyticOn ℂ f (Analysis.slitDomain (Set.univ : Set ℝ)) :=
      Analysis.eow_1d_continuous Set.univ isOpen_univ f
        hf_cont.continuousOn hf_ana_pos hf_ana_neg
    rw [h_slit] at h_on
    exact isOpen_univ.analyticOn_iff_analyticOnNhd.mp h_on
  have hf_ev_zero : f =ᶠ[𝓝 (-Complex.I)] 0 := by
    have h_mem : Analysis.lowerHalfPlane ∈ 𝓝 (-Complex.I) :=
      (isOpen_lt Complex.continuous_im continuous_const).mem_nhds (by simp)
    filter_upwards [h_mem] with w hw
    exact if_neg (not_le_of_gt hw)
  have hf_all_zero : Set.EqOn f 0 Set.univ :=
    hf_ana_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ (-Complex.I)) hf_ev_zero
  intro z hz
  have hz' : 0 ≤ z.re := hz
  have hz_im : 0 ≤ (Complex.I * z).im := by
    simpa [Complex.mul_im] using hz'
  have h_eval : f (Complex.I * z) = 0 := hf_all_zero (Set.mem_univ (Complex.I * z))
  dsimp [f] at h_eval
  rw [if_pos hz_im] at h_eval
  have h_mul : -Complex.I * (Complex.I * z) = z := by
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  rwa [h_mul] at h_eval

def OSHolomorphicSemigroup.IsWeaklyHolomorphic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) : Prop :=
  ∀ χ Ψ : OSHilbert D, ∃ F : ℂ → ℂ,
    (∀ (z : ℂ) (hz : z ∈ rightHalfPlane), F z = ⟪χ, ℰ.Z z hz Ψ⟫_ℂ) ∧
    ContinuousOn F rightHalfPlane ∧
    DifferentiableOn ℂ F {z : ℂ | 0 < z.re}

theorem OSSpectralDecomposition.isWeaklyHolomorphic_toOSHolomorphicSemigroup
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D} {m : ℕ}
    (spec : OSSpectralDecomposition D hcontr m) :
    spec.toOSHolomorphicSemigroup.IsWeaklyHolomorphic := by
  intro χ Ψ
  refine ⟨fun z => ∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ,
    fun z _ => ?_, ?_, ?_⟩
  · change (∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) =
      ⟪χ, spec.entireZ z Ψ⟫_ℂ
    rw [spec.entireZ_apply, inner_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [inner_smul_right]
  · have h_diff : Differentiable ℂ
        (fun z : ℂ => ∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) := by
      have h_term : ∀ k : Fin m,
          Differentiable ℂ (fun z : ℂ => laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) :=
        fun k => (differentiable_laplaceExp (spec.E k)).mul (differentiable_const _)
      fun_prop
    exact h_diff.continuous.continuousOn
  · have h_diff : Differentiable ℂ
        (fun z : ℂ => ∑ k : Fin m, laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) := by
      have h_term : ∀ k : Fin m,
          Differentiable ℂ (fun z : ℂ => laplaceExp (spec.E k) z * ⟪χ, spec.P k Ψ⟫_ℂ) :=
        fun k => (differentiable_laplaceExp (spec.E k)).mul (differentiable_const _)
      fun_prop
    exact h_diff.differentiableOn

theorem isWeaklyHolomorphic_canonicalOSHolomorphicSemigroup
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hcontr : OSContractionCondition D)
    (hsmooth : ∀ (n : ℕ) (α : Fin n → ι), ContDiffOn ℝ (⊤ : ℕ∞) (D.𝒮 n α) (orderedEuclidN n)) :
    (canonicalOSHolomorphicSemigroup D htrans hcontr hsmooth).IsWeaklyHolomorphic := by
  intro χ Ψ
  let Z_tot := canonicalOSHolomorphicSemigroupTotal D htrans hcontr hsmooth
  refine ⟨fun z => ⟪χ, Z_tot z Ψ⟫_ℂ, fun z hz => ?_, ?_, ?_⟩
  · dsimp [Z_tot]
    rw [canonicalOSHolomorphicSemigroupTotal_eq D htrans hcontr hsmooth hz]
  · exact (innerSL ℂ χ).continuous.comp_continuousOn
      (continuousOn_canonicalOSHolomorphicSemigroupTotal_apply D htrans hcontr hsmooth Ψ)
  · let L : (OSHilbert D →L[ℂ] OSHilbert D) →L[ℂ] ℂ :=
      (innerSL ℂ χ).comp (ContinuousLinearMap.apply ℂ (OSHilbert D) Ψ)
    exact L.differentiable.comp_differentiableOn
      (differentiableOn_canonicalOSHolomorphicSemigroupTotal D htrans hcontr hsmooth)

theorem OSAxioms.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_contraction
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcontr : OSContractionCondition hOS.toReflectionPositiveData) :
    (hOS.canonicalHolomorphicSemigroup_of_contraction hcontr).IsWeaklyHolomorphic :=
  isWeaklyHolomorphic_canonicalOSHolomorphicSemigroup hOS.toReflectionPositiveData
    hOS.os1_translation hcontr hOS.os0_smooth

theorem OSAxioms.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    (hOS.canonicalHolomorphicSemigroup_of_timeCluster hcluster).IsWeaklyHolomorphic :=
  hOS.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_contraction _

theorem OSAxioms.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_diagonalBounded
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hdiag : OSDiagonalKernelBounded S 𝒮) :
    (hOS.canonicalHolomorphicSemigroup_of_diagonalBounded hdiag).IsWeaklyHolomorphic :=
  hOS.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_contraction _

lemma mul_exp_neg_mul_le_inv_of_nonneg {E r u : ℝ}
    (hE : 0 ≤ E) (hr : 0 < r) (hru : r ≤ u) :
    E * Real.exp (-(E * u)) ≤ r⁻¹ := by
  have h1 : E * r ≤ Real.exp (E * r) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (E * r))
  have h2 : Real.exp (-(E * u)) ≤ Real.exp (-(E * r)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hru hE))
  have h3 : E * Real.exp (-(E * r)) ≤ r⁻¹ := by
    calc E * Real.exp (-(E * r))
        = r⁻¹ * ((E * r) * Real.exp (-(E * r))) := by
          field_simp [hr.ne']
      _ ≤ r⁻¹ * (Real.exp (E * r) * Real.exp (-(E * r))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
            (inv_nonneg.mpr hr.le)
      _ = r⁻¹ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  exact (mul_le_mul_of_nonneg_left h2 hE).trans h3

theorem OSSpectralMeasure.isWeaklyHolomorphic_toOSHolomorphicSemigroupOfBochner
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    {A : Type*} [MeasurableSpace A]
    (M : OSSpectralMeasure D hcontr A)
    (hE_meas : Measurable M.E)
    (Z : ℂ → (OSHilbert D →L[ℂ] OSHilbert D))
    (h_eq : ∀ (z : ℂ), z ∈ rightHalfPlane → ∀ x : OSHilbert D, Z z x = M.bochnerZ z x)
    (h_int : ∀ (z : ℂ), z ∈ rightHalfPlane → ∀ x : OSHilbert D,
      Integrable (fun a : A => laplaceExp (M.E a) z • M.P a x) M.μ)
    (h_add : ∀ (z₁ z₂ : ℂ), z₁ ∈ rightHalfPlane → z₂ ∈ rightHalfPlane →
      Z (z₁ + z₂) = (Z z₁).comp (Z z₂))
    (h_vac : ∀ (z : ℂ), z ∈ rightHalfPlane → M.bochnerZ z (osVacuum D) = osVacuum D)
    (h_contr : ∀ (z : ℂ), z ∈ rightHalfPlane → ∀ x : OSHilbert D,
      ‖M.bochnerZ z x‖ ≤ ‖x‖) :
    (M.toOSHolomorphicSemigroupOfBochner Z h_eq h_int h_add h_vac h_contr).IsWeaklyHolomorphic := by
  intro χ Ψ
  let g : A → ℂ := fun a => ⟪χ, M.P a Ψ⟫_ℂ
  have hg_int : Integrable g M.μ := by
    have h0 := (OSSpectralMeasure.innerRightCLM (D := D) χ).integrable_comp
      (h_int 0 zero_mem_rightHalfPlane Ψ)
    simpa [g, laplaceExp_zero_right] using h0
  have h_meas_F : ∀ z : ℂ,
      AEStronglyMeasurable (fun a : A => laplaceExp (M.E a) z * g a) M.μ := by
    intro z
    have h_lap_meas : Measurable (fun a : A => laplaceExp (M.E a) z) := by
      unfold laplaceExp
      exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp hE_meas
    exact h_lap_meas.aestronglyMeasurable.mul hg_int.aestronglyMeasurable
  let F : ℂ → ℂ := fun z => ∫ a : A, laplaceExp (M.E a) z * g a ∂M.μ
  refine ⟨F, fun z hz => ?_, ?_, ?_⟩
  · change F z = ⟪χ, Z z Ψ⟫_ℂ
    rw [h_eq z hz Ψ, M.inner_bochnerZ_right z Ψ χ (h_int z hz Ψ)]
  · refine MeasureTheory.continuousOn_of_dominated
      (fun z _ => h_meas_F z)
      (fun z hz => Filter.Eventually.of_forall
        (fun a => M.norm_laplaceExp_mul_inner_proj_le_half_add_norm_sq hz a χ Ψ))
      (M.integrable_half_add_norm_sq χ Ψ)
      (Filter.Eventually.of_forall (fun a =>
        ((differentiable_laplaceExp (M.E a)).continuous.mul continuous_const).continuousOn))
  · intro z₀ hz₀
    have hz₀_pos : 0 < z₀.re := hz₀
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀_pos
    let s : Set ℂ := Metric.ball z₀ r
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr_pos
    have hs_re : ∀ z ∈ s, r ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h_abs : |z.re - z₀.re| < r :=
        (Complex.abs_re_le_norm (z - z₀)).trans_lt hz
      have h_low := (abs_lt.mp h_abs).1
      dsimp [r] at h_low ⊢
      linarith
    let F' : ℂ → A → ℂ := fun z a => (-(M.E a : ℂ) * laplaceExp (M.E a) z) * g a
    have hF'_meas : AEStronglyMeasurable (F' z₀) M.μ := by
      have hE_c : Measurable (fun a : A => -(M.E a : ℂ)) :=
        (continuous_neg.comp Complex.continuous_ofReal).measurable.comp hE_meas
      have h_eq' : F' z₀ = fun a => (-(M.E a : ℂ)) * (laplaceExp (M.E a) z₀ * g a) := by
        ext a
        dsimp [F']
        ring
      rw [h_eq']
      exact hE_c.aestronglyMeasurable.mul (h_meas_F z₀)
    let bound : A → ℝ := fun a => r⁻¹ * ((‖M.P a χ‖ ^ 2 + ‖M.P a Ψ‖ ^ 2) / 2)
    have h_bound_int : Integrable bound M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).const_mul r⁻¹
    have h_bound : ∀ᵐ a : A ∂M.μ, ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
      refine Filter.Eventually.of_forall (fun a z hz => ?_)
      have h_lap_norm : ‖-(M.E a : ℂ) * laplaceExp (M.E a) z‖ ≤ r⁻¹ := by
        have h_exp_arg : -z.re * M.E a = -(M.E a * z.re) := by ring
        rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (M.energy_nonneg a), norm_laplaceExp, h_exp_arg]
        exact mul_exp_neg_mul_le_inv_of_nonneg (M.energy_nonneg a) hr_pos (hs_re z hz)
      have h_g := M.norm_inner_proj_le_half_add_norm_sq a χ Ψ
      dsimp [F', bound]
      rw [norm_mul]
      exact mul_le_mul h_lap_norm h_g (norm_nonneg _) (inv_nonneg.mpr hr_pos.le)
    have h_diff : ∀ᵐ a : A ∂M.μ, ∀ z ∈ s,
        HasDerivAt (fun w => laplaceExp (M.E a) w * g a) (F' z a) z := by
      refine Filter.Eventually.of_forall (fun a z _ => ?_)
      have h_lin : HasDerivAt (fun w : ℂ => -w * (M.E a : ℂ))
          (-1 * (M.E a : ℂ)) z :=
        (hasDerivAt_id z).neg.mul_const (M.E a : ℂ)
      have h_exp : HasDerivAt (laplaceExp (M.E a))
          (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) z :=
        h_lin.cexp
      have h_mul := h_exp.mul_const (g a)
      have h_eq_d : (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) * g a = F' z a := by
        dsimp [F']
        ring
      rwa [h_eq_d] at h_mul
    have hz₀_rhp : z₀ ∈ rightHalfPlane := le_of_lt hz₀_pos
    have hF_z₀_int : Integrable (fun a : A => laplaceExp (M.E a) z₀ * g a) M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).mono' (h_meas_F z₀)
        (Filter.Eventually.of_forall
          (fun a => M.norm_laplaceExp_mul_inner_proj_le_half_add_norm_sq hz₀_rhp a χ Ψ))
    have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds (Filter.Eventually.of_forall h_meas_F) hF_z₀_int hF'_meas
      h_bound h_bound_int h_diff).2
    exact h_deriv.differentiableAt.differentiableWithinAt

theorem OSContinuousSpectralData.isWeaklyHolomorphic
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    {Ω : Type*} [MeasurableSpace Ω]
    (M : OSContinuousSpectralData D hcontr Ω) :
    M.ℰ.IsWeaklyHolomorphic := by
  intro χ Ψ
  let g : Ω → ℂ := fun a => star (M.wave χ a) * M.wave Ψ a
  have hg_int : Integrable g M.μ := M.integrable_star_wave_mul χ Ψ
  have h_meas_F : ∀ z : ℂ,
      AEStronglyMeasurable (fun a : Ω => laplaceExp (M.E a) z * g a) M.μ := by
    intro z
    have h_lap_meas : Measurable (fun a : Ω => laplaceExp (M.E a) z) := by
      unfold laplaceExp
      exact (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable.comp M.measurable_E
    exact h_lap_meas.aestronglyMeasurable.mul hg_int.aestronglyMeasurable
  let F : ℂ → ℂ := fun z => ∫ a : Ω, laplaceExp (M.E a) z * g a ∂M.μ
  refine ⟨F, fun z hz => (M.semigroup_inner_eq z hz χ Ψ).symm, ?_, ?_⟩
  · refine MeasureTheory.continuousOn_of_dominated
      (fun z _ => h_meas_F z)
      (fun z hz => Filter.Eventually.of_forall
        (fun a => M.norm_laplaceExp_mul_wave_le_half_add_norm_sq hz a χ Ψ))
      (M.integrable_half_add_norm_sq χ Ψ)
      (Filter.Eventually.of_forall (fun a =>
        ((differentiable_laplaceExp (M.E a)).continuous.mul continuous_const).continuousOn))
  · intro z₀ hz₀
    have hz₀_pos : 0 < z₀.re := hz₀
    let r : ℝ := z₀.re / 2
    have hr_pos : 0 < r := half_pos hz₀_pos
    let s : Set ℂ := Metric.ball z₀ r
    have hs_nhds : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr_pos
    have hs_re : ∀ z ∈ s, r ≤ z.re := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h_abs : |z.re - z₀.re| < r :=
        (Complex.abs_re_le_norm (z - z₀)).trans_lt hz
      have h_low := (abs_lt.mp h_abs).1
      dsimp [r] at h_low ⊢
      linarith
    let F' : ℂ → Ω → ℂ := fun z a => (-(M.E a : ℂ) * laplaceExp (M.E a) z) * g a
    have hF'_meas : AEStronglyMeasurable (F' z₀) M.μ := by
      have hE_c : Measurable (fun a : Ω => -(M.E a : ℂ)) :=
        (continuous_neg.comp Complex.continuous_ofReal).measurable.comp M.measurable_E
      have h_eq' : F' z₀ = fun a => (-(M.E a : ℂ)) * (laplaceExp (M.E a) z₀ * g a) := by
        ext a
        dsimp [F']
        ring
      rw [h_eq']
      exact hE_c.aestronglyMeasurable.mul (h_meas_F z₀)
    let bound : Ω → ℝ := fun a => r⁻¹ * ((‖M.wave χ a‖ ^ 2 + ‖M.wave Ψ a‖ ^ 2) / 2)
    have h_bound_int : Integrable bound M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).const_mul r⁻¹
    have h_bound : ∀ᵐ a : Ω ∂M.μ, ∀ z ∈ s, ‖F' z a‖ ≤ bound a := by
      refine Filter.Eventually.of_forall (fun a z hz => ?_)
      have h_lap_norm : ‖-(M.E a : ℂ) * laplaceExp (M.E a) z‖ ≤ r⁻¹ := by
        have h_exp_arg : -z.re * M.E a = -(M.E a * z.re) := by ring
        rw [norm_mul, norm_neg, Complex.norm_real,
            Real.norm_of_nonneg (M.energy_nonneg a), norm_laplaceExp, h_exp_arg]
        exact mul_exp_neg_mul_le_inv_of_nonneg (M.energy_nonneg a) hr_pos (hs_re z hz)
      have h_g := M.norm_star_wave_mul_le_half_add_norm_sq a χ Ψ
      dsimp [F', bound]
      rw [norm_mul]
      exact mul_le_mul h_lap_norm h_g (norm_nonneg _) (inv_nonneg.mpr hr_pos.le)
    have h_diff : ∀ᵐ a : Ω ∂M.μ, ∀ z ∈ s,
        HasDerivAt (fun w => laplaceExp (M.E a) w * g a) (F' z a) z := by
      refine Filter.Eventually.of_forall (fun a z _ => ?_)
      have h_lin : HasDerivAt (fun w : ℂ => -w * (M.E a : ℂ))
          (-1 * (M.E a : ℂ)) z :=
        (hasDerivAt_id z).neg.mul_const (M.E a : ℂ)
      have h_exp : HasDerivAt (laplaceExp (M.E a))
          (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) z :=
        h_lin.cexp
      have h_mul := h_exp.mul_const (g a)
      have h_eq_d : (laplaceExp (M.E a) z * (-1 * (M.E a : ℂ))) * g a = F' z a := by
        dsimp [F']
        ring
      rwa [h_eq_d] at h_mul
    have hz₀_rhp : z₀ ∈ rightHalfPlane := le_of_lt hz₀_pos
    have hF_z₀_int : Integrable (fun a : Ω => laplaceExp (M.E a) z₀ * g a) M.μ :=
      (M.integrable_half_add_norm_sq χ Ψ).mono' (h_meas_F z₀)
        (Filter.Eventually.of_forall
          (fun a => M.norm_laplaceExp_mul_wave_le_half_add_norm_sq hz₀_rhp a χ Ψ))
    have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hs_nhds (Filter.Eventually.of_forall h_meas_F) hF_z₀_int hF'_meas
      h_bound h_bound_int h_diff).2
    exact h_deriv.differentiableAt.differentiableWithinAt

theorem osContractionSemigroup_fixed_of_realTimeUnitary_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr)
    (h_holo : ℰ.IsWeaklyHolomorphic)
    {Ψ : OSHilbert D}
    (hfixed : ∀ t : ℝ, ℰ.realTimeUnitary t Ψ = Ψ)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ Ψ = Ψ := by
  apply ext_inner_left ℂ
  intro χ
  rcases h_holo χ Ψ with ⟨F, hF_eq, hF_cont, hF_diff⟩
  let g : ℂ → ℂ := fun z => F z - ⟪χ, Ψ⟫_ℂ
  have hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} :=
    hF_diff.sub (differentiableOn_const _)
  have hg_cont : ContinuousOn g rightHalfPlane :=
    hF_cont.sub continuousOn_const
  have hg_imag : ∀ t : ℝ, g (Complex.I * (t : ℂ)) = 0 := by
    intro t
    dsimp [g]
    rw [hF_eq (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t)]
    change ⟪χ, ℰ.realTimeUnitary t Ψ⟫_ℂ - ⟪χ, Ψ⟫_ℂ = 0
    rw [hfixed t, sub_self]
  have hτ_zero := eq_zero_on_rightHalfPlane_of_imag_zero hg_holo hg_cont hg_imag
    (τ : ℂ) (ofReal_mem_rightHalfPlane hτ)
  dsimp [g] at hτ_zero
  rw [hF_eq (τ : ℂ) (ofReal_mem_rightHalfPlane hτ), ℰ.real_eq τ hτ] at hτ_zero
  exact sub_eq_zero.mp hτ_zero

theorem eq_smul_osVacuum_of_spacetimeTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr)
    (h_holo : ℰ.IsWeaklyHolomorphic)
    (htrans : OSTranslationInvariant D.𝒮)
    (hcluster : OSTimeClusterDecomposition D)
    {Ψ : OSHilbert D}
    (hfixed : ∀ a : Fin 4 → ℝ, ℰ.spacetimeTranslate htrans a Ψ = Ψ) :
    Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D := by
  have h_rt : ∀ t : ℝ, ℰ.realTimeUnitary t Ψ = Ψ := by
    intro t
    have h_a := hfixed (euclidTimeVec t)
    unfold OSHolomorphicSemigroup.spacetimeTranslate at h_a
    have h_sp : spatialPart (euclidTimeVec t) = 0 := by
      ext i
      simp [spatialPart, euclidTimeVec]
    have h_t0 : euclidTimeVec t 0 = t := rfl
    rw [h_sp, h_t0, ContinuousLinearMap.comp_apply, osSpatialTranslate_zero,
        ContinuousLinearMap.id_apply] at h_a
    exact h_a
  exact eq_smul_osVacuum_of_osContractionSemigroup_fixed D hcontr hcluster
    (osContractionSemigroup_fixed_of_realTimeUnitary_fixed ℰ h_holo h_rt)

structure GeneralWightmanAxiomsWithUniqueVacuum
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) extends
    WightmanAxioms R S η where
  vacuumNormalized : WightmanVacuumNormalized S WData.W
  vacuumUnique :
    WightmanVacuumUnique WData
      (wightmanTranslationInvariant_of_poincare R poincare)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def euclidLaplace {n : ℕ} (x : Fin n → Fin 4 → ℝ)
    (q : Fin n → Fin 4 → ℝ) : ℂ :=
  Complex.exp (∑ i : Fin n,
    ((q i 0 : ℂ) * (x i 0 : ℂ) +
      Complex.I * ((q i 1 : ℂ) * (x i 1 : ℂ) +
        (q i 2 : ℂ) * (x i 2 : ℂ) + (q i 3 : ℂ) * (x i 3 : ℂ))))

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_euclidLaplace {n : ℕ} (x : Fin n → Fin 4 → ℝ) :
    Continuous (euclidLaplace x) := by
  unfold euclidLaplace
  refine Complex.continuous_exp.comp (continuous_finsetSum Finset.univ (fun i _ => ?_))
  have hc : ∀ μ : Fin 4, Continuous (fun q : Fin n → Fin 4 → ℝ => (q i μ : ℂ)) :=
    fun μ => Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply i))
  exact ((hc 0).mul continuous_const).add
    (continuous_const.mul
      ((((hc 1).mul continuous_const).add ((hc 2).mul continuous_const)).add
        ((hc 3).mul continuous_const)))

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_wickEmbedN_eq_euclidLaplace (n : ℕ)
    (y : Fin n → Fin 4 → ℝ) (q : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (wickEmbedN n y) q = euclidLaplace y q := by
  unfold vladimirov_kernel euclidLaplace
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  change -Complex.I * minkowskiInnerC (fun μ => (q t μ : ℂ)) (wickEmbed (y t)) = _
  simp only [minkowskiInnerC, wickEmbed, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  ring_nf
  simp only [Complex.I_sq]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_osConcatPoint_eq (j k : ℕ)
    (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ) (p : Fin (j + k) → Fin 4 → ℝ) :
    vladimirov_kernel (j + k) (wickEmbedN (j + k) (osConcatPoint j k x y)) p =
      star (euclidLaplace x (fun i => -p (Fin.castAdd k (Fin.rev i)))) *
        euclidLaplace y (fun t => p (Fin.natAdd j t)) := by
  unfold vladimirov_kernel euclidLaplace
  rw [Fin.sum_univ_add, ← Equiv.sum_comp Fin.revPerm, mul_add,
    Complex.exp_add, Complex.star_def, ← Complex.exp_conj]
  congr 1
  · congr 1
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_pt : wickEmbedN (j + k) (osConcatPoint j k x y)
        (Fin.castAdd k (Fin.revPerm i)) =
        wickEmbed (euclidTimeReflect (x i)) := by
      change wickEmbed (osConcatPoint j k x y (Fin.castAdd k (Fin.rev i))) = _
      rw [osConcatPoint_castAdd, Fin.rev_rev]
    rw [h_pt]
    change -Complex.I * minkowskiInnerC
        (fun μ => (p (Fin.castAdd k (Fin.rev i)) μ : ℂ))
        (wickEmbed (euclidTimeReflect (x i))) =
      (starRingEnd ℂ)
        (((-p (Fin.castAdd k (Fin.rev i)) 0 : ℝ) : ℂ) * (x i 0 : ℂ) +
          Complex.I *
            (((-p (Fin.castAdd k (Fin.rev i)) 1 : ℝ) : ℂ) * (x i 1 : ℂ) +
              ((-p (Fin.castAdd k (Fin.rev i)) 2 : ℝ) : ℂ) * (x i 2 : ℂ) +
              ((-p (Fin.castAdd k (Fin.rev i)) 3 : ℝ) : ℂ) * (x i 3 : ℂ)))
    simp only [minkowskiInnerC, wickEmbed, euclidTimeReflect, Fin.isValue, ↓reduceIte,
      Fin.reduceEq, map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I,
      Complex.ofReal_neg]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have h_pt : wickEmbedN (j + k) (osConcatPoint j k x y)
        (Fin.natAdd j t) = wickEmbed (y t) := by
      change wickEmbed (osConcatPoint j k x y (Fin.natAdd j t)) = _
      rw [osConcatPoint_natAdd]
    rw [h_pt]
    change -Complex.I * minkowskiInnerC
        (fun μ => (p (Fin.natAdd j t) μ : ℂ)) (wickEmbed (y t)) = _
    simp only [minkowskiInnerC, wickEmbed, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    ring_nf
    simp only [Complex.I_sq]
    ring

omit [Fintype ι] [DecidableEq ι] in
lemma orderedEuclidN_time_lt_of_lt {n : ℕ} {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) {u v : Fin n} (huv : u < v) :
    x u 0 < x v 0 := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨v, hv⟩ := v
  change u < v at huv
  induction v, huv using Nat.le_induction with
  | base => exact hx ⟨u, hu⟩ hv
  | succ m hm ih =>
    exact lt_trans (ih (Nat.lt_of_succ_lt hv)) (hx ⟨m, Nat.lt_of_succ_lt hv⟩ hv)

noncomputable def wavepacketOSPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H) :
    OSPreHilbertSpace D →ₗ[ℂ] H :=
  (Finsupp.lsum ℂ (fun A => LinearMap.toSpanSingleton ℂ H (Φ A))).comp
    (OSPreHilbertSpace.equivFinsupp D).toLinearMap

@[simp]
lemma wavepacketOSPreLM_osBasisPre
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H) (A : OSConfig ι) :
    wavepacketOSPreLM D Φ (osBasisPre D A) = Φ A := by
  dsimp [wavepacketOSPreLM, osBasisPre, OSPreHilbertSpace.equivFinsupp]
  simp

theorem inner_wavepacketOSPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (Ψ₁ Ψ₂ : OSPreHilbertSpace D) :
    ⟪wavepacketOSPreLM D Φ Ψ₁, wavepacketOSPreLM D Φ Ψ₂⟫_ℂ = ⟪Ψ₁, Ψ₂⟫_ℂ := by
  let L := wavepacketOSPreLM D Φ
  have hL : ∀ X : OSPreHilbertSpace D,
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • Φ A := by
    intro X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => ?_)
    dsimp only
    rw [L.map_smul, wavepacketOSPreLM_osBasisPre]
  have hX : ∀ X : OSPreHilbertSpace D,
      X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • osBasisPre D A := by
    intro X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rfl
  rw [hL Ψ₁, hL Ψ₂]
  conv_rhs => rw [hX Ψ₁, hX Ψ₂]
  rw [sum_inner (𝕜 := ℂ), sum_inner (𝕜 := ℂ)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum (𝕜 := ℂ), inner_sum (𝕜 := ℂ)]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, h_ker A B, inner_osBasisPre]

theorem norm_wavepacketOSPreLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (Ψ : OSPreHilbertSpace D) :
    ‖wavepacketOSPreLM D Φ Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketOSPreLM D Φ h_ker Ψ Ψ]

noncomputable def wavepacketOSPreCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    OSPreHilbertSpace D →L[ℂ] H :=
  (wavepacketOSPreLM D Φ).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_wavepacketOSPreLM D Φ h_ker Ψ])

noncomputable def wavepacketOSCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    OSHilbert D →L[ℂ] H :=
  (wavepacketOSPreCLM D Φ h_ker).extend (toOSHilbert D)

@[simp]
lemma wavepacketOSCLM_toOSHilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (Ψ : OSPreHilbertSpace D) :
    wavepacketOSCLM D Φ h_ker (toOSHilbert D Ψ) = wavepacketOSPreLM D Φ Ψ :=
  (wavepacketOSPreCLM D Φ h_ker).extend_eq
    UniformSpace.Completion.isDenseInducing_coe.dense
    (UniformSpace.Completion.isUniformInducing_coe _) Ψ

@[simp]
theorem wavepacketOSCLM_osBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (A : OSConfig ι) :
    wavepacketOSCLM D Φ h_ker (osBasis D A) = Φ A := by
  dsimp [osBasis]
  rw [wavepacketOSCLM_toOSHilbert, wavepacketOSPreLM_osBasisPre]

@[simp]
theorem wavepacketOSCLM_osVacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    wavepacketOSCLM D Φ h_ker (osVacuum D) = Φ (osVacuumConfig ι) :=
  wavepacketOSCLM_osBasis D Φ h_ker (osVacuumConfig ι)

theorem inner_wavepacketOSCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (x y : OSHilbert D) :
    ⟪wavepacketOSCLM D Φ h_ker x, wavepacketOSCLM D Φ h_ker y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ₁ Ψ₂ =>
    change ⟪wavepacketOSCLM D Φ h_ker (toOSHilbert D Ψ₁),
        wavepacketOSCLM D Φ h_ker (toOSHilbert D Ψ₂)⟫_ℂ =
      ⟪toOSHilbert D Ψ₁, toOSHilbert D Ψ₂⟫_ℂ
    rw [wavepacketOSCLM_toOSHilbert, wavepacketOSCLM_toOSHilbert,
        inner_toOSHilbert, inner_wavepacketOSPreLM D Φ h_ker Ψ₁ Ψ₂]

theorem norm_wavepacketOSCLM
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (x : OSHilbert D) :
    ‖wavepacketOSCLM D Φ h_ker x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wavepacketOSCLM D Φ h_ker x x]

noncomputable def wavepacketOSLinearIsometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    OSHilbert D →ₗᵢ[ℂ] H where
  toLinearMap := (wavepacketOSCLM D Φ h_ker).toLinearMap
  norm_map' := norm_wavepacketOSCLM D Φ h_ker

@[simp]
theorem wavepacketOSLinearIsometry_osBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (A : OSConfig ι) :
    wavepacketOSLinearIsometry D Φ h_ker (osBasis D A) = Φ A :=
  wavepacketOSCLM_osBasis D Φ h_ker A

@[simp]
theorem wavepacketOSLinearIsometry_osVacuum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B) :
    wavepacketOSLinearIsometry D Φ h_ker (osVacuum D) = Φ (osVacuumConfig ι) :=
  wavepacketOSCLM_osVacuum D Φ h_ker

theorem surjective_wavepacketOSLinearIsometry_of_ortho_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (h_ortho : ∀ χ : H, (∀ A : OSConfig ι, ⟪χ, Φ A⟫_ℂ = 0) → χ = 0) :
    Function.Surjective (wavepacketOSLinearIsometry D Φ h_ker) := by
  let ι_OS := wavepacketOSLinearIsometry D Φ h_ker
  let K : Submodule ℂ H := LinearMap.range ι_OS.toLinearMap
  have hK_closed : IsClosed (K : Set H) :=
    ι_OS.isometry.isUniformInducing.isComplete_range.isClosed
  have hK_ortho : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro χ hχ
    refine h_ortho χ (fun A => ?_)
    have hA_mem : Φ A ∈ K := ⟨osBasis D A, wavepacketOSLinearIsometry_osBasis D Φ h_ker A⟩
    exact Submodule.inner_left_of_mem_orthogonal hA_mem hχ
  have hK_top : K = ⊤ := by
    have h1 : Kᗮᗮ = K := by
      rw [K.orthogonal_orthogonal_eq_closure]
      exact SetLike.ext' hK_closed.closure_eq
    rw [← h1, hK_ortho, Submodule.bot_orthogonal_eq_top]
  intro y
  have hy : y ∈ K := by
    rw [hK_top]
    exact Submodule.mem_top
  exact hy

noncomputable def wavepacketOSLinearIsometryEquiv_of_ortho_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (h_ortho : ∀ χ : H, (∀ A : OSConfig ι, ⟪χ, Φ A⟫_ℂ = 0) → χ = 0) :
    OSHilbert D ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (wavepacketOSLinearIsometry D Φ h_ker)
    (surjective_wavepacketOSLinearIsometry_of_ortho_eq_zero D Φ h_ker h_ortho)

theorem wavepacketOSLinearIsometry_intertwines_contraction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (τ : ℝ) (hτ : 0 ≤ τ) (T : H →L[ℂ] H)
    (h_T : ∀ A : OSConfig ι, Φ (osConfigTimeShift τ hτ A) = T (Φ A))
    (x : OSHilbert D) :
    wavepacketOSLinearIsometry D Φ h_ker (osContractionSemigroup D hcontr τ hτ x) =
      T (wavepacketOSLinearIsometry D Φ h_ker x) := by
  let J := wavepacketOSCLM D Φ h_ker
  change J (osContractionSemigroup D hcontr τ hτ x) = T (J x)
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change J (osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ)) =
      T (J (toOSHilbert D Ψ))
    rw [osContractionSemigroup_toOSHilbert, wavepacketOSCLM_toOSHilbert,
        wavepacketOSCLM_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    unfold osTimeShiftLM Finsupp.sum
    rw [map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, T.map_smul,
        osLiftConfigMap_osBasisPre, wavepacketOSPreLM_osBasisPre,
        wavepacketOSPreLM_osBasisPre, h_T]

theorem wavepacketOSLinearIsometry_intertwines_spatial
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (Φ : OSConfig ι → H)
    (h_ker : ∀ A B : OSConfig ι, ⟪Φ A, Φ B⟫_ℂ = osKernel S D.𝒮 A B)
    (b : Fin 3 → ℝ) (U : H →L[ℂ] H)
    (h_U : ∀ A : OSConfig ι, Φ (osConfigSpatialShift b A) = U (Φ A))
    (x : OSHilbert D) :
    wavepacketOSLinearIsometry D Φ h_ker (osSpatialTranslate D htrans b x) =
      U (wavepacketOSLinearIsometry D Φ h_ker x) := by
  let J := wavepacketOSCLM D Φ h_ker
  change J (osSpatialTranslate D htrans b x) = U (J x)
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change J (osSpatialTranslate D htrans b (toOSHilbert D Ψ)) =
      U (J (toOSHilbert D Ψ))
    rw [osSpatialTranslate_toOSHilbert, wavepacketOSCLM_toOSHilbert,
        wavepacketOSCLM_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    unfold osSpatialTranslateLM Finsupp.sum
    rw [map_sum, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, U.map_smul,
        osLiftConfigMap_osBasisPre, wavepacketOSPreLM_osBasisPre,
        wavepacketOSPreLM_osBasisPre, h_U]

omit [Fintype ι] [DecidableEq ι] in
lemma eq_zero_on_rightHalfPlane_of_real_zero {g : ℂ → ℂ}
    (hg_holo : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
    (hg_cont : ContinuousOn g rightHalfPlane)
    (hg_real : ∀ (τ : ℝ), 0 ≤ τ → g (τ : ℂ) = 0) :
    ∀ z ∈ rightHalfPlane, g z = 0 := by
  have h_open : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hg_ana : AnalyticOnNhd ℂ g {z : ℂ | 0 < z.re} :=
    h_open.analyticOn_iff_analyticOnNhd.mp (hg_holo.analyticOn h_open)
  have h_conv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_mul, zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hy
    · nlinarith
  let r_seq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hr_pos : ∀ n : ℕ, 0 < r_seq n := fun n => by dsimp [r_seq]; positivity
  have h_inv_tendsto : Tendsto (fun n : ℕ => (r_seq n : ℂ)) atTop (𝓝 0) := by
    have hr : Tendsto r_seq atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have h_freq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), g w = 0 := by
    let u : ℕ → ℂ := fun n => (1 : ℂ) + (r_seq n : ℂ)
    have hu_t : Tendsto u atTop (𝓝 (1 : ℂ)) := by
      simpa [u] using tendsto_const_nhds.add h_inv_tendsto
    have hu_ne : ∀ n : ℕ, u n ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
      intro n h1
      rw [Set.mem_singleton_iff] at h1
      have hre := congrArg Complex.re h1
      simp only [u, Complex.add_re, Complex.one_re, Complex.ofReal_re, add_eq_left] at hre
      linarith [hr_pos n]
    have hu_within : Tendsto u atTop (𝓝[≠] (1 : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_t
        (Filter.Eventually.of_forall hu_ne)
    rw [Filter.frequently_iff]
    intro U hU
    rcases (hu_within.eventually hU).exists with ⟨n, hn⟩
    refine ⟨u n, hn, ?_⟩
    have hu_real : u n = ((1 + r_seq n : ℝ) : ℂ) := by dsimp [u]; push_cast; rfl
    rw [hu_real]
    exact hg_real _ (by linarith [hr_pos n])
  have h_open_zero : Set.EqOn g 0 {z : ℂ | 0 < z.re} :=
    hg_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero h_conv.isPreconnected
      (by simp : (1 : ℂ) ∈ {z : ℂ | 0 < z.re}) h_freq
  intro z hz
  let v : ℕ → ℂ := fun n => z + (r_seq n : ℂ)
  have hv_t : Tendsto v atTop (𝓝 z) := by
    simpa [v] using tendsto_const_nhds.add h_inv_tendsto
  have hv_pos : ∀ n : ℕ, 0 < (v n).re := by
    intro n
    have hz_re : 0 ≤ z.re := hz
    simp only [v, Complex.add_re, Complex.ofReal_re]
    linarith [hr_pos n]
  have hv_within : Tendsto v atTop (𝓝[rightHalfPlane] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hv_t
      (Filter.Eventually.of_forall (fun n => (hv_pos n).le))
  have hg_lim₁ : Tendsto (g ∘ v) atTop (𝓝 (g z)) :=
    (hg_cont.continuousWithinAt hz).tendsto.comp hv_within
  have hg_lim₂ : Tendsto (g ∘ v) atTop (𝓝 0) := by
    have h0 : g ∘ v = fun _ : ℕ => (0 : ℂ) :=
      funext (fun n => h_open_zero (hv_pos n))
    rw [h0]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hg_lim₁ hg_lim₂

omit [Fintype ι] [DecidableEq ι] in
private lemma tubeConv_seq_tendsto_zero_of_bdy_cc
    {n : ℕ} {D_flat : (Fin (n * 4) → ℂ) → ℂ}
    (hD_diff : DifferentiableOn ℂ D_flat (TubeDomain (forwardTubeConeFlat n)))
    {θ₀ : Fin (n * 4) → ℝ} (hθ₀ : θ₀ ∈ forwardTubeConeFlat n)
    (hD_bdy_cc : ∀ (φ : (Fin (n * 4) → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Tendsto (fun t : ℝ => ∫ u : Fin (n * 4) → ℝ,
        D_flat (fun p => (u p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) * φ u)
        (𝓝[>] 0) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2)
    (t_seq : ℕ → ℝ) (ht_pos : ∀ m, 0 < t_seq m) (ht_lim : Tendsto t_seq atTop (𝓝 0))
    (u_seq : ℕ → (Fin (n * 4) → ℝ)) (u_star : Fin (n * 4) → ℝ)
    (hu_mem : ∀ m, u_seq m ∈ Metric.closedBall 0 (1 / 2))
    (hu_lim : Tendsto u_seq atTop (𝓝 u_star)) :
    let ψ := Distribution.unitMollifier (n * 4) (half_pos hε)
    let Φ_ε : (Fin (n * 4) → ℝ) → ℝ := fun s => ∫ v : Fin (n * 4) → ℝ, ψ v * ψ (v - s)
    Tendsto (fun m => Distribution.tubeConv D_flat Φ_ε
      (fun p => (u_seq m p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  let d : ℕ := n * 4
  intro ψ Φ_ε
  let χ₁_bump : ContDiffBump (0 : Fin d → ℝ) :=
    Distribution.bumpOfPos d (by norm_num : (0 : ℝ) < 2)
  let χ₁ : (Fin d → ℝ) → ℝ := fun w => χ₁_bump w
  have hχ₁_cd : ContDiff ℝ (⊤ : ℕ∞) χ₁ := χ₁_bump.contDiff
  have hχ₁_supp : HasCompactSupport χ₁ := χ₁_bump.hasCompactSupport
  have hχ₁_one : ∀ w : Fin d → ℝ, ‖w‖ ≤ 1 → χ₁ w = 1 := by
    intro w hw
    have hrIn : χ₁_bump.rIn = 1 := by dsimp [χ₁_bump, Distribution.bumpOfPos]; norm_num
    exact χ₁_bump.one_of_mem_closedBall (by
      rw [hrIn, Metric.mem_closedBall, dist_zero_right]; exact hw)
  have hχ₁_supp_sub : Function.support χ₁ ⊆ Metric.ball 0 2 := by
    rw [χ₁_bump.support_eq]
    rfl
  let ψ_c : (Fin d → ℝ) → ℂ := fun u => (ψ u : ℂ)
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := Distribution.contDiff_unitMollifier d (half_pos hε)
  have hψ_supp : HasCompactSupport ψ :=
    Distribution.hasCompactSupport_unitMollifier d (half_pos hε)
  have hψc_cd : ContDiff ℝ (⊤ : ℕ∞) ψ_c := Complex.ofRealCLM.contDiff.comp hψ_cd
  have hψc_supp : HasCompactSupport ψ_c := hψ_supp.comp_left Complex.ofReal_zero
  let B := BoundedContinuousFunction (Fin d → ℝ) ℂ
  let cutB : B → (Fin d → ℝ) → ℂ := fun g w => g w * (χ₁ w : ℂ)
  let convB : B → (Fin d → ℝ) → ℂ :=
    fun g => (cutB g) ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] ψ_c
  have hcut_cont : ∀ g : B, Continuous (cutB g) := fun g =>
    g.continuous.mul (Complex.continuous_ofReal.comp hχ₁_cd.continuous)
  have hcut_supp : ∀ g : B, HasCompactSupport (cutB g) := fun _ =>
    (hχ₁_supp.comp_left Complex.ofReal_zero).mul_left
  have hconv_cd : ∀ g : B, ContDiff ℝ (⊤ : ℕ∞) (convB g) := fun g =>
    hψc_supp.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      (hcut_cont g).locallyIntegrable hψc_cd
  have hconv_supp : ∀ g : B, HasCompactSupport (convB g) := fun g =>
    (hcut_supp g).convolution (ContinuousLinearMap.mul ℝ ℂ) hψc_supp
  have hconv_zero_outside : ∀ (g : B) (u : Fin d → ℝ),
      u ∉ Metric.closedBall (0 : Fin d → ℝ) 3 → convB g u = 0 := by
    intro g u hu
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    push Not at hu
    dsimp [convB]
    rw [MeasureTheory.convolution_def]
    have h_zero_fn : (fun w : Fin d → ℝ =>
        ContinuousLinearMap.mul ℝ ℂ (cutB g w) (ψ_c (u - w))) = fun _ => 0 := by
      ext w
      by_cases hw : ‖w‖ < 2
      · have huw : ε / 2 < ‖u - w‖ := by
          have htri : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := norm_le_insert' u w
          linarith
        have hψ0 : ψ (u - w) = 0 := by
          by_contra hne
          have hm := Distribution.tsupport_unitMollifier_subset d (half_pos hε)
            (subset_tsupport ψ hne)
          rw [Metric.mem_closedBall, dist_zero_right] at hm
          linarith
        simp [ψ_c, hψ0]
      · push Not at hw
        have hχ0 : χ₁ w = 0 := by
          by_contra hne
          have hm : w ∈ Metric.ball (0 : Fin d → ℝ) 2 := hχ₁_supp_sub hne
          rw [Metric.mem_ball, dist_zero_right] at hm
          linarith
        simp [cutB, hχ0]
    rw [h_zero_fn, MeasureTheory.integral_zero]
  have hconv_norm_le : ∀ (g : B) (u : Fin d → ℝ), ‖convB g u‖ ≤ ‖g‖ := by
    intro g u
    dsimp [convB]
    rw [MeasureTheory.convolution_def]
    have h_int_psi : Integrable (fun w : Fin d → ℝ => ‖g‖ * ψ (u - w)) volume :=
      ((Distribution.integrable_unitMollifier d (half_pos hε)).comp_sub_left u).const_mul ‖g‖
    have h_le : ∀ w : Fin d → ℝ,
        ‖ContinuousLinearMap.mul ℝ ℂ (cutB g w) (ψ_c (u - w))‖ ≤ ‖g‖ * ψ (u - w) := by
      intro w
      have hψ_nn : 0 ≤ ψ (u - w) := Distribution.nonneg_unitMollifier d (half_pos hε) (u - w)
      have hχ_nn : 0 ≤ χ₁ w := χ₁_bump.nonneg
      have hχ_le : χ₁ w ≤ 1 := χ₁_bump.le_one
      change ‖(g w * (χ₁ w : ℂ)) * (ψ (u - w) : ℂ)‖ ≤ ‖g‖ * ψ (u - w)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hχ_nn, Real.norm_of_nonneg hψ_nn]
      have hg_le : ‖g w‖ ≤ ‖g‖ := g.norm_coe_le_norm w
      calc ‖g w‖ * χ₁ w * ψ (u - w)
          ≤ (‖g‖ * 1) * ψ (u - w) :=
            mul_le_mul (mul_le_mul hg_le hχ_le hχ_nn (norm_nonneg g)) le_rfl hψ_nn
              (mul_nonneg (norm_nonneg g) zero_le_one)
        _ = ‖g‖ * ψ (u - w) := by ring
    calc ‖∫ w : Fin d → ℝ, ContinuousLinearMap.mul ℝ ℂ (cutB g w) (ψ_c (u - w))‖
        ≤ ∫ w : Fin d → ℝ, ‖g‖ * ψ (u - w) := norm_integral_le_of_norm_le h_int_psi
            (Filter.Eventually.of_forall h_le)
      _ = ‖g‖ * ∫ w : Fin d → ℝ, ψ (u - w) := MeasureTheory.integral_const_mul _ _
      _ = ‖g‖ * ∫ v : Fin d → ℝ, ψ v := by
          rw [MeasureTheory.integral_sub_left_eq_self ψ volume u]
      _ = ‖g‖ := by rw [Distribution.integral_unitMollifier d (half_pos hε), mul_one]
  have hconv_add : ∀ (g₁ g₂ : B) (u : Fin d → ℝ),
      convB (g₁ + g₂) u = convB g₁ u + convB g₂ u := by
    intro g₁ g₂ u
    dsimp [convB]
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def,
        MeasureTheory.convolution_def]
    have hi₁ : Integrable (fun w : Fin d → ℝ =>
        ContinuousLinearMap.mul ℝ ℂ (cutB g₁ w) (ψ_c (u - w))) :=
      ((hcut_cont g₁).mul (hψc_cd.continuous.comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hcut_supp g₁).mul_right)
    have hi₂ : Integrable (fun w : Fin d → ℝ =>
        ContinuousLinearMap.mul ℝ ℂ (cutB g₂ w) (ψ_c (u - w))) :=
      ((hcut_cont g₂).mul (hψc_cd.continuous.comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hcut_supp g₂).mul_right)
    rw [← MeasureTheory.integral_add hi₁ hi₂]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    change ((g₁ w + g₂ w) * (χ₁ w : ℂ)) * ψ_c (u - w) =
      (g₁ w * (χ₁ w : ℂ)) * ψ_c (u - w) + (g₂ w * (χ₁ w : ℂ)) * ψ_c (u - w)
    ring
  have hconv_smul : ∀ (c : ℂ) (g : B) (u : Fin d → ℝ),
      convB (c • g) u = c * convB g u := by
    intro c g u
    dsimp [convB]
    rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def,
        ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    change ((c * g w) * (χ₁ w : ℂ)) * ψ_c (u - w) =
      c * ((g w * (χ₁ w : ℂ)) * ψ_c (u - w))
    ring
  have hψ_bdd : ∃ M_ψ : ℝ, 0 ≤ M_ψ ∧ ∀ v : Fin d → ℝ, ‖(ψ v : ℂ)‖ ≤ M_ψ := by
    rcases (hψ_supp.isCompact.image
      (Complex.continuous_ofReal.comp hψ_cd.continuous).norm).isBounded.exists_norm_le with
      ⟨M₀, hM₀⟩
    refine ⟨max M₀ 0, le_max_right _ _, fun v => ?_⟩
    by_cases hv_s : v ∈ tsupport ψ
    · have hm := hM₀ ‖(ψ v : ℂ)‖ ⟨v, hv_s, rfl⟩
      rw [Real.norm_of_nonneg (norm_nonneg _)] at hm
      exact hm.trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hv_s, Complex.ofReal_zero, norm_zero]
      exact le_max_right _ _
  rcases hψ_bdd with ⟨M_ψ, _hMψ_nn, hM_ψ⟩
  let g_tr : (Fin d → ℝ) → B := fun u₀ =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun w => (ψ (u₀ - w) : ℂ))
      (Complex.continuous_ofReal.comp
        (hψ_cd.continuous.comp (continuous_const.sub continuous_id)))
      M_ψ (fun w => hM_ψ (u₀ - w))
  have hg_tr_cont : Continuous g_tr := by
    rw [Metric.continuous_iff]
    intro u₀ η hη
    have h_uc : UniformContinuous (fun v : Fin d → ℝ => (ψ v : ℂ)) :=
      hψc_supp.uniformContinuous_of_continuous hψc_cd.continuous
    rcases Metric.uniformContinuous_iff.mp h_uc (η / 2) (half_pos hη) with ⟨δ, hδ, h_close⟩
    refine ⟨δ, hδ, fun u₁ hu₁ => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (half_pos hη).le).mpr fun w => ?_)
      (half_lt_self hη)
    change ‖(ψ (u₁ - w) : ℂ) - (ψ (u₀ - w) : ℂ)‖ ≤ η / 2
    have h_dist : dist (u₁ - w) (u₀ - w) < δ := by
      rwa [dist_sub_right]
    rw [← dist_eq_norm]
    exact (h_close h_dist).le
  have hconv_gtr_eq : ∀ {u₀ : Fin d → ℝ},
      u₀ ∈ Metric.closedBall (0 : Fin d → ℝ) (1 / 2) →
      ∀ u : Fin d → ℝ, convB (g_tr u₀) u = (Φ_ε (u₀ - u) : ℂ) := by
    intro u₀ hu₀ u
    rw [Metric.mem_closedBall, dist_zero_right] at hu₀
    dsimp [convB]
    rw [MeasureTheory.convolution_def]
    have h_cut_eq : ∀ w : Fin d → ℝ,
        ContinuousLinearMap.mul ℝ ℂ (cutB (g_tr u₀) w) (ψ_c (u - w)) =
          (ψ (u₀ - w) : ℂ) * (ψ (u - w) : ℂ) := by
      intro w
      change ((ψ (u₀ - w) : ℂ) * (χ₁ w : ℂ)) * (ψ (u - w) : ℂ) = _
      by_cases hψw : ψ (u₀ - w) = 0
      · simp [hψw]
      · have hw_dist : ‖u₀ - w‖ ≤ ε / 2 := by
          have hm := Distribution.tsupport_unitMollifier_subset d (half_pos hε)
            (subset_tsupport ψ hψw)
          rwa [Metric.mem_closedBall, dist_zero_right] at hm
        have hw_le : ‖w‖ ≤ 1 := by
          have htri : ‖w‖ ≤ ‖u₀‖ + ‖u₀ - w‖ := by
            calc ‖w‖ = ‖u₀ - (u₀ - w)‖ := by abel_nf
              _ ≤ ‖u₀‖ + ‖u₀ - w‖ := norm_sub_le _ _
          linarith
        rw [hχ₁_one w hw_le, Complex.ofReal_one, mul_one]
    simp_rw [h_cut_eq]
    have h_congr : (∫ w : Fin d → ℝ, (ψ (u₀ - w) : ℂ) * (ψ (u - w) : ℂ)) =
        ∫ w : Fin d → ℝ, (fun v : Fin d → ℝ => (ψ v : ℂ) * (ψ (u - (u₀ - v)) : ℂ)) (u₀ - w) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      dsimp only
      rw [sub_sub_cancel]
    rw [h_congr, MeasureTheory.integral_sub_left_eq_self
      (fun v : Fin d → ℝ => (ψ v : ℂ) * (ψ (u - (u₀ - v)) : ℂ)) volume u₀]
    have h_ofReal : (∫ v : Fin d → ℝ, (ψ v : ℂ) * (ψ (u - (u₀ - v)) : ℂ)) =
        ∫ v : Fin d → ℝ, ((ψ v * ψ (v - (u₀ - u)) : ℝ) : ℂ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      dsimp only
      have hv : u - (u₀ - v) = v - (u₀ - u) := by abel
      rw [hv, Complex.ofReal_mul]
    rw [h_ofReal, integral_complex_ofReal]
  have ht_within : Tendsto t_seq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t_seq ht_lim
      (Filter.Eventually.of_forall ht_pos)
  let K₃ : Set (Fin d → ℝ) := Metric.closedBall 0 3
  have hK₃_meas : MeasurableSet K₃ := Metric.isClosed_closedBall.measurableSet
  have hK₃_fin : volume K₃ < ⊤ := measure_closedBall_lt_top
  have h_ell_ex : ∀ m : ℕ, ∃ L : B →L[ℂ] ℂ, ∀ g : B,
      L g = ∫ u : Fin d → ℝ,
        D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) * convB g u := by
    intro m
    have hD_m_cont : Continuous (fun u : Fin d → ℝ =>
        D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I)) := by
      refine hD_diff.continuousOn.comp_continuous
        (continuous_pi fun p =>
          (Complex.continuous_ofReal.comp (continuous_apply p)).add continuous_const)
        (fun u => ?_)
      change (fun p => ((u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I).im) ∈
        forwardTubeConeFlat n
      have him : (fun p => ((u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I).im) =
          (t_seq m) • θ₀ := by
        ext p; simp
      rw [him]
      exact smul_mem_forwardTubeConeFlat n (ht_pos m) hθ₀
    have hD_m_bdd := ((isCompact_closedBall (0 : Fin d → ℝ) 3).image hD_m_cont.norm).isBounded
    rcases hD_m_bdd.exists_norm_le with ⟨M₀, hM₀⟩
    let M_m : ℝ := max M₀ 0
    have hMm_nn : 0 ≤ M_m := le_max_right _ _
    let V₃ : ℝ := (volume K₃).toReal
    let L_lin : B →ₗ[ℂ] ℂ :=
      { toFun := fun g => ∫ u : Fin d → ℝ,
          D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) * convB g u
        map_add' := fun g₁ g₂ => by
          have hi₁ : Integrable (fun u : Fin d → ℝ =>
              D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) *
                convB g₁ u) :=
            (hD_m_cont.mul (hconv_cd g₁).continuous).integrable_of_hasCompactSupport
              (hconv_supp g₁).mul_left
          have hi₂ : Integrable (fun u : Fin d → ℝ =>
              D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) *
                convB g₂ u) :=
            (hD_m_cont.mul (hconv_cd g₂).continuous).integrable_of_hasCompactSupport
              (hconv_supp g₂).mul_left
          rw [← MeasureTheory.integral_add hi₁ hi₂]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [hconv_add, mul_add]
        map_smul' := fun c g => by
          simp only [RingHom.id_apply, smul_eq_mul, ← MeasureTheory.integral_const_mul]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [hconv_smul]
          ring }
    refine ⟨L_lin.mkContinuous (M_m * V₃) (fun g => ?_), fun _ => rfl⟩
    let dom_g : (Fin d → ℝ) → ℝ := Set.indicator K₃ (fun _ => M_m * ‖g‖)
    have hdom_int : Integrable dom_g volume :=
      (integrableOn_const (hs := hK₃_fin.ne) (hC := ENNReal.coe_ne_top)).integrable_indicator
        hK₃_meas
    have h_pt : ∀ u : Fin d → ℝ,
        ‖D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) *
          convB g u‖ ≤ dom_g u := by
      intro u
      by_cases hu : u ∈ K₃
      · simp only [dom_g, Set.indicator_of_mem hu, norm_mul]
        have h1 : ‖D_flat (fun p => (u p : ℂ) +
            ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I)‖ ≤ M_m := by
          have hm_in := hM₀ _ ⟨u, hu, rfl⟩
          rw [Real.norm_of_nonneg (norm_nonneg _)] at hm_in
          exact hm_in.trans (le_max_left _ _)
        exact mul_le_mul h1 (hconv_norm_le g u) (norm_nonneg _) hMm_nn
      · simp [dom_g, hu, hconv_zero_outside g u hu]
    calc ‖L_lin g‖
        ≤ ∫ u : Fin d → ℝ, dom_g u :=
          norm_integral_le_of_norm_le hdom_int (Filter.Eventually.of_forall h_pt)
      _ = (M_m * V₃) * ‖g‖ := by
          dsimp [dom_g, V₃]
          rw [MeasureTheory.integral_indicator hK₃_meas, setIntegral_const,
              MeasureTheory.Measure.real_def, smul_eq_mul]
          ring
  choose ℓ hℓ_apply using h_ell_ex
  have h_pt_tendsto : ∀ g : B, Tendsto (fun m => ℓ m g) atTop (𝓝 0) := by
    intro g
    have h1 := (hD_bdy_cc (convB g) (hconv_cd g) (hconv_supp g)).comp ht_within
    exact h1.congr fun m => (hℓ_apply m g).symm
  have h_pt_bdd : ∀ g : B, ∃ C : ℝ, ∀ m : ℕ, ‖ℓ m g‖ ≤ C := by
    intro g
    have h_rng := Metric.isBounded_range_of_tendsto (fun m => ℓ m g) (h_pt_tendsto g)
    rcases h_rng.exists_norm_le with ⟨C, hC⟩
    exact ⟨C, fun m => hC _ ⟨m, rfl⟩⟩
  rcases banach_steinhaus h_pt_bdd with ⟨C', hC'⟩
  let C_op : ℝ := max C' 0
  have h_diff_tend : Tendsto (fun m => C_op * ‖g_tr (u_seq m) - g_tr u_star‖ +
      ‖ℓ m (g_tr u_star)‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => ‖g_tr (u_seq m) - g_tr u_star‖) atTop (𝓝 0) := by
      have hg_lim := (hg_tr_cont.tendsto u_star).comp hu_lim
      simpa using (hg_lim.sub (tendsto_const_nhds (x := g_tr u_star))).norm
    have h2 : Tendsto (fun m => ‖ℓ m (g_tr u_star)‖) atTop (𝓝 0) := by
      simpa using (h_pt_tendsto (g_tr u_star)).norm
    simpa using (h1.const_mul C_op).add h2
  have h_ell_seq : Tendsto (fun m => ℓ m (g_tr (u_seq m))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) h_diff_tend
    have h_split : ℓ m (g_tr (u_seq m)) =
        ℓ m (g_tr (u_seq m) - g_tr u_star) + ℓ m (g_tr u_star) := by
      rw [← map_add, sub_add_cancel]
    rw [h_split]
    calc ‖ℓ m (g_tr (u_seq m) - g_tr u_star) + ℓ m (g_tr u_star)‖
        ≤ ‖ℓ m (g_tr (u_seq m) - g_tr u_star)‖ + ‖ℓ m (g_tr u_star)‖ := norm_add_le _ _
      _ ≤ ‖ℓ m‖ * ‖g_tr (u_seq m) - g_tr u_star‖ + ‖ℓ m (g_tr u_star)‖ := by
          gcongr
          exact (ℓ m).le_opNorm _
      _ ≤ C_op * ‖g_tr (u_seq m) - g_tr u_star‖ + ‖ℓ m (g_tr u_star)‖ := by
          gcongr
          exact (hC' m).trans (le_max_left _ _)
  refine h_ell_seq.congr fun m => ?_
  rw [hℓ_apply m (g_tr (u_seq m))]
  have h_conv_eq : ∀ u : Fin d → ℝ,
      convB (g_tr (u_seq m)) u = (Φ_ε (u_seq m - u) : ℂ) :=
    hconv_gtr_eq (hu_mem m)
  simp_rw [h_conv_eq]
  dsimp [Distribution.tubeConv]
  let f_m : (Fin d → ℝ) → ℂ := fun s =>
    D_flat (fun p => ((u_seq m - s) p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) *
      (Φ_ε s : ℂ)
  have h_congr_m : (∫ u : Fin d → ℝ,
      D_flat (fun p => (u p : ℂ) + ((t_seq m * θ₀ p : ℝ) : ℂ) * Complex.I) *
        (Φ_ε (u_seq m - u) : ℂ)) =
      ∫ u : Fin d → ℝ, f_m (u_seq m - u) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp [f_m]
    congr 2
    ext p
    simp
  rw [h_congr_m, MeasureTheory.integral_sub_left_eq_self f_m volume (u_seq m)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  dsimp [f_m]
  congr 2
  ext p
  simp
  ring

omit [Fintype ι] [DecidableEq ι] in
private lemma tubeConv_eq_zero_at_base_of_bdy_cc_eps
    {n : ℕ} {D_flat : (Fin (n * 4) → ℂ) → ℂ}
    (hD_diff : DifferentiableOn ℂ D_flat (TubeDomain (forwardTubeConeFlat n)))
    {θ₀ : Fin (n * 4) → ℝ} (hθ₀ : θ₀ ∈ forwardTubeConeFlat n)
    (hD_bdy_cc : ∀ (φ : (Fin (n * 4) → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Tendsto (fun t : ℝ => ∫ u : Fin (n * 4) → ℝ,
        D_flat (fun p => (u p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) * φ u)
        (𝓝[>] 0) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2) :
    let ψ := Distribution.unitMollifier (n * 4) (half_pos hε)
    let Φ_ε : (Fin (n * 4) → ℝ) → ℝ := fun s => ∫ v : Fin (n * 4) → ℝ, ψ v * ψ (v - s)
    Distribution.tubeConv D_flat Φ_ε (fun p => (θ₀ p : ℂ) * Complex.I) = 0 := by
  let d : ℕ := n * 4
  let U_flat : Set (Fin d → ℂ) := TubeDomain (forwardTubeConeFlat n)
  intro ψ Φ_ε
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := Distribution.contDiff_unitMollifier d (half_pos hε)
  have hψ_supp : HasCompactSupport ψ :=
    Distribution.hasCompactSupport_unitMollifier d (half_pos hε)
  have h_eq_Φ : Φ_ε = ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x => ψ (-x)) := by
    ext s
    rw [MeasureTheory.convolution_def]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    change ψ v * ψ (v - s) = ψ v * ψ (-(s - v))
    rw [neg_sub]
  have hΦ_cd : ContDiff ℝ (⊤ : ℕ∞) Φ_ε := by
    rw [h_eq_Φ]
    exact (hψ_supp.comp_homeomorph (Homeomorph.neg _)).contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hψ_cd.continuous.locallyIntegrable
      (hψ_cd.comp contDiff_neg)
  have hΦ_supp : HasCompactSupport Φ_ε := by
    rw [h_eq_Φ]
    exact hψ_supp.convolution (ContinuousLinearMap.mul ℝ ℝ)
      (hψ_supp.comp_homeomorph (Homeomorph.neg _))
  let G_ε : (Fin d → ℂ) → ℂ := Distribution.tubeConv D_flat Φ_ε
  have hG_diff : DifferentiableOn ℂ G_ε U_flat :=
    Distribution.differentiableOn_tubeConv (isOpen_forwardTubeConeFlat n)
      hD_diff hΦ_cd.continuous hΦ_supp
  have h_ball_zero : ∀ u₀ ∈ Metric.ball (0 : Fin d → ℝ) (1 / 4),
      G_ε (fun p => (u₀ p : ℂ) + (θ₀ p : ℂ) * Complex.I) = 0 := by
    intro u₀ hu₀
    rw [Metric.mem_ball, dist_zero_right] at hu₀
    let r₀ : ℝ := (4 * (‖θ₀‖ + 1))⁻¹
    have hr₀_pos : 0 < r₀ := by dsimp [r₀]; positivity
    let F_ε : ℂ → ℂ := fun ζ =>
      if 0 < ζ.im then G_ε (fun p => (u₀ p : ℂ) + ζ * (θ₀ p : ℂ)) else 0
    have h_ray_diff : DifferentiableOn ℂ
        (fun ζ : ℂ => G_ε (fun p => (u₀ p : ℂ) + ζ * (θ₀ p : ℂ))) Analysis.upperHalfPlane := by
      have h_aff : Differentiable ℂ
          (fun ζ : ℂ => fun p : Fin d => (u₀ p : ℂ) + ζ * (θ₀ p : ℂ)) :=
        differentiable_pi.mpr fun p =>
          (differentiable_const _).add (differentiable_id.mul_const _)
      refine hG_diff.comp h_aff.differentiableOn (fun ζ hζ => ?_)
      change (fun p => ((u₀ p : ℂ) + ζ * (θ₀ p : ℂ)).im) ∈ forwardTubeConeFlat n
      have him : (fun p => ((u₀ p : ℂ) + ζ * (θ₀ p : ℂ)).im) = ζ.im • θ₀ := by
        ext p; simp
      rw [him]
      exact smul_mem_forwardTubeConeFlat n hζ hθ₀
    have hF_ana_pos : AnalyticOn ℂ F_ε Analysis.upperHalfPlane := by
      have h_open_uhp : IsOpen Analysis.upperHalfPlane :=
        isOpen_lt continuous_const Complex.continuous_im
      have h_eq : Set.EqOn F_ε
          (fun ζ => G_ε (fun p => (u₀ p : ℂ) + ζ * (θ₀ p : ℂ))) Analysis.upperHalfPlane :=
        fun ζ hζ => if_pos hζ
      exact (h_ray_diff.analyticOn h_open_uhp).congr h_eq
    have hF_ana_neg : AnalyticOn ℂ F_ε Analysis.lowerHalfPlane := by
      have h_eq : Set.EqOn F_ε 0 Analysis.lowerHalfPlane := fun ζ (hζ : ζ.im < 0) =>
        if_neg (not_lt.mpr hζ.le)
      exact analyticOn_const.congr h_eq
    have hF_cont : ContinuousOn F_ε (Analysis.slitDomain (Set.Ioo (-r₀) r₀)) := by
      intro z₀ hz₀
      by_cases him_pos : 0 < z₀.im
      · have h_open_uhp : IsOpen Analysis.upperHalfPlane :=
          isOpen_lt continuous_const Complex.continuous_im
        exact (hF_ana_pos.continuousOn.continuousAt (h_open_uhp.mem_nhds him_pos)
          ).continuousWithinAt
      · by_cases him_neg : z₀.im < 0
        · have h_open_lhp : IsOpen Analysis.lowerHalfPlane :=
            isOpen_lt Complex.continuous_im continuous_const
          exact (hF_ana_neg.continuousOn.continuousAt (h_open_lhp.mem_nhds him_neg)
            ).continuousWithinAt
        · have hz₀_im : z₀.im = 0 := le_antisymm (not_lt.mp him_pos) (not_lt.mp him_neg)
          have hz₀_re : z₀.re ∈ Set.Ioo (-r₀) r₀ := by
            rcases hz₀ with hne | hre
            · exact absurd hz₀_im hne
            · exact hre
          have hF_z₀ : F_ε z₀ = 0 := if_neg him_pos
          refine ContinuousAt.continuousWithinAt ?_
          rw [ContinuousAt, hF_z₀]
          have h_pos_part : Tendsto F_ε (𝓝[{ζ : ℂ | 0 < ζ.im}] z₀) (𝓝 0) := by
            rw [Filter.tendsto_iff_seq_tendsto]
            intro ζ_seq hζ_seq
            have h_ev_im : ∀ᶠ m in atTop, 0 < (ζ_seq m).im :=
              hζ_seq.eventually self_mem_nhdsWithin
            have h_ev_re : ∀ᶠ m in atTop, (ζ_seq m).re ∈ Set.Ioo (-r₀) r₀ := by
              have h_nhds : {ζ : ℂ | ζ.re ∈ Set.Ioo (-r₀) r₀} ∈ 𝓝 z₀ :=
                (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hz₀_re
              exact (tendsto_nhds_of_tendsto_nhdsWithin hζ_seq).eventually h_nhds
            rcases (Filter.eventually_atTop.mp (h_ev_im.and h_ev_re)) with ⟨N₀, hN₀⟩
            rw [← Filter.tendsto_add_atTop_iff_nat N₀]
            let t_seq : ℕ → ℝ := fun m => (ζ_seq (m + N₀)).im
            have ht_pos : ∀ m, 0 < t_seq m := fun m => (hN₀ (m + N₀) (Nat.le_add_left _ _)).1
            have ht_lim : Tendsto t_seq atTop (𝓝 0) := by
              have h1 := (Complex.continuous_im.tendsto z₀).comp
                ((tendsto_nhds_of_tendsto_nhdsWithin hζ_seq).comp (tendsto_add_atTop_nat N₀))
              rwa [hz₀_im] at h1
            let u_seq : ℕ → (Fin d → ℝ) := fun m => u₀ + (ζ_seq (m + N₀)).re • θ₀
            let u_star : Fin d → ℝ := u₀ + z₀.re • θ₀
            have hu_mem : ∀ m, u_seq m ∈ Metric.closedBall 0 (1 / 2) := by
              intro m
              rw [Metric.mem_closedBall, dist_zero_right]
              have hre_m := (hN₀ (m + N₀) (Nat.le_add_left _ _)).2
              have habs : |(ζ_seq (m + N₀)).re| < r₀ := abs_lt.mpr hre_m
              have h_prod : |(ζ_seq (m + N₀)).re| * ‖θ₀‖ ≤ 1 / 4 := by
                have h1 : |(ζ_seq (m + N₀)).re| * (‖θ₀‖ + 1) ≤ r₀ * (‖θ₀‖ + 1) :=
                  mul_le_mul_of_nonneg_right habs.le (by positivity)
                have h2 : r₀ * (‖θ₀‖ + 1) = 1 / 4 := by
                  dsimp [r₀]
                  field_simp
                nlinarith [abs_nonneg (ζ_seq (m + N₀)).re]
              calc ‖u₀ + (ζ_seq (m + N₀)).re • θ₀‖
                  ≤ ‖u₀‖ + ‖(ζ_seq (m + N₀)).re • θ₀‖ := norm_add_le _ _
                _ = ‖u₀‖ + |(ζ_seq (m + N₀)).re| * ‖θ₀‖ := by
                    rw [norm_smul, Real.norm_eq_abs]
                _ ≤ 1 / 2 := by linarith
            have hu_lim : Tendsto u_seq atTop (𝓝 u_star) := by
              have hre_t := (Complex.continuous_re.tendsto z₀).comp
                ((tendsto_nhds_of_tendsto_nhdsWithin hζ_seq).comp (tendsto_add_atTop_nat N₀))
              exact tendsto_const_nhds.add (hre_t.smul tendsto_const_nhds)
            refine (tubeConv_seq_tendsto_zero_of_bdy_cc hD_diff hθ₀ hD_bdy_cc hε hε_le
              t_seq ht_pos ht_lim u_seq u_star hu_mem hu_lim).congr fun m => ?_
            dsimp [F_ε]
            rw [if_pos (ht_pos m)]
            congr 1
            ext p
            dsimp [u_seq, t_seq]
            have hζ_eq : ζ_seq (m + N₀) =
                ((ζ_seq (m + N₀)).re : ℂ) + ((ζ_seq (m + N₀)).im : ℂ) * Complex.I :=
              (Complex.re_add_im _).symm
            conv_rhs => rw [hζ_eq]
            push_cast
            ring
          let S_up : Set ℂ := {ζ : ℂ | 0 < ζ.im}
          have h_neg_part : Tendsto F_ε (𝓝[S_upᶜ] z₀) (𝓝 0) :=
            tendsto_const_nhds.congr' (by
              filter_upwards [self_mem_nhdsWithin] with ζ (hζ : ¬ 0 < ζ.im)
              exact (if_neg hζ).symm)
          have h_sup : 𝓝 z₀ = (𝓝[S_up] z₀) ⊔ (𝓝[S_upᶜ] z₀) := by
            rw [← nhdsWithin_union, Set.union_compl_self, nhdsWithin_univ]
          rw [h_sup]
          exact h_pos_part.sup h_neg_part
    have hF_ana_slit : AnalyticOn ℂ F_ε (Analysis.slitDomain (Set.Ioo (-r₀) r₀)) :=
      Analysis.eow_1d_continuous (Set.Ioo (-r₀) r₀) isOpen_Ioo F_ε
        hF_cont hF_ana_pos hF_ana_neg
    have h0_mem : (0 : ℂ) ∈ Analysis.slitDomain (Set.Ioo (-r₀) r₀) :=
      Or.inr (by simp [hr₀_pos])
    have hF_at0 : AnalyticAt ℂ F_ε (0 : ℝ) := by
      simpa using ((Analysis.isOpen_slitDomain isOpen_Ioo).analyticOn_iff_analyticOnNhd.mp
        hF_ana_slit) 0 h0_mem
    have hF_real0 : ∀ᶠ s : ℝ in 𝓝 0, F_ε (s : ℂ) = 0 := by
      filter_upwards with s
      dsimp [F_ε]
      simp
    have hF_nhds0 : ∀ᶠ ζ : ℂ in 𝓝 (0 : ℂ), F_ε ζ = 0 := by
      simpa using Analysis.analytic_nhds_eq_of_real_eq_1D F_ε 0 0
        hF_at0 analyticAt_const hF_real0
    rcases Metric.mem_nhds_iff.mp hF_nhds0 with ⟨δ₀, hδ₀, hF_ball⟩
    let ζ₁ : ℂ := ((δ₀ / 2 : ℝ) : ℂ) * Complex.I
    have hζ₁_uhp : ζ₁ ∈ Analysis.upperHalfPlane := by
      change 0 < ζ₁.im
      simp [ζ₁, half_pos hδ₀]
    have h_open_uhp : IsOpen Analysis.upperHalfPlane :=
      isOpen_lt continuous_const Complex.continuous_im
    have h_conv_uhp : Convex ℝ Analysis.upperHalfPlane := by
      intro a ha b hb c₁ c₂ hc₁ hc₂ hc₁₂
      change 0 < (c₁ • a + c₂ • b).im
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rcases eq_or_lt_of_le hc₁ with rfl | hc₁_pos
      · simp only [zero_add] at hc₁₂
        rw [hc₁₂, zero_mul, zero_add, one_mul]
        exact hb
      · have : 0 < a.im := ha
        have : 0 < b.im := hb
        nlinarith
    have hF_nhds_ζ₁ : ∀ᶠ ζ : ℂ in 𝓝 ζ₁, F_ε ζ = 0 := by
      have hζ₁_in : ζ₁ ∈ Metric.ball (0 : ℂ) δ₀ := by
        rw [Metric.mem_ball, dist_zero_right]
        have h_norm : ‖ζ₁‖ = δ₀ / 2 := by
          simp only [ζ₁, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, abs_of_pos (half_pos hδ₀)]
        rw [h_norm]
        exact half_lt_self hδ₀
      filter_upwards [Metric.isOpen_ball.mem_nhds hζ₁_in] with ζ hζ
      exact hF_ball hζ
    have hF_uhp_zero := (h_open_uhp.analyticOn_iff_analyticOnNhd.mp hF_ana_pos
      ).eqOn_zero_of_preconnected_of_eventuallyEq_zero h_conv_uhp.isPreconnected
      hζ₁_uhp hF_nhds_ζ₁
    have hI_uhp : Complex.I ∈ Analysis.upperHalfPlane := by
      change 0 < Complex.I.im
      simp
    have hFI : F_ε Complex.I = 0 := hF_uhp_zero hI_uhp
    have hFI_eq : F_ε Complex.I = G_ε (fun p => (u₀ p : ℂ) + Complex.I * (θ₀ p : ℂ)) :=
      if_pos (by simp : 0 < Complex.I.im)
    rw [hFI_eq] at hFI
    simpa [mul_comm Complex.I] using hFI
  simpa [G_ε] using h_ball_zero 0 (Metric.mem_ball_self (by norm_num))

omit [Fintype ι] [DecidableEq ι] in
private lemma tubeConv_eq_zero_of_bdy_cc_eps
    {n : ℕ} {D_flat : (Fin (n * 4) → ℂ) → ℂ}
    (hD_diff : DifferentiableOn ℂ D_flat (TubeDomain (forwardTubeConeFlat n)))
    {θ₀ : Fin (n * 4) → ℝ} (hθ₀ : θ₀ ∈ forwardTubeConeFlat n)
    (hD_bdy_cc : ∀ (φ : (Fin (n * 4) → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Tendsto (fun t : ℝ => ∫ u : Fin (n * 4) → ℝ,
        D_flat (fun p => (u p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) * φ u)
        (𝓝[>] 0) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε_le : ε ≤ 1 / 2) :
    let ψ := Distribution.unitMollifier (n * 4) (half_pos hε)
    let Φ_ε : (Fin (n * 4) → ℝ) → ℝ := fun s => ∫ v : Fin (n * 4) → ℝ, ψ v * ψ (v - s)
    ∀ w ∈ TubeDomain (forwardTubeConeFlat n), Distribution.tubeConv D_flat Φ_ε w = 0 := by
  let d : ℕ := n * 4
  let U_flat : Set (Fin d → ℂ) := TubeDomain (forwardTubeConeFlat n)
  have hU_open : IsOpen U_flat := isOpen_TubeDomain (isOpen_forwardTubeConeFlat n)
  have hU_conv : Convex ℝ U_flat := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    have h_im : (fun p => ((a • w₁ + b • w₂) p).im) =
        a • (fun p => (w₁ p).im) + b • (fun p => (w₂ p).im) := by
      ext p; simp
    change (fun p => ((a • w₁ + b • w₂) p).im) ∈ forwardTubeConeFlat n
    rw [h_im]
    exact convex_forwardTubeConeFlat n hw₁ hw₂ ha hb hab
  intro ψ Φ_ε
  have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := Distribution.contDiff_unitMollifier d (half_pos hε)
  have hψ_supp : HasCompactSupport ψ :=
    Distribution.hasCompactSupport_unitMollifier d (half_pos hε)
  have h_eq_Φ : Φ_ε = ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x => ψ (-x)) := by
    ext s
    rw [MeasureTheory.convolution_def]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    change ψ v * ψ (v - s) = ψ v * ψ (-(s - v))
    rw [neg_sub]
  have hΦ_cd : ContDiff ℝ (⊤ : ℕ∞) Φ_ε := by
    rw [h_eq_Φ]
    exact (hψ_supp.comp_homeomorph (Homeomorph.neg _)).contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hψ_cd.continuous.locallyIntegrable
      (hψ_cd.comp contDiff_neg)
  have hΦ_supp : HasCompactSupport Φ_ε := by
    rw [h_eq_Φ]
    exact hψ_supp.convolution (ContinuousLinearMap.mul ℝ ℝ)
      (hψ_supp.comp_homeomorph (Homeomorph.neg _))
  let G_ε : (Fin d → ℂ) → ℂ := Distribution.tubeConv D_flat Φ_ε
  have hG_diff : DifferentiableOn ℂ G_ε U_flat :=
    Distribution.differentiableOn_tubeConv (isOpen_forwardTubeConeFlat n)
      hD_diff hΦ_cd.continuous hΦ_supp
  let w₀ : Fin d → ℂ := fun p => (θ₀ p : ℂ) * Complex.I
  have hw₀ : w₀ ∈ U_flat := by
    change (fun p => (w₀ p).im) ∈ forwardTubeConeFlat n
    have him : (fun p => (w₀ p).im) = θ₀ := by ext p; simp [w₀]
    rwa [him]
  refine differentiableOn_eq_zero_of_convex_shifted_real hU_open hU_conv hw₀ hG_diff (fun u₀ => ?_)
  let D_sh : (Fin d → ℂ) → ℂ := fun w => D_flat (w + fun p => (u₀ p : ℂ))
  have hD_sh_diff : DifferentiableOn ℂ D_sh U_flat := by
    refine hD_diff.comp (differentiable_id.add (differentiable_const _)).differentiableOn
      (fun w hw => ?_)
    change (fun p => ((w + fun q => (u₀ q : ℂ)) p).im) ∈ forwardTubeConeFlat n
    have him : (fun p => ((w + fun q => (u₀ q : ℂ)) p).im) = fun p => (w p).im := by
      ext p; simp
    rwa [him]
  have hD_sh_bdy : ∀ (φ : (Fin d → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Tendsto (fun t : ℝ => ∫ u : Fin d → ℝ,
        D_sh (fun p => (u p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) * φ u)
        (𝓝[>] 0) (𝓝 0) := by
    intro φ hφ_cd hφ_supp
    let φ_sh : (Fin d → ℝ) → ℂ := fun s => φ (s - u₀)
    have hφ_sh_cd : ContDiff ℝ (⊤ : ℕ∞) φ_sh :=
      hφ_cd.comp (contDiff_id.sub contDiff_const)
    have hφ_sh_supp : HasCompactSupport φ_sh :=
      hφ_supp.comp_homeomorph (Homeomorph.subRight u₀)
    refine (hD_bdy_cc φ_sh hφ_sh_cd hφ_sh_supp).congr fun t => ?_
    let g_s : (Fin d → ℝ) → ℂ := fun s =>
      D_flat (fun p => (s p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) * φ_sh s
    have h_add := MeasureTheory.integral_add_right_eq_self (μ := volume) g_s u₀
    refine h_add.symm.trans
      (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_))
    dsimp [g_s, φ_sh, D_sh]
    rw [add_sub_cancel_right]
    congr 2
    ext p
    simp
    ring
  have h0_sh := tubeConv_eq_zero_at_base_of_bdy_cc_eps hD_sh_diff hθ₀ hD_sh_bdy hε hε_le
  have h_tc_eq : G_ε ((fun p => (u₀ p : ℂ)) + w₀) =
      Distribution.tubeConv D_sh Φ_ε w₀ := by
    dsimp [G_ε, Distribution.tubeConv, D_sh, w₀]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    dsimp only
    congr 2
    ext p
    simp
    ring
  exact h_tc_eq.trans h0_sh

omit [Fintype ι] [DecidableEq ι] in
theorem tubeExtension_eq_of_wightman_eq {W : WightmanFamily ι}
    (E₁ E₂ : TubeExtension W) (n : ℕ) (α : Fin n → ι)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    E₁.H n α z = E₂.H n α z := by
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  rcases n with _ | _ | n_pred
  · let f₀ : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ := momentumWavepacketSchwartz 0 0
    have h_int1 : ∀ t : ℝ,
        (∫ x : Fin 0 → Fin 4 → ℝ,
          E₁.H 0 α (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f₀ x) =
        E₁.H 0 α z := by
      intro t
      have h_sub : (fun x : Fin 0 → Fin 4 → ℝ =>
          E₁.H 0 α (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f₀ x) =
          fun x => E₁.H 0 α z * f₀ x := by
        ext x
        congr 2
        exact Subsingleton.elim _ z
      rw [h_sub, MeasureTheory.integral_const_mul,
          integral_momentumWavepacketSchwartz_zero 0, mul_one]
    have h_int2 : ∀ t : ℝ,
        (∫ x : Fin 0 → Fin 4 → ℝ,
          E₂.H 0 α (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f₀ x) =
        E₂.H 0 α z := by
      intro t
      have h_sub : (fun x : Fin 0 → Fin 4 → ℝ =>
          E₂.H 0 α (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f₀ x) =
          fun x => E₂.H 0 α z * f₀ x := by
        ext x
        congr 2
        exact Subsingleton.elim _ z
      rw [h_sub, MeasureTheory.integral_const_mul,
          integral_momentumWavepacketSchwartz_zero 0, mul_one]
    have hb1 := E₁.boundary 0 α f₀ unit_time_vector hv
    have hb2 := E₂.boundary 0 α f₀ unit_time_vector hv
    simp_rw [h_int1] at hb1
    simp_rw [h_int2] at hb2
    exact (tendsto_nhds_unique tendsto_const_nhds hb1).trans
      (tendsto_nhds_unique tendsto_const_nhds hb2).symm
  · let D : (Fin 1 → Fin 4 → ℂ) → ℂ := fun w => E₁.H 1 α w - E₂.H 1 α w
    have h_univ : forward_tube_n 1 = Set.univ := by
      ext w
      simp only [Set.mem_univ, iff_true]
      intro i hi
      have hi0 : i.val = 0 := Fin.val_eq_zero i
      omega
    have hD_diff : DifferentiableOn ℂ D Set.univ := by
      rw [← h_univ]
      exact ((E₁.analytic 1 α).sub (E₂.analytic 1 α)).differentiableOn
    have hD_int_zero : ∀ (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ),
        HasCompactSupport (f : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        ∫ x : Fin 1 → Fin 4 → ℝ, D (fun i k => (x i k : ℂ)) * f x = 0 := by
      intro f hf_supp
      have hb := (E₁.boundary 1 α f unit_time_vector hv).sub
        (E₂.boundary 1 α f unit_time_vector hv)
      rw [sub_self] at hb
      have hcont1 : Continuous (fun x : Fin 1 → Fin 4 → ℝ => E₁.H 1 α (fun i k => (x i k : ℂ))) :=
        (E₁.analytic 1 α).continuousOn.comp_continuous
          (continuous_pi fun i => continuous_pi fun k =>
            Complex.continuous_ofReal.comp ((continuous_apply k).comp (continuous_apply i)))
          (fun _ => by rw [h_univ]; trivial)
      have hcont2 : Continuous (fun x : Fin 1 → Fin 4 → ℝ => E₂.H 1 α (fun i k => (x i k : ℂ))) :=
        (E₂.analytic 1 α).continuousOn.comp_continuous
          (continuous_pi fun i => continuous_pi fun k =>
            Complex.continuous_ofReal.comp ((continuous_apply k).comp (continuous_apply i)))
          (fun _ => by rw [h_univ]; trivial)
      have hint1 : Integrable (fun x : Fin 1 → Fin 4 → ℝ =>
          E₁.H 1 α (fun i k => (x i k : ℂ)) * f x) :=
        (hcont1.mul f.continuous).integrable_of_hasCompactSupport hf_supp.mul_left
      have hint2 : Integrable (fun x : Fin 1 → Fin 4 → ℝ =>
          E₂.H 1 α (fun i k => (x i k : ℂ)) * f x) :=
        (hcont2.mul f.continuous).integrable_of_hasCompactSupport hf_supp.mul_left
      have h_const : (fun t : ℝ =>
          (∫ x : Fin 1 → Fin 4 → ℝ,
            E₁.H 1 α (fun i k => (x i k : ℂ) +
              Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f x) -
          (∫ x : Fin 1 → Fin 4 → ℝ,
            E₂.H 1 α (fun i k => (x i k : ℂ) +
              Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f x)) =
          fun _ => ∫ x : Fin 1 → Fin 4 → ℝ, D (fun i k => (x i k : ℂ)) * f x := by
        ext t
        simp_rw [shift_zero_of_fin_one]
        rw [← MeasureTheory.integral_sub hint1 hint2]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp [D]
        ring
      rw [h_const] at hb
      exact tendsto_nhds_unique tendsto_const_nhds hb
    let D_flat : (Fin (1 * 4) → ℂ) → ℂ := fun w => D ((spacetimeFlatCLE_C 1).symm w)
    have hDf_diff : DifferentiableOn ℂ D_flat (TubeDomain (Set.univ : Set (Fin (1 * 4) → ℝ))) := by
      have h_tu : TubeDomain (Set.univ : Set (Fin (1 * 4) → ℝ)) = Set.univ := by
        ext w; simp [TubeDomain]
      rw [h_tu]
      exact hD_diff.comp (spacetimeFlatCLE_C 1).symm.toContinuousLinearMap.differentiableOn
        (Set.mapsTo_univ _ _)
    let ε_seq : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
    have hε_pos : ∀ k, 0 < ε_seq k := fun k => by dsimp [ε_seq]; positivity
    have hε_lim : Tendsto ε_seq atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h_real : ∀ u₀ : Fin (1 * 4) → ℝ, D_flat (fun p => (u₀ p : ℂ)) = 0 := by
      intro u₀
      have h_tc_zero : ∀ k : ℕ,
          Distribution.tubeConv D_flat (Distribution.unitMollifier (1 * 4) (hε_pos k))
            (fun p => (u₀ p : ℂ)) = 0 := by
        intro k
        let χ := Distribution.unitMollifier (1 * 4) (hε_pos k)
        let φ : (Fin (1 * 4) → ℝ) → ℂ := fun s => (χ (u₀ - s) : ℂ)
        have hφ_cd : ContDiff ℝ (⊤ : ℕ∞) φ :=
          Complex.ofRealCLM.contDiff.comp
            ((Distribution.contDiff_unitMollifier (1 * 4) (hε_pos k)).comp
              (contDiff_const.sub contDiff_id))
        have hφ_supp : HasCompactSupport φ :=
          ((Distribution.hasCompactSupport_unitMollifier (1 * 4) (hε_pos k)).comp_homeomorph
            (Homeomorph.subLeft u₀)).comp_left Complex.ofReal_zero
        let ψ_S : SchwartzMap (Fin (1 * 4) → ℝ) ℂ := hφ_supp.toSchwartzMap hφ_cd
        let f_S : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := schwartzFlatCLM 1 ψ_S
        have hf_supp : HasCompactSupport (f_S : (Fin 1 → Fin 4 → ℝ) → ℂ) :=
          hφ_supp.comp_homeomorph (spacetimeFlatCLE 1).toHomeomorph
        have h0 := hD_int_zero f_S hf_supp
        have h_eq_int : Distribution.tubeConv D_flat χ (fun p => (u₀ p : ℂ)) =
            ∫ x : Fin 1 → Fin 4 → ℝ, D (fun i μ => (x i μ : ℂ)) * f_S x := by
          dsimp [Distribution.tubeConv]
          let g_s : (Fin (1 * 4) → ℝ) → ℂ := fun s => D_flat (fun p => (s p : ℂ)) * φ s
          have h_lhs_congr : (∫ t : Fin (1 * 4) → ℝ,
              D_flat (fun p => (u₀ p : ℂ) - (t p : ℂ)) * (χ t : ℂ)) =
              ∫ t : Fin (1 * 4) → ℝ, g_s (u₀ - t) := by
            refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            dsimp [g_s, φ]
            rw [sub_sub_cancel]
            congr 2
            ext p
            simp
          rw [h_lhs_congr, MeasureTheory.integral_sub_left_eq_self g_s volume u₀,
              ← integral_comp_spacetimeFlatCLE 1]
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp [g_s, D_flat, f_S, ψ_S]
          have h_symm : (spacetimeFlatCLE_C 1).symm (fun p => (spacetimeFlatCLE 1 x p : ℂ)) =
              fun i μ => (x i μ : ℂ) := by
            ext i μ
            simp only [spacetimeFlatCLE_C_symm_apply, spacetimeFlatCLE_apply,
              Equiv.symm_apply_apply]
          rw [h_symm]
          rfl
        exact h_eq_int.trans h0
      have h_tend := Distribution.tendsto_tubeConv_unitMollifier isOpen_univ
        hDf_diff.continuousOn (by simp [TubeDomain] : (fun p => (u₀ p : ℂ)) ∈ TubeDomain Set.univ)
        hε_pos hε_lim
      simp_rw [h_tc_zero] at h_tend
      exact (tendsto_nhds_unique tendsto_const_nhds h_tend).symm
    have hDf_all : ∀ w ∈ (Set.univ : Set (Fin (1 * 4) → ℂ)), D_flat w = 0 := by
      have hDf_univ : DifferentiableOn ℂ D_flat Set.univ := by
        have h_tu : TubeDomain (Set.univ : Set (Fin (1 * 4) → ℝ)) = Set.univ := by
          ext w; simp [TubeDomain]
        rwa [h_tu] at hDf_diff
      exact differentiableOn_eq_zero_of_convex_shifted_real isOpen_univ convex_univ
        (Set.mem_univ (0 : Fin (1 * 4) → ℂ)) hDf_univ
        (fun u₀ => by simpa using h_real u₀)
    have hz_eq := hDf_all (spacetimeFlatCLE_C 1 z) trivial
    dsimp [D_flat, D] at hz_eq
    rw [ContinuousLinearEquiv.symm_apply_apply] at hz_eq
    exact sub_eq_zero.mp hz_eq
  · let n : ℕ := n_pred + 2
    let d : ℕ := n * 4
    let U_flat : Set (Fin d → ℂ) := TubeDomain (forwardTubeConeFlat n)
    have hU_open : IsOpen U_flat := isOpen_TubeDomain (isOpen_forwardTubeConeFlat n)
    let D_flat : (Fin d → ℂ) → ℂ := fun w => tubeForwardFlat E₁ n α w - tubeForwardFlat E₂ n α w
    have hD_diff : DifferentiableOn ℂ D_flat U_flat :=
      (differentiableOn_tubeForwardFlat E₁ n α).sub (differentiableOn_tubeForwardFlat E₂ n α)
    let θ₀ : Fin d → ℝ := tubeBaseImFlat n
    have hθ₀ : θ₀ ∈ forwardTubeConeFlat n := tubeBaseImFlat_mem_forwardTubeConeFlat n
    have hD_bdy_cc : ∀ (φ : (Fin d → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        Tendsto (fun t : ℝ => ∫ u : Fin d → ℝ,
          D_flat (fun p => (u p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) * φ u)
          (𝓝[>] 0) (𝓝 0) := by
      intro φ hφ_cd hφ_supp
      let ψ_S : SchwartzMap (Fin d → ℝ) ℂ := hφ_supp.toSchwartzMap hφ_cd
      let f_S : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := schwartzFlatCLM n ψ_S
      have hf_supp : HasCompactSupport (f_S : (Fin n → Fin 4 → ℝ) → ℂ) :=
        hφ_supp.comp_homeomorph (spacetimeFlatCLE n).toHomeomorph
      have hb := (E₁.boundary n α f_S unit_time_vector hv).sub
        (E₂.boundary n α f_S unit_time_vector hv)
      rw [sub_self] at hb
      refine hb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hz_mem : ∀ x : Fin n → Fin 4 → ℝ,
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) ∈
            forward_tube_n n := fun x =>
        tubeApproach_mem_forward_tube_n n x unit_time_vector hv t ht
      have h_line_cont : Continuous (fun x : Fin n → Fin 4 → ℝ =>
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ))) :=
        continuous_pi fun i => continuous_pi fun k =>
          (Complex.continuous_ofReal.comp
            ((continuous_apply k).comp (continuous_apply i))).add continuous_const
      have hint1 : Integrable (fun x : Fin n → Fin 4 → ℝ =>
          E₁.H n α (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f_S x) :=
        (((E₁.analytic n α).continuousOn.comp_continuous h_line_cont hz_mem).mul
          f_S.continuous).integrable_of_hasCompactSupport hf_supp.mul_left
      have hint2 : Integrable (fun x : Fin n → Fin 4 → ℝ =>
          E₂.H n α (fun i k => (x i k : ℂ) +
            Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f_S x) :=
        (((E₂.analytic n α).continuousOn.comp_continuous h_line_cont hz_mem).mul
          f_S.continuous).integrable_of_hasCompactSupport hf_supp.mul_left
      rw [← MeasureTheory.integral_sub hint1 hint2, ← integral_comp_spacetimeFlatCLE n]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have h_symm_pt : (spacetimeFlatCLE_C n).symm
          (fun p => (spacetimeFlatCLE n x p : ℂ) + ((t * θ₀ p : ℝ) : ℂ) * Complex.I) =
          fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ) := by
        ext i k
        simp only [spacetimeFlatCLE_C_symm_apply, θ₀, tubeBaseImFlat, spacetimeFlatCLE_apply,
          Equiv.symm_apply_apply]
        push_cast
        ring
      have h_fS : f_S x = φ (spacetimeFlatCLE n x) := rfl
      change (E₁.H n α _ * f_S x) - (E₂.H n α _ * f_S x) =
        (E₁.H n α ((spacetimeFlatCLE_C n).symm _) -
          E₂.H n α ((spacetimeFlatCLE_C n).symm _)) * φ (spacetimeFlatCLE n x)
      rw [h_symm_pt, h_fS]
      exact (sub_mul _ _ _).symm
    let z_flat : Fin d → ℂ := spacetimeFlatCLE_C n z
    have hz_flat : z_flat ∈ U_flat := (mem_tubeDomain_forwardTubeConeFlat_iff n z).mpr hz
    let ε_seq : ℕ → ℝ := fun k => ((k : ℝ) + 2)⁻¹
    have hε_pos : ∀ k, 0 < ε_seq k := fun k => by dsimp [ε_seq]; positivity
    have hε_le : ∀ k, ε_seq k ≤ 1 / 2 := fun k => by
      dsimp [ε_seq]
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hε_lim : Tendsto ε_seq atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    let Φ_seq : ℕ → (Fin d → ℝ) → ℝ := fun k s =>
      ∫ v : Fin d → ℝ, Distribution.unitMollifier d (half_pos (hε_pos k)) v *
        Distribution.unitMollifier d (half_pos (hε_pos k)) (v - s)
    have h_tc_all_zero : ∀ k : ℕ, Distribution.tubeConv D_flat (Φ_seq k) z_flat = 0 :=
      fun k => tubeConv_eq_zero_of_bdy_cc_eps hD_diff hθ₀ hD_bdy_cc
        (hε_pos k) (hε_le k) z_flat hz_flat
    have hΦ_props : ∀ k : ℕ,
        ContDiff ℝ (⊤ : ℕ∞) (Φ_seq k) ∧
        (∀ s, 0 ≤ Φ_seq k s) ∧
        (∀ s, s ∉ Metric.closedBall (0 : Fin d → ℝ) (ε_seq k) → Φ_seq k s = 0) ∧
        Integrable (Φ_seq k) volume ∧
        (∫ s : Fin d → ℝ, Φ_seq k s = 1) := by
      intro k
      let ψ := Distribution.unitMollifier d (half_pos (hε_pos k))
      have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ :=
        Distribution.contDiff_unitMollifier d (half_pos (hε_pos k))
      have hψ_supp : HasCompactSupport ψ :=
        Distribution.hasCompactSupport_unitMollifier d (half_pos (hε_pos k))
      have h_eq : Φ_seq k = ψ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x => ψ (-x)) := by
        ext s
        rw [MeasureTheory.convolution_def]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        change ψ v * ψ (v - s) = ψ v * ψ (-(s - v))
        rw [neg_sub]
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (Φ_seq k) := by
        rw [h_eq]
        exact (hψ_supp.comp_homeomorph (Homeomorph.neg _)).contDiff_convolution_right
          (ContinuousLinearMap.mul ℝ ℝ) hψ_cd.continuous.locallyIntegrable
          (hψ_cd.comp contDiff_neg)
      have hsupp : HasCompactSupport (Φ_seq k) := by
        rw [h_eq]
        exact hψ_supp.convolution (ContinuousLinearMap.mul ℝ ℝ)
          (hψ_supp.comp_homeomorph (Homeomorph.neg _))
      have hnn : ∀ s, 0 ≤ Φ_seq k s := fun s =>
        integral_nonneg fun v => mul_nonneg
          (Distribution.nonneg_unitMollifier d (half_pos (hε_pos k)) v)
          (Distribution.nonneg_unitMollifier d (half_pos (hε_pos k)) (v - s))
      have h_out : ∀ s, s ∉ Metric.closedBall (0 : Fin d → ℝ) (ε_seq k) → Φ_seq k s = 0 := by
        intro s hs
        rw [Metric.mem_closedBall, dist_zero_right] at hs
        push Not at hs
        dsimp [Φ_seq]
        have h0_fn : (fun v : Fin d → ℝ => ψ v * ψ (v - s)) = fun _ => 0 := by
          ext v
          by_cases hv_le : ‖v‖ ≤ ε_seq k / 2
          · have hvs : ε_seq k / 2 < ‖v - s‖ := by
              have htri : ‖s‖ ≤ ‖v‖ + ‖v - s‖ := by
                calc ‖s‖ = ‖v - (v - s)‖ := by abel_nf
                  _ ≤ ‖v‖ + ‖v - s‖ := norm_sub_le _ _
              linarith
            have hψ0 : ψ (v - s) = 0 := by
              by_contra hne
              have hm := Distribution.tsupport_unitMollifier_subset d (half_pos (hε_pos k))
                (subset_tsupport ψ hne)
              rw [Metric.mem_closedBall, dist_zero_right] at hm
              linarith
            simp [hψ0]
          · push Not at hv_le
            have hψ0 : ψ v = 0 := by
              by_contra hne
              have hm := Distribution.tsupport_unitMollifier_subset d (half_pos (hε_pos k))
                (subset_tsupport ψ hne)
              rw [Metric.mem_closedBall, dist_zero_right] at hm
              linarith
            simp [hψ0]
        rw [h0_fn, MeasureTheory.integral_zero]
      have hint : Integrable (Φ_seq k) volume :=
        hcd.continuous.integrable_of_hasCompactSupport hsupp
      have hint_one : ∫ s : Fin d → ℝ, Φ_seq k s = 1 := by
        dsimp [Φ_seq]
        have h_prod_int : Integrable (Function.uncurry fun s v : Fin d → ℝ => ψ v * ψ (v - s))
            (volume.prod volume) := by
          have h_cont_p : Continuous (Function.uncurry fun s v : Fin d → ℝ => ψ v * ψ (v - s)) :=
            (hψ_cd.continuous.comp continuous_snd).mul
              (hψ_cd.continuous.comp (continuous_snd.sub continuous_fst))
          have h_supp_p : HasCompactSupport
              (Function.uncurry fun s v : Fin d → ℝ => ψ v * ψ (v - s)) := by
            refine HasCompactSupport.of_support_subset_isCompact
              ((isCompact_closedBall (0 : Fin d → ℝ) (ε_seq k)).prod
                (isCompact_closedBall (0 : Fin d → ℝ) (ε_seq k / 2))) ?_
            rintro ⟨s, v⟩ hsv
            rw [Function.mem_support, Function.uncurry_apply_pair] at hsv
            have hv_ne : ψ v ≠ 0 := left_ne_zero_of_mul hsv
            have hvs_ne : ψ (v - s) ≠ 0 := right_ne_zero_of_mul hsv
            have hv_b := Distribution.tsupport_unitMollifier_subset d (half_pos (hε_pos k))
              (subset_tsupport ψ hv_ne)
            have hvs_b := Distribution.tsupport_unitMollifier_subset d (half_pos (hε_pos k))
              (subset_tsupport ψ hvs_ne)
            refine ⟨?_, hv_b⟩
            rw [Metric.mem_closedBall, dist_zero_right] at hv_b hvs_b ⊢
            have htri : ‖s‖ ≤ ‖v‖ + ‖v - s‖ := by
              calc ‖s‖ = ‖v - (v - s)‖ := by abel_nf
                _ ≤ ‖v‖ + ‖v - s‖ := norm_sub_le _ _
            linarith
          exact h_cont_p.integrable_of_hasCompactSupport h_supp_p
        rw [MeasureTheory.integral_integral_swap h_prod_int]
        have h_inner : ∀ v : Fin d → ℝ,
            (∫ s : Fin d → ℝ, ψ v * ψ (v - s)) = ψ v := by
          intro v
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_sub_left_eq_self ψ volume v,
              Distribution.integral_unitMollifier d (half_pos (hε_pos k)), mul_one]
        simp_rw [h_inner]
        exact Distribution.integral_unitMollifier d (half_pos (hε_pos k))
      exact ⟨hcd, hnn, h_out, hint, hint_one⟩
    have h_tend_fz : Tendsto (fun k => Distribution.tubeConv D_flat (Φ_seq k) z_flat)
        atTop (𝓝 (D_flat z_flat)) := by
      let sh : (Fin d → ℝ) → (Fin d → ℂ) := fun s p => z_flat p - (s p : ℂ)
      have hsh_cont : Continuous sh :=
        continuous_pi fun p =>
          continuous_const.sub (Complex.continuous_ofReal.comp (continuous_apply p))
      have hsh0 : sh 0 = z_flat := by ext p; simp [sh]
      have hf_at : ContinuousAt (D_flat ∘ sh) 0 := by
        have h1 : ContinuousAt D_flat (sh 0) := by
          rw [hsh0]
          exact hD_diff.continuousOn.continuousAt (hU_open.mem_nhds hz_flat)
        exact h1.comp hsh_cont.continuousAt
      rw [Metric.tendsto_atTop]
      intro η hη
      rcases Metric.continuousAt_iff.mp hf_at (η / 2) (half_pos hη) with ⟨δ, hδ, h_close⟩
      rcases (Metric.tendsto_atTop.mp hε_lim) (δ / 2) (half_pos hδ) with ⟨K, hK⟩
      refine ⟨K, fun k hk => ?_⟩
      obtain ⟨hcd_k, hnn_k, hout_k, hint_k, hint1_k⟩ := hΦ_props k
      have hε_lt : ε_seq k < δ := by
        have h1 := hK k hk
        rw [Real.dist_eq, sub_zero, abs_of_pos (hε_pos k)] at h1
        linarith
      have hΦ_int_c : Integrable (fun s => (Φ_seq k s : ℂ)) volume :=
        Complex.ofRealCLM.integrable_comp hint_k
      have h_fz_eq : D_flat z_flat = ∫ s, D_flat z_flat * (Φ_seq k s : ℂ) := by
        rw [MeasureTheory.integral_const_mul, integral_complex_ofReal, hint1_k,
            Complex.ofReal_one, mul_one]
      have hf_int : Integrable (fun s => D_flat (sh s) * (Φ_seq k s : ℂ)) volume := by
        have hsupp_k : HasCompactSupport (Φ_seq k) :=
          HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (ε_seq k))
            (fun s hs => by by_contra hnot; exact hs (hout_k s hnot))
        exact ((hD_diff.continuousOn.comp_continuous hsh_cont
          fun s => Distribution.tube_sub_ofReal_mem hz_flat s).mul
          (Complex.continuous_ofReal.comp hcd_k.continuous)).integrable_of_hasCompactSupport
          ((hsupp_k.comp_left Complex.ofReal_zero).mul_left)
      rw [dist_eq_norm]
      have h_diff_eq : Distribution.tubeConv D_flat (Φ_seq k) z_flat - D_flat z_flat =
          ∫ s, (D_flat (sh s) - D_flat z_flat) * (Φ_seq k s : ℂ) := by
        conv_lhs => rw [h_fz_eq]
        dsimp [Distribution.tubeConv, sh]
        rw [← MeasureTheory.integral_sub hf_int (hΦ_int_c.const_mul (D_flat z_flat))]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => by ring)
      rw [h_diff_eq]
      have h_pt : ∀ s : Fin d → ℝ,
          ‖(D_flat (sh s) - D_flat z_flat) * (Φ_seq k s : ℂ)‖ ≤ (η / 2) * Φ_seq k s := by
        intro s
        by_cases hΦs : Φ_seq k s = 0
        · simp [hΦs]
        · have hs_ball : s ∈ Metric.closedBall (0 : Fin d → ℝ) (ε_seq k) := by
            by_contra hnot
            exact hΦs (hout_k s hnot)
          have hs_δ : dist s 0 < δ := lt_of_le_of_lt (Metric.mem_closedBall.mp hs_ball) hε_lt
          have hf_le : ‖D_flat (sh s) - D_flat z_flat‖ ≤ η / 2 := by
            have hc := h_close hs_δ
            dsimp [Function.comp] at hc
            rw [hsh0, dist_eq_norm] at hc
            exact hc.le
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn_k s)]
          exact mul_le_mul_of_nonneg_right hf_le (hnn_k s)
      calc ‖∫ s, (D_flat (sh s) - D_flat z_flat) * (Φ_seq k s : ℂ)‖
          ≤ ∫ s, (η / 2) * Φ_seq k s :=
            norm_integral_le_of_norm_le (hint_k.const_mul (η / 2))
              (Filter.Eventually.of_forall h_pt)
        _ = η / 2 := by rw [MeasureTheory.integral_const_mul, hint1_k, mul_one]
        _ < η := half_lt_self hη
    simp_rw [h_tc_all_zero] at h_tend_fz
    have hz_zero : D_flat z_flat = 0 := (tendsto_nhds_unique tendsto_const_nhds h_tend_fz).symm
    dsimp [D_flat, tubeForwardFlat, z_flat] at hz_zero
    rw [ContinuousLinearEquiv.symm_apply_apply] at hz_zero
    exact sub_eq_zero.mp hz_zero

omit [Fintype ι] [DecidableEq ι] in
lemma norm_le_max_concatProjCLM (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖x‖ ≤ max ‖concatProjLeftCLM j k x‖ ‖concatProjRightCLM j k x‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr fun s => ?_
  by_cases hs : s.val < j
  · let i : Fin j := Fin.rev ⟨s.val, hs⟩
    have hs_eq : s = Fin.castAdd k (Fin.rev i) := by
      dsimp [i]
      rw [Fin.rev_rev]
      ext
      rfl
    rw [hs_eq]
    exact (norm_le_pi_norm (concatProjLeftCLM j k x) i).trans (le_max_left _ _)
  · have h_ge : j ≤ s.val := by omega
    let t : Fin k := ⟨s.val - j, Nat.sub_lt_left_of_lt_add h_ge s.isLt⟩
    have hs_eq : s = Fin.natAdd j t := by
      ext
      dsimp [t]
      omega
    rw [hs_eq]
    exact (norm_le_pi_norm (concatProjRightCLM j k x) t).trans (le_max_right _ _)

omit [Fintype ι] [DecidableEq ι] in
lemma norm_pow_le_add_concatProjCLM (j k l : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖x‖ ^ l ≤ ‖concatProjLeftCLM j k x‖ ^ l + ‖concatProjRightCLM j k x‖ ^ l := by
  have h1 := pow_le_pow_left₀ (norm_nonneg x) (norm_le_max_concatProjCLM j k x) l
  rcases le_total ‖concatProjLeftCLM j k x‖ ‖concatProjRightCLM j k x‖ with hle | hle
  · rw [max_eq_right hle] at h1
    exact h1.trans (le_add_of_nonneg_left (pow_nonneg (norm_nonneg _) l))
  · rw [max_eq_left hle] at h1
    exact h1.trans (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) l))

omit [Fintype ι] [DecidableEq ι] in
lemma norm_iteratedFDeriv_conj_f_comp_concatProjLeft_le (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) (l q : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖concatProjLeftCLM j k x‖ ^ l *
      ‖iteratedFDeriv ℝ q
        (fun y : Fin (j + k) → Fin 4 → ℝ => (starRingEnd ℂ) (f (concatProjLeftCLM j k y))) x‖ ≤
      SchwartzMap.seminorm ℝ l q f := by
  let L := concatProjLeftCLM j k
  let C_conj : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap
  have hC_norm : ‖C_conj‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      change ‖(starRingEnd ℂ) w‖ ≤ 1 * ‖w‖
      rw [one_mul, RingHomIsometric.norm_map]
  have hf_sm : ContDiff ℝ (q : ℕ∞) (f : (Fin j → Fin 4 → ℝ) → ℂ) :=
    (f.smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
  have h_fn : (fun y : Fin (j + k) → Fin 4 → ℝ => (starRingEnd ℂ) (f (L y))) =
      C_conj ∘ ((f : (Fin j → Fin 4 → ℝ) → ℂ) ∘ L) := rfl
  rw [h_fn, C_conj.iteratedFDeriv_comp_left (hf_sm.comp L.contDiff).contDiffAt le_rfl]
  have h_c1 : ‖C_conj.compContinuousMultilinearMap
      (iteratedFDeriv ℝ q ((f : (Fin j → Fin 4 → ℝ) → ℂ) ∘ L) x)‖ ≤
      ‖iteratedFDeriv ℝ q ((f : (Fin j → Fin 4 → ℝ) → ℂ) ∘ L) x‖ := by
    have h := C_conj.norm_compContinuousMultilinearMap_le
      (iteratedFDeriv ℝ q ((f : (Fin j → Fin 4 → ℝ) → ℂ) ∘ L) x)
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q ((f : (Fin j → Fin 4 → ℝ) → ℂ) ∘ L) x)]
  have h_c2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ q (f : (Fin j → Fin 4 → ℝ) → ℂ) (L x)) (fun _ : Fin q => L)
  rw [← L.iteratedFDeriv_comp_right hf_sm x le_rfl] at h_c2
  have h_prod : (∏ _ : Fin q, ‖L‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg L) (fun _ _ => opNorm_concatProjLeftCLM_le_one j k)
  have h_le_f : ‖C_conj.compContinuousMultilinearMap
      (iteratedFDeriv ℝ q ((f : (Fin j → Fin 4 → ℝ) → ℂ) ∘ L) x)‖ ≤
      ‖iteratedFDeriv ℝ q (f : (Fin j → Fin 4 → ℝ) → ℂ) (L x)‖ := by
    have h_pnn : 0 ≤ ∏ _ : Fin q, ‖L‖ := Finset.prod_nonneg fun _ _ => norm_nonneg L
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (f : (Fin j → Fin 4 → ℝ) → ℂ) (L x))]
  calc ‖L x‖ ^ l * ‖C_conj.compContinuousMultilinearMap _‖
      ≤ ‖L x‖ ^ l * ‖iteratedFDeriv ℝ q (f : (Fin j → Fin 4 → ℝ) → ℂ) (L x)‖ :=
        mul_le_mul_of_nonneg_left h_le_f (pow_nonneg (norm_nonneg _) l)
    _ ≤ SchwartzMap.seminorm ℝ l q f := SchwartzMap.le_seminorm ℝ l q f (L x)

omit [Fintype ι] [DecidableEq ι] in
lemma norm_iteratedFDeriv_g_comp_concatProjRight_le (j k : ℕ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) (l q : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    ‖concatProjRightCLM j k x‖ ^ l *
      ‖iteratedFDeriv ℝ q
        (fun y : Fin (j + k) → Fin 4 → ℝ => g (concatProjRightCLM j k y)) x‖ ≤
      SchwartzMap.seminorm ℝ l q g := by
  let R_p := concatProjRightCLM j k
  have hg_sm : ContDiff ℝ (q : ℕ∞) (g : (Fin k → Fin 4 → ℝ) → ℂ) :=
    (g.smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
  have h_fn : (fun y : Fin (j + k) → Fin 4 → ℝ => g (R_p y)) =
      (g : (Fin k → Fin 4 → ℝ) → ℂ) ∘ R_p := rfl
  rw [h_fn, R_p.iteratedFDeriv_comp_right hg_sm x le_rfl]
  have h_c2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ q (g : (Fin k → Fin 4 → ℝ) → ℂ) (R_p x)) (fun _ : Fin q => R_p)
  have h_prod : (∏ _ : Fin q, ‖R_p‖) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg R_p)
      (fun _ _ => opNorm_concatProjRightCLM_le_one j k)
  have h_le_g : ‖(iteratedFDeriv ℝ q (g : (Fin k → Fin 4 → ℝ) → ℂ) (R_p x)).compContinuousLinearMap
      (fun _ : Fin q => R_p)‖ ≤
      ‖iteratedFDeriv ℝ q (g : (Fin k → Fin 4 → ℝ) → ℂ) (R_p x)‖ := by
    have h_pnn : 0 ≤ ∏ _ : Fin q, ‖R_p‖ := Finset.prod_nonneg fun _ _ => norm_nonneg R_p
    nlinarith [norm_nonneg (iteratedFDeriv ℝ q (g : (Fin k → Fin 4 → ℝ) → ℂ) (R_p x))]
  calc ‖R_p x‖ ^ l * ‖(iteratedFDeriv ℝ q (g : (Fin k → Fin 4 → ℝ) → ℂ) (R_p x)
          ).compContinuousLinearMap (fun _ => R_p)‖
      ≤ ‖R_p x‖ ^ l * ‖iteratedFDeriv ℝ q (g : (Fin k → Fin 4 → ℝ) → ℂ) (R_p x)‖ :=
        mul_le_mul_of_nonneg_left h_le_g (pow_nonneg (norm_nonneg _) l)
    _ ≤ SchwartzMap.seminorm ℝ l q g := SchwartzMap.le_seminorm ℝ l q g (R_p x)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def borchersConcatSchwartz (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ where
  toFun x := (starRingEnd ℂ) (f (concatProjLeftCLM j k x)) * g (concatProjRightCLM j k x)
  smooth' :=
    (Complex.conjCLE.contDiff.comp ((f.smooth ⊤).comp (concatProjLeftCLM j k).contDiff)).mul
      ((g.smooth ⊤).comp (concatProjRightCLM j k).contDiff)
  decay' l m := by
    let B_val : ℝ := ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
      (SchwartzMap.seminorm ℝ l q f * SchwartzMap.seminorm ℝ 0 (m - q) g +
        SchwartzMap.seminorm ℝ 0 q f * SchwartzMap.seminorm ℝ l (m - q) g)
    refine ⟨B_val, fun x => ?_⟩
    let fL : (Fin (j + k) → Fin 4 → ℝ) → ℂ := fun y => (starRingEnd ℂ) (f (concatProjLeftCLM j k y))
    let gR : (Fin (j + k) → Fin 4 → ℝ) → ℂ := fun y => g (concatProjRightCLM j k y)
    have hfL_sm : ContDiff ℝ (⊤ : ℕ∞) fL :=
      Complex.conjCLE.contDiff.comp ((f.smooth ⊤).comp (concatProjLeftCLM j k).contDiff)
    have hgR_sm : ContDiff ℝ (⊤ : ℕ∞) gR :=
      (g.smooth ⊤).comp (concatProjRightCLM j k).contDiff
    have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fL) (g := gR) (n := m) (N := (⊤ : ℕ∞))
      hfL_sm hgR_sm x (WithTop.coe_le_coe.mpr le_top)
    have h_pow := norm_pow_le_add_concatProjCLM j k l x
    calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => fL y * gR y) x‖
        ≤ (‖concatProjLeftCLM j k x‖ ^ l + ‖concatProjRightCLM j k x‖ ^ l) *
            ∑ q ∈ Finset.range (m + 1),
              (m.choose q : ℝ) * ‖iteratedFDeriv ℝ q fL x‖ * ‖iteratedFDeriv ℝ (m - q) gR x‖ :=
          mul_le_mul h_pow h_leib (norm_nonneg _)
            (add_nonneg (pow_nonneg (norm_nonneg _) l) (pow_nonneg (norm_nonneg _) l))
      _ = ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
            ((‖concatProjLeftCLM j k x‖ ^ l * ‖iteratedFDeriv ℝ q fL x‖) *
              (‖concatProjRightCLM j k x‖ ^ 0 * ‖iteratedFDeriv ℝ (m - q) gR x‖) +
            (‖concatProjLeftCLM j k x‖ ^ 0 * ‖iteratedFDeriv ℝ q fL x‖) *
              (‖concatProjRightCLM j k x‖ ^ l * ‖iteratedFDeriv ℝ (m - q) gR x‖)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [pow_zero, one_mul]
          ring
      _ ≤ B_val := by
          refine Finset.sum_le_sum fun q _ => ?_
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Nat.cast_nonneg _)
          · exact mul_le_mul
              (norm_iteratedFDeriv_conj_f_comp_concatProjLeft_le j k f l q x)
              (norm_iteratedFDeriv_g_comp_concatProjRight_le j k g 0 (m - q) x)
              (by positivity) (apply_nonneg _ _)
          · exact mul_le_mul
              (norm_iteratedFDeriv_conj_f_comp_concatProjLeft_le j k f 0 q x)
              (norm_iteratedFDeriv_g_comp_concatProjRight_le j k g l (m - q) x)
              (by positivity) (apply_nonneg _ _)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma borchersConcatSchwartz_apply (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (x : Fin (j + k) → Fin 4 → ℝ) :
    borchersConcatSchwartz j k f g x =
      (starRingEnd ℂ) (f (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        g (fun i => x (Fin.natAdd j i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma borchersConcatSchwartz_eq_wightmanConcatSchwartz (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) :
    borchersConcatSchwartz j k f.val g.val = wightmanConcatSchwartz j k f g := by
  ext x
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma seminorm_borchersConcatSchwartz_le (j k l m : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    SchwartzMap.seminorm ℝ l m (borchersConcatSchwartz j k f g) ≤
      ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
        (SchwartzMap.seminorm ℝ l q f * SchwartzMap.seminorm ℝ 0 (m - q) g +
          SchwartzMap.seminorm ℝ 0 q f * SchwartzMap.seminorm ℝ l (m - q) g) := by
  let B_val : ℝ := ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
    (SchwartzMap.seminorm ℝ l q f * SchwartzMap.seminorm ℝ 0 (m - q) g +
      SchwartzMap.seminorm ℝ 0 q f * SchwartzMap.seminorm ℝ l (m - q) g)
  have hB_nn : 0 ≤ B_val := Finset.sum_nonneg fun q _ =>
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
        (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  refine SchwartzMap.seminorm_le_bound ℝ l m (borchersConcatSchwartz j k f g) hB_nn fun x => ?_
  let fL : (Fin (j + k) → Fin 4 → ℝ) → ℂ := fun y => (starRingEnd ℂ) (f (concatProjLeftCLM j k y))
  let gR : (Fin (j + k) → Fin 4 → ℝ) → ℂ := fun y => g (concatProjRightCLM j k y)
  have hfL_sm : ContDiff ℝ (⊤ : ℕ∞) fL :=
    Complex.conjCLE.contDiff.comp ((f.smooth ⊤).comp (concatProjLeftCLM j k).contDiff)
  have hgR_sm : ContDiff ℝ (⊤ : ℕ∞) gR :=
    (g.smooth ⊤).comp (concatProjRightCLM j k).contDiff
  have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fL) (g := gR) (n := m) (N := (⊤ : ℕ∞))
    hfL_sm hgR_sm x (WithTop.coe_le_coe.mpr le_top)
  have h_pow := norm_pow_le_add_concatProjCLM j k l x
  calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (borchersConcatSchwartz j k f g :
          (Fin (j + k) → Fin 4 → ℝ) → ℂ) x‖
      ≤ (‖concatProjLeftCLM j k x‖ ^ l + ‖concatProjRightCLM j k x‖ ^ l) *
          ∑ q ∈ Finset.range (m + 1),
            (m.choose q : ℝ) * ‖iteratedFDeriv ℝ q fL x‖ * ‖iteratedFDeriv ℝ (m - q) gR x‖ :=
        mul_le_mul h_pow h_leib (norm_nonneg _)
          (add_nonneg (pow_nonneg (norm_nonneg _) l) (pow_nonneg (norm_nonneg _) l))
    _ = ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
          ((‖concatProjLeftCLM j k x‖ ^ l * ‖iteratedFDeriv ℝ q fL x‖) *
            (‖concatProjRightCLM j k x‖ ^ 0 * ‖iteratedFDeriv ℝ (m - q) gR x‖) +
          (‖concatProjLeftCLM j k x‖ ^ 0 * ‖iteratedFDeriv ℝ q fL x‖) *
            (‖concatProjRightCLM j k x‖ ^ l * ‖iteratedFDeriv ℝ (m - q) gR x‖)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [pow_zero, one_mul]
        ring
    _ ≤ B_val := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (Nat.cast_nonneg _)
        · exact mul_le_mul
            (norm_iteratedFDeriv_conj_f_comp_concatProjLeft_le j k f l q x)
            (norm_iteratedFDeriv_g_comp_concatProjRight_le j k g 0 (m - q) x)
            (by positivity) (apply_nonneg _ _)
        · exact mul_le_mul
            (norm_iteratedFDeriv_conj_f_comp_concatProjLeft_le j k f 0 q x)
            (norm_iteratedFDeriv_g_comp_concatProjRight_le j k g l (m - q) x)
            (by positivity) (apply_nonneg _ _)

lemma wightmanBasis_compactSchwartzAdd
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι)
    (f₁ f₂ : CompactSchwartz j) :
    wightmanBasis WData ⟨j, (α, compactSchwartzAdd j f₁ f₂)⟩ =
      wightmanBasis WData ⟨j, (α, f₁)⟩ + wightmanBasis WData ⟨j, (α, f₂)⟩ := by
  dsimp [wightmanBasis]
  rw [← map_add]
  refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
  · rw [inner_add_right, inner_wightmanBasisPre, inner_wightmanBasisPre, inner_wightmanBasisPre]
    simp only [wightmanKernel_mk, wightmanConcatSchwartz_add_right, map_add, mul_add,
      Finset.sum_add_distrib]
  · rw [inner_add_left, inner_wightmanBasisPre, inner_wightmanBasisPre, inner_wightmanBasisPre]
    simp only [wightmanKernel_mk, wightmanConcatSchwartz_add_left, map_add, mul_add,
      Finset.sum_add_distrib]
  · rw [inner_add_left, inner_add_right, inner_add_right,
        inner_wightmanBasisPre, inner_wightmanBasisPre, inner_wightmanBasisPre,
        inner_wightmanBasisPre, inner_wightmanBasisPre]
    simp only [wightmanKernel_mk, wightmanConcatSchwartz_add_left,
      wightmanConcatSchwartz_add_right, map_add, mul_add, Finset.sum_add_distrib]
    abel

lemma wightmanBasis_compactSchwartzSMul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι)
    (c : ℂ) (f : CompactSchwartz j) :
    wightmanBasis WData ⟨j, (α, compactSchwartzSMul j c f)⟩ =
      c • wightmanBasis WData ⟨j, (α, f)⟩ := by
  dsimp [wightmanBasis]
  rw [← map_smul]
  refine completion_coe_eq_of_inner_eq ?_ ?_ ?_
  · rw [inner_smul_right, inner_wightmanBasisPre, inner_wightmanBasisPre]
    simp only [wightmanKernel_mk, wightmanConcatSchwartz_smul_right, map_smul, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => by ring
  · rw [inner_smul_left, inner_wightmanBasisPre, inner_wightmanBasisPre]
    simp only [wightmanKernel_mk, wightmanConcatSchwartz_smul_left, map_smul, smul_eq_mul,
      Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun β _ => by ring
  · rw [inner_smul_left, inner_smul_right, inner_wightmanBasisPre, inner_wightmanBasisPre]
    simp only [wightmanKernel_mk, wightmanConcatSchwartz_smul_left,
      wightmanConcatSchwartz_smul_right, map_smul, smul_eq_mul, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun β _ => by ring

lemma exists_wightmanBasis_seminorm_bound
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι) :
    ∃ (s : Finset (ℕ × ℕ)) (K : ℝ), 0 < K ∧
      ∀ f_c : CompactSchwartz j,
        ‖wightmanBasis WData ⟨j, (α, f_c)⟩‖ ≤
          K * (s.sup (schwartzSeminormFamily ℝ (Fin j → Fin 4 → ℝ) ℂ)) f_c.val := by
  let T_diag : SchwartzMap (Fin (j + j) → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    ∑ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) • WData.W (j + j) (Fin.append (β ∘ Fin.rev) α)
  obtain ⟨s₀, C_T, hCT_pos, hT_bound⟩ := schwartz_clm_bound (j + j) T_diag
  let s : Finset (ℕ × ℕ) :=
    s₀.biUnion fun lm =>
      (Finset.range (lm.2 + 1)).biUnion fun q =>
        {(lm.1, q), (0, lm.2 - q), (0, q), (lm.1, lm.2 - q)}
  let M : ℝ :=
    (∑ lm ∈ s₀, ∑ q ∈ Finset.range (lm.2 + 1), (lm.2.choose q : ℝ) * 2) + 1
  have hM_pos : 0 < M := by
    dsimp [M]
    have h_nn : 0 ≤ ∑ lm ∈ s₀, ∑ q ∈ Finset.range (lm.2 + 1), (lm.2.choose q : ℝ) * 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    linarith
  let K : ℝ := Real.sqrt (C_T * M) + 1
  have hK_pos : 0 < K := by dsimp [K]; positivity
  refine ⟨s, K, hK_pos, fun f_c => ?_⟩
  let fam := schwartzSeminormFamily ℝ (Fin j → Fin 4 → ℝ) ℂ
  let p_s := (s.sup fam) f_c.val
  have hps_nn : 0 ≤ p_s := apply_nonneg _ _
  have h_sup_le : (s₀.sup (schwartzSeminormFamily ℝ (Fin (j + j) → Fin 4 → ℝ) ℂ))
      (borchersConcatSchwartz j j f_c.val f_c.val) ≤ M * p_s ^ 2 := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun lm hlm => ?_
    have h_sem := seminorm_borchersConcatSchwartz_le j j lm.1 lm.2 f_c.val f_c.val
    change SchwartzMap.seminorm ℝ lm.1 lm.2 (borchersConcatSchwartz j j f_c.val f_c.val) ≤ _
    have h_lm_le : SchwartzMap.seminorm ℝ lm.1 lm.2
        (borchersConcatSchwartz j j f_c.val f_c.val) ≤
        (∑ q ∈ Finset.range (lm.2 + 1), (lm.2.choose q : ℝ) * 2) * p_s ^ 2 := by
      refine h_sem.trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun q hq => ?_
      have h_in1 : (lm.1, q) ∈ s := Finset.mem_biUnion.mpr ⟨lm, hlm,
        Finset.mem_biUnion.mpr ⟨q, hq, by simp⟩⟩
      have h_in2 : (0, lm.2 - q) ∈ s := Finset.mem_biUnion.mpr ⟨lm, hlm,
        Finset.mem_biUnion.mpr ⟨q, hq, by simp⟩⟩
      have h_in3 : (0, q) ∈ s := Finset.mem_biUnion.mpr ⟨lm, hlm,
        Finset.mem_biUnion.mpr ⟨q, hq, by simp⟩⟩
      have h_in4 : (lm.1, lm.2 - q) ∈ s := Finset.mem_biUnion.mpr ⟨lm, hlm,
        Finset.mem_biUnion.mpr ⟨q, hq, by simp⟩⟩
      have hle1 : SchwartzMap.seminorm ℝ lm.1 q f_c.val ≤ p_s :=
        Seminorm.le_def.mp (Finset.le_sup (f := fam) h_in1) f_c.val
      have hle2 : SchwartzMap.seminorm ℝ 0 (lm.2 - q) f_c.val ≤ p_s :=
        Seminorm.le_def.mp (Finset.le_sup (f := fam) h_in2) f_c.val
      have hle3 : SchwartzMap.seminorm ℝ 0 q f_c.val ≤ p_s :=
        Seminorm.le_def.mp (Finset.le_sup (f := fam) h_in3) f_c.val
      have hle4 : SchwartzMap.seminorm ℝ lm.1 (lm.2 - q) f_c.val ≤ p_s :=
        Seminorm.le_def.mp (Finset.le_sup (f := fam) h_in4) f_c.val
      have hp1 : SchwartzMap.seminorm ℝ lm.1 q f_c.val *
          SchwartzMap.seminorm ℝ 0 (lm.2 - q) f_c.val ≤ p_s ^ 2 := by
        rw [sq]; exact mul_le_mul hle1 hle2 (apply_nonneg _ _) hps_nn
      have hp2 : SchwartzMap.seminorm ℝ 0 q f_c.val *
          SchwartzMap.seminorm ℝ lm.1 (lm.2 - q) f_c.val ≤ p_s ^ 2 := by
        rw [sq]; exact mul_le_mul hle3 hle4 (apply_nonneg _ _) hps_nn
      have h_sum2 : SchwartzMap.seminorm ℝ lm.1 q f_c.val *
          SchwartzMap.seminorm ℝ 0 (lm.2 - q) f_c.val +
          SchwartzMap.seminorm ℝ 0 q f_c.val *
          SchwartzMap.seminorm ℝ lm.1 (lm.2 - q) f_c.val ≤ 2 * p_s ^ 2 := by linarith
      calc (lm.2.choose q : ℝ) * (SchwartzMap.seminorm ℝ lm.1 q f_c.val *
            SchwartzMap.seminorm ℝ 0 (lm.2 - q) f_c.val +
            SchwartzMap.seminorm ℝ 0 q f_c.val *
            SchwartzMap.seminorm ℝ lm.1 (lm.2 - q) f_c.val)
          ≤ (lm.2.choose q : ℝ) * (2 * p_s ^ 2) :=
            mul_le_mul_of_nonneg_left h_sum2 (Nat.cast_nonneg _)
        _ = (lm.2.choose q : ℝ) * 2 * p_s ^ 2 := by ring
    refine h_lm_le.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg p_s))
    have h_single : (∑ q ∈ Finset.range (lm.2 + 1), (lm.2.choose q : ℝ) * 2) ≤
        ∑ lm' ∈ s₀, ∑ q ∈ Finset.range (lm'.2 + 1), (lm'.2.choose q : ℝ) * 2 :=
      Finset.single_le_sum
        (f := fun lm' : ℕ × ℕ => ∑ q ∈ Finset.range (lm'.2 + 1), (lm'.2.choose q : ℝ) * 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hlm
    dsimp [M]
    linarith
  have h_norm_sq : ‖wightmanBasis WData ⟨j, (α, f_c)⟩‖ ^ 2 ≤ (K * p_s) ^ 2 := by
    have h_re_eq : ‖wightmanBasis WData ⟨j, (α, f_c)⟩‖ ^ 2 =
        (⟪wightmanBasis WData ⟨j, (α, f_c)⟩, wightmanBasis WData ⟨j, (α, f_c)⟩⟫_ℂ).re := by
      have h_nsq := @norm_sq_eq_re_inner ℂ _ _ _ _ (wightmanBasis WData ⟨j, (α, f_c)⟩)
      exact h_nsq
    have h_ker_eq : ⟪wightmanBasis WData ⟨j, (α, f_c)⟩,
        wightmanBasis WData ⟨j, (α, f_c)⟩⟫_ℂ =
        T_diag (borchersConcatSchwartz j j f_c.val f_c.val) := by
      rw [inner_wightmanBasis, wightmanKernel_mk,
          ← borchersConcatSchwartz_eq_wightmanConcatSchwartz]
      dsimp [T_diag]
      rw [FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun β _ => rfl
    rw [h_re_eq, h_ker_eq]
    calc (T_diag (borchersConcatSchwartz j j f_c.val f_c.val)).re
        ≤ ‖T_diag (borchersConcatSchwartz j j f_c.val f_c.val)‖ := Complex.re_le_norm _
      _ ≤ C_T * (s₀.sup (schwartzSeminormFamily ℝ (Fin (j + j) → Fin 4 → ℝ) ℂ))
            (borchersConcatSchwartz j j f_c.val f_c.val) := hT_bound _
      _ ≤ C_T * (M * p_s ^ 2) := mul_le_mul_of_nonneg_left h_sup_le hCT_pos.le
      _ = (Real.sqrt (C_T * M) * p_s) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), mul_assoc]
      _ ≤ (K * p_s) ^ 2 := by
          have h_rt_le : Real.sqrt (C_T * M) * p_s ≤ K * p_s :=
            mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hps_nn
          exact pow_le_pow_left₀ (by positivity) h_rt_le 2
  have h_abs := sq_le_sq.mp h_norm_sq
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hK_pos.le hps_nn)] at h_abs
  exact h_abs

omit [Fintype ι] [DecidableEq ι] in
lemma compactCutoff_add (n : ℕ) (f₁ f₂ : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (m : ℕ) :
    compactCutoff n (f₁ + f₂) m =
      compactSchwartzAdd n (compactCutoff n f₁ m) (compactCutoff n f₂ m) := by
  apply Subtype.ext
  ext x
  simp [compactCutoff_val, compactSchwartzAdd_val, schwartzCutoffSeq_apply, mul_add]

omit [Fintype ι] [DecidableEq ι] in
lemma compactCutoff_smul (n : ℕ) (c : ℂ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (m : ℕ) :
    compactCutoff n (c • f) m =
      compactSchwartzSMul n c (compactCutoff n f m) := by
  apply Subtype.ext
  ext x
  simp only [compactCutoff_val, schwartzCutoffSeq_apply, compactSchwartzSMul_val,
    _root_.smul_apply, smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
def compactSchwartzSub (n : ℕ) (f₁ f₂ : CompactSchwartz n) : CompactSchwartz n :=
  compactSchwartzAdd n f₁ (compactSchwartzSMul n (-1) f₂)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma compactSchwartzSub_val (n : ℕ) (f₁ f₂ : CompactSchwartz n) :
    (compactSchwartzSub n f₁ f₂).val = f₁.val - f₂.val := by
  ext x
  change f₁.val x + (-1 : ℂ) * f₂.val x = f₁.val x - f₂.val x
  ring

lemma wightmanBasis_compactSchwartzSub
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι)
    (f₁ f₂ : CompactSchwartz j) :
    wightmanBasis WData ⟨j, (α, compactSchwartzSub j f₁ f₂)⟩ =
      wightmanBasis WData ⟨j, (α, f₁)⟩ - wightmanBasis WData ⟨j, (α, f₂)⟩ := by
  dsimp [compactSchwartzSub]
  rw [wightmanBasis_compactSchwartzAdd, wightmanBasis_compactSchwartzSMul,
      neg_one_smul, sub_eq_add_neg]

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_finset_sup_schwartzSeminorm (j : ℕ) (s : Finset (ℕ × ℕ)) :
    Continuous (⇑(s.sup (schwartzSeminormFamily ℝ (Fin j → Fin 4 → ℝ) ℂ))) := by
  have h_with : WithSeminorms (schwartzSeminormFamily ℝ (Fin j → Fin 4 → ℝ) ℂ) :=
    schwartz_withSeminorms ℝ _ _
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Seminorm.bot_eq_zero]
    exact continuous_const
  | @insert a s' _ ih =>
    rw [Finset.sup_insert]
    exact (h_with.continuous_seminorm a).max ih

lemma cauchySeq_wightmanBasis_compactCutoff
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    CauchySeq (fun m : ℕ => wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩) := by
  obtain ⟨s, K, hK_pos, h_bd⟩ := exists_wightmanBasis_seminorm_bound WData j α
  let p := s.sup (schwartzSeminormFamily ℝ (Fin j → Fin 4 → ℝ) ℂ)
  have hp_cont : Continuous ⇑p := continuous_finset_sup_schwartzSeminorm j s
  have h_sub_tendsto : Tendsto (fun m : ℕ => schwartzCutoffSeq j f m - f) atTop (𝓝 0) := by
    have h1 := (schwartzCutoffSeq_tendsto j f).sub (tendsto_const_nhds (x := f))
    rwa [sub_self] at h1
  have hp_tendsto : Tendsto (fun m : ℕ => p (schwartzCutoffSeq j f m - f)) atTop (𝓝 0) := by
    have h1 := (hp_cont.tendsto 0).comp h_sub_tendsto
    rwa [map_zero] at h1
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hεK_pos : 0 < ε / (2 * K) := by positivity
  have h_ev := hp_tendsto.eventually (gt_mem_nhds hεK_pos)
  rw [Filter.eventually_atTop] at h_ev
  rcases h_ev with ⟨N, hN⟩
  refine ⟨N, fun m₁ hm₁ m₂ hm₂ => ?_⟩
  rw [dist_eq_norm, ← wightmanBasis_compactSchwartzSub]
  have h_val : (compactSchwartzSub j (compactCutoff j f m₁) (compactCutoff j f m₂)).val =
      (schwartzCutoffSeq j f m₁ - f) - (schwartzCutoffSeq j f m₂ - f) := by
    rw [compactSchwartzSub_val, compactCutoff_val, compactCutoff_val]
    abel
  calc ‖wightmanBasis WData ⟨j, (α, compactSchwartzSub j
          (compactCutoff j f m₁) (compactCutoff j f m₂))⟩‖
      ≤ K * p (compactSchwartzSub j (compactCutoff j f m₁) (compactCutoff j f m₂)).val :=
        h_bd _
    _ = K * p ((schwartzCutoffSeq j f m₁ - f) - (schwartzCutoffSeq j f m₂ - f)) := by
        rw [h_val]
    _ ≤ K * (p (schwartzCutoffSeq j f m₁ - f) + p (schwartzCutoffSeq j f m₂ - f)) :=
        mul_le_mul_of_nonneg_left (map_sub_le_add p _ _) hK_pos.le
    _ < K * (ε / (2 * K) + ε / (2 * K)) :=
        mul_lt_mul_of_pos_left (add_lt_add (hN m₁ hm₁) (hN m₂ hm₂)) hK_pos
    _ = ε := by field_simp; ring

noncomputable def wightmanSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι) :
    SchwartzMap (Fin j → Fin 4 → ℝ) ℂ →L[ℂ] WightmanHilbert WData := by
  let limFun : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ → WightmanHilbert WData :=
    fun f => (cauchySeq_tendsto_of_complete
      (cauchySeq_wightmanBasis_compactCutoff WData j α f)).choose
  have h_lim : ∀ f, Tendsto
      (fun m : ℕ => wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩)
      atTop (𝓝 (limFun f)) :=
    fun f => (cauchySeq_tendsto_of_complete
      (cauchySeq_wightmanBasis_compactCutoff WData j α f)).choose_spec
  let L : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ →ₗ[ℂ] WightmanHilbert WData :=
    { toFun := limFun
      map_add' := fun f₁ f₂ => by
        have h12 := (h_lim f₁).add (h_lim f₂)
        have h_add : Tendsto
            (fun m : ℕ => wightmanBasis WData ⟨j, (α, compactCutoff j (f₁ + f₂) m)⟩)
            atTop (𝓝 (limFun f₁ + limFun f₂)) := by
          refine h12.congr fun m => ?_
          rw [compactCutoff_add, wightmanBasis_compactSchwartzAdd]
        exact tendsto_nhds_unique (h_lim (f₁ + f₂)) h_add
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        have hc := (h_lim f).const_smul c
        have h_smul : Tendsto
            (fun m : ℕ => wightmanBasis WData ⟨j, (α, compactCutoff j (c • f) m)⟩)
            atTop (𝓝 (c • limFun f)) := by
          refine hc.congr fun m => ?_
          rw [compactCutoff_smul, wightmanBasis_compactSchwartzSMul]
        exact tendsto_nhds_unique (h_lim (c • f)) h_smul }
  refine { L with cont := ?_ }
  obtain ⟨s, K, hK_pos, h_bd⟩ := exists_wightmanBasis_seminorm_bound WData j α
  let p := s.sup (schwartzSeminormFamily ℝ (Fin j → Fin 4 → ℝ) ℂ)
  have hp_cont : Continuous ⇑p := continuous_finset_sup_schwartzSeminorm j s
  have hL_bd : ∀ f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ, ‖L f‖ ≤ K * p f := by
    intro f
    have h_lhs : Tendsto
        (fun m : ℕ => ‖wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩‖)
        atTop (𝓝 ‖L f‖) := (h_lim f).norm
    have h_rhs : Tendsto
        (fun m : ℕ => K * p (schwartzCutoffSeq j f m))
        atTop (𝓝 (K * p f)) :=
      ((hp_cont.tendsto f).comp (schwartzCutoffSeq_tendsto j f)).const_mul K
    exact le_of_tendsto_of_tendsto h_lhs h_rhs
      (Filter.Eventually.of_forall fun m => h_bd (compactCutoff j f m))
  refine continuous_of_continuousAt_zero L ?_
  rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
  have h_zero_tend : Tendsto (fun f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ => K * p f)
      (𝓝 0) (𝓝 0) := by
    simpa [map_zero, mul_zero] using (hp_cont.tendsto 0).const_mul K
  exact squeeze_zero (fun _ => norm_nonneg _) hL_bd h_zero_tend

theorem tendsto_wightmanBasis_compactCutoff
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    Tendsto (fun m : ℕ => wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩)
      atTop (𝓝 (wightmanSchwartzVec WData j α f)) :=
  (cauchySeq_tendsto_of_complete
    (cauchySeq_wightmanBasis_compactCutoff WData j α f)).choose_spec

@[simp]
theorem wightmanSchwartzVec_compact
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j : ℕ) (α : Fin j → ι)
    (f_c : CompactSchwartz j) :
    wightmanSchwartzVec WData j α f_c.val = wightmanBasis WData ⟨j, (α, f_c)⟩ := by
  rcases Metric.isBounded_iff_subset_ball (0 : Fin j → Fin 4 → ℝ) |>.mp
      f_c.property.isCompact.isBounded with ⟨R_b, hR_sub⟩
  obtain ⟨M_nat, hM_nat⟩ := exists_nat_gt (max R_b 0)
  have h_ev : ∀ᶠ m : ℕ in atTop, compactCutoff j f_c.val m = f_c := by
    filter_upwards [Filter.eventually_ge_atTop M_nat] with m hm
    apply Subtype.ext
    ext x
    rw [compactCutoff_val, schwartzCutoffSeq_apply]
    by_cases hx : x ∈ tsupport (f_c.val : (Fin j → Fin 4 → ℝ) → ℂ)
    · have hx_ball : x ∈ Metric.ball (0 : Fin j → Fin 4 → ℝ) R_b := hR_sub hx
      rw [Metric.mem_ball, dist_zero_right] at hx_ball
      have hm_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hx_lt : ‖x‖ < (m : ℝ) + 1 := by
        have h1 : R_b ≤ max R_b 0 := le_max_left _ _
        have h2 : (M_nat : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
        linarith
      have hy_ball : (((m : ℝ) + 1)⁻¹) • x ∈ Metric.ball (0 : Fin j → Fin 4 → ℝ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hm_pos), inv_mul_lt_iff₀ hm_pos, mul_one]
        exact hx_lt
      have h_one : vladimirov_cutoff_bump_schwartz j ((((m : ℝ) + 1)⁻¹) • x) = 1 := by
        change ((vladimirovCutoffBump j 1 Real.zero_lt_one
          ((((m : ℝ) + 1)⁻¹) • x) : ℝ) : ℂ) = 1
        rw [vladimirov_cutoff_bump_one_of_mem_ball_gen j 1 le_rfl _ hy_ball]
        simp
      rw [h_one, one_mul]
    · have hfx : f_c.val x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [hfx, mul_zero]
  have h_const : Tendsto
      (fun m : ℕ => wightmanBasis WData ⟨j, (α, compactCutoff j f_c.val m)⟩)
      atTop (𝓝 (wightmanBasis WData ⟨j, (α, f_c)⟩)) :=
    tendsto_const_nhds.congr' (h_ev.mono fun m hm => by dsimp only; rw [hm])
  exact tendsto_nhds_unique (tendsto_wightmanBasis_compactCutoff WData j α f_c.val) h_const

theorem inner_wightmanSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ⟪wightmanSchwartzVec WData j α f, wightmanSchwartzVec WData k α' g⟫_ℂ =
      ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          WData.W (j + k) (Fin.append (β ∘ Fin.rev) α') (borchersConcatSchwartz j k f g) := by
  have h_lhs : Tendsto
      (fun m : ℕ => ⟪wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩,
        wightmanBasis WData ⟨k, (α', compactCutoff k g m)⟩⟫_ℂ)
      atTop (𝓝 ⟪wightmanSchwartzVec WData j α f, wightmanSchwartzVec WData k α' g⟫_ℂ) :=
    Filter.Tendsto.inner
      (tendsto_wightmanBasis_compactCutoff WData j α f)
      (tendsto_wightmanBasis_compactCutoff WData k α' g)
  have h_cat := tendsto_wightmanConcatSchwartz_compactCutoff j k f g
    (borchersConcatSchwartz j k f g) (borchersConcatSchwartz_apply j k f g)
  have h_rhs : Tendsto
      (fun m : ℕ => ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          WData.W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m)))
      atTop (𝓝 (∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          WData.W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (borchersConcatSchwartz j k f g))) := by
    refine tendsto_finsetSum Finset.univ fun β _ => ?_
    exact (((WData.W (j + k) (Fin.append (β ∘ Fin.rev) α')).continuous.tendsto _).comp
      h_cat).const_mul _
  have h_eq : (fun m : ℕ => ⟪wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩,
        wightmanBasis WData ⟨k, (α', compactCutoff k g m)⟩⟫_ℂ) =
      (fun m : ℕ => ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          WData.W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k (compactCutoff j f m) (compactCutoff k g m))) := by
    ext m
    rw [inner_wightmanBasis, wightmanKernel_mk]
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

theorem wightmanTranslate_wightmanSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S)
    (htrans : WightmanTranslationInvariant WData.W)
    (a : Fin 4 → ℝ) (j : ℕ) (α : Fin j → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    wightmanTranslate WData htrans a (wightmanSchwartzVec WData j α f) =
      wightmanSchwartzVec WData j α (schwartzDiagTranslateN j a f) := by
  have h_lhs : Tendsto
      (fun m : ℕ => wightmanTranslate WData htrans a
        (wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩))
      atTop (𝓝 (wightmanTranslate WData htrans a (wightmanSchwartzVec WData j α f))) :=
    ((wightmanTranslate WData htrans a).continuous.tendsto _).comp
      (tendsto_wightmanBasis_compactCutoff WData j α f)
  have h_rhs : Tendsto
      (fun m : ℕ => wightmanSchwartzVec WData j α
        (schwartzDiagTranslateN j a (schwartzCutoffSeq j f m)))
      atTop (𝓝 (wightmanSchwartzVec WData j α (schwartzDiagTranslateN j a f))) :=
    ((wightmanSchwartzVec WData j α).continuous.tendsto _).comp
      (((schwartzDiagTranslateN j a).continuous.tendsto _).comp
        (schwartzCutoffSeq_tendsto j f))
  have h_eq : (fun m : ℕ => wightmanTranslate WData htrans a
        (wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩)) =
      (fun m : ℕ => wightmanSchwartzVec WData j α
        (schwartzDiagTranslateN j a (schwartzCutoffSeq j f m))) := by
    ext m
    rw [wightmanTranslate_wightmanBasis]
    dsimp [wightmanConfigTranslate]
    rw [← wightmanSchwartzVec_compact WData j α
      (compactSchwartzTranslate j a (compactCutoff j f m))]
    rfl
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

omit [Fintype ι] [DecidableEq ι] in
def posTubeExtendLM (k : ℕ) :
    (Fin k → Fin 4 → ℂ) →ₗ[ℂ] (Fin (k + 1) → Fin 4 → ℂ) where
  toFun z := Fin.cons 0 z
  map_add' z₁ z₂ := by
    ext i μ
    refine Fin.cases ?_ ?_ i
    · simp
    · intro u
      simp
  map_smul' c z := by
    ext i μ
    refine Fin.cases ?_ ?_ i
    · simp
    · intro u
      simp

omit [Fintype ι] [DecidableEq ι] in
noncomputable def posTubeExtendCLM (k : ℕ) :
    (Fin k → Fin 4 → ℂ) →L[ℂ] (Fin (k + 1) → Fin 4 → ℂ) :=
  (posTubeExtendLM k).mkContinuous 1 fun z => by
    rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun i => ?_
    refine Fin.cases ?_ ?_ i
    · change ‖(0 : Fin 4 → ℂ)‖ ≤ ‖z‖
      rw [norm_zero]
      exact norm_nonneg z
    · intro u
      exact norm_le_pi_norm z u

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma posTubeExtendCLM_zero (k : ℕ) (z : Fin k → Fin 4 → ℂ) :
    posTubeExtendCLM k z 0 = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma posTubeExtendCLM_succ (k : ℕ) (z : Fin k → Fin 4 → ℂ) (u : Fin k) :
    posTubeExtendCLM k z (Fin.succ u) = z u := rfl

omit [Fintype ι] [DecidableEq ι] in
def posTubeN (k : ℕ) : Set (Fin k → Fin 4 → ℂ) :=
  { z | posTubeExtendCLM k z ∈ forward_tube_n (k + 1) }

omit [Fintype ι] [DecidableEq ι] in
lemma isOpen_posTubeN (k : ℕ) : IsOpen (posTubeN k) :=
  (forward_tube_n_isOpen (k + 1)).preimage (posTubeExtendCLM k).continuous

omit [Fintype ι] [DecidableEq ι] in
lemma wickEmbedN_mem_posTubeN {k : ℕ} {y : Fin k → Fin 4 → ℝ}
    (hy : y ∈ posOrderedEuclidN k) :
    wickEmbedN k y ∈ posTubeN k := by
  change posTubeExtendCLM k (wickEmbedN k y) ∈ forward_tube_n (k + 1)
  let y_ext : Fin (k + 1) → Fin 4 → ℝ := Fin.cons 0 y
  have h_eq : posTubeExtendCLM k (wickEmbedN k y) = wickEmbedN (k + 1) y_ext := by
    ext i μ
    refine Fin.cases ?_ ?_ i
    · simp [wickEmbedN, wickEmbed, y_ext]
    · intro u
      rfl
  rw [h_eq]
  refine wickEmbedN_mem_forward_tube_n (k + 1) (fun i hi => ?_)
  by_cases hi0 : i.val = 0
  · have hi_eq : i = 0 := Fin.ext hi0
    have hk0 : 0 < k := by omega
    have hi1_eq : (⟨i.val + 1, hi⟩ : Fin (k + 1)) = Fin.succ ⟨0, hk0⟩ := by
      ext
      dsimp
      omega
    have h_lhs : y_ext i 0 = 0 := congrArg (fun idx => y_ext idx 0) hi_eq
    have h_rhs : y_ext ⟨i.val + 1, hi⟩ 0 = y ⟨0, hk0⟩ 0 :=
      congrArg (fun idx => y_ext idx 0) hi1_eq
    rw [h_lhs, h_rhs]
    exact hy.1 ⟨0, hk0⟩
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have hm1 : m + 1 < k := by omega
    have hm0 : m < k := by omega
    have hi_eq : i = Fin.succ ⟨m, hm0⟩ := Fin.ext hm
    have hi1_eq : (⟨i.val + 1, hi⟩ : Fin (k + 1)) = Fin.succ ⟨m + 1, hm1⟩ := by
      ext
      dsimp
      omega
    have h_lhs : y_ext i 0 = y ⟨m, hm0⟩ 0 := congrArg (fun idx => y_ext idx 0) hi_eq
    have h_rhs : y_ext ⟨i.val + 1, hi⟩ 0 = y ⟨m + 1, hm1⟩ 0 :=
      congrArg (fun idx => y_ext idx 0) hi1_eq
    rw [h_lhs, h_rhs]
    have hm_fin : (⟨m, hm0⟩ : Fin k).val + 1 < k := hm1
    exact hy.2 ⟨m, hm0⟩ hm_fin

omit [Fintype ι] [DecidableEq ι] in
def embedZeroSumMomentumLM (k : ℕ) :
    (Fin k → Fin 4 → ℝ) →ₗ[ℝ] (Fin (k + 1) → Fin 4 → ℝ) where
  toFun q := Fin.cons (-∑ u : Fin k, q u) q
  map_add' q₁ q₂ := by
    ext i μ
    refine Fin.cases ?_ ?_ i
    · simp [Finset.sum_add_distrib]
      ring
    · intro u
      simp
  map_smul' c q := by
    ext i μ
    refine Fin.cases ?_ ?_ i
    · simp [Finset.mul_sum]
    · intro u
      simp

omit [Fintype ι] [DecidableEq ι] in
noncomputable def embedZeroSumMomentumCLM (k : ℕ) :
    (Fin k → Fin 4 → ℝ) →L[ℝ] (Fin (k + 1) → Fin 4 → ℝ) :=
  (embedZeroSumMomentumLM k).mkContinuous ((k : ℝ) + 1) fun q => by
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk_nn (norm_nonneg q))).mpr fun i => ?_
    refine Fin.cases ?_ ?_ i
    · change ‖-∑ u : Fin k, q u‖ ≤ ((k : ℝ) + 1) * ‖q‖
      rw [norm_neg]
      calc ‖∑ u : Fin k, q u‖
          ≤ ∑ u : Fin k, ‖q u‖ := norm_sum_le _ _
        _ ≤ ∑ _u : Fin k, ‖q‖ := Finset.sum_le_sum fun u _ => norm_le_pi_norm q u
        _ = (k : ℝ) * ‖q‖ := by simp
        _ ≤ ((k : ℝ) + 1) * ‖q‖ := by nlinarith [norm_nonneg q]
    · intro u
      calc ‖q u‖ ≤ ‖q‖ := norm_le_pi_norm q u
        _ ≤ ((k : ℝ) + 1) * ‖q‖ := by nlinarith [norm_nonneg q]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma embedZeroSumMomentumCLM_zero (k : ℕ) (q : Fin k → Fin 4 → ℝ) :
    embedZeroSumMomentumCLM k q 0 = -∑ u : Fin k, q u := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma embedZeroSumMomentumCLM_succ (k : ℕ) (q : Fin k → Fin 4 → ℝ) (u : Fin k) :
    embedZeroSumMomentumCLM k q (Fin.succ u) = q u := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma antilipschitzWith_embedZeroSumMomentum (k : ℕ) :
    AntilipschitzWith 1 (embedZeroSumMomentumCLM k) := by
  refine AntilipschitzWith.of_le_mul_dist fun q₁ q₂ => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun u => ?_
  simpa using norm_le_pi_norm (embedZeroSumMomentumCLM k (q₁ - q₂)) (Fin.succ u)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def pullbackTailSchwartzCLM (k : ℕ) :
    SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin k → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (embedZeroSumMomentumCLM k).hasTemperateGrowth
    (antilipschitzWith_embedZeroSumMomentum k)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma pullbackTailSchwartzCLM_apply (k : ℕ)
    (ψ : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ) (q : Fin k → Fin 4 → ℝ) :
    pullbackTailSchwartzCLM k ψ q = ψ (embedZeroSumMomentumCLM k q) := rfl

omit [Fintype ι] [DecidableEq ι] in
def tailOpenNhd (k : ℕ) : Set (Fin k → Fin 4 → ℝ) :=
  (embedZeroSumMomentumCLM k) ⁻¹' coneOpenNhd (k + 1)

omit [Fintype ι] [DecidableEq ι] in
lemma isOpen_tailOpenNhd (k : ℕ) : IsOpen (tailOpenNhd k) :=
  (isOpen_coneOpenNhd (k + 1)).preimage (embedZeroSumMomentumCLM k).continuous

omit [Fintype ι] [DecidableEq ι] in
lemma zero_mem_tailOpenNhd_zero (q : Fin 0 → Fin 4 → ℝ) :
    q ∈ tailOpenNhd 0 := by
  have h0 : embedZeroSumMomentumCLM 0 q ∈ spectralRegion 1 := by
    refine ⟨?_, fun m => ?_⟩
    · rw [Fin.sum_univ_one, embedZeroSumMomentumCLM_zero]
      simp
    · have hm : m = 0 := Subsingleton.elim m 0
      subst hm
      rw [Finset.sum_filter, Fin.sum_univ_one]
      simp [zero_mem_closure_forward_light_cone]
  exact spectralRegion_subset_coneOpenNhd 1 h0

omit [Fintype ι] [DecidableEq ι] in
lemma left_castAdd_sum_mem_closure_of_spectralRegion (j k : ℕ)
    {p : Fin (j + k) → Fin 4 → ℝ} (hp : p ∈ spectralRegion (j + k)) :
    (∑ s : Fin j, p (Fin.castAdd k s)) ∈ closure forward_light_cone := by
  by_cases hj : j = 0
  · subst hj
    simpa using zero_mem_closure_forward_light_cone
  · let m₀ : Fin (j + k) := ⟨j - 1, by omega⟩
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

omit [Fintype ι] [DecidableEq ι] in
lemma embedZeroSumMomentum_right_mem_spectralRegion (j k : ℕ)
    {p : Fin (j + k) → Fin 4 → ℝ} (hp : p ∈ spectralRegion (j + k)) :
    embedZeroSumMomentumCLM k (fun u => p (Fin.natAdd j u)) ∈ spectralRegion (k + 1) := by
  let q_R : Fin k → Fin 4 → ℝ := fun u => p (Fin.natAdd j u)
  have h_sum_zero : -∑ u : Fin k, q_R u = ∑ s : Fin j, p (Fin.castAdd k s) := by
    have h_tot := hp.1
    rw [Fin.sum_univ_add] at h_tot
    ext μ
    have hμ := congr_fun h_tot μ
    simp only [Pi.add_apply, Pi.zero_apply, Finset.sum_apply, Pi.neg_apply, q_R] at hμ ⊢
    linarith
  refine ⟨?_, fun m => ?_⟩
  · rw [Fin.sum_univ_succ, embedZeroSumMomentumCLM_zero]
    simp
  · rw [Finset.sum_filter, Fin.sum_univ_succ, embedZeroSumMomentumCLM_zero]
    refine Fin.cases ?_ ?_ m
    · simp only [le_rfl, ↓reduceIte]
      have h2 : (∑ u : Fin k,
          if Fin.succ u ≤ (0 : Fin (k + 1)) then
            embedZeroSumMomentumCLM k q_R (Fin.succ u) else 0) = 0 := by
        refine Finset.sum_eq_zero fun u _ => if_neg ?_
        rw [Fin.le_iff_val_le_val]
        dsimp
        omega
      rw [h2, add_zero, h_sum_zero]
      exact left_castAdd_sum_mem_closure_of_spectralRegion j k hp
    · intro l
      simp only [Fin.zero_le, ↓reduceIte, Fin.succ_le_succ_iff, embedZeroSumMomentumCLM_succ]
      rw [h_sum_zero]
      let m_l : Fin (j + k) := Fin.natAdd j l
      have h_eq : (∑ s : Fin j, p (Fin.castAdd k s)) +
          (∑ u : Fin k, if u ≤ l then q_R u else 0) = partial_sum_p (j + k) p m_l := by
        dsimp [partial_sum_p]
        rw [Finset.sum_filter, Fin.sum_univ_add]
        congr 1
        · refine Finset.sum_congr rfl fun s _ => (if_pos ?_).symm
          rw [Fin.le_iff_val_le_val]
          dsimp [m_l]
          omega
        · refine Finset.sum_congr rfl fun u _ => ?_
          have h_iff : u ≤ l ↔ Fin.natAdd j u ≤ m_l := by
            rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
            dsimp [m_l]
            omega
          by_cases hul : u ≤ l
          · rw [if_pos hul, if_pos (h_iff.mp hul)]
          · rw [if_neg hul, if_neg (mt h_iff.mpr hul)]
      rw [h_eq]
      exact hp.2 m_l

omit [Fintype ι] [DecidableEq ι] in
lemma embedZeroSumMomentum_left_mem_spectralRegion (j k : ℕ)
    {p : Fin (j + k) → Fin 4 → ℝ} (hp : p ∈ spectralRegion (j + k)) :
    embedZeroSumMomentumCLM j (fun i => -p (Fin.castAdd k (Fin.rev i))) ∈
      spectralRegion (j + 1) := by
  let q_L : Fin j → Fin 4 → ℝ := fun i => -p (Fin.castAdd k (Fin.rev i))
  have h_sum_zero : -∑ i : Fin j, q_L i = ∑ s : Fin j, p (Fin.castAdd k s) := by
    dsimp [q_L]
    rw [Finset.sum_neg_distrib, neg_neg]
    exact Equiv.sum_comp Fin.revPerm (fun s : Fin j => p (Fin.castAdd k s))
  refine ⟨?_, fun m => ?_⟩
  · rw [Fin.sum_univ_succ, embedZeroSumMomentumCLM_zero]
    simp
  · rw [Finset.sum_filter, Fin.sum_univ_succ, embedZeroSumMomentumCLM_zero]
    refine Fin.cases ?_ ?_ m
    · simp only [le_rfl, ↓reduceIte]
      have h2 : (∑ i : Fin j,
          if Fin.succ i ≤ (0 : Fin (j + 1)) then
            embedZeroSumMomentumCLM j q_L (Fin.succ i) else 0) = 0 := by
        refine Finset.sum_eq_zero fun i _ => if_neg ?_
        rw [Fin.le_iff_val_le_val]
        dsimp
        omega
      rw [h2, add_zero, h_sum_zero]
      exact left_castAdd_sum_mem_closure_of_spectralRegion j k hp
    · intro l
      simp only [Fin.zero_le, ↓reduceIte, Fin.succ_le_succ_iff, embedZeroSumMomentumCLM_succ]
      rw [h_sum_zero]
      have h_rev_sum : (∑ i : Fin j, if i ≤ l then q_L i else 0) =
          -∑ s : Fin j, if Fin.rev s ≤ l then p (Fin.castAdd k s) else 0 := by
        rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin j => if i ≤ l then q_L i else 0),
          ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        change (if Fin.rev s ≤ l then -p (Fin.castAdd k (Fin.rev (Fin.rev s))) else 0) = _
        rw [Fin.rev_rev]
        split_ifs <;> simp
      have h_comb : (∑ s : Fin j, p (Fin.castAdd k s)) +
          (∑ i : Fin j, if i ≤ l then q_L i else 0) =
          ∑ s : Fin j, if ¬Fin.rev s ≤ l then p (Fin.castAdd k s) else 0 := by
        rw [h_rev_sum, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hs : Fin.rev s ≤ l
        · simp [hs]
        · simp [hs]
      rw [h_comb]
      by_cases hlj : l.val + 1 = j
      · have h_zero : (∑ s : Fin j,
            if ¬Fin.rev s ≤ l then p (Fin.castAdd k s) else 0) = 0 := by
          refine Finset.sum_eq_zero fun s _ => if_neg ?_
          push Not
          rw [Fin.le_iff_val_le_val, Fin.val_rev]
          omega
        rw [h_zero]
        exact zero_mem_closure_forward_light_cone
      · let m'_l : Fin (j + k) := ⟨j - 2 - l.val, by omega⟩
        have h_eq : (∑ s : Fin j,
            if ¬Fin.rev s ≤ l then p (Fin.castAdd k s) else 0) =
            partial_sum_p (j + k) p m'_l := by
          dsimp [partial_sum_p]
          rw [Finset.sum_filter, Fin.sum_univ_add]
          have h2 : (∑ u : Fin k,
              if Fin.natAdd j u ≤ m'_l then p (Fin.natAdd j u) else 0) = 0 := by
            refine Finset.sum_eq_zero fun u _ => if_neg ?_
            rw [Fin.le_iff_val_le_val]
            dsimp [m'_l]
            omega
          rw [h2, add_zero]
          refine Finset.sum_congr rfl fun s _ => ?_
          have h_iff : ¬Fin.rev s ≤ l ↔ Fin.castAdd k s ≤ m'_l := by
            rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val, Fin.val_rev]
            dsimp [m'_l]
            omega
          by_cases hs : ¬Fin.rev s ≤ l
          · rw [if_pos hs, if_pos (h_iff.mp hs)]
          · rw [if_neg hs, if_neg (mt h_iff.mpr hs)]
        rw [h_eq]
        exact hp.2 m'_l

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_embedZeroSumMomentum (k : ℕ)
    (w : Fin (k + 1) → Fin 4 → ℂ) (q : Fin k → Fin 4 → ℝ) :
    vladimirov_kernel (k + 1) w (embedZeroSumMomentumCLM k q) =
      vladimirov_kernel k (fun u => w (Fin.succ u) - w 0) q := by
  unfold vladimirov_kernel
  congr 1
  congr 1
  rw [Fin.sum_univ_succ, embedZeroSumMomentumCLM_zero]
  simp only [embedZeroSumMomentumCLM_succ]
  have h0 : minkowskiInnerC (fun μ => ((-∑ u : Fin k, q u) μ : ℂ)) (w 0) =
      -∑ u : Fin k, minkowskiInnerC (fun μ => (q u μ : ℂ)) (w 0) := by
    unfold minkowskiInnerC
    have hμ : ∀ μ : Fin 4, ((-∑ u : Fin k, q u) μ : ℂ) * w 0 μ =
        ∑ u : Fin k, -((q u μ : ℂ) * w 0 μ) := fun μ => by
      rw [Pi.neg_apply, Finset.sum_apply, Complex.ofReal_neg, Complex.ofReal_sum,
        neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [hμ 0, hμ 1, hμ 2, hμ 3, ← Finset.sum_neg_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [h0, neg_add_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [minkowskiInnerC, Pi.sub_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_posTubeExtend_embedZeroSumMomentum (k : ℕ)
    (z : Fin k → Fin 4 → ℂ) (q : Fin k → Fin 4 → ℝ) :
    vladimirov_kernel (k + 1) (posTubeExtendCLM k z) (embedZeroSumMomentumCLM k q) =
      vladimirov_kernel k z q := by
  rw [vladimirov_kernel_embedZeroSumMomentum]
  have h_sub : (fun u : Fin k => posTubeExtendCLM k z (Fin.succ u) - posTubeExtendCLM k z 0) =
      z := by
    ext u μ
    simp
  rw [h_sub]

omit [Fintype ι] [DecidableEq ι] in
def sumTailLM (k : ℕ) :
    (Fin (k + 1) → Fin 4 → ℝ) →ₗ[ℝ] (Fin (1 + k) → Fin 4 → ℝ) where
  toFun p := Fin.append (fun _ : Fin 1 => ∑ m : Fin (k + 1), p m)
    (fun u : Fin k => p (Fin.succ u))
  map_add' p₁ p₂ := by
    ext i μ
    refine Fin.addCases (fun i₀ => ?_) (fun u => ?_) i
    · simp [Fin.append_left, Finset.sum_add_distrib]
    · simp [Fin.append_right]
  map_smul' c p := by
    ext i μ
    refine Fin.addCases (fun i₀ => ?_) (fun u => ?_) i
    · simp [Fin.append_left, Finset.mul_sum]
    · simp [Fin.append_right]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def sumTailCLM (k : ℕ) :
    (Fin (k + 1) → Fin 4 → ℝ) →L[ℝ] (Fin (1 + k) → Fin 4 → ℝ) :=
  (sumTailLM k).mkContinuous ((k : ℝ) + 1) fun p => by
    have hk_nn : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk_nn (norm_nonneg p))).mpr fun i => ?_
    refine Fin.addCases (fun i₀ => ?_) (fun u => ?_) i
    · change ‖Fin.append (fun _ : Fin 1 => ∑ m : Fin (k + 1), p m)
          (fun u : Fin k => p (Fin.succ u)) (Fin.castAdd k i₀)‖ ≤ _
      rw [Fin.append_left]
      calc ‖∑ m : Fin (k + 1), p m‖
          ≤ ∑ m : Fin (k + 1), ‖p m‖ := norm_sum_le _ _
        _ ≤ ∑ _m : Fin (k + 1), ‖p‖ := Finset.sum_le_sum fun m _ => norm_le_pi_norm p m
        _ = ((k : ℝ) + 1) * ‖p‖ := by
          simp [Nat.cast_add]
    · change ‖Fin.append (fun _ : Fin 1 => ∑ m : Fin (k + 1), p m)
          (fun u : Fin k => p (Fin.succ u)) (Fin.natAdd 1 u)‖ ≤ _
      rw [Fin.append_right]
      calc ‖p (Fin.succ u)‖ ≤ ‖p‖ := norm_le_pi_norm p (Fin.succ u)
        _ ≤ ((k : ℝ) + 1) * ‖p‖ := by nlinarith [norm_nonneg p]

omit [Fintype ι] [DecidableEq ι] in
lemma antilipschitzWith_sumTail (k : ℕ) :
    AntilipschitzWith ((k : NNReal) + 1) (sumTailCLM k) := by
  refine AntilipschitzWith.of_le_mul_dist fun p₁ p₂ => ?_
  rw [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, dist_eq_norm, dist_eq_norm, ← map_sub]
  let d := p₁ - p₂
  let r := sumTailCLM k d
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hk_nn (norm_nonneg r))).mpr fun m => ?_
  refine Fin.cases ?_ ?_ m
  · have h_tot : ∑ i : Fin (k + 1), d i = r (Fin.castAdd k 0) := by
      change ∑ i : Fin (k + 1), d i =
        Fin.append (fun _ : Fin 1 => ∑ i : Fin (k + 1), d i)
          (fun u : Fin k => d (Fin.succ u)) (Fin.castAdd k 0)
      rw [Fin.append_left]
    have h_succ : ∀ u : Fin k, d (Fin.succ u) = r (Fin.natAdd 1 u) := fun u => by
      change d (Fin.succ u) =
        Fin.append (fun _ : Fin 1 => ∑ i : Fin (k + 1), d i)
          (fun u' : Fin k => d (Fin.succ u')) (Fin.natAdd 1 u)
      rw [Fin.append_right]
    have hd0 : d 0 = r (Fin.castAdd k 0) - ∑ u : Fin k, r (Fin.natAdd 1 u) := by
      have h_split := Fin.sum_univ_succ d
      rw [h_tot] at h_split
      have h_sum_r : (∑ u : Fin k, d (Fin.succ u)) = ∑ u : Fin k, r (Fin.natAdd 1 u) :=
        Finset.sum_congr rfl fun u _ => h_succ u
      rw [h_sum_r] at h_split
      exact eq_sub_of_add_eq h_split.symm
    change ‖d 0‖ ≤ ((k : ℝ) + 1) * ‖r‖
    rw [hd0]
    calc ‖r (Fin.castAdd k 0) - ∑ u : Fin k, r (Fin.natAdd 1 u)‖
        ≤ ‖r (Fin.castAdd k 0)‖ + ‖∑ u : Fin k, r (Fin.natAdd 1 u)‖ := norm_sub_le _ _
      _ ≤ ‖r‖ + ∑ u : Fin k, ‖r (Fin.natAdd 1 u)‖ :=
        add_le_add (norm_le_pi_norm r _) (norm_sum_le _ _)
      _ ≤ ‖r‖ + ∑ _u : Fin k, ‖r‖ :=
        add_le_add le_rfl (Finset.sum_le_sum fun u _ => norm_le_pi_norm r _)
      _ = ((k : ℝ) + 1) * ‖r‖ := by
        simp
        ring
  · intro u
    have h_succ : d (Fin.succ u) = r (Fin.natAdd 1 u) := by
      change d (Fin.succ u) =
        Fin.append (fun _ : Fin 1 => ∑ i : Fin (k + 1), d i)
          (fun u' : Fin k => d (Fin.succ u')) (Fin.natAdd 1 u)
      rw [Fin.append_right]
    change ‖d (Fin.succ u)‖ ≤ ((k : ℝ) + 1) * ‖r‖
    rw [h_succ]
    calc ‖r (Fin.natAdd 1 u)‖ ≤ ‖r‖ := norm_le_pi_norm r _
      _ ≤ ((k : ℝ) + 1) * ‖r‖ := by nlinarith [norm_nonneg r]

omit [Fintype ι] [DecidableEq ι] in
lemma exists_zeroSumLift_schwartz (k : ℕ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ∃ f_lift : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ,
      ∀ q : Fin k → Fin 4 → ℝ,
        minkowskiFourier f_lift (embedZeroSumMomentumCLM k q) = minkowskiFourier g q := by
  let ψ_prod : SchwartzMap (Fin (1 + k) → Fin 4 → ℝ) ℂ :=
    schwartzProdSplit 1 k (vladimirov_cutoff_bump_schwartz 1) (minkowskiFourierCLM k g)
  let ψ_mom : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ :=
    SchwartzMap.compCLMOfAntilipschitz ℂ
      (sumTailCLM k).hasTemperateGrowth (antilipschitzWith_sumTail k) ψ_prod
  refine ⟨invMinkowskiFourierCLM (k + 1) ψ_mom, fun q => ?_⟩
  rw [minkowskiFourier_invMinkowskiFourierCLM_all]
  change ψ_prod (sumTailCLM k (embedZeroSumMomentumCLM k q)) = minkowskiFourier g q
  rw [schwartzProdSplit_apply]
  have h_sum0 : ∑ m : Fin (k + 1), embedZeroSumMomentumCLM k q m = 0 := by
    rw [Fin.sum_univ_succ, embedZeroSumMomentumCLM_zero]
    simp
  have h_left : (fun i : Fin 1 =>
      sumTailCLM k (embedZeroSumMomentumCLM k q) (Fin.castAdd k (Fin.rev i))) = 0 := by
    ext i μ
    change Fin.append (fun _ : Fin 1 => ∑ m : Fin (k + 1), embedZeroSumMomentumCLM k q m)
      (fun u : Fin k => embedZeroSumMomentumCLM k q (Fin.succ u))
      (Fin.castAdd k (Fin.rev i)) μ = 0
    rw [Fin.append_left, h_sum0]
    rfl
  have h_right : (fun u : Fin k =>
      sumTailCLM k (embedZeroSumMomentumCLM k q) (Fin.natAdd 1 u)) = q := by
    ext u μ
    change Fin.append (fun _ : Fin 1 => ∑ m : Fin (k + 1), embedZeroSumMomentumCLM k q m)
      (fun u' : Fin k => embedZeroSumMomentumCLM k q (Fin.succ u'))
      (Fin.natAdd 1 u) μ = q u μ
    rw [Fin.append_right, embedZeroSumMomentumCLM_succ]
  rw [h_left, h_right]
  have h_bump : vladimirov_cutoff_bump_schwartz 1 0 = 1 := by
    change ((vladimirovCutoffBump 1 1 Real.zero_lt_one 0 : ℝ) : ℂ) = 1
    rw [vladimirov_cutoff_bump_one_of_mem_ball_gen 1 1 le_rfl 0
      (Metric.mem_ball_self Real.zero_lt_one)]
    simp
  rw [h_bump, one_mul, minkowskiFourierCLM_apply]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def osToWightmanTest (k : ℕ) (z : Fin k → Fin 4 → ℂ)
    (hz : z ∈ posTubeN k) : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ :=
  if hk : 0 < k then
    invMinkowskiFourierCLM k
      (pullbackTailSchwartzCLM k
        (cone_psi_schwartz (k + 1) (by omega) (posTubeExtendCLM k z) hz))
  else
    momentumWavepacketSchwartz k 0

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_osToWightmanTest_on_tailOpenNhd (k : ℕ)
    (z : Fin k → Fin 4 → ℂ) (hz : z ∈ posTubeN k)
    {q : Fin k → Fin 4 → ℝ} (hq : q ∈ tailOpenNhd k) :
    minkowskiFourier (osToWightmanTest k z hz) q = vladimirov_kernel k z q := by
  unfold osToWightmanTest
  by_cases hk : 0 < k
  · rw [dif_pos hk, minkowskiFourier_invMinkowskiFourierCLM_all, pullbackTailSchwartzCLM_apply]
    change cone_psi (k + 1) (posTubeExtendCLM k z) (embedZeroSumMomentumCLM k q) = _
    dsimp [cone_psi]
    rw [coneSpectralCutoff_eq_one_of_mem_coneOpenNhd (k + 1) hq, Complex.ofReal_one, one_mul,
      vladimirov_kernel_posTubeExtend_embedZeroSumMomentum]
  · rw [dif_neg hk]
    have hk0 : k = 0 := by omega
    subst hk0
    have h_fourier : minkowskiFourier (momentumWavepacketSchwartz 0 0) q = 1 := by
      have h_eq : minkowskiFourier (momentumWavepacketSchwartz 0 0) q =
          ∫ x : Fin 0 → Fin 4 → ℝ, momentumWavepacketSchwartz 0 0 x := by
        unfold minkowskiFourier
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        simp
      rw [h_eq, integral_momentumWavepacketSchwartz_zero 0]
    have h_ker : vladimirov_kernel 0 z q = 1 := by
      unfold vladimirov_kernel
      simp
    rw [h_fourier, h_ker]

theorem wightman_borchersConcatSchwartz_osToWightmanTest_eq_schwinger
    (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι} (E : TubeExtension W)
    {𝒮 : SchwingerFamily ι}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x)
    (j k : ℕ) (γ : Fin (j + k) → ι)
    {x : Fin j → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN j)
    {y : Fin k → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN k) :
    W (j + k) γ (borchersConcatSchwartz j k
      (osToWightmanTest j (wickEmbedN j x) (wickEmbedN_mem_posTubeN hx))
      (osToWightmanTest k (wickEmbedN k y) (wickEmbedN_mem_posTubeN hy))) =
    𝒮 (j + k) γ (osConcatPoint j k x y) := by
  let f_x := osToWightmanTest j (wickEmbedN j x) (wickEmbedN_mem_posTubeN hx)
  let g_y := osToWightmanTest k (wickEmbedN k y) (wickEmbedN_mem_posTubeN hy)
  let G_xy := borchersConcatSchwartz j k f_x g_y
  let z_xy := wickEmbedN (j + k) (osConcatPoint j k x y)
  have h_ord : osConcatPoint j k x y ∈ orderedEuclidN (j + k) :=
    osConcatPoint_mem_orderedEuclidN j k hx hy
  have hz_xy : z_xy ∈ forward_tube_n (j + k) := wickEmbedN_mem_forward_tube_n (j + k) h_ord
  have h_schw_eq : 𝒮 (j + k) γ (osConcatPoint j k x y) =
      cone_H W (j + k) γ z_xy := by
    rw [h_schw (j + k) γ (osConcatPoint j k x y) h_ord]
    exact tubeExtension_eq_of_wightman_eq E
      (coneVladimirovTubeExtension R W hspec hP) (j + k) γ hz_xy
  rw [h_schw_eq]
  let π_L : (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin j → Fin 4 → ℝ) :=
    -(concatProjLeftCLM j k)
  let π_R : (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) :=
    concatProjRightCLM j k
  have h_fourier_G : ∀ p : Fin (j + k) → Fin 4 → ℝ,
      π_L p ∈ tailOpenNhd j → π_R p ∈ tailOpenNhd k →
      minkowskiFourier G_xy p = vladimirov_kernel (j + k) z_xy p := by
    intro p hpL hpR
    rw [minkowskiFourier_borchersProduct_eq j k f_x g_y G_xy
      (borchersConcatSchwartz_apply j k f_x g_y) p]
    have hpL' : (fun i => -p (Fin.castAdd k (Fin.rev i))) ∈ tailOpenNhd j := hpL
    have hpR' : (fun i => p (Fin.natAdd j i)) ∈ tailOpenNhd k := hpR
    have hL := minkowskiFourier_osToWightmanTest_on_tailOpenNhd j (wickEmbedN j x)
      (wickEmbedN_mem_posTubeN hx) hpL'
    have hR := minkowskiFourier_osToWightmanTest_on_tailOpenNhd k (wickEmbedN k y)
      (wickEmbedN_mem_posTubeN hy) hpR'
    dsimp [f_x, g_y, z_xy]
    rw [hL, hR, vladimirov_kernel_wickEmbedN_eq_euclidLaplace,
      vladimirov_kernel_wickEmbedN_eq_euclidLaplace,
      ← Complex.star_def, ← vladimirov_kernel_osConcatPoint_eq]
  have h_spec_L : ∀ p ∈ spectralRegion (j + k), π_L p ∈ tailOpenNhd j := fun p hp =>
    spectralRegion_subset_coneOpenNhd (j + 1)
      (embedZeroSumMomentum_left_mem_spectralRegion j k hp)
  have h_spec_R : ∀ p ∈ spectralRegion (j + k), π_R p ∈ tailOpenNhd k := fun p hp =>
    spectralRegion_subset_coneOpenNhd (k + 1)
      (embedZeroSumMomentum_right_mem_spectralRegion j k hp)
  by_cases hn : j + k ≤ 1
  · dsimp [cone_H]
    rw [dif_pos hn]
    let U := Metric.ball (0 : Fin (j + k) → Fin 4 → ℝ) 1 ∩
      (π_L ⁻¹' tailOpenNhd j ∩ π_R ⁻¹' tailOpenNhd k)
    have hU_open : IsOpen U :=
      Metric.isOpen_ball.inter
        (((isOpen_tailOpenNhd j).preimage π_L.continuous).inter
          ((isOpen_tailOpenNhd k).preimage π_R.continuous))
    have hU_sub : spectralRegion (j + k) ⊆ U := by
      intro p hp
      refine ⟨?_, h_spec_L p hp, h_spec_R p hp⟩
      have hp0 : p = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with h0 | h1
        · ext i μ
          exact False.elim (Nat.not_lt_zero i.val (h0 ▸ i.isLt))
        · ext i μ
          have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by omega)
          have h_single : ∑ t : Fin (j + k), p t = p ⟨0, by omega⟩ :=
            Finset.sum_eq_single ⟨0, by omega⟩
              (fun b _ hb => False.elim (hb (Fin.ext (by omega))))
              (fun h => False.elim (h (Finset.mem_univ _)))
          rw [hi0, ← h_single, hp.1]
          rfl
      rw [hp0]
      exact Metric.mem_ball_self Real.zero_lt_one
    refine W_eq_of_fourier_eq W hspec (j + k) γ G_xy
      (invMinkowskiFourierCLM (j + k)
        (vladimirov_psi_schwartz (j + k) 1 Real.zero_lt_one z_xy))
      U hU_open hU_sub fun p hp => ?_
    rw [h_fourier_G p hp.2.1 hp.2.2, minkowskiFourier_invMinkowskiFourierCLM_all]
    have hp_norm : ‖p‖ ≤ 1 := by
      have hb := hp.1
      rw [Metric.mem_ball, dist_zero_right] at hb
      exact hb.le
    exact (vladimirov_psi_schwartz_eval_of_norm_le Real.zero_lt_one z_xy hp_norm).symm
  · dsimp [cone_H]
    rw [dif_neg hn, cone_psi_schwartz_total_eq hn hz_xy]
    let U := coneOpenNhd (j + k) ∩ (π_L ⁻¹' tailOpenNhd j ∩ π_R ⁻¹' tailOpenNhd k)
    have hU_open : IsOpen U :=
      (isOpen_coneOpenNhd (j + k)).inter
        (((isOpen_tailOpenNhd j).preimage π_L.continuous).inter
          ((isOpen_tailOpenNhd k).preimage π_R.continuous))
    have hU_sub : spectralRegion (j + k) ⊆ U := fun p hp =>
      ⟨spectralRegion_subset_coneOpenNhd (j + k) hp, h_spec_L p hp, h_spec_R p hp⟩
    refine W_eq_of_fourier_eq W hspec (j + k) γ G_xy
      (invMinkowskiFourierCLM (j + k) (cone_psi_schwartz (j + k) hn z_xy hz_xy))
      U hU_open hU_sub fun p hp => ?_
    rw [h_fourier_G p hp.2.1 hp.2.2, minkowskiFourier_invMinkowskiFourierCLM_all]
    change _ = cone_psi (j + k) z_xy p
    dsimp [cone_psi]
    rw [coneSpectralCutoff_eq_one_of_mem_coneOpenNhd (j + k) hp.1, Complex.ofReal_one, one_mul]

theorem wightmanSchwartzVec_eq_of_fourier_eq_on_tailOpenNhd
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hspec : SpectrumCondition WData.W)
    (k : ℕ) (α : Fin k → ι)
    (f₁ f₂ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)
    (h_eq : ∀ q ∈ tailOpenNhd k, minkowskiFourier f₁ q = minkowskiFourier f₂ q) :
    wightmanSchwartzVec WData k α f₁ = wightmanSchwartzVec WData k α f₂ := by
  rw [← sub_eq_zero, ← map_sub, ← inner_self_eq_zero (𝕜 := ℂ), inner_wightmanSchwartzVec]
  refine Finset.sum_eq_zero fun β _ => ?_
  let π_L : (Fin (k + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) := -(concatProjLeftCLM k k)
  let U := π_L ⁻¹' tailOpenNhd k
  have hU_open : IsOpen U := (isOpen_tailOpenNhd k).preimage π_L.continuous
  have hU_sub : spectralRegion (k + k) ⊆ U := fun p hp =>
    spectralRegion_subset_coneOpenNhd (k + 1)
      (embedZeroSumMomentum_left_mem_spectralRegion k k hp)
  have hW0 : WData.W (k + k) (Fin.append (β ∘ Fin.rev) α)
      (borchersConcatSchwartz k k (f₁ - f₂) (f₁ - f₂)) = 0 := by
    refine hspec (k + k) (Fin.append (β ∘ Fin.rev) α) _ ⟨U, hU_open, hU_sub, fun p hp => ?_⟩
    rw [minkowskiFourier_borchersProduct_eq k k (f₁ - f₂) (f₁ - f₂) _
      (borchersConcatSchwartz_apply k k (f₁ - f₂) (f₁ - f₂)) p]
    have hq0 : minkowskiFourier (f₁ - f₂) (fun i => -p (Fin.castAdd k (Fin.rev i))) = 0 := by
      have h_sub_f : minkowskiFourier (f₁ - f₂) (fun i => -p (Fin.castAdd k (Fin.rev i))) =
          minkowskiFourier f₁ (fun i => -p (Fin.castAdd k (Fin.rev i))) -
            minkowskiFourier f₂ (fun i => -p (Fin.castAdd k (Fin.rev i))) := by
        rw [← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply,
          minkowskiFourierCLM_apply, minkowskiFourierCLM_apply]
      rw [h_sub_f, sub_eq_zero]
      exact h_eq _ hp
    rw [hq0, star_zero, zero_mul]
  rw [hW0, mul_zero]

namespace ForwardConeOSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

noncomputable def osToWightmanVec
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A : OSConfig ι) :
    P.WightmanHilbertSpace :=
  wightmanSchwartzVec P.toWightmanPositiveData A.1 A.2.1
    (osToWightmanTest A.1 (wickEmbedN A.1 A.2.2.val) (wickEmbedN_mem_posTubeN A.2.2.property))

@[simp]
lemma osToWightmanVec_osVacuumConfig
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.osToWightmanVec (osVacuumConfig ι) = P.wightmanVacuumVec := by
  dsimp [osToWightmanVec, osVacuumConfig, osToWightmanTest, wightmanVacuumVec]
  exact wightmanSchwartzVec_compact P.toWightmanPositiveData 0 Fin.elim0
    (momentumWavepacketCompactSchwartz 0 0)

theorem inner_osToWightmanVec
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A B : OSConfig ι) :
    ⟪P.osToWightmanVec A, P.osToWightmanVec B⟫_ℂ = osKernel S 𝒮 A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  dsimp [osToWightmanVec, osKernel, osConcatIdx]
  rw [inner_wightmanSchwartzVec]
  refine Finset.sum_congr rfl fun β _ => ?_
  congr 1
  exact wightman_borchersConcatSchwartz_osToWightmanTest_eq_schwinger
    R P.E P.spectrum P.poincare P.schwinger_eq j k (Fin.append (β ∘ Fin.rev) α') hx hy

theorem ortho_osToWightmanVec_eq_zero
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (χ : P.WightmanHilbertSpace)
    (h_orth : ∀ A : OSConfig ι, ⟪χ, P.osToWightmanVec A⟫_ℂ = 0) :
    χ = 0 := by
  refine eq_zero_of_inner_wightmanBasis_eq_zero P.toWightmanPositiveData fun cfg => ?_
  rw [inner_eq_zero_symm]
  rcases cfg with ⟨k, α, f_c⟩
  rw [← wightmanSchwartzVec_compact P.toWightmanPositiveData k α f_c]
  generalize f_c.val = g
  by_cases hk : 0 < k
  · have hn : ¬k + 1 ≤ 1 := by omega
    let L_vec : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ →L[ℂ] P.WightmanHilbertSpace :=
      (wightmanSchwartzVec P.toWightmanPositiveData k α).comp
        ((invMinkowskiFourierCLM k).comp (pullbackTailSchwartzCLM k))
    let T : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
      (innerSL ℂ χ).comp L_vec
    have hT_ana : AnalyticOn ℂ (fun w => T (cone_psi_schwartz_total (k + 1) hn w))
        (forward_tube_n (k + 1)) :=
      AnalyticOnNhd.analyticOn fun w hw => cone_psi_schwartz_analyticAt hn hw T
    have hT_euclid : ∀ x ∈ posOrderedEuclidN (k + 1),
        T (cone_psi_schwartz_total (k + 1) hn (wickEmbedN (k + 1) x)) = 0 := by
      intro x hx
      have hx_tube : wickEmbedN (k + 1) x ∈ forward_tube_n (k + 1) :=
        wickEmbedN_mem_forward_tube_n (k + 1) hx.2
      rw [cone_psi_schwartz_total_eq hn hx_tube]
      let y_diff : Fin k → Fin 4 → ℝ := fun u => x (Fin.succ u) - x 0
      have hy_diff : y_diff ∈ posOrderedEuclidN k := by
        refine ⟨fun u => ?_, fun u hu => ?_⟩
        · have hlt := orderedEuclidN_time_lt_of_lt hx.2 (Fin.succ_pos u)
          dsimp [y_diff]
          linarith
        · have hlt := hx.2 (Fin.succ u) (Nat.succ_lt_succ hu)
          have h_idx : (⟨(Fin.succ u).val + 1, Nat.succ_lt_succ hu⟩ : Fin (k + 1)) =
              Fin.succ ⟨u.val + 1, hu⟩ := Fin.ext rfl
          rw [h_idx] at hlt
          change x (Fin.succ u) 0 - x 0 0 < x (Fin.succ ⟨u.val + 1, hu⟩) 0 - x 0 0
          linarith
      have h_pull_eq : pullbackTailSchwartzCLM k
          (cone_psi_schwartz (k + 1) hn (wickEmbedN (k + 1) x) hx_tube) =
          pullbackTailSchwartzCLM k
            (cone_psi_schwartz (k + 1) hn (posTubeExtendCLM k (wickEmbedN k y_diff))
              (wickEmbedN_mem_posTubeN hy_diff)) := by
        ext q
        change cone_psi (k + 1) (wickEmbedN (k + 1) x) (embedZeroSumMomentumCLM k q) =
          cone_psi (k + 1) (posTubeExtendCLM k (wickEmbedN k y_diff))
            (embedZeroSumMomentumCLM k q)
        dsimp [cone_psi]
        congr 1
        rw [vladimirov_kernel_embedZeroSumMomentum,
          vladimirov_kernel_posTubeExtend_embedZeroSumMomentum]
        have h_sub_w : (fun u : Fin k =>
            wickEmbedN (k + 1) x (Fin.succ u) - wickEmbedN (k + 1) x 0) =
            wickEmbedN k y_diff := by
          ext u μ
          by_cases hμ : μ = 0
          · subst hμ
            simp [wickEmbedN, wickEmbed, y_diff]
            ring
          · simp [wickEmbedN, wickEmbed, y_diff, hμ]
        rw [h_sub_w]
      have h_vec_eq : L_vec (cone_psi_schwartz (k + 1) hn (wickEmbedN (k + 1) x) hx_tube) =
          P.osToWightmanVec ⟨k, (α, ⟨y_diff, hy_diff⟩)⟩ := by
        dsimp [L_vec, osToWightmanVec, osToWightmanTest]
        rw [dif_pos hk, h_pull_eq]
      change ⟪χ, L_vec (cone_psi_schwartz (k + 1) hn (wickEmbedN (k + 1) x) hx_tube)⟫_ℂ = 0
      rw [h_vec_eq]
      exact h_orth ⟨k, (α, ⟨y_diff, hy_diff⟩)⟩
    have hT_tube : ∀ w ∈ forward_tube_n (k + 1),
        T (cone_psi_schwartz_total (k + 1) hn w) = 0 :=
      analyticOn_forward_tube_eq_zero_of_posOrderedEuclidN_eq_zero (k + 1) hT_ana hT_euclid
    obtain ⟨f_lift, hf_lift⟩ := exists_zeroSumLift_schwartz k g
    have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
    have h_conv_zero : ∀ (t : ℝ) (ht : 0 < t),
        T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht) = 0 := by
      intro t ht
      rw [clm_conv_schwartz_eq_integral (k + 1) hn T f_lift unit_time_vector hv t ht]
      refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      have hw_mem := tubeApproach_mem_forward_tube_n (k + 1) x unit_time_vector hv t ht
      have h0 := hT_tube _ hw_mem
      rw [cone_psi_schwartz_total_eq hn hw_mem] at h0
      rw [h0, mul_zero]
      rfl
    have h_tend : Tendsto (fun t : ℝ =>
        if ht : 0 < t then T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht) else 0)
        (𝓝[>] 0) (𝓝 (T (cone_limit_schwartz (k + 1) f_lift))) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨s, C_T, hCT_pos, hT_bound⟩ := schwartz_clm_bound (k + 1) T
      have h_each : ∀ km ∈ s, ∀ᶠ t : ℝ in 𝓝[>] 0,
          (if ht : 0 < t then
            (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ km)
              (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht -
                cone_limit_schwartz (k + 1) f_lift)
          else 0) < ε / C_T := fun km _ =>
        (conv_schwartz_tendsto_limit (k + 1) hn f_lift unit_time_vector hv km).eventually
          (Iio_mem_nhds (div_pos hε hCT_pos))
      filter_upwards [self_mem_nhdsWithin, (Filter.eventually_all_finset s).mpr h_each]
        with t ht h_km
      have ht_pos : 0 < t := ht
      rw [dif_pos ht_pos, dist_eq_norm, ← map_sub]
      have h_sup_lt : (s.sup (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ))
          (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
            cone_limit_schwartz (k + 1) f_lift) < ε / C_T := by
        classical
        have h_sub : ∀ u : Finset (ℕ × ℕ), u ⊆ s →
            (u.sup (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ))
              (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
                cone_limit_schwartz (k + 1) f_lift) < ε / C_T := by
          intro u
          induction u using Finset.induction_on with
          | empty =>
            intro _
            rw [Finset.sup_empty, Seminorm.bot_eq_zero, _root_.zero_apply]
            exact div_pos hε hCT_pos
          | @insert a u ha ih =>
            intro hu
            rw [Finset.sup_insert, Seminorm.sup_apply]
            have ha_lt := h_km a (hu (Finset.mem_insert_self a u))
            rw [dif_pos ht_pos] at ha_lt
            exact max_lt ha_lt (ih fun km hkm => hu (Finset.mem_insert_of_mem hkm))
        exact h_sub s fun _ h => h
      calc ‖T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
              cone_limit_schwartz (k + 1) f_lift)‖
          ≤ C_T * (s.sup (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ))
              (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
                cone_limit_schwartz (k + 1) f_lift) := hT_bound _
        _ < C_T * (ε / C_T) := mul_lt_mul_of_pos_left h_sup_lt hCT_pos
        _ = ε := mul_div_cancel₀ ε hCT_pos.ne'
    have h_ev0 : (fun t : ℝ =>
        if ht : 0 < t then T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht) else 0) =
        fun _ => (0 : ℂ) := by
      ext t
      split_ifs with ht
      · exact h_conv_zero t ht
      · rfl
    rw [h_ev0] at h_tend
    haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
    have h_lim0 : T (cone_limit_schwartz (k + 1) f_lift) = 0 :=
      tendsto_nhds_unique h_tend tendsto_const_nhds
    let g_cut : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ :=
      invMinkowskiFourierCLM k
        (pullbackTailSchwartzCLM k (cone_limit_schwartz (k + 1) f_lift))
    have hg_eq_vec : wightmanSchwartzVec P.toWightmanPositiveData k α g_cut =
        wightmanSchwartzVec P.toWightmanPositiveData k α g := by
      refine wightmanSchwartzVec_eq_of_fourier_eq_on_tailOpenNhd P.toWightmanPositiveData
        P.spectrum k α g_cut g fun q hq => ?_
      dsimp [g_cut]
      rw [minkowskiFourier_invMinkowskiFourierCLM_all, pullbackTailSchwartzCLM_apply,
        cone_limit_schwartz_apply,
        coneSpectralCutoff_eq_one_of_mem_coneOpenNhd (k + 1) hq,
        Complex.ofReal_one, one_mul, hf_lift q]
    rw [← hg_eq_vec]
    exact h_lim0
  · have hk0 : k = 0 := by omega
    subst hk0
    have hc_ne : momentumWavepacketSchwartz 0 0 0 ≠ 0 := by
      intro hc
      have h_int := integral_momentumWavepacketSchwartz_zero 0
      have h_fn0 : ∀ x : Fin 0 → Fin 4 → ℝ, momentumWavepacketSchwartz 0 0 x = 0 := fun x => by
        rw [Subsingleton.elim x 0, hc]
      have h_int0 : ∫ x : Fin 0 → Fin 4 → ℝ, momentumWavepacketSchwartz 0 0 x = 0 :=
        MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall h_fn0)
      rw [h_int0] at h_int
      exact zero_ne_one h_int
    let A₀ : OSConfig ι :=
      ⟨0, (α, ⟨euclidOrderedBasePoint 0, euclidOrderedBasePoint_mem_posOrderedEuclidN 0⟩)⟩
    have h_test0 : osToWightmanTest 0 (wickEmbedN 0 A₀.2.2.val)
        (wickEmbedN_mem_posTubeN A₀.2.2.property) = momentumWavepacketSchwartz 0 0 := rfl
    have hg_smul : g = (g 0 / momentumWavepacketSchwartz 0 0 0) •
        osToWightmanTest 0 (wickEmbedN 0 A₀.2.2.val)
          (wickEmbedN_mem_posTubeN A₀.2.2.property) := by
      rw [h_test0]
      ext x
      rw [Subsingleton.elim x 0, _root_.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hc_ne]
    rw [hg_smul, map_smul, inner_smul_right]
    have h0 := h_orth A₀
    dsimp [osToWightmanVec, A₀] at h0 ⊢
    rw [h0, mul_zero]

noncomputable def osToWightmanLinearIsometryEquiv
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.Hilbert ≃ₗᵢ[ℂ] P.WightmanHilbertSpace :=
  wavepacketOSLinearIsometryEquiv_of_ortho_eq_zero P.osData P.osToWightmanVec
    P.inner_osToWightmanVec P.ortho_osToWightmanVec_eq_zero

@[simp]
theorem osToWightmanLinearIsometryEquiv_osBasis
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A : OSConfig ι) :
    P.osToWightmanLinearIsometryEquiv (osBasis P.osData A) = P.osToWightmanVec A :=
  wavepacketOSLinearIsometry_osBasis P.osData P.osToWightmanVec P.inner_osToWightmanVec A

@[simp]
theorem osToWightmanLinearIsometryEquiv_vacuum
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.osToWightmanLinearIsometryEquiv P.vacuum = P.wightmanVacuumVec := by
  dsimp [osToWightmanLinearIsometryEquiv, wavepacketOSLinearIsometryEquiv_of_ortho_eq_zero, vacuum]
  change wavepacketOSLinearIsometry P.osData P.osToWightmanVec P.inner_osToWightmanVec
    (osVacuum P.osData) = P.wightmanVacuumVec
  rw [wavepacketOSLinearIsometry_osVacuum, osToWightmanVec_osVacuumConfig]

theorem osToWightmanVec_spatialShift
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (b : Fin 3 → ℝ) (A : OSConfig ι) :
    P.osToWightmanVec (osConfigSpatialShift b A) =
      wightmanSpatialTranslate P.toWightmanPositiveData
        (wightmanTranslationInvariant_of_poincare R P.poincare) b (P.osToWightmanVec A) := by
  let htr := wightmanTranslationInvariant_of_poincare R P.poincare
  rcases A with ⟨k, α, y, hy⟩
  dsimp [osToWightmanVec, osConfigSpatialShift, wightmanSpatialTranslate]
  rw [wightmanTranslate_wightmanSchwartzVec]
  refine wightmanSchwartzVec_eq_of_fourier_eq_on_tailOpenNhd P.toWightmanPositiveData
    P.spectrum k α _ _ fun q hq => ?_
  rw [minkowskiFourier_osToWightmanTest_on_tailOpenNhd _ _ _ hq,
    minkowskiFourier_schwartzDiagTranslateN,
    minkowskiFourier_osToWightmanTest_on_tailOpenNhd _ _ _ hq,
    vladimirov_kernel_wickEmbedN_eq_euclidLaplace,
    vladimirov_kernel_wickEmbedN_eq_euclidLaplace]
  unfold euclidLaplace
  rw [← Complex.exp_add]
  congr 1
  have hb0 : euclidSpatialVec b 0 = 0 := rfl
  have hb1 : euclidSpatialVec b 1 = b 0 := rfl
  have hb2 : euclidSpatialVec b 2 = b 1 := rfl
  have hb3 : euclidSpatialVec b 3 = b 2 := rfl
  rw [minkowskiInner_explicit]
  simp only [Finset.sum_apply, Pi.add_apply, hb0, hb1, hb2, hb3]
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem osToWightmanLinearIsometryEquiv_spatialTranslate
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (b : Fin 3 → ℝ) (x : P.Hilbert) :
    P.osToWightmanLinearIsometryEquiv (P.spatialTranslate b x) =
      wightmanSpatialTranslate P.toWightmanPositiveData
        (wightmanTranslationInvariant_of_poincare R P.poincare) b
        (P.osToWightmanLinearIsometryEquiv x) :=
  wavepacketOSLinearIsometry_intertwines_spatial P.osData P.osAxioms.os1_translation
    P.osToWightmanVec P.inner_osToWightmanVec b _ (P.osToWightmanVec_spatialShift b) x

omit [Fintype ι] [DecidableEq ι] in
noncomputable def wickTimeShiftN (k : ℕ) (y : Fin k → Fin 4 → ℝ) (z : ℂ) :
    Fin k → Fin 4 → ℂ :=
  fun u μ => wickEmbedN k y u μ + if μ = 0 then z * Complex.I else 0

omit [Fintype ι] [DecidableEq ι] in
lemma posTubeExtend_wickTimeShiftN_eq (k : ℕ) (y : Fin k → Fin 4 → ℝ) (z : ℂ) :
    posTubeExtendCLM k (wickEmbedN k y) +
        z • posTubeExtendCLM k (fun _ μ => if μ = 0 then Complex.I else 0) =
      posTubeExtendCLM k (wickTimeShiftN k y z) := by
  ext i μ
  refine Fin.cases ?_ ?_ i
  · simp
  · intro u
    dsimp [wickTimeShiftN]
    split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
lemma wickTimeShiftN_mem_posTubeN {k : ℕ} (hk : 0 < k)
    {y : Fin k → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN k)
    {z : ℂ} (hz_re : -y ⟨0, hk⟩ 0 < z.re) :
    wickTimeShiftN k y z ∈ posTubeN k := by
  change posTubeExtendCLM k (wickTimeShiftN k y z) ∈ forward_tube_n (k + 1)
  intro i hi
  by_cases hi0 : i.val = 0
  · have hi_eq : i = 0 := Fin.ext hi0
    have hi1_eq : (⟨i.val + 1, hi⟩ : Fin (k + 1)) = Fin.succ ⟨0, hk⟩ := by
      ext
      dsimp
      omega
    have h_lhs : posTubeExtendCLM k (wickTimeShiftN k y z) i = 0 := by
      rw [hi_eq]
      exact posTubeExtendCLM_zero k _
    have h_rhs : posTubeExtendCLM k (wickTimeShiftN k y z) ⟨i.val + 1, hi⟩ =
        wickTimeShiftN k y z ⟨0, hk⟩ := by
      rw [hi1_eq]
      exact posTubeExtendCLM_succ k _ _
    rw [h_lhs, h_rhs]
    have h_im : (fun μ : Fin 4 => -((0 - wickTimeShiftN k y z ⟨0, hk⟩) μ).im) =
        euclidTimeVec (y ⟨0, hk⟩ 0 + z.re) := by
      ext μ
      fin_cases μ <;> simp [wickTimeShiftN, wickEmbedN, wickEmbed, euclidTimeVec]
    rw [h_im]
    refine ⟨by simp [euclidTimeVec]; linarith, ?_⟩
    rw [minkowskiInner_explicit]
    simp only [euclidTimeVec, Fin.isValue, ↓reduceIte, Fin.reduceEq]
    have hpos : 0 < y ⟨0, hk⟩ 0 + z.re := by linarith
    nlinarith
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    have hm1 : m + 1 < k := by omega
    have hm0 : m < k := by omega
    have hi_eq : i = Fin.succ ⟨m, hm0⟩ := Fin.ext hm
    have hi1_eq : (⟨i.val + 1, hi⟩ : Fin (k + 1)) = Fin.succ ⟨m + 1, hm1⟩ := by
      ext
      dsimp
      omega
    have h_lhs : posTubeExtendCLM k (wickTimeShiftN k y z) i =
        wickTimeShiftN k y z ⟨m, hm0⟩ :=
      (congrArg (posTubeExtendCLM k (wickTimeShiftN k y z)) hi_eq).trans
        (posTubeExtendCLM_succ k _ _)
    have h_rhs : posTubeExtendCLM k (wickTimeShiftN k y z) ⟨i.val + 1, hi⟩ =
        wickTimeShiftN k y z ⟨m + 1, hm1⟩ :=
      (congrArg (posTubeExtendCLM k (wickTimeShiftN k y z)) hi1_eq).trans
        (posTubeExtendCLM_succ k _ _)
    rw [h_lhs, h_rhs]
    have h_im : (fun μ : Fin 4 =>
        -((wickTimeShiftN k y z ⟨m, hm0⟩ -
          wickTimeShiftN k y z ⟨m + 1, hm1⟩) μ).im) =
        (fun μ : Fin 4 =>
          -((wickEmbed (y ⟨m, hm0⟩) - wickEmbed (y ⟨m + 1, hm1⟩)) μ).im) := by
      ext μ
      fin_cases μ <;> simp [wickTimeShiftN, wickEmbedN, wickEmbed]
    rw [h_im]
    have hm_fin : (⟨m, hm0⟩ : Fin k).val + 1 < k := hm1
    exact (wickEmbed_sub_neg_im_mem_forward_light_cone_iff _ _).mpr
      (hy.2 ⟨m, hm0⟩ hm_fin)

lemma osToWightmanVec_wickTimeShift_mul_I
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    {k : ℕ} (α' : Fin k → ι)
    {y : Fin k → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN k) (t : ℝ)
    (hz_it_mem : wickTimeShiftN k y (Complex.I * (t : ℂ)) ∈ posTubeN k) :
    wightmanSchwartzVec P.toWightmanPositiveData k α'
        (osToWightmanTest k (wickTimeShiftN k y (Complex.I * (t : ℂ))) hz_it_mem) =
      wightmanTimeTranslate P.toWightmanPositiveData
        (wightmanTranslationInvariant_of_poincare R P.poincare) (-t)
        (P.osToWightmanVec ⟨k, (α', ⟨y, hy⟩)⟩) := by
  dsimp [wightmanTimeTranslate, osToWightmanVec]
  rw [wightmanTranslate_wightmanSchwartzVec]
  refine wightmanSchwartzVec_eq_of_fourier_eq_on_tailOpenNhd P.toWightmanPositiveData
    P.spectrum k α' _ _ fun q hq => ?_
  rw [minkowskiFourier_osToWightmanTest_on_tailOpenNhd _ _ _ hq,
    minkowskiFourier_schwartzDiagTranslateN,
    minkowskiFourier_osToWightmanTest_on_tailOpenNhd _ _ _ hq]
  unfold vladimirov_kernel
  rw [← Complex.exp_add]
  congr 1
  have ht0 : euclidTimeVec (-t) 0 = -t := rfl
  have ht1 : euclidTimeVec (-t) 1 = 0 := rfl
  have ht2 : euclidTimeVec (-t) 2 = 0 := rfl
  have ht3 : euclidTimeVec (-t) 3 = 0 := rfl
  rw [minkowskiInner_explicit]
  simp only [Finset.sum_apply, ht0, ht1, ht2, ht3, mul_zero, sub_zero]
  push_cast
  have h_Ii : Complex.I * (t : ℂ) * Complex.I = -(t : ℂ) := by
    calc Complex.I * (t : ℂ) * Complex.I = (Complex.I * Complex.I) * (t : ℂ) := by ring
      _ = -(t : ℂ) := by rw [Complex.I_mul_I]; ring
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [minkowskiInnerC, wickTimeShiftN, Fin.isValue, ↓reduceIte, Fin.reduceEq, h_Ii]
  ring

theorem osToWightmanLinearIsometryEquiv_realTimeUnitary
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (t : ℝ) (x : P.Hilbert) :
    P.osToWightmanLinearIsometryEquiv (P.semigroup.realTimeUnitary t x) =
      wightmanTimeTranslate P.toWightmanPositiveData
        (wightmanTranslationInvariant_of_poincare R P.poincare) (-t)
        (P.osToWightmanLinearIsometryEquiv x) := by
  let htr := wightmanTranslationInvariant_of_poincare R P.poincare
  let J : P.Hilbert →L[ℂ] P.WightmanHilbertSpace :=
    P.osToWightmanLinearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have h_basis : ∀ A : OSConfig ι,
      J (P.semigroup.realTimeUnitary t (osBasis P.osData A)) =
        wightmanTimeTranslate P.toWightmanPositiveData htr (-t) (P.osToWightmanVec A) := by
    intro A
    rcases A with ⟨k, α', y, hy⟩
    by_cases hk : 0 < k
    · have hn : ¬k + 1 ≤ 1 := by omega
      let A_cfg : OSConfig ι := ⟨k, (α', ⟨y, hy⟩)⟩
      suffices h_diff : J (P.semigroup.realTimeUnitary t (osBasis P.osData A_cfg)) -
          wightmanTimeTranslate P.toWightmanPositiveData htr (-t) (P.osToWightmanVec A_cfg) = 0 from
        sub_eq_zero.mp h_diff
      refine P.ortho_osToWightmanVec_eq_zero _ fun B => ?_
      rw [inner_eq_zero_symm, inner_sub_right, sub_eq_zero]
      have h_lhs_inner : ⟪P.osToWightmanVec B,
          J (P.semigroup.realTimeUnitary t (osBasis P.osData A_cfg))⟫_ℂ =
          ⟪osBasis P.osData B, P.semigroup.realTimeUnitary t (osBasis P.osData A_cfg)⟫_ℂ := by
        rw [← P.osToWightmanLinearIsometryEquiv_osBasis B]
        exact P.osToWightmanLinearIsometryEquiv.inner_map_map _ _
      rw [h_lhs_inner]
      rcases h_holo (osBasis P.osData B) (osBasis P.osData A_cfg) with
        ⟨F_L, hFL_eq, hFL_cont, hFL_diff⟩
      let v_dir : Fin (k + 1) → Fin 4 → ℂ :=
        posTubeExtendCLM k (fun _ μ => if μ = 0 then Complex.I else 0)
      let Φ_aff : ℂ → (Fin (k + 1) → Fin 4 → ℂ) :=
        fun z => posTubeExtendCLM k (wickEmbedN k y) + z • v_dir
      let T_B : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
        (innerSL ℂ (P.osToWightmanVec B)).comp
          ((wightmanSchwartzVec P.toWightmanPositiveData k α').comp
            ((invMinkowskiFourierCLM k).comp (pullbackTailSchwartzCLM k)))
      let F_R : ℂ → ℂ := fun z => T_B (cone_psi_schwartz_total (k + 1) hn (Φ_aff z))
      have hFR_ana : ∀ z ∈ rightHalfPlane, AnalyticAt ℂ F_R z := by
        intro z hz
        have hz_re : -y ⟨0, hk⟩ 0 < z.re := by
          have hy0 : 0 < y ⟨0, hk⟩ 0 := hy.1 ⟨0, hk⟩
          have hz0 : 0 ≤ z.re := hz
          linarith
        have hΦ_mem : Φ_aff z ∈ forward_tube_n (k + 1) := by
          dsimp [Φ_aff, v_dir]
          rw [posTubeExtend_wickTimeShiftN_eq]
          exact wickTimeShiftN_mem_posTubeN hk hy hz_re
        have h_aff_ana : AnalyticAt ℂ Φ_aff z :=
          analyticAt_const.add (analyticAt_id.smul analyticAt_const)
        exact (cone_psi_schwartz_analyticAt hn hΦ_mem T_B).comp h_aff_ana
      have h_real_eq : ∀ (τ : ℝ), 0 ≤ τ → F_L (τ : ℂ) - F_R (τ : ℂ) = 0 := by
        intro τ hτ
        rw [sub_eq_zero, hFL_eq (τ : ℂ) (ofReal_mem_rightHalfPlane hτ), P.semigroup.real_eq τ hτ]
        change ⟪osBasis P.osData B,
          osContractionSemigroup P.osData P.contraction τ hτ (osBasis P.osData A_cfg)⟫_ℂ =
          F_R (τ : ℂ)
        have h_os_shift : osContractionSemigroup P.osData P.contraction τ hτ
            (osBasis P.osData A_cfg) = osBasis P.osData (osConfigTimeShift τ hτ A_cfg) := by
          dsimp [osBasis]
          rw [osContractionSemigroup_toOSHilbert]
          dsimp [osTimeShiftLM]
          rw [osLiftConfigMap_osBasisPre]
        rw [h_os_shift,
          ← P.osToWightmanLinearIsometryEquiv.inner_map_map,
          osToWightmanLinearIsometryEquiv_osBasis,
          osToWightmanLinearIsometryEquiv_osBasis]
        have hz_τ : wickTimeShiftN k y (τ : ℂ) = wickEmbedN k (fun u => y u + euclidTimeVec τ) := by
          ext u μ
          by_cases hμ : μ = 0
          · subst hμ
            simp [wickTimeShiftN, wickEmbedN, wickEmbed, euclidTimeVec]
            ring
          · simp [wickTimeShiftN, wickEmbedN, wickEmbed, euclidTimeVec, hμ]
        have hΦ_τ : Φ_aff (τ : ℂ) =
            posTubeExtendCLM k (wickEmbedN k (fun u => y u + euclidTimeVec τ)) := by
          change posTubeExtendCLM k (wickEmbedN k y) +
              (τ : ℂ) • posTubeExtendCLM k (fun _ μ => if μ = 0 then Complex.I else 0) = _
          rw [posTubeExtend_wickTimeShiftN_eq, hz_τ]
        have h_mem_τ : posTubeExtendCLM k (wickEmbedN k (fun u => y u + euclidTimeVec τ)) ∈
            forward_tube_n (k + 1) :=
          wickEmbedN_mem_posTubeN (timeShift_mem_posOrderedEuclidN k hy hτ)
        dsimp [F_R]
        rw [hΦ_τ, cone_psi_schwartz_total_eq hn h_mem_τ]
        dsimp [T_B, osToWightmanVec, osConfigTimeShift, osToWightmanTest, A_cfg]
        rw [dif_pos hk]
      have h_imag_eq : F_L (Complex.I * (t : ℂ)) = F_R (Complex.I * (t : ℂ)) := by
        refine sub_eq_zero.mp (eq_zero_on_rightHalfPlane_of_real_zero
          (hFL_diff.sub fun z (hz : 0 < z.re) =>
            (hFR_ana z hz.le).differentiableAt.differentiableWithinAt)
          (hFL_cont.sub fun z hz => (hFR_ana z hz).continuousAt.continuousWithinAt)
          h_real_eq (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t))
      have hFL_it : F_L (Complex.I * (t : ℂ)) =
          ⟪osBasis P.osData B, P.semigroup.realTimeUnitary t (osBasis P.osData A_cfg)⟫_ℂ :=
        hFL_eq (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t)
      have hFR_it : F_R (Complex.I * (t : ℂ)) =
          ⟪P.osToWightmanVec B,
            wightmanTimeTranslate P.toWightmanPositiveData htr (-t)
              (P.osToWightmanVec A_cfg)⟫_ℂ := by
        have hz_it_mem : wickTimeShiftN k y (Complex.I * (t : ℂ)) ∈ posTubeN k := by
          apply wickTimeShiftN_mem_posTubeN hk hy
          have hy0 : 0 < y ⟨0, hk⟩ 0 := hy.1 ⟨0, hk⟩
          simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, one_mul, sub_self]
          linarith
        dsimp [F_R, Φ_aff, v_dir]
        rw [posTubeExtend_wickTimeShiftN_eq, cone_psi_schwartz_total_eq hn hz_it_mem]
        change ⟪P.osToWightmanVec B,
            wightmanSchwartzVec P.toWightmanPositiveData k α'
              (invMinkowskiFourierCLM k
                (pullbackTailSchwartzCLM k
                  (cone_psi_schwartz (k + 1) hn
                    (posTubeExtendCLM k (wickTimeShiftN k y (Complex.I * (t : ℂ))))
                    hz_it_mem)))⟫_ℂ = _
        have h_test_eq : invMinkowskiFourierCLM k
            (pullbackTailSchwartzCLM k
              (cone_psi_schwartz (k + 1) hn
                (posTubeExtendCLM k (wickTimeShiftN k y (Complex.I * (t : ℂ)))) hz_it_mem)) =
            osToWightmanTest k (wickTimeShiftN k y (Complex.I * (t : ℂ))) hz_it_mem := by
          dsimp [osToWightmanTest]
          rw [dif_pos hk]
        rw [h_test_eq, P.osToWightmanVec_wickTimeShift_mul_I α' hy t hz_it_mem]
      exact hFL_it.symm.trans (h_imag_eq.trans hFR_it)
    · have hk0 : k = 0 := by omega
      subst hk0
      have hA_vac : (⟨0, (α', ⟨y, hy⟩)⟩ : OSConfig ι) = osVacuumConfig ι := by
        dsimp [osVacuumConfig]
        congr 1
        ext1
        · exact Subsingleton.elim _ _
        · apply Subtype.ext
          exact Subsingleton.elim _ _
      rw [hA_vac]
      have h_vac_t : P.semigroup.realTimeUnitary t P.vacuum = P.vacuum :=
        P.semigroup.realTimeUnitary_vacuum t
      change P.osToWightmanLinearIsometryEquiv
          (P.semigroup.realTimeUnitary t P.vacuum) =
        wightmanTimeTranslate P.toWightmanPositiveData htr (-t)
          (P.osToWightmanVec (osVacuumConfig ι))
      rw [h_vac_t, P.osToWightmanLinearIsometryEquiv_vacuum,
        P.osToWightmanVec_osVacuumConfig]
      exact (wightmanTimeTranslate_vacuum P.toWightmanPositiveData htr (-t)).symm
  let U_t : P.Hilbert →L[ℂ] P.Hilbert := P.semigroup.realTimeUnitary t
  let L_lhs : P.Hilbert →L[ℂ] P.WightmanHilbertSpace := J.comp U_t
  let L_rhs : P.Hilbert →L[ℂ] P.WightmanHilbertSpace :=
    (wightmanTimeTranslate P.toWightmanPositiveData htr (-t)).comp J
  change L_lhs x = L_rhs x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq L_lhs.continuous L_rhs.continuous
  | ih Ψ =>
    change L_lhs (toOSHilbert P.osData Ψ) = L_rhs (toOSHilbert P.osData Ψ)
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre P.osData Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre P.osData Ψ]
    unfold Finsupp.sum
    rw [map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    dsimp only
    rw [map_smul, L_lhs.map_smul, L_rhs.map_smul]
    congr 1
    change J (P.semigroup.realTimeUnitary t (osBasis P.osData A)) =
      wightmanTimeTranslate P.toWightmanPositiveData htr (-t) (J (osBasis P.osData A))
    rw [h_basis A]
    congr 1
    exact (P.osToWightmanLinearIsometryEquiv_osBasis A).symm

theorem osToWightmanLinearIsometryEquiv_spacetimeTranslate
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (a : Fin 4 → ℝ) (x : P.Hilbert) :
    P.osToWightmanLinearIsometryEquiv
        (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) x) =
      wightmanTranslate P.toWightmanPositiveData
        (wightmanTranslationInvariant_of_poincare R P.poincare) a
        (P.osToWightmanLinearIsometryEquiv x) := by
  let htr := wightmanTranslationInvariant_of_poincare R P.poincare
  have h_sp : spatialPart (euclidTimeReflect a) = spatialPart a := by
    ext i
    simp [spatialPart, euclidTimeReflect]
  have h_t : -(euclidTimeReflect a 0) = a 0 := by
    simp [euclidTimeReflect]
  unfold OSHolomorphicSemigroup.spacetimeTranslate
  simp only [ContinuousLinearMap.comp_apply, h_sp]
  rw [P.osToWightmanLinearIsometryEquiv_realTimeUnitary h_holo, h_t]
  change wightmanTimeTranslate P.toWightmanPositiveData htr (a 0)
      (P.osToWightmanLinearIsometryEquiv (P.spatialTranslate (spatialPart a) x)) = _
  rw [P.osToWightmanLinearIsometryEquiv_spatialTranslate,
    wightmanTranslate_eq_time_comp_spatial P.toWightmanPositiveData htr a]
  rfl

theorem osToWightmanLinearIsometryEquiv_symm_wightmanTranslate
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (a : Fin 4 → ℝ) (y : P.WightmanHilbertSpace) :
    P.osToWightmanLinearIsometryEquiv.symm
        (wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare R P.poincare) a y) =
      P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a)
        (P.osToWightmanLinearIsometryEquiv.symm y) := by
  apply P.osToWightmanLinearIsometryEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply,
    P.osToWightmanLinearIsometryEquiv_spacetimeTranslate h_holo,
    LinearIsometryEquiv.apply_symm_apply]

noncomputable def canonicalOSWavepacket
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A : WightmanConfig ι) :
    P.Hilbert :=
  P.osToWightmanLinearIsometryEquiv.symm (P.wightmanBasisVec A)

theorem inner_canonicalOSWavepacket
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (A B : WightmanConfig ι) :
    ⟪P.canonicalOSWavepacket A, P.canonicalOSWavepacket B⟫_ℂ =
      wightmanKernel S P.W A B := by
  dsimp [canonicalOSWavepacket, wightmanBasisVec]
  rw [P.osToWightmanLinearIsometryEquiv.symm.inner_map_map, inner_wightmanBasis]
  rfl

@[simp]
theorem canonicalOSWavepacket_vacuum
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) :
    P.canonicalOSWavepacket (wightmanVacuumConfig ι) = P.vacuum := by
  apply P.osToWightmanLinearIsometryEquiv.injective
  dsimp [canonicalOSWavepacket]
  rw [LinearIsometryEquiv.apply_symm_apply, P.osToWightmanLinearIsometryEquiv_vacuum]
  rfl

theorem canonicalOSWavepacket_translate
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (a : Fin 4 → ℝ) (A : WightmanConfig ι) :
    P.canonicalOSWavepacket (wightmanConfigTranslate a A) =
      P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a)
        (P.canonicalOSWavepacket A) := by
  dsimp [canonicalOSWavepacket, wightmanBasisVec]
  rw [← wightmanTranslate_wightmanBasis P.toWightmanPositiveData
    (wightmanTranslationInvariant_of_poincare R P.poincare) a A]
  exact P.osToWightmanLinearIsometryEquiv_symm_wightmanTranslate h_holo a _

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuumOfWavepacket
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (hnorm : OSVacuumNormalized 𝒮)
    (hcluster : OSTimeClusterDecomposition P.osData)
    (Φ : WightmanConfig ι → P.Hilbert)
    (h_ker : ∀ A B : WightmanConfig ι, ⟪Φ A, Φ B⟫_ℂ = wightmanKernel S P.W A B)
    (h_vac : Φ (wightmanVacuumConfig ι) = P.vacuum)
    (h_trans : ∀ (a : Fin 4 → ℝ) (A : WightmanConfig ι),
      Φ (wightmanConfigTranslate a A) =
        P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) (Φ A)) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η where
  toWightmanAxioms := P.toWightmanAxioms
  vacuumNormalized :=
    (wightmanVacuumNormalized_iff_osVacuumNormalized_of_schwinger_eq S P.E 𝒮
      P.schwinger_eq).mpr hnorm
  vacuumUnique :=
    let htr := wightmanTranslationInvariant_of_poincare R P.poincare
    let ι_W := wavepacketWightmanLinearIsometry P.toWightmanPositiveData Φ h_ker
    let U : (Fin 4 → ℝ) → P.Hilbert →L[ℂ] P.Hilbert :=
      fun a => P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a)
    wightmanVacuumUnique_of_linearIsometry P.toWightmanPositiveData htr ι_W
      ((wavepacketWightmanLinearIsometry_wightmanVacuum
        P.toWightmanPositiveData Φ h_ker).trans h_vac)
      U
      (wavepacketWightmanLinearIsometry_intertwines_translate
        P.toWightmanPositiveData htr Φ h_ker U h_trans)
      (fun _ hfixed => eq_smul_osVacuum_of_spacetimeTranslate_fixed
        P.semigroup h_holo P.osAxioms.os1_translation hcluster
        (fun a => by
          have h := hfixed (euclidTimeReflect a)
          dsimp [U] at h
          rwa [euclidTimeReflect_involutive] at h))

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuum
    (P : ForwardConeOSReconstructedWightman R S η 𝒮)
    (h_holo : P.semigroup.IsWeaklyHolomorphic)
    (hnorm : OSVacuumNormalized 𝒮)
    (hcluster : OSTimeClusterDecomposition P.osData) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  P.toGeneralWightmanAxiomsWithUniqueVacuumOfWavepacket h_holo hnorm hcluster
    P.canonicalOSWavepacket
    P.inner_canonicalOSWavepacket
    P.canonicalOSWavepacket_vacuum
    (P.canonicalOSWavepacket_translate h_holo)

noncomputable def permutedSchwinger
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) : SchwingerFamily ι :=
  schwingerFromPermutedTube R P.W η P.E

theorem permutedSchwinger_eq_on_orderedEuclidN
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (hη : η = 1 ∨ η = -1)
    (hloc : LocalCommutativity η P.W)
    (n : ℕ) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    P.permutedSchwinger n α x = 𝒮 n α x :=
  (schwingerFromPermutedTube_eq_schwingerFromTube_on_orderedEuclidN_of_localCommutativity
    R P.W hη P.E P.tube_covariant hloc n α hx).trans (P.schwinger_eq n α x hx).symm

theorem toFullEuclidOSAxioms
    (P : ForwardConeOSReconstructedWightman R S η 𝒮) (hη : η = 1 ∨ η = -1)
    (hloc : LocalCommutativity η P.W) :
    FullEuclidOSAxioms R S η P.permutedSchwinger :=
  let h_ord : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → P.permutedSchwinger n α x = 𝒮 n α x :=
    fun n α _ hx => P.permutedSchwinger_eq_on_orderedEuclidN hη hloc n α hx
  { os0_smooth :=
      schwingerFromPermutedTube_contDiffOn_of_localCommutativity
        R P.W hη P.E P.tube_covariant hloc
    os1_translation :=
      schwingerFromPermutedTube_translation_invariant_of_localCommutativity
        R P.W hη P.E P.tube_covariant P.tube_translationInvariant hloc
    os1_rotation :=
      schwingerFromPermutedTube_rotCovariant_of_localCommutativity
        R P.W hη P.E P.tube_covariant hloc
    os2_hermiticity :=
      (osHermiticity_congr_of_eq_on_orderedEuclidN S h_ord).mpr P.osAxioms.os2_hermiticity
    os2_positivity :=
      (osReflectionPositive_congr_of_eq_on_orderedEuclidN S h_ord).mpr
        P.osAxioms.os2_positivity
    os3_permutation :=
      schwingerFromPermutedTube_permutation_of_localCommutativity
        R P.W hη P.E P.tube_covariant hloc }

end ForwardConeOSReconstructedWightman

noncomputable def generalWightmanAxiomsWithUniqueVacuumOfBridge
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hnorm : OSVacuumNormalized 𝒮)
    (bridge : ForwardConeOSEuclideanTubeBridge R S η 𝒮) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  (forwardConeOSReconstructedWightmanOfBridge R S η 𝒮 hOS hcluster
    bridge).toGeneralWightmanAxiomsWithUniqueVacuum
    (hOS.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_timeCluster hcluster)
    hnorm hcluster

namespace OSReconstructionData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}
  {hOS : OSAxioms R S η 𝒮}
  {hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData}

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuum
    (G : OSReconstructionData hOS hcluster)
    (hnorm : OSVacuumNormalized 𝒮) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  G.toForwardConeOSReconstructedWightman.toGeneralWightmanAxiomsWithUniqueVacuum
    G.spec.isWeaklyHolomorphic_toOSHolomorphicSemigroup
    hnorm hcluster

end OSReconstructionData

namespace OSMeasureReconstructionData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}
  {hOS : OSAxioms R S η 𝒮}
  {hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData}

noncomputable def toWightmanAxioms
    (G : OSMeasureReconstructionData hOS hcluster) :
    WightmanAxioms R S η :=
  G.toForwardConeOSReconstructedWightman.toWightmanAxioms

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuum
    (G : OSMeasureReconstructionData hOS hcluster)
    (hnorm : OSVacuumNormalized 𝒮) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  G.toForwardConeOSReconstructedWightman.toGeneralWightmanAxiomsWithUniqueVacuum
    G.spec.isWeaklyHolomorphic
    hnorm hcluster

end OSMeasureReconstructionData

theorem coneVladimirov_euclidExtendedTubePermLocality_of_localCommutativity
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : LocalCommutativity η W) :
    EuclidExtendedTubePermLocality η
      (spinor_H_ext R W (coneVladimirovTubeExtension R W hspec hP)) :=
  euclidExtendedTubePermLocality_of_localCommutativity R W
    (coneVladimirovTubeExtension R W hspec hP)
    (coneVladimirov_tubeCovariant R W hspec hP) hloc

theorem coneVladimirov_fullEuclidOSAxioms_of_localCommutativity
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (W : WightmanFamily ι)
    {η : ℂ} (hη : η = 1 ∨ η = -1)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : LocalCommutativity η W)
    (hherm : TubeWickHermiticity S (coneVladimirovTubeExtension R W hspec hP))
    (hpos : OSReflectionPositive S
      (schwingerFromTube (coneVladimirovTubeExtension R W hspec hP))) :
    FullEuclidOSAxioms R S η
      (schwingerFromPermutedTube R W η (coneVladimirovTubeExtension R W hspec hP)) :=
  schwingerFromPermutedTube_fullEuclidOSAxioms_of_localCommutativity R S W hη
    (coneVladimirovTubeExtension R W hspec hP)
    (coneVladimirov_tubeCovariant R W hspec hP)
    (coneVladimirov_tubeTranslationInvariant R W hspec hP)
    hherm hpos hloc

lemma mem_forward_light_cone_iff_coneGap_pos (v : Fin 4 → ℝ) :
    v ∈ forward_light_cone ↔ 0 < coneGap v := by
  refine ⟨coneGap_pos v, fun hgap => ?_⟩
  dsimp [coneGap] at hgap
  have hs_nn : 0 ≤ (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by positivity
  have hsqrt_nn : 0 ≤ Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := Real.sqrt_nonneg _
  have hv0 : 0 < v 0 := by linarith
  have hlt : Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) < v 0 := by linarith
  have hsq : (Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2)) ^ 2 < (v 0) ^ 2 :=
    pow_lt_pow_left₀ hlt hsqrt_nn two_ne_zero
  rw [Real.sq_sqrt hs_nn] at hsq
  refine ⟨hv0, ?_⟩
  rw [minkowskiInner_explicit]
  linarith

lemma coneGap_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (v : Fin 4 → ℝ) :
    coneGap (t • v) = t * coneGap v := by
  dsimp [coneGap]
  have h_sq : (t * v 1) ^ 2 + (t * v 2) ^ 2 + (t * v 3) ^ 2 =
      t ^ 2 * ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by ring
  rw [h_sq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  ring

lemma coneGap_add_ge (u v : Fin 4 → ℝ) :
    coneGap u + coneGap v ≤ coneGap (u + v) := by
  dsimp [coneGap]
  have hu_nn : 0 ≤ (u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2 := by positivity
  have hv_nn : 0 ≤ (v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2 := by positivity
  have hCS := cauchy_schwarz_3 (u 1) (u 2) (u 3) (v 1) (v 2) (v 3)
  have h_prod : u 1 * v 1 + u 2 * v 2 + u 3 * v 3 ≤
      Real.sqrt ((u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2) *
        Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
    rw [← Real.sqrt_mul hu_nn]
    exact Real.le_sqrt_of_sq_le hCS
  have h_sum_sq : (u 1 + v 1) ^ 2 + (u 2 + v 2) ^ 2 + (u 3 + v 3) ^ 2 ≤
      (Real.sqrt ((u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2) +
        Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2)) ^ 2 := by
    have h1 := Real.sq_sqrt hu_nn
    have h2 := Real.sq_sqrt hv_nn
    nlinarith
  have h_sqrt_le : Real.sqrt ((u 1 + v 1) ^ 2 + (u 2 + v 2) ^ 2 + (u 3 + v 3) ^ 2) ≤
      Real.sqrt ((u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2) +
        Real.sqrt ((v 1) ^ 2 + (v 2) ^ 2 + (v 3) ^ 2) := by
    have h := Real.sqrt_le_sqrt h_sum_sq
    rwa [Real.sqrt_sq (by positivity)] at h
  linarith

lemma coneGap_ge_neg_four_norm (w : Fin 4 → ℝ) :
    -(4 * ‖w‖) ≤ coneGap w := by
  dsimp [coneGap]
  have hw0 : -‖w‖ ≤ w 0 := neg_le_of_abs_le (Real.norm_eq_abs (w 0) ▸ norm_le_pi_norm w 0)
  have hw_i : ∀ i : Fin 4, (w i) ^ 2 ≤ ‖w‖ ^ 2 := fun i => by
    have hi := norm_le_pi_norm w i
    rw [Real.norm_eq_abs] at hi
    exact sq_le_sq.mpr (by rwa [abs_of_nonneg (norm_nonneg w)])
  have h_sq : (w 1) ^ 2 + (w 2) ^ 2 + (w 3) ^ 2 ≤ (3 * ‖w‖) ^ 2 := by
    have h1 := hw_i 1
    have h2 := hw_i 2
    have h3 := hw_i 3
    nlinarith [sq_nonneg ‖w‖]
  have h_sqrt : Real.sqrt ((w 1) ^ 2 + (w 2) ^ 2 + (w 3) ^ 2) ≤ 3 * ‖w‖ := by
    have h := Real.sqrt_le_sqrt h_sq
    rwa [Real.sqrt_sq (by positivity)] at h
  linarith

lemma abs_coneGap_sub_le (u v : Fin 4 → ℝ) :
    |coneGap u - coneGap v| ≤ 4 * ‖u - v‖ := by
  rw [abs_le]
  constructor
  · have h1 := coneGap_add_ge v (u - v)
    rw [add_sub_cancel] at h1
    have h2 := coneGap_ge_neg_four_norm (u - v)
    linarith
  · have h1 := coneGap_add_ge u (v - u)
    rw [add_sub_cancel] at h1
    have h2 := coneGap_ge_neg_four_norm (v - u)
    rw [norm_sub_rev] at h2
    linarith

lemma one_le_prod_real {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 1 ≤ f a) : 1 ≤ ∏ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha1 : 1 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs1 : 1 ≤ ∏ b ∈ s, f b := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    nlinarith

noncomputable def tubeGapFactor (n : ℕ) (z : Fin n → Fin 4 → ℂ) : ℝ :=
  ∏ j : Fin (n - 1),
    (1 + (coneGap (diff_im n z ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j)))⁻¹)

def OSTubeGrowthBound {κ : Type*}
    (H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ (n : ℕ) (α : Fin n → κ), ∃ (C : ℝ) (M N : ℕ), 0 ≤ C ∧
    ∀ z ∈ forward_tube_n n,
      ‖H n α z‖ ≤ C * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N

lemma one_le_tubeGapFactor {n : ℕ} {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    1 ≤ tubeGapFactor n z := by
  unfold tubeGapFactor
  refine one_le_prod_real Finset.univ _ fun j _ => ?_
  have hg := coneGap_pos
    (diff_im n z ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))
    (hz ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))
  linarith [inv_nonneg.mpr hg.le]

lemma tubeGapFactor_nonneg {n : ℕ} {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    0 ≤ tubeGapFactor n z :=
  zero_le_one.trans (one_le_tubeGapFactor hz)

lemma tubeGapFactor_shift_eq (n : ℕ) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    tubeGapFactor n (fun i => z i + a) = tubeGapFactor n z := by
  unfold tubeGapFactor
  refine Finset.prod_congr rfl fun j _ => ?_
  have hd : diff_im n (fun i => z i + a) ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j) =
      diff_im n z ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j) := by
    ext μ
    simp [diff_im, diff_z]
  rw [hd]

noncomputable def zImPoint (n : ℕ) (x y : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℂ :=
  fun i μ => (x i μ : ℂ) + Complex.I * (y i μ : ℂ)

def tubeImDir (n : ℕ) (v : Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i μ => (i.val : ℝ) * v μ

lemma tubeBoundaryLine_eq_zImPoint (n : ℕ) (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ) :
    tubeBoundaryLine n x v t = zImPoint n x (t • tubeImDir n v) := by
  ext i μ
  dsimp [tubeBoundaryLine, zImPoint, tubeImDir]
  push_cast
  ring

lemma diff_im_zImPoint (n : ℕ) (x y : Fin n → Fin 4 → ℝ) (i : Fin n) (hi : i.val + 1 < n) :
    diff_im n (zImPoint n x y) i hi = fun μ => y ⟨i.val + 1, hi⟩ μ - y i μ := by
  ext μ
  simp [diff_im, diff_z, zImPoint]

lemma zImPoint_mem_forward_tube_iff (n : ℕ) (x y : Fin n → Fin 4 → ℝ) :
    zImPoint n x y ∈ forward_tube_n n ↔ zImPoint n 0 y ∈ forward_tube_n n := by
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have hi' : diff_im n (zImPoint n x y) i hi ∈ forward_light_cone := h i hi
    change diff_im n (zImPoint n 0 y) i hi ∈ forward_light_cone
    rwa [diff_im_zImPoint, ← diff_im_zImPoint n 0 y i hi] at hi'
  · have hi' : diff_im n (zImPoint n 0 y) i hi ∈ forward_light_cone := h i hi
    change diff_im n (zImPoint n x y) i hi ∈ forward_light_cone
    rwa [diff_im_zImPoint, ← diff_im_zImPoint n x y i hi] at hi'

lemma tubeGapFactor_zImPoint_eq (n : ℕ) (x y : Fin n → Fin 4 → ℝ) :
    tubeGapFactor n (zImPoint n x y) = tubeGapFactor n (zImPoint n 0 y) := by
  unfold tubeGapFactor
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [diff_im_zImPoint, diff_im_zImPoint]

lemma norm_zImPoint_le (n : ℕ) (x y : Fin n → Fin 4 → ℝ) :
    ‖zImPoint n x y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y))).mpr fun μ => ?_
  dsimp [zImPoint]
  calc ‖(x i μ : ℂ) + Complex.I * (y i μ : ℂ)‖
      ≤ ‖(x i μ : ℂ)‖ + ‖Complex.I * (y i μ : ℂ)‖ := norm_add_le _ _
    _ = ‖x i μ‖ + ‖y i μ‖ := by simp [Complex.norm_real]
    _ ≤ ‖x‖ + ‖y‖ :=
      add_le_add ((norm_le_pi_norm (x i) μ).trans (norm_le_pi_norm x i))
        ((norm_le_pi_norm (y i) μ).trans (norm_le_pi_norm y i))

lemma norm_tubeImDir_le (n : ℕ) (v : Fin 4 → ℝ) :
    ‖tubeImDir n v‖ ≤ (n : ℝ) * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
  dsimp [tubeImDir]
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg i.val), ← Real.norm_eq_abs (v μ)]
  exact mul_le_mul (Nat.cast_le.mpr i.isLt.le) (norm_le_pi_norm v μ)
    (norm_nonneg _) (Nat.cast_nonneg n)

lemma tubeGapFactor_tubeBoundaryLine_pow_le (n N : ℕ) (x : Fin n → Fin 4 → ℝ)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (tubeGapFactor n (tubeBoundaryLine n x v t)) ^ N ≤
      (1 + (coneGap v)⁻¹) ^ ((n - 1) * N) / t ^ ((n - 1) * N) := by
  have hg_pos : 0 < coneGap v := coneGap_pos v hv
  have ht_pos : 0 < t := ht.1
  have h_term : ∀ j : Fin (n - 1),
      1 + (coneGap (diff_im n (tubeBoundaryLine n x v t)
          ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j)))⁻¹ ≤
        (1 + (coneGap v)⁻¹) / t := by
    intro j
    have h_diff : diff_im n (tubeBoundaryLine n x v t)
        ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j) = t • v := by
      rw [tubeBoundaryLine_eq_zImPoint, diff_im_zImPoint]
      ext μ
      dsimp [tubeImDir]
      push_cast
      ring
    rw [h_diff, coneGap_smul_of_nonneg ht_pos.le v, mul_inv]
    calc 1 + t⁻¹ * (coneGap v)⁻¹
        = (t + (coneGap v)⁻¹) / t := by field_simp [ht_pos.ne']
      _ ≤ (1 + (coneGap v)⁻¹) / t :=
        div_le_div_of_nonneg_right (by linarith [ht.2]) ht_pos.le
  have h_prod : tubeGapFactor n (tubeBoundaryLine n x v t) ≤
      ((1 + (coneGap v)⁻¹) / t) ^ (n - 1) := by
    unfold tubeGapFactor
    calc ∏ j : Fin (n - 1),
          (1 + (coneGap (diff_im n (tubeBoundaryLine n x v t)
            ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j)))⁻¹)
        ≤ ∏ _j : Fin (n - 1), ((1 + (coneGap v)⁻¹) / t) := by
          refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => h_term j)
          have hgj := coneGap_pos _
            (tubeBoundaryLine_mem_forward_tube n x v hv ht_pos
              ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))
          positivity
      _ = ((1 + (coneGap v)⁻¹) / t) ^ (n - 1) := by rw [Finset.prod_const, Finset.card_fin]
  have h_pow := pow_le_pow_left₀
    (tubeGapFactor_nonneg (tubeBoundaryLine_mem_forward_tube n x v hv ht_pos)) h_prod N
  rwa [← pow_mul, div_pow] at h_pow

lemma exists_uniform_ball_in_forward_tube {n : ℕ} {y : Fin n → Fin 4 → ℝ}
    (hy : zImPoint n 0 y ∈ forward_tube_n n) :
    ∃ (ρ B_gap : ℝ), 0 < ρ ∧ 0 ≤ B_gap ∧
      ∀ (x : Fin n → Fin 4 → ℝ) {w : Fin n → Fin 4 → ℂ},
        w ∈ Metric.ball (zImPoint n x y) ρ →
        w ∈ forward_tube_n n ∧ tubeGapFactor n w ≤ B_gap := by
  by_cases hn : n ≤ 1
  · refine ⟨1, 1, zero_lt_one, zero_le_one, fun x w _ => ⟨fun i hi => by omega, ?_⟩⟩
    have h0 : n - 1 = 0 := by omega
    unfold tubeGapFactor
    have h_card : (Finset.univ : Finset (Fin (n - 1))) = ∅ := by
      ext j
      exact False.elim (Nat.not_lt_zero j.val (h0 ▸ j.isLt))
    rw [h_card, Finset.prod_empty]
  · have hn_pos : 0 < n - 1 := by omega
    haveI : Nonempty (Fin (n - 1)) := ⟨⟨0, hn_pos⟩⟩
    let g_fn : Fin (n - 1) → ℝ := fun j =>
      coneGap (diff_im n (zImPoint n 0 y) ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))
    obtain ⟨j_min, _, hj_min⟩ := Finset.exists_min_image Finset.univ g_fn Finset.univ_nonempty
    have hg_min_pos : 0 < g_fn j_min :=
      coneGap_pos _ (hy ⟨j_min.val, fin_sub_one_lt j_min⟩ (fin_sub_one_succ_lt j_min))
    let ρ : ℝ := g_fn j_min / 16
    have hρ_pos : 0 < ρ := by dsimp [ρ]; positivity
    let B_gap : ℝ := (1 + (g_fn j_min / 2)⁻¹) ^ (n - 1)
    refine ⟨ρ, B_gap, hρ_pos, by positivity, fun x w hw => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw_gap : ∀ (i : Fin n) (hi : i.val + 1 < n),
        g_fn j_min / 2 ≤ coneGap (diff_im n w i hi) := by
      intro i hi
      let j : Fin (n - 1) := ⟨i.val, by omega⟩
      have hj_le : g_fn j_min ≤ g_fn j := hj_min j (Finset.mem_univ j)
      have hg_x : coneGap (diff_im n (zImPoint n x y) i hi) = g_fn j := by
        dsimp [g_fn, j]
        rw [diff_im_zImPoint, diff_im_zImPoint]
      have h_diff_norm : ‖diff_im n w i hi - diff_im n (zImPoint n x y) i hi‖ ≤
          2 * ‖w - zImPoint n x y‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
        dsimp [diff_im, diff_z]
        have h_im1 : |(w i μ - zImPoint n x y i μ).im| ≤ ‖w - zImPoint n x y‖ :=
          (Complex.abs_im_le_norm _).trans
            ((norm_le_pi_norm ((w - zImPoint n x y) i) μ).trans
              (norm_le_pi_norm (w - zImPoint n x y) i))
        have h_im2 : |(w ⟨i.val + 1, hi⟩ μ - zImPoint n x y ⟨i.val + 1, hi⟩ μ).im| ≤
            ‖w - zImPoint n x y‖ :=
          (Complex.abs_im_le_norm _).trans
            ((norm_le_pi_norm ((w - zImPoint n x y) ⟨i.val + 1, hi⟩) μ).trans
              (norm_le_pi_norm (w - zImPoint n x y) ⟨i.val + 1, hi⟩))
        have h_eq : -((w i μ).im - (w ⟨i.val + 1, hi⟩ μ).im) -
            -((zImPoint n x y i μ).im - (zImPoint n x y ⟨i.val + 1, hi⟩ μ).im) =
            (w ⟨i.val + 1, hi⟩ μ - zImPoint n x y ⟨i.val + 1, hi⟩ μ).im -
              (w i μ - zImPoint n x y i μ).im := by
          simp only [Complex.sub_im]
          ring
        rw [h_eq]
        exact (abs_sub _ _).trans (by linarith)
      have h_abs := (abs_coneGap_sub_le (diff_im n w i hi) (diff_im n (zImPoint n x y) i hi))
      have h_sub_le := (le_abs_self _).trans
        (abs_sub_comm (coneGap (diff_im n w i hi)) _ ▸ h_abs)
      rw [hg_x] at h_sub_le
      have h8 : 4 * ‖diff_im n w i hi - diff_im n (zImPoint n x y) i hi‖ ≤ g_fn j_min / 2 := by
        dsimp [ρ] at hw
        linarith
      linarith
    refine ⟨fun i hi => ?_, ?_⟩
    · change diff_im n w i hi ∈ forward_light_cone
      exact (mem_forward_light_cone_iff_coneGap_pos _).mpr (by linarith [hw_gap i hi])
    · unfold tubeGapFactor
      calc ∏ j : Fin (n - 1),
            (1 + (coneGap (diff_im n w ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j)))⁻¹)
          ≤ ∏ _j : Fin (n - 1), (1 + (g_fn j_min / 2)⁻¹) := by
            refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
            · have hgj := hw_gap ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j)
              have : 0 < coneGap (diff_im n w ⟨j.val, fin_sub_one_lt j⟩
                  (fin_sub_one_succ_lt j)) := by linarith
              positivity
            · linarith [inv_anti₀ (half_pos hg_min_pos)
                (hw_gap ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))]
        _ = B_gap := by rw [Finset.prod_const, Finset.card_fin]

lemma one_add_norm_pow_le_two_pow_mul {E : Type*} [SeminormedAddCommGroup E]
    (M : ℕ) (x : E) :
    (1 + ‖x‖) ^ M ≤ (2 : ℝ) ^ M * (‖x‖ ^ 0 + ‖x‖ ^ M) := by
  rcases le_total ‖x‖ 1 with hx | hx
  · have h1 : 1 + ‖x‖ ≤ 2 := by linarith
    calc (1 + ‖x‖) ^ M ≤ (2 : ℝ) ^ M := pow_le_pow_left₀ (by positivity) h1 M
      _ = (2 : ℝ) ^ M * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ M * (‖x‖ ^ 0 + ‖x‖ ^ M) := by
        gcongr
        rw [pow_zero]
        linarith [pow_nonneg (norm_nonneg x) M]
  · have h1 : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
    calc (1 + ‖x‖) ^ M ≤ (2 * ‖x‖) ^ M := pow_le_pow_left₀ (by positivity) h1 M
      _ = (2 : ℝ) ^ M * ‖x‖ ^ M := mul_pow 2 ‖x‖ M
      _ ≤ (2 : ℝ) ^ M * (‖x‖ ^ 0 + ‖x‖ ^ M) := by
        gcongr
        linarith [pow_zero ‖x‖]

noncomputable def schwartzPolyWeightConst (n M : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ((2 : ℝ) ^ (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower *
      ∫ x : Fin n → Fin 4 → ℝ,
        (1 + ‖x‖) ^ (-((volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower : ℝ)))

lemma schwartzPolyWeightConst_nonneg (n M : ℕ) :
    0 ≤ schwartzPolyWeightConst n M := by
  unfold schwartzPolyWeightConst
  refine mul_nonneg (by positivity) (mul_nonneg (by positivity) ?_)
  exact integral_nonneg fun x => Real.rpow_nonneg (by positivity) _

noncomputable def schwartzPolyIntegralBound (n M : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) : ℝ :=
  let P := (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower
  schwartzPolyWeightConst n M *
    (2 * SchwartzMap.seminorm ℝ 0 0 g +
      SchwartzMap.seminorm ℝ P 0 g +
      SchwartzMap.seminorm ℝ (M + P) 0 g)

lemma schwartzPolyIntegralBound_nonneg (n M : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    0 ≤ schwartzPolyIntegralBound n M g := by
  unfold schwartzPolyIntegralBound
  refine mul_nonneg (schwartzPolyWeightConst_nonneg n M) ?_
  have h1 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 g := apply_nonneg _ _
  have h2 : 0 ≤ SchwartzMap.seminorm ℝ
      (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower 0 g := apply_nonneg _ _
  have h3 : 0 ≤ SchwartzMap.seminorm ℝ
      (M + (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower) 0 g := apply_nonneg _ _
  linarith

@[simp]
lemma schwartzPolyIntegralBound_zero (n M : ℕ) :
    schwartzPolyIntegralBound n M 0 = 0 := by
  simp [schwartzPolyIntegralBound]

lemma continuous_schwartzPolyIntegralBound (n M : ℕ) :
    Continuous (schwartzPolyIntegralBound n M) := by
  have hw := schwartz_withSeminorms ℝ (Fin n → Fin 4 → ℝ) ℂ
  unfold schwartzPolyIntegralBound
  refine continuous_const.mul ?_
  exact (((continuous_const.mul (hw.continuous_seminorm (0, 0))).add
    (hw.continuous_seminorm (_, 0))).add (hw.continuous_seminorm (_, 0)))

lemma integrable_one_add_norm_pow_mul_schwartz (n M : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Integrable (fun x : Fin n → Fin 4 → ℝ => (1 + ‖x‖) ^ M * ‖g x‖) volume := by
  have h0 := g.integrable_pow_mul (volume : Measure (Fin n → Fin 4 → ℝ)) 0
  have hM := g.integrable_pow_mul (volume : Measure (Fin n → Fin 4 → ℝ)) M
  refine (((h0.add hM).const_mul ((2 : ℝ) ^ M))).mono' ?_ ?_
  · exact ((continuous_const.add continuous_norm).pow M).mul
      g.continuous.norm |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    calc (1 + ‖x‖) ^ M * ‖g x‖
        ≤ ((2 : ℝ) ^ M * (‖x‖ ^ 0 + ‖x‖ ^ M)) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right (one_add_norm_pow_le_two_pow_mul M x) (norm_nonneg _)
      _ = (2 : ℝ) ^ M * (‖x‖ ^ 0 * ‖g x‖ + ‖x‖ ^ M * ‖g x‖) := by ring

lemma integral_one_add_norm_pow_mul_schwartz_le (n M : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, (1 + ‖x‖) ^ M * ‖g x‖) ≤
      schwartzPolyIntegralBound n M g := by
  have h0 := g.integrable_pow_mul (volume : Measure (Fin n → Fin 4 → ℝ)) 0
  have hM := g.integrable_pow_mul (volume : Measure (Fin n → Fin 4 → ℝ)) M
  have h_mono : (∫ x : Fin n → Fin 4 → ℝ, (1 + ‖x‖) ^ M * ‖g x‖) ≤
      (2 : ℝ) ^ M * ((∫ x, ‖x‖ ^ 0 * ‖g x‖) + (∫ x, ‖x‖ ^ M * ‖g x‖)) := by
    rw [← MeasureTheory.integral_add h0 hM, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono
      (integrable_one_add_norm_pow_mul_schwartz n M g) ((h0.add hM).const_mul _) fun x => ?_
    dsimp only
    calc (1 + ‖x‖) ^ M * ‖g x‖
        ≤ ((2 : ℝ) ^ M * (‖x‖ ^ 0 + ‖x‖ ^ M)) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right (one_add_norm_pow_le_two_pow_mul M x) (norm_nonneg _)
      _ = (2 : ℝ) ^ M * (‖x‖ ^ 0 * ‖g x‖ + ‖x‖ ^ M * ‖g x‖) := by ring
  have hb0 : (∫ x : Fin n → Fin 4 → ℝ, ‖x‖ ^ 0 * ‖g x‖) ≤
      ((2 : ℝ) ^ (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower *
        ∫ x : Fin n → Fin 4 → ℝ,
          (1 + ‖x‖) ^ (-((volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower : ℝ))) *
      (SchwartzMap.seminorm ℝ 0 0 g +
        SchwartzMap.seminorm ℝ
          (0 + (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower) 0 g) := by
    simpa [norm_iteratedFDeriv_zero] using
      SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ
        (volume : Measure (Fin n → Fin 4 → ℝ)) g 0 0
  have hbM : (∫ x : Fin n → Fin 4 → ℝ, ‖x‖ ^ M * ‖g x‖) ≤
      ((2 : ℝ) ^ (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower *
        ∫ x : Fin n → Fin 4 → ℝ,
          (1 + ‖x‖) ^ (-((volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower : ℝ))) *
      (SchwartzMap.seminorm ℝ 0 0 g +
        SchwartzMap.seminorm ℝ
          (M + (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower) 0 g) := by
    simpa [norm_iteratedFDeriv_zero] using
      SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ
        (volume : Measure (Fin n → Fin 4 → ℝ)) g M 0
  rw [zero_add] at hb0
  refine h_mono.trans ?_
  unfold schwartzPolyIntegralBound schwartzPolyWeightConst
  have h2M : 0 ≤ (2 : ℝ) ^ M := by positivity
  have hI : 0 ≤ (2 : ℝ) ^ (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower *
      ∫ x : Fin n → Fin 4 → ℝ,
        (1 + ‖x‖) ^ (-((volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower : ℝ)) := by
    refine mul_nonneg (by positivity) (integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _)
  nlinarith

noncomputable def schwartzDirDerivCLM (n : ℕ) (d : Fin n → Fin 4 → ℝ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) d

@[simp]
lemma schwartzDirDerivCLM_apply (n : ℕ) (d : Fin n → Fin 4 → ℝ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (x : Fin n → Fin 4 → ℝ) :
    schwartzDirDerivCLM n d g x = fderiv ℝ g x d := rfl

lemma schwartzDirDerivCLM_dir_add (n : ℕ) (d₁ d₂ : Fin n → Fin 4 → ℝ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzDirDerivCLM n (d₁ + d₂) g =
      schwartzDirDerivCLM n d₁ g + schwartzDirDerivCLM n d₂ g := by
  ext x
  simp [schwartzDirDerivCLM_apply, map_add]

lemma schwartzDirDerivCLM_dir_smul (n : ℕ) (r : ℝ) (d : Fin n → Fin 4 → ℝ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzDirDerivCLM n (r • d) g = (r : ℂ) • schwartzDirDerivCLM n d g := by
  ext x
  change fderiv ℝ g x (r • d) = (r : ℂ) * fderiv ℝ g x d
  rw [map_smul, Complex.real_smul]

lemma norm_fderiv_tube_dir_le_of_ball_bound {n M : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {z₀ : Fin n → Fin 4 → ℂ} {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (h_sub : Metric.ball z₀ (2 * R) ⊆ forward_tube_n n)
    (h_bd : ∀ w ∈ Metric.ball z₀ (2 * R), ‖H w‖ ≤ B * (1 + ‖w‖) ^ M)
    (d : Fin n → Fin 4 → ℂ) :
    ‖fderiv ℂ H z₀ d‖ ≤
      ((‖d‖ + 1) / R) * B * (1 + ‖z₀‖ + R) ^ M := by
  let r : ℝ := R / (‖d‖ + 1)
  have hd1_pos : 0 < ‖d‖ + 1 := by positivity
  have hr_pos : 0 < r := div_pos hR hd1_pos
  let φ : ℂ → ℂ := fun ζ => H (z₀ + ζ • d)
  have h_maps : Set.MapsTo (fun ζ : ℂ => z₀ + ζ • d) (Metric.ball 0 (2 * r))
      (Metric.ball z₀ (2 * R)) := by
    intro ζ hζ
    rw [Metric.mem_ball, dist_zero_right] at hζ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖ζ‖ * ‖d‖ ≤ ‖ζ‖ * (‖d‖ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg ζ)
      _ < (2 * r) * (‖d‖ + 1) := mul_lt_mul_of_pos_right hζ hd1_pos
      _ = 2 * R := by dsimp [r]; field_simp [hd1_pos.ne']
  have hH_diff : DifferentiableOn ℂ H (forward_tube_n n) := h_ana.differentiableOn
  have hφ_diff2 : DifferentiableOn ℂ φ (Metric.ball 0 (2 * r)) :=
    (hH_diff.mono h_sub).comp (differentiableOn_const z₀ |>.add
      (differentiableOn_id.smul_const d)) h_maps
  have h_cl_sub : closure (Metric.ball (0 : ℂ) r) ⊆ Metric.ball (0 : ℂ) (2 * r) :=
    Metric.closure_ball_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by linarith))
  have hφ_dc : DiffContOnCl ℂ φ (Metric.ball 0 r) :=
    ⟨hφ_diff2.mono (Metric.ball_subset_ball (by linarith)),
      hφ_diff2.continuousOn.mono h_cl_sub⟩
  have hz0_mem : z₀ ∈ forward_tube_n n := h_sub (Metric.mem_ball_self (by linarith))
  have hdf_z0 : HasFDerivAt H (fderiv ℂ H z₀) z₀ :=
    (hH_diff.differentiableAt ((forward_tube_n_isOpen n).mem_nhds hz0_mem)).hasFDerivAt
  have hd_aff : HasDerivAt (fun ζ : ℂ => z₀ + ζ • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const d).const_add z₀
  have hφ_deriv0 : deriv φ 0 = fderiv ℂ H z₀ d := by
    have hz0_eq : z₀ + (0 : ℂ) • d = z₀ := by simp
    have hdf_z0' : HasFDerivAt H (fderiv ℂ H z₀) (z₀ + (0 : ℂ) • d) := hz0_eq.symm ▸ hdf_z0
    exact (hdf_z0'.comp_hasDerivAt 0 hd_aff).deriv
  rw [← hφ_deriv0]
  have h_sph : ∀ ζ ∈ Metric.sphere (0 : ℂ) r, ‖φ ζ‖ ≤ B * (1 + ‖z₀‖ + R) ^ M := by
    intro ζ hζ
    have hζ_norm : ‖ζ‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hζ
    have hw_ball : z₀ + ζ • d ∈ Metric.ball z₀ (2 * R) := by
      apply h_maps
      rw [Metric.mem_ball, dist_zero_right, hζ_norm]
      linarith
    have hw_norm : ‖z₀ + ζ • d‖ ≤ ‖z₀‖ + R := by
      calc ‖z₀ + ζ • d‖ ≤ ‖z₀‖ + ‖ζ • d‖ := norm_add_le _ _
        _ = ‖z₀‖ + r * ‖d‖ := by rw [norm_smul, hζ_norm]
        _ ≤ ‖z₀‖ + r * (‖d‖ + 1) := by gcongr; linarith
        _ = ‖z₀‖ + R := by dsimp [r]; field_simp [hd1_pos.ne']
    exact (h_bd _ hw_ball).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) M) hB)
  have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr_pos hφ_dc h_sph
  refine h_cauchy.trans (le_of_eq ?_)
  dsimp [r]
  field_simp [hR.ne', hd1_pos.ne']

lemma integrable_zImPoint_mul_schwartz {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {y : Fin n → Fin 4 → ℝ} (hy : zImPoint n 0 y ∈ forward_tube_n n)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Integrable (fun x : Fin n → Fin 4 → ℝ => H (zImPoint n x y) * g x) volume := by
  have h_cont_x : Continuous (fun x : Fin n → Fin 4 → ℝ => zImPoint n x y) := by
    refine continuous_pi fun i => continuous_pi fun μ => ?_
    exact (Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply i))).add
      continuous_const
  have h_H_cont : Continuous (fun x : Fin n → Fin 4 → ℝ => H (zImPoint n x y)) :=
    h_ana.continuousOn.comp_continuous h_cont_x fun x =>
      (zImPoint_mem_forward_tube_iff n x y).mpr hy
  let K : ℝ := C_H * (1 + ‖y‖) ^ M * (tubeGapFactor n (zImPoint n 0 y)) ^ N_H
  refine ((integrable_one_add_norm_pow_mul_schwartz n M g).const_mul K).mono'
    (h_H_cont.mul g.continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have hx_mem : zImPoint n x y ∈ forward_tube_n n :=
    (zImPoint_mem_forward_tube_iff n x y).mpr hy
  have h_Hz := h_bd (zImPoint n x y) hx_mem
  rw [tubeGapFactor_zImPoint_eq n x y] at h_Hz
  have h_z_le : 1 + ‖zImPoint n x y‖ ≤ (1 + ‖y‖) * (1 + ‖x‖) := by
    have h1 := norm_zImPoint_le n x y
    nlinarith [norm_nonneg x, norm_nonneg y]
  have h_pow : (1 + ‖zImPoint n x y‖) ^ M ≤ (1 + ‖y‖) ^ M * (1 + ‖x‖) ^ M :=
    (pow_le_pow_left₀ (by positivity) h_z_le M).trans_eq (mul_pow _ _ M)
  have h_gap_nn : 0 ≤ (tubeGapFactor n (zImPoint n 0 y)) ^ N_H :=
    pow_nonneg (tubeGapFactor_nonneg hy) N_H
  calc ‖H (zImPoint n x y)‖ * ‖g x‖
      ≤ (C_H * ((1 + ‖y‖) ^ M * (1 + ‖x‖) ^ M) *
          (tubeGapFactor n (zImPoint n 0 y)) ^ N_H) * ‖g x‖ := by
        refine mul_le_mul_of_nonneg_right (h_Hz.trans ?_) (norm_nonneg _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_pow hCH) h_gap_nn
    _ = K * ((1 + ‖x‖) ^ M * ‖g x‖) := by dsimp [K]; ring

lemma hasDerivAt_zImPoint_schwartz {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    (y₀ d : Fin n → Fin 4 → ℝ) (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    {s : ℝ} (hs : zImPoint n 0 (y₀ + s • d) ∈ forward_tube_n n) :
    HasDerivAt
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x (y₀ + t • d)) * g x)
      (Complex.I * ∫ x : Fin n → Fin 4 → ℝ,
        H (zImPoint n x (y₀ + s • d)) * (schwartzDirDerivCLM n (-d) g) x) s := by
  obtain ⟨ρ, B_gap, hρ_pos, hB_nn, h_ball⟩ := exists_uniform_ball_in_forward_tube hs
  let d_c : Fin n → Fin 4 → ℂ := fun i μ => (d i μ : ℂ)
  have hd_c_norm : ‖d_c‖ ≤ ‖d‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mpr fun μ => ?_
    simpa [d_c, Complex.norm_real] using
      (norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)
  let R₀ : ℝ := ρ / 4
  have hR₀_pos : 0 < R₀ := by dsimp [R₀]; positivity
  let δ : ℝ := min 1 (R₀ / (‖d‖ + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hR₀_pos (by positivity))
  let ys : Fin n → Fin 4 → ℝ := y₀ + s • d
  have hH_diff : DifferentiableOn ℂ H (forward_tube_n n) := h_ana.differentiableOn
  let B_H : ℝ := C_H * B_gap ^ N_H
  have hBH_nn : 0 ≤ B_H := mul_nonneg hCH (pow_nonneg hB_nn N_H)
  have h_c_bd : ∀ (x : Fin n → Fin 4 → ℝ) {z : Fin n → Fin 4 → ℂ},
      ‖z - zImPoint n x ys‖ < R₀ →
      ‖fderiv ℂ H z d_c‖ ≤
        ((‖d_c‖ + 1) / R₀) * B_H * (1 + ‖ys‖ + 2 * R₀) ^ M * (1 + ‖x‖) ^ M := by
    intro x z hz_lt
    have h_sub2 : Metric.ball z (2 * R₀) ⊆ forward_tube_n n := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hw_ρ : w ∈ Metric.ball (zImPoint n x ys) ρ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_tri : ‖w - zImPoint n x ys‖ ≤ ‖w - z‖ + ‖z - zImPoint n x ys‖ := by
          simpa using norm_add_le (w - z) (z - zImPoint n x ys)
        dsimp [R₀] at hw hz_lt
        linarith
      exact (h_ball x hw_ρ).1
    have h_bd2 : ∀ w ∈ Metric.ball z (2 * R₀), ‖H w‖ ≤ B_H * (1 + ‖w‖) ^ M := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have hw_ρ : w ∈ Metric.ball (zImPoint n x ys) ρ := by
        rw [Metric.mem_ball, dist_eq_norm]
        have h_tri : ‖w - zImPoint n x ys‖ ≤ ‖w - z‖ + ‖z - zImPoint n x ys‖ := by
          simpa using norm_add_le (w - z) (z - zImPoint n x ys)
        dsimp [R₀] at hw hz_lt
        linarith
      obtain ⟨hw_mem, hw_gap⟩ := h_ball x hw_ρ
      calc ‖H w‖ ≤ C_H * (1 + ‖w‖) ^ M * (tubeGapFactor n w) ^ N_H := h_bd w hw_mem
        _ ≤ C_H * (1 + ‖w‖) ^ M * B_gap ^ N_H := by
          gcongr
          exact tubeGapFactor_nonneg hw_mem
        _ = B_H * (1 + ‖w‖) ^ M := by dsimp [B_H]; ring
    have h_est := norm_fderiv_tube_dir_le_of_ball_bound h_ana hR₀_pos hBH_nn h_sub2 h_bd2 d_c
    refine h_est.trans ?_
    have hz_norm : ‖z‖ ≤ ‖x‖ + ‖ys‖ + R₀ := by
      have h1 : ‖z‖ ≤ ‖z - zImPoint n x ys‖ + ‖zImPoint n x ys‖ := by
        simpa using norm_add_le (z - zImPoint n x ys) (zImPoint n x ys)
      have h2 := norm_zImPoint_le n x ys
      linarith
    have h_prod : 1 + ‖z‖ + R₀ ≤ (1 + ‖ys‖ + 2 * R₀) * (1 + ‖x‖) := by
      nlinarith [norm_nonneg x, norm_nonneg ys]
    have h_pow : (1 + ‖z‖ + R₀) ^ M ≤ (1 + ‖ys‖ + 2 * R₀) ^ M * (1 + ‖x‖) ^ M :=
      (pow_le_pow_left₀ (by positivity) h_prod M).trans_eq (mul_pow _ _ M)
    calc ((‖d_c‖ + 1) / R₀) * B_H * (1 + ‖z‖ + R₀) ^ M
        ≤ ((‖d_c‖ + 1) / R₀) * B_H * ((1 + ‖ys‖ + 2 * R₀) ^ M * (1 + ‖x‖) ^ M) :=
          mul_le_mul_of_nonneg_left h_pow (by positivity)
      _ = ((‖d_c‖ + 1) / R₀) * B_H * (1 + ‖ys‖ + 2 * R₀) ^ M * (1 + ‖x‖) ^ M := by ring
  let K_der : ℝ := ((‖d_c‖ + 1) / R₀) * B_H * (1 + ‖ys‖ + 2 * R₀) ^ M
  have h_im_deriv : HasDerivAt
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x (y₀ + t • d)) * g x)
      (∫ x : Fin n → Fin 4 → ℝ,
        (Complex.I * fderiv ℂ H (zImPoint n x ys) d_c) * g x) s := by
    have h_nhds_s : Set.Ioo (s - δ) (s + δ) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun t x => H (zImPoint n x (y₀ + t • d)) * g x)
      (F' := fun t x => (Complex.I * fderiv ℂ H (zImPoint n x (y₀ + t • d)) d_c) * g x)
      (bound := fun x => K_der * ((1 + ‖x‖) ^ M * ‖g x‖))
      h_nhds_s ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [h_nhds_s] with t ht
      have ht_lt : |t - s| < δ := abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have ht_mem : zImPoint n 0 (y₀ + t • d) ∈ forward_tube_n n := by
        refine (h_ball 0 ?_).1
        rw [Metric.mem_ball, dist_eq_norm]
        have h_sub_z : ‖zImPoint n 0 (y₀ + t • d) - zImPoint n 0 ys‖ ≤ |t - s| * ‖d‖ := by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
          simp only [Pi.sub_apply]
          have h_eq : zImPoint n 0 (y₀ + t • d) i μ - zImPoint n 0 ys i μ =
              Complex.I * (((t - s) * d i μ : ℝ) : ℂ) := by
            dsimp [zImPoint, ys]
            push_cast
            ring
          rw [h_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (d i μ)]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)) (abs_nonneg _)
        have hδ_le : δ ≤ R₀ / (‖d‖ + 1) := min_le_right _ _
        have h1 : |t - s| * ‖d‖ < R₀ := by
          calc |t - s| * ‖d‖ ≤ |t - s| * (‖d‖ + 1) :=
                mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
            _ < (R₀ / (‖d‖ + 1)) * (‖d‖ + 1) :=
                mul_lt_mul_of_pos_right (ht_lt.trans_le hδ_le) (by positivity)
            _ = R₀ := div_mul_cancel₀ R₀ (by positivity)
        dsimp [R₀] at h1
        linarith
      exact (integrable_zImPoint_mul_schwartz h_ana hCH h_bd ht_mem g).aestronglyMeasurable
    · exact integrable_zImPoint_mul_schwartz h_ana hCH h_bd hs g
    · have h_cont_fderiv : Continuous
          (fun x : Fin n → Fin 4 → ℝ =>
            (Complex.I * fderiv ℂ H (zImPoint n x ys) d_c) * g x) := by
        have h_zx : Continuous (fun x : Fin n → Fin 4 → ℝ => zImPoint n x ys) :=
          continuous_pi fun i => continuous_pi fun μ =>
            (Complex.continuous_ofReal.comp
              ((continuous_apply μ).comp (continuous_apply i))).add continuous_const
        have h_fd : ContinuousOn (fun z => fderiv ℂ H z d_c) (forward_tube_n n) := by
          have hc := h_ana.contDiffOn (n := (1 : ℕ∞)) (forward_tube_n_isOpen n).uniqueDiffOn
          exact (ContinuousLinearMap.apply ℂ ℂ d_c).continuous.comp_continuousOn
            (hc.continuousOn_fderiv_of_isOpen (forward_tube_n_isOpen n) le_rfl)
        exact (continuous_const.mul (h_fd.comp_continuous h_zx fun x =>
          (zImPoint_mem_forward_tube_iff n x ys).mpr hs)).mul g.continuous
      exact h_cont_fderiv.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x t ht => ?_
      have ht_lt : |t - s| < δ := abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hz_lt : ‖zImPoint n x (y₀ + t • d) - zImPoint n x ys‖ < R₀ := by
        have h_sub_z : ‖zImPoint n x (y₀ + t • d) - zImPoint n x ys‖ ≤ |t - s| * ‖d‖ := by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
          simp only [Pi.sub_apply]
          have h_eq : zImPoint n x (y₀ + t • d) i μ - zImPoint n x ys i μ =
              Complex.I * (((t - s) * d i μ : ℝ) : ℂ) := by
            dsimp [zImPoint, ys]
            push_cast
            ring
          rw [h_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (d i μ)]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)) (abs_nonneg _)
        have hδ_le : δ ≤ R₀ / (‖d‖ + 1) := min_le_right _ _
        calc ‖zImPoint n x (y₀ + t • d) - zImPoint n x ys‖
            ≤ |t - s| * (‖d‖ + 1) :=
              h_sub_z.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
          _ < (R₀ / (‖d‖ + 1)) * (‖d‖ + 1) :=
              mul_lt_mul_of_pos_right (ht_lt.trans_le hδ_le) (by positivity)
          _ = R₀ := div_mul_cancel₀ R₀ (by positivity)
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      calc ‖fderiv ℂ H (zImPoint n x (y₀ + t • d)) d_c‖ * ‖g x‖
          ≤ (K_der * (1 + ‖x‖) ^ M) * ‖g x‖ :=
            mul_le_mul_of_nonneg_right (h_c_bd x hz_lt) (norm_nonneg _)
        _ = K_der * ((1 + ‖x‖) ^ M * ‖g x‖) := mul_assoc _ _ _
    · exact (integrable_one_add_norm_pow_mul_schwartz n M g).const_mul K_der
    · refine Filter.Eventually.of_forall fun x t ht => ?_
      have ht_lt : |t - s| < δ := abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hz_mem : zImPoint n x (y₀ + t • d) ∈ forward_tube_n n := by
        refine (h_ball x ?_).1
        rw [Metric.mem_ball, dist_eq_norm]
        have h_sub_z : ‖zImPoint n x (y₀ + t • d) - zImPoint n x ys‖ ≤ |t - s| * ‖d‖ := by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
          simp only [Pi.sub_apply]
          have h_eq : zImPoint n x (y₀ + t • d) i μ - zImPoint n x ys i μ =
              Complex.I * (((t - s) * d i μ : ℝ) : ℂ) := by
            dsimp [zImPoint, ys]
            push_cast
            ring
          rw [h_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (d i μ)]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)) (abs_nonneg _)
        have hδ_le : δ ≤ R₀ / (‖d‖ + 1) := min_le_right _ _
        have h1 : |t - s| * ‖d‖ < R₀ := by
          calc |t - s| * ‖d‖ ≤ |t - s| * (‖d‖ + 1) :=
                mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
            _ < (R₀ / (‖d‖ + 1)) * (‖d‖ + 1) :=
                mul_lt_mul_of_pos_right (ht_lt.trans_le hδ_le) (by positivity)
            _ = R₀ := div_mul_cancel₀ R₀ (by positivity)
        dsimp [R₀] at h1
        linarith
      have hdf_zt : HasFDerivAt H (fderiv ℂ H (zImPoint n x (y₀ + t • d)))
          (zImPoint n x (y₀ + t • d)) :=
        (hH_diff.differentiableAt ((forward_tube_n_isOpen n).mem_nhds hz_mem)).hasFDerivAt
      have hd_line : HasDerivAt (fun τ : ℝ => zImPoint n x (y₀ + τ • d))
          (Complex.I • d_c) t := by
        rw [hasDerivAt_pi]
        intro i
        rw [hasDerivAt_pi]
        intro μ
        have hr : HasDerivAt (fun τ : ℝ => y₀ i μ + τ * d i μ) (d i μ) t := by
          simpa using ((hasDerivAt_id t).mul_const (d i μ)).const_add (y₀ i μ)
        have hc := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hr).const_mul
          Complex.I).const_add (x i μ : ℂ)
        simpa [zImPoint, d_c] using hc
      have hd_H : HasDerivAt (fun τ : ℝ => H (zImPoint n x (y₀ + τ • d)))
          (Complex.I * fderiv ℂ H (zImPoint n x (y₀ + t • d)) d_c) t := by
        have hc := (hdf_zt.restrictScalars ℝ).comp_hasDerivAt t hd_line
        rwa [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul] at hc
      exact hd_H.mul_const (g x)
  let G_re : ℝ → ℂ := fun r => ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n (x + r • d) ys) * g x
  have h_re1 : HasDerivAt G_re
      (∫ x : Fin n → Fin 4 → ℝ, fderiv ℂ H (zImPoint n x ys) d_c * g x) 0 := by
    have h_nhds0 : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
    have h_val0 : (∫ x : Fin n → Fin 4 → ℝ, fderiv ℂ H (zImPoint n x ys) d_c * g x) =
        ∫ x : Fin n → Fin 4 → ℝ,
          fderiv ℂ H (zImPoint n (x + (0 : ℝ) • d) ys) d_c * g x := by
      simp only [zero_smul, add_zero]
    rw [h_val0]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun r x => H (zImPoint n (x + r • d) ys) * g x)
      (F' := fun r x => fderiv ℂ H (zImPoint n (x + r • d) ys) d_c * g x)
      (bound := fun x => K_der * ((1 + ‖x‖) ^ M * ‖g x‖))
      h_nhds0 ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [h_nhds0] with r _
      have h_cont_xr : Continuous (fun x : Fin n → Fin 4 → ℝ => H (zImPoint n (x + r • d) ys)) :=
        h_ana.continuousOn.comp_continuous
          (continuous_pi fun i => continuous_pi fun μ =>
            (Complex.continuous_ofReal.comp
              ((continuous_apply μ).comp (continuous_apply i |>.comp
                (continuous_id.add continuous_const)))).add continuous_const)
          fun x => (zImPoint_mem_forward_tube_iff n (x + r • d) ys).mpr hs
      exact (h_cont_xr.mul g.continuous).aestronglyMeasurable
    · simpa [G_re] using integrable_zImPoint_mul_schwartz h_ana hCH h_bd hs g
    · simp only [zero_smul, add_zero]
      have h_zx : Continuous (fun x : Fin n → Fin 4 → ℝ => zImPoint n x ys) :=
        continuous_pi fun i => continuous_pi fun μ =>
          (Complex.continuous_ofReal.comp
            ((continuous_apply μ).comp (continuous_apply i))).add continuous_const
      have h_fd : ContinuousOn (fun z => fderiv ℂ H z d_c) (forward_tube_n n) :=
        (ContinuousLinearMap.apply ℂ ℂ d_c).continuous.comp_continuousOn
          ((h_ana.contDiffOn (n := (1 : ℕ∞))
            (forward_tube_n_isOpen n).uniqueDiffOn).continuousOn_fderiv_of_isOpen
            (forward_tube_n_isOpen n) le_rfl)
      exact ((h_fd.comp_continuous h_zx fun x =>
        (zImPoint_mem_forward_tube_iff n x ys).mpr hs).mul g.continuous).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x r hr => ?_
      have hr_lt : |r| < δ := abs_lt.mpr hr
      have hz_lt : ‖zImPoint n (x + r • d) ys - zImPoint n x ys‖ < R₀ := by
        have h_sub_z : ‖zImPoint n (x + r • d) ys - zImPoint n x ys‖ ≤ |r| * ‖d‖ := by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
          simp only [Pi.sub_apply]
          have h_eq : zImPoint n (x + r • d) ys i μ - zImPoint n x ys i μ =
              ((r * d i μ : ℝ) : ℂ) := by
            dsimp [zImPoint]
            push_cast
            ring
          rw [h_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (d i μ)]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)) (abs_nonneg _)
        have hδ_le : δ ≤ R₀ / (‖d‖ + 1) := min_le_right _ _
        calc ‖zImPoint n (x + r • d) ys - zImPoint n x ys‖
            ≤ |r| * (‖d‖ + 1) :=
              h_sub_z.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
          _ < (R₀ / (‖d‖ + 1)) * (‖d‖ + 1) :=
              mul_lt_mul_of_pos_right (hr_lt.trans_le hδ_le) (by positivity)
          _ = R₀ := div_mul_cancel₀ R₀ (by positivity)
      rw [norm_mul]
      calc ‖fderiv ℂ H (zImPoint n (x + r • d) ys) d_c‖ * ‖g x‖
          ≤ (K_der * (1 + ‖x‖) ^ M) * ‖g x‖ :=
            mul_le_mul_of_nonneg_right (h_c_bd x hz_lt) (norm_nonneg _)
        _ = K_der * ((1 + ‖x‖) ^ M * ‖g x‖) := mul_assoc _ _ _
    · exact (integrable_one_add_norm_pow_mul_schwartz n M g).const_mul K_der
    · refine Filter.Eventually.of_forall fun x r _ => ?_
      have hz_mem : zImPoint n (x + r • d) ys ∈ forward_tube_n n :=
        (zImPoint_mem_forward_tube_iff n (x + r • d) ys).mpr hs
      have hdf_zr : HasFDerivAt H (fderiv ℂ H (zImPoint n (x + r • d) ys))
          (zImPoint n (x + r • d) ys) :=
        (hH_diff.differentiableAt ((forward_tube_n_isOpen n).mem_nhds hz_mem)).hasFDerivAt
      have hd_line : HasDerivAt (fun τ : ℝ => zImPoint n (x + τ • d) ys) d_c r := by
        rw [hasDerivAt_pi]
        intro i
        rw [hasDerivAt_pi]
        intro μ
        have hr' : HasDerivAt (fun τ : ℝ => x i μ + τ * d i μ) (d i μ) r := by
          simpa using ((hasDerivAt_id r).mul_const (d i μ)).const_add (x i μ)
        have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r hr').add_const
          (Complex.I * (ys i μ : ℂ))
        simpa [zImPoint, d_c] using hc
      exact ((hdf_zr.restrictScalars ℝ).comp_hasDerivAt r hd_line).mul_const (g x)
  have hG_shift : ∀ r : ℝ, G_re r =
      ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x ys) * g (x - r • d) := by
    intro r
    dsimp [G_re]
    have h_eq : (fun x : Fin n → Fin 4 → ℝ => H (zImPoint n (x + r • d) ys) * g x) =
        fun x => H (zImPoint n ((x + r • d)) ys) * g ((x + r • d) - r • d) := by
      ext x
      rw [add_sub_cancel_right]
    rw [h_eq]
    exact MeasureTheory.integral_add_right_eq_self
      (fun u => H (zImPoint n u ys) * g (u - r • d)) (r • d)
  let dg := schwartzDirDerivCLM n (-d) g
  let P_int : ℕ := (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower
  let L_pow : ℕ := M + P_int
  let S_dg : ℝ := (2 : ℝ) ^ L_pow *
    (SchwartzMap.seminorm ℝ 0 0 dg + SchwartzMap.seminorm ℝ L_pow 0 dg)
  let K_H0 : ℝ := C_H * (1 + ‖ys‖) ^ M * (tubeGapFactor n (zImPoint n 0 ys)) ^ N_H
  let K_g : ℝ := K_H0 * (S_dg * (1 + ‖d‖) ^ L_pow)
  have hKH0_nn : 0 ≤ K_H0 :=
    mul_nonneg (mul_nonneg hCH (by positivity)) (pow_nonneg (tubeGapFactor_nonneg hs) N_H)
  have h_re2 : HasDerivAt G_re
      (∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x ys) * dg x) 0 := by
    rw [funext hG_shift]
    have h_nhds1 : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have h_val1 : (∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x ys) * dg x) =
        ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x ys) * dg (x - (0 : ℝ) • d) := by
      simp only [zero_smul, sub_zero]
    rw [h_val1]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun r x => H (zImPoint n x ys) * g (x - r • d))
      (F' := fun r x => H (zImPoint n x ys) * dg (x - r • d))
      (bound := fun x => K_g * (1 + ‖x‖) ^ (-(P_int : ℝ)))
      h_nhds1 ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [h_nhds1] with r _
      have h_H_cont : Continuous (fun x : Fin n → Fin 4 → ℝ => H (zImPoint n x ys)) :=
        h_ana.continuousOn.comp_continuous
          (continuous_pi fun i => continuous_pi fun μ =>
            (Complex.continuous_ofReal.comp
              ((continuous_apply μ).comp (continuous_apply i))).add continuous_const)
          fun x => (zImPoint_mem_forward_tube_iff n x ys).mpr hs
      exact (h_H_cont.mul (g.continuous.comp
        (continuous_id.sub continuous_const))).aestronglyMeasurable
    · simpa using integrable_zImPoint_mul_schwartz h_ana hCH h_bd hs g
    · simp only [zero_smul, sub_zero]
      exact (integrable_zImPoint_mul_schwartz h_ana hCH h_bd hs dg).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x r hr => ?_
      have hr_abs : |r| ≤ 1 := abs_le.mpr ⟨hr.1.le, hr.2.le⟩
      have hx_mem : zImPoint n x ys ∈ forward_tube_n n :=
        (zImPoint_mem_forward_tube_iff n x ys).mpr hs
      have h_Hz : ‖H (zImPoint n x ys)‖ ≤ K_H0 * (1 + ‖x‖) ^ M := by
        have h1 := h_bd (zImPoint n x ys) hx_mem
        rw [tubeGapFactor_zImPoint_eq n x ys] at h1
        have h_z_le : 1 + ‖zImPoint n x ys‖ ≤ (1 + ‖ys‖) * (1 + ‖x‖) := by
          have hn_z := norm_zImPoint_le n x ys
          nlinarith [norm_nonneg x, norm_nonneg ys]
        have h_pow : (1 + ‖zImPoint n x ys‖) ^ M ≤ (1 + ‖ys‖) ^ M * (1 + ‖x‖) ^ M :=
          (pow_le_pow_left₀ (by positivity) h_z_le M).trans_eq (mul_pow _ _ M)
        calc ‖H (zImPoint n x ys)‖
            ≤ C_H * ((1 + ‖ys‖) ^ M * (1 + ‖x‖) ^ M) *
                (tubeGapFactor n (zImPoint n 0 ys)) ^ N_H :=
              h1.trans (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h_pow hCH)
                (pow_nonneg (tubeGapFactor_nonneg hs) N_H))
          _ = K_H0 * (1 + ‖x‖) ^ M := by dsimp [K_H0]; ring
      let u := x - r • d
      have hu_dg : (1 + ‖u‖) ^ L_pow * ‖dg u‖ ≤ S_dg := by
        have h00 : ‖u‖ ^ 0 * ‖dg u‖ ≤ SchwartzMap.seminorm ℝ 0 0 dg := by
          simpa [norm_iteratedFDeriv_zero] using dg.norm_iteratedFDeriv_le_seminorm ℝ 0 u
        have hL0 : ‖u‖ ^ L_pow * ‖dg u‖ ≤ SchwartzMap.seminorm ℝ L_pow 0 dg := by
          simpa [norm_iteratedFDeriv_zero] using dg.le_seminorm ℝ L_pow 0 u
        calc (1 + ‖u‖) ^ L_pow * ‖dg u‖
            ≤ ((2 : ℝ) ^ L_pow * (‖u‖ ^ 0 + ‖u‖ ^ L_pow)) * ‖dg u‖ :=
              mul_le_mul_of_nonneg_right (one_add_norm_pow_le_two_pow_mul L_pow u) (norm_nonneg _)
          _ = (2 : ℝ) ^ L_pow * (‖u‖ ^ 0 * ‖dg u‖ + ‖u‖ ^ L_pow * ‖dg u‖) := by ring
          _ ≤ S_dg := by
            dsimp [S_dg]
            exact mul_le_mul_of_nonneg_left (add_le_add h00 hL0) (by positivity)
      have hx_le : 1 + ‖x‖ ≤ (1 + ‖d‖) * (1 + ‖u‖) := by
        have hx_eq : x = u + r • d := by simp [u]
        have hx_norm : ‖x‖ ≤ ‖u‖ + ‖d‖ := by
          rw [hx_eq]
          calc ‖u + r • d‖ ≤ ‖u‖ + ‖r • d‖ := norm_add_le _ _
            _ = ‖u‖ + |r| * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
            _ ≤ ‖u‖ + 1 * ‖d‖ := add_le_add le_rfl
              (mul_le_mul_of_nonneg_right hr_abs (norm_nonneg d))
            _ = ‖u‖ + ‖d‖ := by ring
        nlinarith [norm_nonneg u, norm_nonneg d]
      have hx_pow : (1 + ‖x‖) ^ M * (1 + ‖x‖) ^ P_int ≤
          (1 + ‖d‖) ^ L_pow * (1 + ‖u‖) ^ L_pow := by
        rw [← pow_add]
        exact (pow_le_pow_left₀ (by positivity) hx_le L_pow).trans_eq (mul_pow _ _ L_pow)
      have hx_dg_mul : ((1 + ‖x‖) ^ M * ‖dg u‖) * (1 + ‖x‖) ^ P_int ≤
          S_dg * (1 + ‖d‖) ^ L_pow := by
        calc ((1 + ‖x‖) ^ M * ‖dg u‖) * (1 + ‖x‖) ^ P_int
            = ((1 + ‖x‖) ^ M * (1 + ‖x‖) ^ P_int) * ‖dg u‖ := by ring
          _ ≤ ((1 + ‖d‖) ^ L_pow * (1 + ‖u‖) ^ L_pow) * ‖dg u‖ :=
            mul_le_mul_of_nonneg_right hx_pow (norm_nonneg _)
          _ = (1 + ‖d‖) ^ L_pow * ((1 + ‖u‖) ^ L_pow * ‖dg u‖) := by ring
          _ ≤ (1 + ‖d‖) ^ L_pow * S_dg :=
            mul_le_mul_of_nonneg_left hu_dg (by positivity)
          _ = S_dg * (1 + ‖d‖) ^ L_pow := mul_comm _ _
      have hx_dg : (1 + ‖x‖) ^ M * ‖dg u‖ ≤
          (S_dg * (1 + ‖d‖) ^ L_pow) * (1 + ‖x‖) ^ (-(P_int : ℝ)) := by
        have hx_pos_pow : 0 < (1 + ‖x‖) ^ P_int := by positivity
        have hrpow_eq : (1 + ‖x‖) ^ (-(P_int : ℝ)) = ((1 + ‖x‖) ^ P_int)⁻¹ := by
          rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
        rw [hrpow_eq, ← div_eq_mul_inv, le_div_iff₀ hx_pos_pow]
        exact hx_dg_mul
      rw [norm_mul]
      calc ‖H (zImPoint n x ys)‖ * ‖dg (x - r • d)‖
          ≤ (K_H0 * (1 + ‖x‖) ^ M) * ‖dg u‖ :=
            mul_le_mul_of_nonneg_right h_Hz (norm_nonneg _)
        _ = K_H0 * ((1 + ‖x‖) ^ M * ‖dg u‖) := mul_assoc _ _ _
        _ ≤ K_H0 * ((S_dg * (1 + ‖d‖) ^ L_pow) * (1 + ‖x‖) ^ (-(P_int : ℝ))) :=
          mul_le_mul_of_nonneg_left hx_dg hKH0_nn
        _ = K_g * (1 + ‖x‖) ^ (-(P_int : ℝ)) := by dsimp [K_g]; ring
    · exact ((volume : Measure (Fin n → Fin 4 → ℝ)).integrable_pow_neg_integrablePower).const_mul
        K_g
    · refine Filter.Eventually.of_forall fun x r _ => ?_
      have h_dg_eq : dg (x - r • d) =
          (fderiv ℝ g (x - r • d)) ((0 : Fin n → Fin 4 → ℝ) - (1 : ℝ) • d) := by
        simp [dg]
      rw [h_dg_eq]
      exact ((g.differentiableAt.hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_const r x).sub ((hasDerivAt_id r).smul_const d))).const_mul
          (H (zImPoint n x ys)))
  have h_eq_re : (∫ x : Fin n → Fin 4 → ℝ, fderiv ℂ H (zImPoint n x ys) d_c * g x) =
      ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x ys) * dg x :=
    h_re1.unique h_re2
  have h_pull : (∫ x : Fin n → Fin 4 → ℝ,
      (Complex.I * fderiv ℂ H (zImPoint n x ys) d_c) * g x) =
      Complex.I * ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x ys) * dg x := by
    have h_assoc : (fun x : Fin n → Fin 4 → ℝ =>
        (Complex.I * fderiv ℂ H (zImPoint n x ys) d_c) * g x) =
        fun x => Complex.I * (fderiv ℂ H (zImPoint n x ys) d_c * g x) := by
      ext x
      exact mul_assoc _ _ _
    rw [h_assoc, MeasureTheory.integral_const_mul, h_eq_re]
  rwa [h_pull] at h_im_deriv

lemma odeReduceBound_mono (k : ℕ) {C₁ C₂ : ℕ → ℝ} (h : ∀ j, C₁ j ≤ C₂ j) (m : ℕ) :
    Distribution.odeReduceBound k C₁ m ≤ Distribution.odeReduceBound k C₂ m := by
  induction k generalizing C₁ C₂ m with
  | zero => exact h (m + 2)
  | succ k ih =>
    exact ih (fun j => add_le_add (mul_le_mul_of_nonneg_left (h j) (by positivity))
      (h (j + 1))) m

lemma odeReduceBound_zero (k m : ℕ) :
    Distribution.odeReduceBound k (fun _ => 0) m = 0 := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    simpa [Distribution.odeReduceBound] using ih m

lemma continuous_odeReduceBound {X : Type*} [TopologicalSpace X] (k m : ℕ)
    {C : X → ℕ → ℝ} (hC : ∀ j, Continuous (fun x => C x j)) :
    Continuous (fun x => Distribution.odeReduceBound k (C x) m) := by
  induction k generalizing C m with
  | zero => exact hC (m + 2)
  | succ k ih =>
    exact ih m (fun j => (continuous_const.mul (hC j)).add (hC (j + 1)))

lemma odeLipschitzBound_mono (N : ℕ) {C₁ C₂ : ℕ → ℝ} (h : ∀ j, C₁ j ≤ C₂ j) :
    Distribution.odeLipschitzBound N C₁ ≤ Distribution.odeLipschitzBound N C₂ := by
  cases N with
  | zero => exact h 1
  | succ k =>
    dsimp [Distribution.odeLipschitzBound]
    have hb := odeReduceBound_mono k h 1
    have h1 := h 1
    have h2 := h 2
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by positivity
    nlinarith

lemma odeLipschitzBound_zero (N : ℕ) :
    Distribution.odeLipschitzBound N (fun _ => 0) = 0 := by
  cases N with
  | zero => rfl
  | succ k =>
    simp [Distribution.odeLipschitzBound, odeReduceBound_zero]

lemma continuous_odeLipschitzBound {X : Type*} [TopologicalSpace X] (N : ℕ)
    {C : X → ℕ → ℝ} (hC : ∀ j, Continuous (fun x => C x j)) :
    Continuous (fun x => Distribution.odeLipschitzBound N (C x)) := by
  cases N with
  | zero => exact hC 1
  | succ k =>
    dsimp [Distribution.odeLipschitzBound]
    exact (continuous_const.mul (hC 1)).add
      (continuous_const.mul ((continuous_const.mul (hC 2)).add
        (continuous_const.mul (continuous_odeReduceBound k 1 hC))))

noncomputable def tubeRayCoeff (n M N_H : ℕ) (C_H : ℝ) (v : Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (j : ℕ) : ℝ :=
  C_H * (1 + (n : ℝ) * ‖v‖) ^ M * (1 + (coneGap v)⁻¹) ^ ((n - 1) * N_H) *
    schwartzPolyIntegralBound n M (((schwartzDirDerivCLM n (-tubeImDir n v))^[j]) f)

lemma tubeRayCoeff_nonneg {n M N_H : ℕ} {C_H : ℝ} (hCH : 0 ≤ C_H)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (j : ℕ) :
    0 ≤ tubeRayCoeff n M N_H C_H v f j := by
  unfold tubeRayCoeff
  have hg : 0 < coneGap v := coneGap_pos v hv
  have h1 : 0 ≤ 1 + (coneGap v)⁻¹ := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg hCH (by positivity)) (pow_nonneg h1 _))
    (schwartzPolyIntegralBound_nonneg n M _)

lemma iter_zero_of_map_zero {E : Type*} [Zero E] {L : E → E}
    (hL : L 0 = 0) (j : ℕ) : (L^[j]) 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hL]

lemma continuous_iter_clm {E : Type*} [TopologicalSpace E]
    {L : E → E} (hL : Continuous L) (j : ℕ) : Continuous (L^[j]) := by
  induction j with
  | zero => exact continuous_id
  | succ j ih =>
    rw [Function.iterate_succ]
    exact ih.comp hL

lemma tubeRayCoeff_zero_f (n M N_H : ℕ) (C_H : ℝ) (v : Fin 4 → ℝ) (j : ℕ) :
    tubeRayCoeff n M N_H C_H v 0 j = 0 := by
  unfold tubeRayCoeff
  have h0 : ((schwartzDirDerivCLM n (-tubeImDir n v))^[j]) 0 = 0 :=
    iter_zero_of_map_zero (map_zero (schwartzDirDerivCLM n (-tubeImDir n v))) j
  rw [h0, schwartzPolyIntegralBound_zero, mul_zero]

lemma continuous_tubeRayCoeff_f (n M N_H : ℕ) (C_H : ℝ) (v : Fin 4 → ℝ) (j : ℕ) :
    Continuous (fun f => tubeRayCoeff n M N_H C_H v f j) := by
  unfold tubeRayCoeff
  exact continuous_const.mul ((continuous_schwartzPolyIntegralBound n M).comp
    (continuous_iter_clm (schwartzDirDerivCLM n (-tubeImDir n v)).continuous j))

lemma continuous_iter_schwartzDirDerivCLM_seg (n : ℕ) (v₁ v₂ : Fin 4 → ℝ)
    (h : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (j : ℕ) :
    Continuous (fun s : ℝ =>
      ((schwartzDirDerivCLM n (-tubeImDir n ((1 - s) • v₁ + s • v₂)))^[j]) h) := by
  induction j with
  | zero => exact continuous_const
  | succ j ih =>
    have h_step : (fun s : ℝ =>
        ((schwartzDirDerivCLM n (-tubeImDir n ((1 - s) • v₁ + s • v₂)))^[j + 1]) h) =
        fun s => ((1 - s : ℝ) : ℂ) • schwartzDirDerivCLM n (-tubeImDir n v₁)
            (((schwartzDirDerivCLM n (-tubeImDir n ((1 - s) • v₁ + s • v₂)))^[j]) h) +
          (s : ℝ) • schwartzDirDerivCLM n (-tubeImDir n v₂)
            (((schwartzDirDerivCLM n (-tubeImDir n ((1 - s) • v₁ + s • v₂)))^[j]) h) := by
      ext s x
      rw [Function.iterate_succ_apply']
      have h_dir : -tubeImDir n ((1 - s) • v₁ + s • v₂) =
          (1 - s) • (-tubeImDir n v₁) + s • (-tubeImDir n v₂) := by
        ext i μ
        dsimp [tubeImDir]
        ring
      rw [h_dir, schwartzDirDerivCLM_dir_add, schwartzDirDerivCLM_dir_smul,
        schwartzDirDerivCLM_dir_smul]
      rfl
    rw [h_step]
    have hc1 : Continuous (fun s : ℝ => ((1 - s : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)
    have hc2 : Continuous (fun s : ℝ => (s : ℝ)) := continuous_id
    exact (hc1.smul ((schwartzDirDerivCLM n (-tubeImDir n v₁)).continuous.comp ih)).add
      ((Complex.continuous_ofReal.comp hc2).smul
        ((schwartzDirDerivCLM n (-tubeImDir n v₂)).continuous.comp ih))

noncomputable def tubeRayIterIntegral (n : ℕ) (H : (Fin n → Fin 4 → ℂ) → ℂ)
    (v : Fin 4 → ℝ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  ∫ x : Fin n → Fin 4 → ℝ,
    H (tubeBoundaryLine n x v t) * (((schwartzDirDerivCLM n (-tubeImDir n v))^[j]) f) x

lemma hasDerivAt_tubeRayIterIntegral {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (tubeRayIterIntegral n H v f j)
      (Complex.I * tubeRayIterIntegral n H v f (j + 1) t) t := by
  let g := ((schwartzDirDerivCLM n (-tubeImDir n v))^[j]) f
  have h_mem : zImPoint n 0 ((0 : Fin n → Fin 4 → ℝ) + t • tubeImDir n v) ∈
      forward_tube_n n := by
    rw [zero_add, ← tubeBoundaryLine_eq_zImPoint]
    exact tubeBoundaryLine_mem_forward_tube n 0 v hv ht
  have hd := hasDerivAt_zImPoint_schwartz h_ana hCH h_bd 0 (tubeImDir n v) g h_mem
  have h_fn : (fun τ : ℝ =>
      ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x (0 + τ • tubeImDir n v)) * g x) =
      tubeRayIterIntegral n H v f j := by
    ext τ
    simp only [zero_add, ← tubeBoundaryLine_eq_zImPoint]
    rfl
  have h_val : Complex.I * (∫ x : Fin n → Fin 4 → ℝ,
      H (zImPoint n x (0 + t • tubeImDir n v)) *
        (schwartzDirDerivCLM n (-tubeImDir n v) g) x) =
      Complex.I * tubeRayIterIntegral n H v f (j + 1) t := by
    congr 1
    unfold tubeRayIterIntegral
    congr 1
    ext x
    rw [zero_add, ← tubeBoundaryLine_eq_zImPoint]
    dsimp only [g]
    rw [← Function.iterate_succ_apply' (schwartzDirDerivCLM n (-tubeImDir n v)) j f]
  rwa [h_fn, h_val] at hd

lemma norm_tubeRayIterIntegral_le {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (j : ℕ)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖tubeRayIterIntegral n H v f j t‖ ≤
      tubeRayCoeff n M N_H C_H v f j / t ^ ((n - 1) * N_H) := by
  let g := ((schwartzDirDerivCLM n (-tubeImDir n v))^[j]) f
  have ht_pos : 0 < t := ht.1
  have hg_pos : 0 < coneGap v := coneGap_pos v hv
  let K_t : ℝ := C_H * (1 + (n : ℝ) * ‖v‖) ^ M *
    ((1 + (coneGap v)⁻¹) ^ ((n - 1) * N_H) / t ^ ((n - 1) * N_H))
  have hKt_nn : 0 ≤ K_t := by
    dsimp [K_t]
    positivity
  have h_pt : ∀ x : Fin n → Fin 4 → ℝ,
      ‖H (tubeBoundaryLine n x v t) * g x‖ ≤ K_t * ((1 + ‖x‖) ^ M * ‖g x‖) := by
    intro x
    rw [norm_mul]
    have hz_mem : tubeBoundaryLine n x v t ∈ forward_tube_n n :=
      tubeBoundaryLine_mem_forward_tube n x v hv ht_pos
    have h1 := h_bd (tubeBoundaryLine n x v t) hz_mem
    have h_z_norm : ‖tubeBoundaryLine n x v t‖ ≤ ‖x‖ + (n : ℝ) * ‖v‖ := by
      rw [tubeBoundaryLine_eq_zImPoint]
      calc ‖zImPoint n x (t • tubeImDir n v)‖
          ≤ ‖x‖ + ‖t • tubeImDir n v‖ := norm_zImPoint_le n x _
        _ = ‖x‖ + t * ‖tubeImDir n v‖ := by
          rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
        _ ≤ ‖x‖ + 1 * ((n : ℝ) * ‖v‖) := add_le_add le_rfl
          (mul_le_mul ht.2 (norm_tubeImDir_le n v) (norm_nonneg _) zero_le_one)
        _ = ‖x‖ + (n : ℝ) * ‖v‖ := by ring
    have h_z_prod : 1 + ‖tubeBoundaryLine n x v t‖ ≤
        (1 + (n : ℝ) * ‖v‖) * (1 + ‖x‖) := by
      nlinarith [h_z_norm, norm_nonneg x,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (norm_nonneg v)]
    have h_z_pow : (1 + ‖tubeBoundaryLine n x v t‖) ^ M ≤
        (1 + (n : ℝ) * ‖v‖) ^ M * (1 + ‖x‖) ^ M :=
      (pow_le_pow_left₀ (by positivity) h_z_prod M).trans_eq (mul_pow _ _ M)
    have h_gap := tubeGapFactor_tubeBoundaryLine_pow_le n N_H x hv ht
    have h_H_le : ‖H (tubeBoundaryLine n x v t)‖ ≤ K_t * (1 + ‖x‖) ^ M := by
      calc ‖H (tubeBoundaryLine n x v t)‖
          ≤ C_H * (1 + ‖tubeBoundaryLine n x v t‖) ^ M *
              (tubeGapFactor n (tubeBoundaryLine n x v t)) ^ N_H := h1
        _ ≤ C_H * ((1 + (n : ℝ) * ‖v‖) ^ M * (1 + ‖x‖) ^ M) *
              ((1 + (coneGap v)⁻¹) ^ ((n - 1) * N_H) / t ^ ((n - 1) * N_H)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h_z_pow hCH) h_gap
            (pow_nonneg (tubeGapFactor_nonneg hz_mem) N_H) (by positivity)
        _ = K_t * (1 + ‖x‖) ^ M := by dsimp [K_t]; ring
    calc ‖H (tubeBoundaryLine n x v t)‖ * ‖g x‖
        ≤ (K_t * (1 + ‖x‖) ^ M) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right h_H_le (norm_nonneg _)
      _ = K_t * ((1 + ‖x‖) ^ M * ‖g x‖) := mul_assoc _ _ _
  have hy_mem : zImPoint n 0 (t • tubeImDir n v) ∈ forward_tube_n n := by
    rw [← tubeBoundaryLine_eq_zImPoint]
    exact tubeBoundaryLine_mem_forward_tube n 0 v hv ht_pos
  have h_int_norm : Integrable
      (fun x : Fin n → Fin 4 → ℝ => ‖H (tubeBoundaryLine n x v t) * g x‖) volume := by
    have h_int := (integrable_zImPoint_mul_schwartz h_ana hCH h_bd hy_mem g).norm
    simpa only [← tubeBoundaryLine_eq_zImPoint] using h_int
  calc ‖tubeRayIterIntegral n H v f j t‖
      ≤ ∫ x : Fin n → Fin 4 → ℝ, ‖H (tubeBoundaryLine n x v t) * g x‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x : Fin n → Fin 4 → ℝ, K_t * ((1 + ‖x‖) ^ M * ‖g x‖) :=
      MeasureTheory.integral_mono h_int_norm
        ((integrable_one_add_norm_pow_mul_schwartz n M g).const_mul K_t) h_pt
    _ = K_t * ∫ x : Fin n → Fin 4 → ℝ, (1 + ‖x‖) ^ M * ‖g x‖ :=
      MeasureTheory.integral_const_mul _ _
    _ ≤ K_t * schwartzPolyIntegralBound n M g :=
      mul_le_mul_of_nonneg_left (integral_one_add_norm_pow_mul_schwartz_le n M g) hKt_nn
    _ = tubeRayCoeff n M N_H C_H v f j / t ^ ((n - 1) * N_H) := by
      dsimp [K_t, tubeRayCoeff, g]
      ring

lemma lipschitz_tubeRayIterIntegral_zero {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ∀ t₁ ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ t₂ ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖tubeRayIterIntegral n H v f 0 t₁ - tubeRayIterIntegral n H v f 0 t₂‖ ≤
        Distribution.odeLipschitzBound ((n - 1) * N_H)
          (tubeRayCoeff n M N_H C_H v f) * |t₁ - t₂| := by
  refine Distribution.ode_poly_singularity_lipschitz
    (fun j => tubeRayCoeff_nonneg hCH hv f j)
    (fun j t ht => hasDerivAt_tubeRayIterIntegral h_ana hCH h_bd hv f j ht.1)
    (fun j s hs => norm_tubeRayIterIntegral_le h_ana hCH h_bd hv f j
      ⟨hs.1, by linarith [hs.2]⟩)

lemma exists_tendsto_tubeBoundary_ray {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ∃ w : ℂ,
      Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, H (tubeBoundaryLine n x v t) * f x)
        (𝓝[>] 0) (𝓝 w) ∧
      ‖w‖ ≤ (2 : ℝ) ^ ((n - 1) * N_H) * tubeRayCoeff n M N_H C_H v f 0 +
        Distribution.odeLipschitzBound ((n - 1) * N_H)
          (tubeRayCoeff n M N_H C_H v f) * (1 / 2) := by
  let L_lip : ℝ := Distribution.odeLipschitzBound ((n - 1) * N_H)
    (tubeRayCoeff n M N_H C_H v f)
  have hL_nn : 0 ≤ L_lip :=
    Distribution.odeLipschitzBound_nonneg _ (fun j => tubeRayCoeff_nonneg hCH hv f j)
  have h_lip := lipschitz_tubeRayIterIntegral_zero h_ana hCH h_bd hv f
  let t_seq : ℕ → ℝ := fun k => (1 / 4 : ℝ) / ((k : ℝ) + 1)
  have ht_seq_mem : ∀ k : ℕ, t_seq k ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    intro k
    have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    refine ⟨by dsimp [t_seq]; positivity, ?_⟩
    dsimp [t_seq]
    rw [div_le_iff₀ hk_pos]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let a_seq : ℕ → ℂ := fun k => tubeRayIterIntegral n H v f 0 (t_seq k)
  have h_cauchy : CauchySeq a_seq := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt ((L_lip + 1) / ε)
    refine ⟨K, fun m hm l hl => ?_⟩
    rw [dist_eq_norm]
    have hK_pos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    have hm_le : t_seq m ≤ (1 / 4 : ℝ) / ((K : ℝ) + 1) := by
      dsimp [t_seq]
      exact div_le_div_of_nonneg_left (by norm_num) hK_pos
        (by exact_mod_cast Nat.succ_le_succ hm)
    have hl_le : t_seq l ≤ (1 / 4 : ℝ) / ((K : ℝ) + 1) := by
      dsimp [t_seq]
      exact div_le_div_of_nonneg_left (by norm_num) hK_pos
        (by exact_mod_cast Nat.succ_le_succ hl)
    have h_diff_le : |t_seq m - t_seq l| ≤ 1 / (2 * ((K : ℝ) + 1)) := by
      rw [abs_le]
      have hm0 := (ht_seq_mem m).1
      have hl0 := (ht_seq_mem l).1
      have h_quarter_le : (1 / 4 : ℝ) / ((K : ℝ) + 1) ≤ 1 / (2 * ((K : ℝ) + 1)) := by
        rw [div_le_div_iff₀ hK_pos (by positivity)]
        linarith
      constructor <;> linarith
    have h1 := h_lip (t_seq m) (ht_seq_mem m) (t_seq l) (ht_seq_mem l)
    have h2 : L_lip * |t_seq m - t_seq l| < ε := by
      calc L_lip * |t_seq m - t_seq l|
          ≤ L_lip * (1 / (2 * ((K : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h_diff_le hL_nn
        _ ≤ (L_lip + 1) * (1 / ((K : ℝ) + 1)) := by
          have h_inv_le : 1 / (2 * ((K : ℝ) + 1)) ≤ 1 / ((K : ℝ) + 1) :=
            one_div_le_one_div_of_le hK_pos (by linarith)
          exact mul_le_mul (by linarith) h_inv_le (by positivity) (by positivity)
        _ < (L_lip + 1) * (ε / (L_lip + 1)) := by
          refine mul_lt_mul_of_pos_left ?_ (by positivity)
          rw [div_lt_div_iff₀ hK_pos (by positivity)]
          linarith [(div_lt_iff₀ hε).mp hK, hε]
        _ = ε := mul_div_cancel₀ ε (by positivity)
    exact h1.trans_lt h2
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have ht_seq_zero : Tendsto t_seq atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [t_seq, div_eq_mul_inv] using h1.const_mul (1 / 4 : ℝ)
  have h_rate : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖tubeRayIterIntegral n H v f 0 t - w‖ ≤ L_lip * t := by
    intro t ht
    have h_lhs : Tendsto (fun k : ℕ => ‖tubeRayIterIntegral n H v f 0 t - a_seq k‖)
        atTop (𝓝 ‖tubeRayIterIntegral n H v f 0 t - w‖) :=
      (tendsto_const_nhds.sub hw).norm
    have h_rhs : Tendsto (fun k : ℕ => L_lip * |t - t_seq k|)
        atTop (𝓝 (L_lip * t)) := by
      have habs : |t - 0| = t := by rw [sub_zero, abs_of_pos ht.1]
      have h_lim_abs : Tendsto (fun k : ℕ => L_lip * |t - t_seq k|)
          atTop (𝓝 (L_lip * |t - 0|)) :=
        (tendsto_const_nhds (x := L_lip)).mul
          (((tendsto_const_nhds (x := t)).sub ht_seq_zero).abs)
      rwa [habs] at h_lim_abs
    exact le_of_tendsto_of_tendsto h_lhs h_rhs
      (Filter.Eventually.of_forall fun k => h_lip t ht (t_seq k) (ht_seq_mem k))
  refine ⟨w, ?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    let δ : ℝ := min (1 / 2) (ε / (L_lip + 1))
    refine ⟨δ, lt_min (by norm_num) (div_pos hε (by positivity)), fun t ht_pos ht_dist => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos ht_pos] at ht_dist
    have ht_ioc : t ∈ Set.Ioc (0 : ℝ) (1 / 2) :=
      ⟨ht_pos, ht_dist.le.trans (min_le_left _ _)⟩
    rw [dist_eq_norm]
    have h_eq0 : (∫ x : Fin n → Fin 4 → ℝ, H (tubeBoundaryLine n x v t) * f x) =
        tubeRayIterIntegral n H v f 0 t := rfl
    rw [h_eq0]
    calc ‖tubeRayIterIntegral n H v f 0 t - w‖
        ≤ L_lip * t := h_rate t ht_ioc
      _ ≤ (L_lip + 1) * t := mul_le_mul_of_nonneg_right (by linarith) ht_pos.le
      _ < (L_lip + 1) * (ε / (L_lip + 1)) :=
        mul_lt_mul_of_pos_left (ht_dist.trans_le (min_le_right _ _)) (by positivity)
      _ = ε := mul_div_cancel₀ ε (by positivity)
  · have h_half_mem : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := ⟨by norm_num, le_rfl⟩
    have h_half_bd := norm_tubeRayIterIntegral_le h_ana hCH h_bd hv f 0
      (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    have h_div_eq : tubeRayCoeff n M N_H C_H v f 0 / (1 / 2 : ℝ) ^ ((n - 1) * N_H) =
        (2 : ℝ) ^ ((n - 1) * N_H) * tubeRayCoeff n M N_H C_H v f 0 := by
      rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
    rw [h_div_eq] at h_half_bd
    have h_tri : ‖w‖ ≤ ‖tubeRayIterIntegral n H v f 0 (1 / 2)‖ +
        ‖tubeRayIterIntegral n H v f 0 (1 / 2) - w‖ := by
      simpa [norm_sub_rev] using norm_add_le (tubeRayIterIntegral n H v f 0 (1 / 2))
        (w - tubeRayIterIntegral n H v f 0 (1 / 2))
    linarith [h_rate (1 / 2) h_half_mem]

lemma tendsto_tubeBoundary_ray_unique {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {v₁ v₂ : Fin 4 → ℝ} (hv₁ : v₁ ∈ forward_light_cone) (hv₂ : v₂ ∈ forward_light_cone)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) {w₁ w₂ : ℂ}
    (hw₁ : Tendsto (fun t : ℝ => ∫ x, H (tubeBoundaryLine n x v₁ t) * f x) (𝓝[>] 0) (𝓝 w₁))
    (hw₂ : Tendsto (fun t : ℝ => ∫ x, H (tubeBoundaryLine n x v₂ t) * f x) (𝓝[>] 0) (𝓝 w₂)) :
    w₁ = w₂ := by
  let h := schwartzDirDerivCLM n (-tubeImDir n (v₂ - v₁)) f
  let v_seg : ℝ → Fin 4 → ℝ := fun s => (1 - s) • v₁ + s • v₂
  let g_min : ℝ := min (coneGap v₁) (coneGap v₂)
  have hg_min_pos : 0 < g_min := lt_min (coneGap_pos v₁ hv₁) (coneGap_pos v₂ hv₂)
  have hv_seg_gap : ∀ s ∈ Set.Icc (0 : ℝ) 1, g_min ≤ coneGap (v_seg s) := by
    intro s hs
    have h1 := coneGap_add_ge ((1 - s) • v₁) (s • v₂)
    rw [coneGap_smul_of_nonneg (by linarith [hs.2]), coneGap_smul_of_nonneg hs.1] at h1
    have hg1 : g_min ≤ coneGap v₁ := min_le_left _ _
    have hg2 : g_min ≤ coneGap v₂ := min_le_right _ _
    have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
    nlinarith [hs.1]
  have hv_seg_cone : ∀ s ∈ Set.Icc (0 : ℝ) 1, v_seg s ∈ forward_light_cone := fun s hs =>
    (mem_forward_light_cone_iff_coneGap_pos _).mpr (hg_min_pos.trans_le (hv_seg_gap s hs))
  have hv_seg_norm : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖v_seg s‖ ≤ ‖v₁‖ + ‖v₂‖ := by
    intro s hs
    calc ‖(1 - s) • v₁ + s • v₂‖
        ≤ ‖(1 - s) • v₁‖ + ‖s • v₂‖ := norm_add_le _ _
      _ = (1 - s) * ‖v₁‖ + s * ‖v₂‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [hs.2]),
          Real.norm_of_nonneg hs.1]
      _ ≤ 1 * ‖v₁‖ + 1 * ‖v₂‖ := add_le_add
        (mul_le_mul_of_nonneg_right (by linarith [hs.1]) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _))
      _ = ‖v₁‖ + ‖v₂‖ := by ring
  have h_poly_ub : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      schwartzPolyIntegralBound n M
        (((schwartzDirDerivCLM n (-tubeImDir n (v_seg s)))^[j]) h) ≤ B := by
    intro j
    have hc : Continuous (fun s : ℝ => schwartzPolyIntegralBound n M
        (((schwartzDirDerivCLM n (-tubeImDir n (v_seg s)))^[j]) h)) :=
      (continuous_schwartzPolyIntegralBound n M).comp
        (continuous_iter_schwartzDirDerivCLM_seg n v₁ v₂ h j)
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
    have hs_le := hB s hs
    rw [Real.norm_of_nonneg (schwartzPolyIntegralBound_nonneg n M _)] at hs_le
    exact hs_le.trans (le_max_left _ _)
  let B_poly : ℕ → ℝ := fun j => (h_poly_ub j).choose
  let C_seg : ℕ → ℝ := fun j =>
    C_H * (1 + (n : ℝ) * (‖v₁‖ + ‖v₂‖)) ^ M * (1 + g_min⁻¹) ^ ((n - 1) * N_H) * B_poly j
  have h_coeff_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ j : ℕ,
      tubeRayCoeff n M N_H C_H (v_seg s) h j ≤ C_seg j := by
    intro s hs j
    unfold tubeRayCoeff
    dsimp [C_seg]
    have h_v : (1 + (n : ℝ) * ‖v_seg s‖) ^ M ≤ (1 + (n : ℝ) * (‖v₁‖ + ‖v₂‖)) ^ M := by
      refine pow_le_pow_left₀ (by positivity) ?_ M
      nlinarith [hv_seg_norm s hs, Nat.cast_nonneg (α := ℝ) n]
    have h_g : (1 + (coneGap (v_seg s))⁻¹) ^ ((n - 1) * N_H) ≤
        (1 + g_min⁻¹) ^ ((n - 1) * N_H) := by
      refine pow_le_pow_left₀ ?_ ?_ _
      · have hg_s := hv_seg_gap s hs
        have : 0 < coneGap (v_seg s) := hg_min_pos.trans_le hg_s
        positivity
      · gcongr
        exact hv_seg_gap s hs
    have h_p : schwartzPolyIntegralBound n M
        (((schwartzDirDerivCLM n (-tubeImDir n (v_seg s)))^[j]) h) ≤ B_poly j :=
      (h_poly_ub j).choose_spec.2 s hs
    refine mul_le_mul ?_ h_p (schwartzPolyIntegralBound_nonneg n M _) (by positivity)
    refine mul_le_mul (mul_le_mul_of_nonneg_left h_v hCH) h_g ?_ (by positivity)
    have hg_s := hv_seg_gap s hs
    have : 0 < coneGap (v_seg s) := hg_min_pos.trans_le hg_s
    positivity
  let M_seg : ℝ := (2 : ℝ) ^ ((n - 1) * N_H) * C_seg 0 +
    Distribution.odeLipschitzBound ((n - 1) * N_H) C_seg
  have h_Ih_bd : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖tubeRayIterIntegral n H (v_seg s) h 0 t‖ ≤ M_seg := by
    intro s hs t ht
    have hv_s := hv_seg_cone s hs
    have h_half := norm_tubeRayIterIntegral_le h_ana hCH h_bd hv_s h 0
      (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    have h_div_eq : tubeRayCoeff n M N_H C_H (v_seg s) h 0 / (1 / 2 : ℝ) ^ ((n - 1) * N_H) =
        (2 : ℝ) ^ ((n - 1) * N_H) * tubeRayCoeff n M N_H C_H (v_seg s) h 0 := by
      rw [one_div, inv_pow, div_inv_eq_mul, mul_comm]
    rw [h_div_eq] at h_half
    have h_lip := lipschitz_tubeRayIterIntegral_zero h_ana hCH h_bd hv_s h
      t ht (1 / 2) ⟨by norm_num, le_rfl⟩
    have ht_diff : |t - 1 / 2| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hL_mono := odeLipschitzBound_mono ((n - 1) * N_H) (h_coeff_le s hs)
    have hL_nn := Distribution.odeLipschitzBound_nonneg ((n - 1) * N_H)
      (fun j => tubeRayCoeff_nonneg (M := M) (N_H := N_H) hCH hv_s h j)
    have h_tri : ‖tubeRayIterIntegral n H (v_seg s) h 0 t‖ ≤
        ‖tubeRayIterIntegral n H (v_seg s) h 0 (1 / 2)‖ +
          ‖tubeRayIterIntegral n H (v_seg s) h 0 t -
            tubeRayIterIntegral n H (v_seg s) h 0 (1 / 2)‖ := by
      simpa [add_comm] using norm_add_le
        (tubeRayIterIntegral n H (v_seg s) h 0 t -
          tubeRayIterIntegral n H (v_seg s) h 0 (1 / 2))
        (tubeRayIterIntegral n H (v_seg s) h 0 (1 / 2))
    have hc0 := h_coeff_le s hs 0
    have h_lip1 : ‖tubeRayIterIntegral n H (v_seg s) h 0 t -
        tubeRayIterIntegral n H (v_seg s) h 0 (1 / 2)‖ ≤
        Distribution.odeLipschitzBound ((n - 1) * N_H) C_seg := by
      calc ‖tubeRayIterIntegral n H (v_seg s) h 0 t -
            tubeRayIterIntegral n H (v_seg s) h 0 (1 / 2)‖
          ≤ Distribution.odeLipschitzBound ((n - 1) * N_H)
              (tubeRayCoeff n M N_H C_H (v_seg s) h) * |t - 1 / 2| := h_lip
        _ ≤ Distribution.odeLipschitzBound ((n - 1) * N_H)
              (tubeRayCoeff n M N_H C_H (v_seg s) h) * 1 :=
          mul_le_mul_of_nonneg_left ht_diff hL_nn
        _ ≤ Distribution.odeLipschitzBound ((n - 1) * N_H) C_seg := by linarith
    have h_c0_pow : (2 : ℝ) ^ ((n - 1) * N_H) * tubeRayCoeff n M N_H C_H (v_seg s) h 0 ≤
        (2 : ℝ) ^ ((n - 1) * N_H) * C_seg 0 :=
      mul_le_mul_of_nonneg_left hc0 (by positivity)
    dsimp [M_seg]
    linarith
  have h_diff_ray : ∀ t ∈ Set.Ioc (0 : ℝ) (1 / 2),
      ‖(∫ x, H (tubeBoundaryLine n x v₂ t) * f x) -
        (∫ x, H (tubeBoundaryLine n x v₁ t) * f x)‖ ≤ M_seg * t := by
    intro t ht
    let y₀ := t • tubeImDir n v₁
    let d := t • tubeImDir n (v₂ - v₁)
    have h_line_eq : ∀ s (x : Fin n → Fin 4 → ℝ),
        tubeBoundaryLine n x (v_seg s) t = zImPoint n x (y₀ + s • d) := by
      intro s x
      ext i μ
      dsimp [tubeBoundaryLine, zImPoint, y₀, d, tubeImDir, v_seg]
      push_cast
      ring
    have h_dw : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun τ : ℝ => ∫ x, H (tubeBoundaryLine n x (v_seg τ) t) * f x)
          (Complex.I * ((t : ℂ) * tubeRayIterIntegral n H (v_seg s) h 0 t))
          (Set.Icc 0 1) s := by
      intro s hs
      have hs_mem : zImPoint n 0 (y₀ + s • d) ∈ forward_tube_n n := by
        rw [← h_line_eq s 0]
        exact tubeBoundaryLine_mem_forward_tube n 0 (v_seg s) (hv_seg_cone s hs) ht.1
      have hd := hasDerivAt_zImPoint_schwartz h_ana hCH h_bd y₀ d f hs_mem
      have h_fn : (fun τ : ℝ => ∫ x, H (zImPoint n x (y₀ + τ • d)) * f x) =
          fun τ => ∫ x, H (tubeBoundaryLine n x (v_seg τ) t) * f x := by
        ext τ
        simp only [h_line_eq]
      have h_val : (∫ x, H (zImPoint n x (y₀ + s • d)) * (schwartzDirDerivCLM n (-d) f) x) =
          (t : ℂ) * tubeRayIterIntegral n H (v_seg s) h 0 t := by
        have h_neg_d : -d = t • (-tubeImDir n (v₂ - v₁)) := by
          ext i μ
          dsimp [d]
          simp [mul_neg]
        have h_ig : (fun x => H (zImPoint n x (y₀ + s • d)) *
            (schwartzDirDerivCLM n (-d) f) x) =
            fun x => (t : ℂ) * (H (tubeBoundaryLine n x (v_seg s) t) * h x) := by
          ext x
          rw [← h_line_eq s x, h_neg_d, schwartzDirDerivCLM_dir_smul]
          change H (tubeBoundaryLine n x (v_seg s) t) * ((t : ℂ) * h x) = _
          ring
        rw [h_ig, MeasureTheory.integral_const_mul]
        rfl
      rw [h_fn, h_val] at hd
      exact hd.hasDerivWithinAt
    have h_nb : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖Complex.I * ((t : ℂ) * tubeRayIterIntegral n H (v_seg s) h 0 t)‖ ≤ M_seg * t := by
      intro s hs
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ht.1.le, mul_comm]
      exact mul_le_mul_of_nonneg_right (h_Ih_bd s hs t ht) ht.1.le
    have h_mvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      h_dw h_nb ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    have hv0 : v_seg 0 = v₁ := by ext μ; simp [v_seg]
    have hv1 : v_seg 1 = v₂ := by ext μ; simp [v_seg]
    simpa [hv0, hv1] using h_mvt
  have h_lim_lhs : Tendsto
      (fun t : ℝ => ‖(∫ x, H (tubeBoundaryLine n x v₂ t) * f x) -
        (∫ x, H (tubeBoundaryLine n x v₁ t) * f x)‖)
      (𝓝[>] 0) (𝓝 ‖w₂ - w₁‖) := (hw₂.sub hw₁).norm
  have h_lim_rhs : Tendsto (fun t : ℝ => M_seg * t) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => M_seg * t) (𝓝[>] (0 : ℝ)) (𝓝 (M_seg * 0)) :=
      (tendsto_const_nhds (x := M_seg)).mul
        (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ))))
    simpa using h0
  have h_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖(∫ x, H (tubeBoundaryLine n x v₂ t) * f x) -
        (∫ x, H (tubeBoundaryLine n x v₁ t) * f x)‖ ≤ M_seg * t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
    exact h_diff_ray t ⟨ht.1, ht.2.le⟩
  have h_norm_le : ‖w₂ - w₁‖ ≤ 0 := le_of_tendsto_of_tendsto h_lim_lhs h_lim_rhs h_ev
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h_norm_le)).symm

noncomputable def vladimirovFromTubeVal {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) (n : ℕ) (α : Fin n → κ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) : ℂ :=
  (exists_tendsto_tubeBoundary_ray (h_ana n α) (h_growth n α).choose_spec.choose_spec.choose_spec.1
    (h_growth n α).choose_spec.choose_spec.choose_spec.2
    unit_time_vector_mem_forward_light_cone f).choose

lemma tendsto_vladimirovFromTubeVal_unit {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) (n : ℕ) (α : Fin n → κ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        H n α (tubeBoundaryLine n x unit_time_vector t) * f x)
      (𝓝[>] 0) (𝓝 (vladimirovFromTubeVal h_ana h_growth n α f)) :=
  (exists_tendsto_tubeBoundary_ray (h_ana n α)
    (h_growth n α).choose_spec.choose_spec.choose_spec.1
    (h_growth n α).choose_spec.choose_spec.choose_spec.2
    unit_time_vector_mem_forward_light_cone f).choose_spec.1

lemma tendsto_vladimirovFromTubeVal {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) (n : ℕ) (α : Fin n → κ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) {v : Fin 4 → ℝ} (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, H n α (tubeBoundaryLine n x v t) * f x)
      (𝓝[>] 0) (𝓝 (vladimirovFromTubeVal h_ana h_growth n α f)) := by
  obtain ⟨C_H, M, N_H, hCH, h_bd⟩ := h_growth n α
  obtain ⟨w_v, hw_v, _⟩ := exists_tendsto_tubeBoundary_ray (h_ana n α) hCH h_bd hv f
  have h_eq := tendsto_tubeBoundary_ray_unique (h_ana n α) hCH h_bd
    hv unit_time_vector_mem_forward_light_cone f hw_v
    (tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α f)
  rwa [h_eq] at hw_v

noncomputable def vladimirovFromTubeCLM {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) (n : ℕ) (α : Fin n → κ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ := by
  let L_lin : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →ₗ[ℂ] ℂ :=
    { toFun := vladimirovFromTubeVal h_ana h_growth n α
      map_add' := fun f g => by
        obtain ⟨C_H, M, N_H, hCH, h_bd⟩ := h_growth n α
        have hf := tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α f
        have hg := tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α g
        have hfg := tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α (f + g)
        have h_ev : (fun t : ℝ => ∫ x,
            H n α (tubeBoundaryLine n x unit_time_vector t) * (f + g) x) =ᶠ[𝓝[>] 0]
            fun t => (∫ x, H n α (tubeBoundaryLine n x unit_time_vector t) * f x) +
              (∫ x, H n α (tubeBoundaryLine n x unit_time_vector t) * g x) := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          have hy : zImPoint n 0 (t • tubeImDir n unit_time_vector) ∈ forward_tube_n n := by
            rw [← tubeBoundaryLine_eq_zImPoint]
            exact tubeBoundaryLine_mem_forward_tube n 0 unit_time_vector
              unit_time_vector_mem_forward_light_cone ht
          have h_if : Integrable (fun x =>
              H n α (tubeBoundaryLine n x unit_time_vector t) * f x) volume := by
            simpa only [← tubeBoundaryLine_eq_zImPoint] using
              integrable_zImPoint_mul_schwartz (h_ana n α) hCH h_bd hy f
          have h_ig : Integrable (fun x =>
              H n α (tubeBoundaryLine n x unit_time_vector t) * g x) volume := by
            simpa only [← tubeBoundaryLine_eq_zImPoint] using
              integrable_zImPoint_mul_schwartz (h_ana n α) hCH h_bd hy g
          have h_add_pt : (fun x =>
              H n α (tubeBoundaryLine n x unit_time_vector t) * (f + g) x) =
              fun x => H n α (tubeBoundaryLine n x unit_time_vector t) * f x +
                H n α (tubeBoundaryLine n x unit_time_vector t) * g x := by
            ext x
            exact mul_add _ _ _
          rw [h_add_pt, MeasureTheory.integral_add h_if h_ig]
        exact tendsto_nhds_unique hfg ((hf.add hg).congr' h_ev.symm)
      map_smul' := fun c f => by
        have hf := tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α f
        have hcf := tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α (c • f)
        have h_ev : (fun t : ℝ => ∫ x,
            H n α (tubeBoundaryLine n x unit_time_vector t) * (c • f) x) =ᶠ[𝓝[>] 0]
            fun t => c * ∫ x, H n α (tubeBoundaryLine n x unit_time_vector t) * f x := by
          filter_upwards [self_mem_nhdsWithin] with t _
          have h_pt : (fun x => H n α (tubeBoundaryLine n x unit_time_vector t) * (c • f) x) =
              fun x => c * (H n α (tubeBoundaryLine n x unit_time_vector t) * f x) := by
            ext x
            change H n α (tubeBoundaryLine n x unit_time_vector t) * (c * f x) = _
            ring
          rw [h_pt, MeasureTheory.integral_const_mul]
        simpa using tendsto_nhds_unique hcf ((hf.const_mul c).congr' h_ev.symm) }
  refine { toLinearMap := L_lin, cont := ?_ }
  refine continuous_of_tendsto_nhds_zero L_lin ?_
  let C_H := (h_growth n α).choose
  let M := (h_growth n α).choose_spec.choose
  let N_H := (h_growth n α).choose_spec.choose_spec.choose
  let U_bd : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ → ℝ := fun f =>
    (2 : ℝ) ^ ((n - 1) * N_H) * tubeRayCoeff n M N_H C_H unit_time_vector f 0 +
      Distribution.odeLipschitzBound ((n - 1) * N_H)
        (tubeRayCoeff n M N_H C_H unit_time_vector f) * (1 / 2)
  have hU_cont : Continuous U_bd :=
    (continuous_const.mul (continuous_tubeRayCoeff_f n M N_H C_H unit_time_vector 0)).add
      ((continuous_odeLipschitzBound ((n - 1) * N_H)
        (fun j => continuous_tubeRayCoeff_f n M N_H C_H unit_time_vector j)).mul continuous_const)
  have hU_zero : U_bd 0 = 0 := by
    dsimp [U_bd]
    have h_fn : tubeRayCoeff n M N_H C_H unit_time_vector 0 = fun _ => 0 := by
      ext j
      exact tubeRayCoeff_zero_f n M N_H C_H unit_time_vector j
    rw [h_fn, odeLipschitzBound_zero]
    ring
  have hU_lim : Tendsto U_bd (𝓝 0) (𝓝 0) := hU_zero ▸ hU_cont.continuousAt
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun f => ?_) hU_lim)
  exact (exists_tendsto_tubeBoundary_ray (h_ana n α)
    (h_growth n α).choose_spec.choose_spec.choose_spec.1
    (h_growth n α).choose_spec.choose_spec.choose_spec.2
    unit_time_vector_mem_forward_light_cone f).choose_spec.2

@[simp]
lemma vladimirovFromTubeCLM_apply {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) (n : ℕ) (α : Fin n → κ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovFromTubeCLM h_ana h_growth n α f =
      vladimirovFromTubeVal h_ana h_growth n α f := rfl

noncomputable def vladimirovFromTubeWightmanFamily {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) : WightmanFamily κ :=
  fun n α => _root_.ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ)
    (SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) ℂ (vladimirovFromTubeCLM h_ana h_growth n α)

@[simp]
lemma vladimirovFromTubeWightmanFamily_apply {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) (n : ℕ) (α : Fin n → κ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vladimirovFromTubeWightmanFamily h_ana h_growth n α f =
      vladimirovFromTubeVal h_ana h_growth n α f := rfl

noncomputable def vladimirovFromTubeExtension {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H) :
    TubeExtension (vladimirovFromTubeWightmanFamily h_ana h_growth) where
  H := H
  analytic := h_ana
  boundary := fun n α f _v hv => tendsto_vladimirovFromTubeVal h_ana h_growth n α f hv

lemma minkowskiFourier_schwartzDirDerivCLM (n : ℕ) (d : Fin n → Fin 4 → ℝ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (schwartzDirDerivCLM n d f) p =
      (Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ) : ℂ)) *
        minkowskiFourier f p := by
  rw [← minkowskiFourierCLM_apply, ← minkowskiFourierCLM_apply]
  let e : (EuclideanSpace ℝ (Fin n × Fin 4)) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
    (piSpaceEquiv n).symm.trans (minkowskiFlipEquiv n)
  let m : EuclideanSpace ℝ (Fin n × Fin 4) := piSpaceEquiv n (minkowskiFlipFun n d)
  have hem : e m = d := by
    change minkowskiFlipEquiv n ((piSpaceEquiv n).symm
      (piSpaceEquiv n (minkowskiFlipFun n d))) = d
    rw [(piSpaceEquiv n).symm_apply_apply]
    exact minkowskiFlipFun_involutive n d
  let g_euclid : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  let ξ : EuclideanSpace ℝ (Fin n × Fin 4) := piSpaceEquiv n (posScaledMomentumN n p)
  have h_comp : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (schwartzDirDerivCLM n d f) =
      LineDeriv.lineDerivOp m g_euclid := by
    dsimp [g_euclid, schwartzDirDerivCLM]
    rw [← hem]
    exact (SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv (𝕜 := ℂ) m e f).symm
  have h_eval1 : (minkowskiFourierCLM n (schwartzDirDerivCLM n d f)) p =
      (FourierTransform.fourier (LineDeriv.lineDerivOp m g_euclid)) ξ := by
    change ((schwartzCompCLE ((posScaledMomentumEquivN n).trans (piSpaceEquiv n)))
      ((schwartzFourierCLE (EuclideanSpace ℝ (Fin n × Fin 4)))
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (schwartzDirDerivCLM n d f)))) p = _
    rw [h_comp]
    rfl
  have h_eval2 : (minkowskiFourierCLM n f) p = (FourierTransform.fourier g_euclid) ξ := rfl
  rw [h_eval1, h_eval2, SchwartzMap.fourier_lineDerivOp_eq]
  have h_temp : (fun u : EuclideanSpace ℝ (Fin n × Fin 4) => inner ℝ u m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [_root_.smul_apply, SchwartzMap.smulLeftCLM_apply_apply h_temp]
  simp only [Complex.real_smul, smul_eq_mul, real_inner_comm m ξ]
  have h_ph := fourier_phase_eq_n n p d
  have h_in : 2 * Real.pi * inner ℝ m ξ = ∑ k : Fin n, minkowskiInner (p k) (d k) := by
    dsimp [m, ξ]
    linarith
  have h_cast : (2 * (Real.pi : ℂ) * Complex.I) *
      (((inner ℝ m ξ : ℝ) : ℂ) * (FourierTransform.fourier g_euclid) ξ) =
      (Complex.I * (((2 * Real.pi * inner ℝ m ξ : ℝ) : ℂ))) *
        (FourierTransform.fourier g_euclid) ξ := by
    push_cast
    ring
  rw [h_cast, h_in]

noncomputable def zImPointIntegralCLM {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {y : Fin n → Fin 4 → ℝ} (hy : zImPoint n 0 y ∈ forward_tube_n n) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ := by
  let L_lin : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x y) * f x
      map_add' := fun f g => by
        have hf := integrable_zImPoint_mul_schwartz h_ana hCH h_bd hy f
        have hg := integrable_zImPoint_mul_schwartz h_ana hCH h_bd hy g
        have h_pt : (fun x => H (zImPoint n x y) * (f + g) x) =
            fun x => H (zImPoint n x y) * f x + H (zImPoint n x y) * g x := by
          ext x
          exact mul_add _ _ _
        rw [h_pt, MeasureTheory.integral_add hf hg]
      map_smul' := fun c f => by
        have h_pt : (fun x => H (zImPoint n x y) * (c • f) x) =
            fun x => c * (H (zImPoint n x y) * f x) := by
          ext x
          change H (zImPoint n x y) * (c * f x) = _
          ring
        rw [h_pt, MeasureTheory.integral_const_mul]
        rfl }
  refine { toLinearMap := L_lin, cont := ?_ }
  refine continuous_of_tendsto_nhds_zero L_lin ?_
  let K : ℝ := C_H * (1 + ‖y‖) ^ M * (tubeGapFactor n (zImPoint n 0 y)) ^ N_H
  have hK_cont : Continuous (fun f => K * schwartzPolyIntegralBound n M f) :=
    continuous_const.mul (continuous_schwartzPolyIntegralBound n M)
  have hK_lim : Tendsto (fun f => K * schwartzPolyIntegralBound n M f) (𝓝 0) (𝓝 0) := by
    have h0 : K * schwartzPolyIntegralBound n M 0 = 0 := by
      rw [schwartzPolyIntegralBound_zero, mul_zero]
    exact h0 ▸ hK_cont.continuousAt
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) (fun f => ?_) hK_lim)
  have h_pt_le : ∀ x : Fin n → Fin 4 → ℝ,
      ‖H (zImPoint n x y) * f x‖ ≤ K * ((1 + ‖x‖) ^ M * ‖f x‖) := by
    intro x
    rw [norm_mul]
    have hz : zImPoint n x y ∈ forward_tube_n n := (zImPoint_mem_forward_tube_iff n x y).mpr hy
    have h_Hz := h_bd _ hz
    rw [tubeGapFactor_zImPoint_eq n x y] at h_Hz
    have h_z_le : 1 + ‖zImPoint n x y‖ ≤ (1 + ‖y‖) * (1 + ‖x‖) := by
      have hn1 := norm_zImPoint_le n x y
      nlinarith [norm_nonneg x, norm_nonneg y]
    have h_pow : (1 + ‖zImPoint n x y‖) ^ M ≤ (1 + ‖y‖) ^ M * (1 + ‖x‖) ^ M :=
      (pow_le_pow_left₀ (by positivity) h_z_le M).trans_eq (mul_pow _ _ M)
    have h_gap_nn : 0 ≤ (tubeGapFactor n (zImPoint n 0 y)) ^ N_H :=
      pow_nonneg (tubeGapFactor_nonneg hy) N_H
    calc ‖H (zImPoint n x y)‖ * ‖f x‖
        ≤ (C_H * ((1 + ‖y‖) ^ M * (1 + ‖x‖) ^ M) *
            (tubeGapFactor n (zImPoint n 0 y)) ^ N_H) * ‖f x‖ := by
          refine mul_le_mul_of_nonneg_right (h_Hz.trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_pow hCH) h_gap_nn
      _ = K * ((1 + ‖x‖) ^ M * ‖f x‖) := by dsimp [K]; ring
  calc ‖L_lin f‖ ≤ ∫ x : Fin n → Fin 4 → ℝ, ‖H (zImPoint n x y) * f x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x : Fin n → Fin 4 → ℝ, K * ((1 + ‖x‖) ^ M * ‖f x‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((integrable_one_add_norm_pow_mul_schwartz n M f).const_mul K)
          (Filter.Eventually.of_forall h_pt_le)
    _ = K * ∫ x : Fin n → Fin 4 → ℝ, (1 + ‖x‖) ^ M * ‖f x‖ :=
        MeasureTheory.integral_const_mul K _
    _ ≤ K * schwartzPolyIntegralBound n M f :=
        mul_le_mul_of_nonneg_left (integral_one_add_norm_pow_mul_schwartz_le n M f)
          (mul_nonneg (mul_nonneg hCH (by positivity))
            (pow_nonneg (tubeGapFactor_nonneg hy) N_H))

@[simp]
lemma zImPointIntegralCLM_apply {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {y : Fin n → Fin 4 → ℝ} (hy : zImPoint n 0 y ∈ forward_tube_n n)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    zImPointIntegralCLM h_ana hCH h_bd hy f =
      ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x y) * f x := rfl

lemma exists_cone_sep_of_notMem_closure {Q : Fin 4 → ℝ}
    (hQ : Q ∉ closure forward_light_cone) :
    ∃ w ∈ forward_light_cone, minkowskiInner Q w < 0 := by
  rw [closure_forward_light_cone_eq] at hQ
  let sq_sp : ℝ := (Q 1) ^ 2 + (Q 2) ^ 2 + (Q 3) ^ 2
  let s_Q : ℝ := Real.sqrt sq_sp
  have hsq_nn : 0 ≤ sq_sp := by positivity
  have hs_nn : 0 ≤ s_Q := Real.sqrt_nonneg _
  have hs_sq : s_Q ^ 2 = sq_sp := Real.sq_sqrt hsq_nn
  have hQ0_lt : Q 0 < s_Q := by
    by_contra h_ge
    push Not at h_ge
    apply hQ
    refine ⟨by linarith, ?_⟩
    rw [minkowskiInner_explicit]
    have h1 : s_Q ^ 2 ≤ (Q 0) ^ 2 := by nlinarith
    dsimp [sq_sp] at hs_sq
    linarith
  by_cases hs0 : s_Q = 0
  · refine ⟨unit_time_vector, unit_time_vector_mem_forward_light_cone, ?_⟩
    rw [minkowskiInner_explicit]
    simp only [unit_time_vector, ↓reduceIte, Fin.isValue, Fin.reduceEq, mul_one, mul_zero]
    linarith
  · have hs_pos : 0 < s_Q := lt_of_le_of_ne hs_nn (Ne.symm hs0)
    let θ : ℝ := max 0 ((Q 0 + s_Q) / (2 * s_Q))
    have hθ_nn : 0 ≤ θ := le_max_left _ _
    have hθ_lt : θ < 1 := by
      refine max_lt zero_lt_one ?_
      rw [div_lt_one (by positivity)]
      linarith
    let c : ℝ := θ / s_Q
    let w : Fin 4 → ℝ := fun μ => if μ = 0 then 1 else c * Q μ
    have hw_cone : w ∈ forward_light_cone := by
      refine ⟨by simp [w], ?_⟩
      rw [minkowskiInner_explicit]
      simp only [w, ↓reduceIte, Fin.isValue, Fin.reduceEq]
      have h_sp : (c * Q 1) * (c * Q 1) + (c * Q 2) * (c * Q 2) + (c * Q 3) * (c * Q 3) =
          θ ^ 2 := by
        calc (c * Q 1) * (c * Q 1) + (c * Q 2) * (c * Q 2) + (c * Q 3) * (c * Q 3)
            = c ^ 2 * sq_sp := by dsimp [sq_sp]; ring
          _ = (θ / s_Q) ^ 2 * s_Q ^ 2 := by rw [← hs_sq]
          _ = θ ^ 2 := by
              rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hs_pos.ne')]
      have hθ_sq : θ ^ 2 < 1 := by nlinarith
      linarith
    refine ⟨w, hw_cone, ?_⟩
    rw [minkowskiInner_explicit]
    simp only [w, ↓reduceIte, Fin.isValue, Fin.reduceEq, mul_one]
    have h_dot : Q 1 * (c * Q 1) + Q 2 * (c * Q 2) + Q 3 * (c * Q 3) = θ * s_Q := by
      calc Q 1 * (c * Q 1) + Q 2 * (c * Q 2) + Q 3 * (c * Q 3)
          = c * sq_sp := by dsimp [sq_sp]; ring
        _ = (θ / s_Q) * s_Q ^ 2 := by rw [← hs_sq]
        _ = θ * s_Q := by field_simp [hs_pos.ne']
    have h_goal_eq : Q 0 - Q 1 * (c * Q 1) - Q 2 * (c * Q 2) - Q 3 * (c * Q 3) =
        Q 0 - θ * s_Q := by linarith
    rw [h_goal_eq]
    by_cases h_neg : (Q 0 + s_Q) / (2 * s_Q) ≤ 0
    · have hθ0 : θ = 0 := max_eq_left h_neg
      have hQ0_neg : Q 0 ≤ -s_Q := by
        have h_num : Q 0 + s_Q ≤ 0 := by
          by_contra hp
          push Not at hp
          have h_div : 0 < (Q 0 + s_Q) / (2 * s_Q) := div_pos hp (by positivity)
          linarith
        linarith
      rw [hθ0, zero_mul]
      linarith
    · push Not at h_neg
      have hθ_val : θ = (Q 0 + s_Q) / (2 * s_Q) := max_eq_right h_neg.le
      have h_prod : θ * s_Q = (Q 0 + s_Q) / 2 := by
        rw [hθ_val]
        field_simp [hs_pos.ne']
      linarith

lemma exists_div_exp_sub_one_schwartz (n : ℕ) {q : Fin n → Fin 4 → ℝ}
    (hq : ∑ i : Fin n, q i ≠ 0) :
    ∃ r_q : ℝ, 0 < r_q ∧ ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ Metric.ball q r_q →
      ∃ (a : Fin 4 → ℝ) (h : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
        invMinkowskiFourierCLM n g =
          schwartzDiagTranslateN n a (invMinkowskiFourierCLM n h) -
            invMinkowskiFourierCLM n h := by
  let P_tot : Fin 4 → ℝ := ∑ i : Fin n, q i
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : Fin 4, P_tot μ₀ ≠ 0 := by
    by_contra h_all
    push Not at h_all
    exact hq (funext h_all)
  let sgn : ℝ := if μ₀.val = 0 then 1 else -1
  let a : Fin 4 → ℝ := fun μ => if μ.val = μ₀.val then sgn * Real.pi / P_tot μ₀ else 0
  have ha_inner : minkowskiInner P_tot a = Real.pi := by
    rw [minkowskiInner_explicit]
    fin_cases μ₀ <;>
      (dsimp [a, sgn] at hμ₀ ⊢; field_simp [hμ₀]; ring)
  let L_tot : (Fin n → Fin 4 → ℝ) →L[ℝ] ℝ :=
    ((LinearMap.mkContinuous
      { toFun := fun u : Fin 4 → ℝ => minkowskiInner u a
        map_add' := fun u v => by simp [minkowskiInner_explicit]; ring
        map_smul' := fun r u => by simp [minkowskiInner_explicit]; ring }
      (∑ μ : Fin 4, |a μ|)
      (fun u => by
        change ‖minkowskiInner u a‖ ≤ (∑ μ : Fin 4, |a μ|) * ‖u‖
        rw [minkowskiInner_explicit, Real.norm_eq_abs]
        have h0 := norm_le_pi_norm u 0
        have h1 := norm_le_pi_norm u 1
        have h2 := norm_le_pi_norm u 2
        have h3 := norm_le_pi_norm u 3
        rw [Fin.sum_univ_four]
        have ha0 : |u 0 * a 0| ≤ ‖u‖ * |a 0| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
        have ha1 : |u 1 * a 1| ≤ ‖u‖ * |a 1| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        have ha2 : |u 2 * a 2| ≤ ‖u‖ * |a 2| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        have ha3 : |u 3 * a 3| ≤ ‖u‖ * |a 3| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        calc |u 0 * a 0 - u 1 * a 1 - u 2 * a 2 - u 3 * a 3|
            ≤ |u 0 * a 0| + |u 1 * a 1| + |u 2 * a 2| + |u 3 * a 3| := by
              have t1 := abs_sub (u 0 * a 0 - u 1 * a 1 - u 2 * a 2) (u 3 * a 3)
              have t2 := abs_sub (u 0 * a 0 - u 1 * a 1) (u 2 * a 2)
              have t3 := abs_sub (u 0 * a 0) (u 1 * a 1)
              linarith
          _ ≤ |a 0| * ‖u‖ + |a 1| * ‖u‖ + |a 2| * ‖u‖ + |a 3| * ‖u‖ := by linarith
          _ = (|a 0| + |a 1| + |a 2| + |a 3|) * ‖u‖ := by ring))).comp
      (total_momentum_CLM n)
  let ψ : (Fin n → Fin 4 → ℝ) → ℂ :=
    fun p => Complex.exp (-(Complex.I * ((L_tot p : ℝ) : ℂ))) - 1
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (Complex.contDiff_exp.comp
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp L_tot.contDiff)).neg)).sub
      contDiff_const
  have hψ_q : ψ q = -2 := by
    dsimp [ψ, L_tot, total_momentum_CLM, total_momentum_LM]
    change Complex.exp (-(Complex.I * ((minkowskiInner P_tot a : ℝ) : ℂ))) - 1 = -2
    rw [ha_inner]
    have h_neg : -(Complex.I * (Real.pi : ℂ)) = (Real.pi : ℂ) * Complex.I -
        (2 : ℂ) * ↑Real.pi * Complex.I := by ring
    rw [h_neg, Complex.exp_sub, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I]
    norm_num
  have hψ_q_norm : ‖ψ q‖ = 2 := by rw [hψ_q]; norm_num
  have h_cont_at : ContinuousAt ψ q := hψ_smooth.continuous.continuousAt
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp h_cont_at 1 zero_lt_one
  let r_q : ℝ := δ / 2
  have hrq_pos : 0 < r_q := half_pos hδ_pos
  refine ⟨r_q, hrq_pos, fun g hg_supp => ?_⟩
  have hψ_ne : ∀ p ∈ Metric.ball q δ, ψ p ≠ 0 := by
    intro p hp hz
    have h_dist := hδ hp
    rw [hz, dist_zero_left, hψ_q_norm] at h_dist
    linarith
  let h_fn : (Fin n → Fin 4 → ℝ) → ℂ := fun p => (ψ p)⁻¹ * g p
  have hh_supp : HasCompactSupport h_fn := by
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall q r_q) fun p hp => ?_
    rw [Function.mem_support] at hp
    have hgp : p ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ) := by
      refine subset_tsupport _ (Function.mem_support.mpr fun hg0 => hp ?_)
      dsimp [h_fn]
      rw [hg0, mul_zero]
    exact Metric.ball_subset_closedBall (hg_supp hgp)
  have hh_smooth : ContDiff ℝ (⊤ : ℕ∞) h_fn := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp_ts : p ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
    · have hp_δ : p ∈ Metric.ball q δ :=
        Metric.ball_subset_ball (by dsimp [r_q]; linarith) (hg_supp hp_ts)
      exact ((hψ_smooth.contDiffAt).inv (hψ_ne p hp_δ)).mul (g.smooth ⊤).contDiffAt
    · have h_compl : (tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ))ᶜ ∈ 𝓝 p :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hp_ts
      have h_ev : h_fn =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
        filter_upwards [h_compl] with u hu
        have hg0 : g u = 0 := by
          by_contra hne
          exact hu (subset_tsupport _ (Function.mem_support.mpr hne))
        dsimp [h_fn]
        rw [hg0, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq h_ev
  let h : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := hh_supp.toSchwartzMap hh_smooth
  refine ⟨a, h, ?_⟩
  apply minkowskiFourier_injective
  intro p
  have h_sub_f : minkowskiFourier
      (schwartzDiagTranslateN n a (invMinkowskiFourierCLM n h) - invMinkowskiFourierCLM n h) p =
      minkowskiFourier (schwartzDiagTranslateN n a (invMinkowskiFourierCLM n h)) p -
        minkowskiFourier (invMinkowskiFourierCLM n h) p := by
    rw [← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply,
      minkowskiFourierCLM_apply, minkowskiFourierCLM_apply]
  rw [minkowskiFourier_invMinkowskiFourierCLM_all, h_sub_f,
    minkowskiFourier_schwartzDiagTranslateN, minkowskiFourier_invMinkowskiFourierCLM_all]
  change g p = Complex.exp (-(Complex.I * ((L_tot p : ℝ) : ℂ))) * h_fn p - h_fn p
  have h_mul : ψ p * h_fn p = g p := by
    by_cases hp_ts : p ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
    · have hp_δ : p ∈ Metric.ball q δ :=
        Metric.ball_subset_ball (by dsimp [r_q]; linarith) (hg_supp hp_ts)
      dsimp [h_fn]
      rw [← mul_assoc, mul_inv_cancel₀ (hψ_ne p hp_δ), one_mul]
    · have hg0 : g p = 0 := by
        by_contra hne
        exact hp_ts (subset_tsupport _ (Function.mem_support.mpr hne))
      dsimp [h_fn]
      rw [hg0, mul_zero, mul_zero]
  calc g p = ψ p * h_fn p := h_mul.symm
    _ = Complex.exp (-(Complex.I * ((L_tot p : ℝ) : ℂ))) * h_fn p - h_fn p := by
        dsimp [ψ]; ring

private lemma norm_iteratedFDeriv_exp_scaled_linear_le {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) {δ Λ : ℝ} (hΛ : 0 ≤ Λ) (p : V) (hp : L p ≤ -δ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun u : V => Complex.exp ((Λ : ℂ) * ((L u : ℝ) : ℂ))) p‖ ≤
      Real.exp (-δ * Λ) * ((1 + Λ) ^ m *
        ‖iteratedFDeriv ℝ m (fun v : V => Complex.exp ((L v : ℝ) : ℂ)) 0‖) := by
  let E_1 : V → ℂ := fun v => Complex.exp ((L v : ℝ) : ℂ)
  let E_Λ : V → ℂ := fun u => Complex.exp ((Λ : ℂ) * ((L u : ℝ) : ℂ))
  have hE1_sm : ContDiff ℝ (m : ℕ∞) E_1 :=
    (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.comp L.contDiff)).of_le le_top
  have h_shift : (fun v : V => E_Λ (p + v)) =
      fun v : V => (ContinuousLinearMap.mul ℝ ℂ (E_Λ p)) (E_1 (Λ • v)) := by
    ext v
    change Complex.exp ((Λ : ℂ) * ((L (p + v) : ℝ) : ℂ)) =
      E_Λ p * Complex.exp ((L (Λ • v) : ℝ) : ℂ)
    rw [map_add, map_smul, smul_eq_mul]
    have h_add : (Λ : ℂ) * (((L p + L v : ℝ) : ℂ)) =
        (Λ : ℂ) * ((L p : ℝ) : ℂ) + ((Λ * L v : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h_add, Complex.exp_add]
  have h_smul_sm : ContDiff ℝ (m : ℕ∞) (fun v : V => E_1 (Λ • v)) :=
    hE1_sm.comp ((contDiff_const (c := Λ)).smul contDiff_id)
  have h_at0 : iteratedFDeriv ℝ m E_Λ p = iteratedFDeriv ℝ m (fun v => E_Λ (p + v)) 0 := by
    rw [iteratedFDeriv_comp_add_left, add_zero]
  change ‖iteratedFDeriv ℝ m E_Λ p‖ ≤ _
  rw [h_at0, h_shift]
  have h_left := (ContinuousLinearMap.mul ℝ ℂ (E_Λ p)).norm_iteratedFDeriv_comp_left
    (f := fun v : V => E_1 (Λ • v)) (x := (0 : V)) h_smul_sm.contDiffAt le_rfl
  have h_op : ‖ContinuousLinearMap.mul ℝ ℂ (E_Λ p)‖ ≤ ‖E_Λ p‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => (norm_mul (E_Λ p) y).le
  have h_ep : ‖E_Λ p‖ ≤ Real.exp (-δ * Λ) := by
    dsimp [E_Λ]
    have h_re : ((Λ : ℂ) * ((L p : ℝ) : ℂ)).re = Λ * L p := by
      simp [Complex.mul_re]
    rw [Complex.norm_exp, h_re]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h_sc := congrFun (iteratedFDeriv_comp_const_smul Λ hE1_sm) 0
  simp only [smul_zero] at h_sc
  rw [h_sc, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hΛ] at h_left
  have h_pow : Λ ^ m ≤ (1 + Λ) ^ m := pow_le_pow_left₀ hΛ (by linarith) m
  have h_op_ep : ‖ContinuousLinearMap.mul ℝ ℂ (E_Λ p)‖ ≤ Real.exp (-δ * Λ) := h_op.trans h_ep
  calc ‖iteratedFDeriv ℝ m (fun v => (ContinuousLinearMap.mul ℝ ℂ (E_Λ p)) (E_1 (Λ • v))) 0‖
      ≤ ‖ContinuousLinearMap.mul ℝ ℂ (E_Λ p)‖ *
          (Λ ^ m * ‖iteratedFDeriv ℝ m E_1 0‖) := h_left
    _ ≤ Real.exp (-δ * Λ) * ((1 + Λ) ^ m * ‖iteratedFDeriv ℝ m E_1 0‖) :=
        mul_le_mul h_op_ep
          (mul_le_mul_of_nonneg_right h_pow (norm_nonneg _))
          (by positivity) (Real.exp_nonneg _)

private lemma forward_light_cone_add_mem {u v : Fin 4 → ℝ}
    (hu : u ∈ forward_light_cone) (hv : v ∈ forward_light_cone) :
    u + v ∈ forward_light_cone := by
  have h2u := forward_light_cone_smul 2 two_pos u hu
  have h2v := forward_light_cone_smul 2 two_pos v hv
  have h_mid := forward_light_cone_convex h2u h2v
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have h_eq : (1 / 2 : ℝ) • (2 : ℝ) • u + (1 / 2 : ℝ) • (2 : ℝ) • v = u + v := by
    ext μ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rwa [h_eq] at h_mid

private noncomputable def schwartzPolySeminorm (n M : ℕ) :
    Seminorm ℝ (SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :=
  let P := (volume : Measure (Fin n → Fin 4 → ℝ)).integrablePower
  Real.toNNReal (schwartzPolyWeightConst n M) • ((2 : NNReal) • SchwartzMap.seminorm ℝ 0 0 +
    SchwartzMap.seminorm ℝ P 0 +
    SchwartzMap.seminorm ℝ (M + P) 0)

private lemma schwartzPolySeminorm_apply (n M : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzPolySeminorm n M g = schwartzPolyIntegralBound n M g := by
  simp only [schwartzPolySeminorm, schwartzPolyIntegralBound, _root_.smul_apply,
    _root_.add_apply, NNReal.smul_def, Real.coe_toNNReal _ (schwartzPolyWeightConst_nonneg n M),
    NNReal.coe_ofNat, smul_eq_mul]

private lemma hasDerivAt_vladimirov_cone_ray_eq_zero {n M N_H : ℕ}
    {H : (Fin n → Fin 4 → ℂ) → ℂ} (h_ana : AnalyticOn ℂ H (forward_tube_n n))
    {C_H : ℝ} (hCH : 0 ≤ C_H)
    (h_bd : ∀ z ∈ forward_tube_n n,
      ‖H z‖ ≤ C_H * (1 + ‖z‖) ^ M * (tubeGapFactor n z) ^ N_H)
    {R : ℝ} (hR_pos : 0 < R) (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (y₀ d : Fin n → Fin 4 → ℝ) (s : ℝ)
    (hys : zImPoint n 0 (y₀ + s • d) ∈ forward_tube_n n) :
    HasDerivAt
      (fun τ : ℝ => ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x (y₀ + τ • d)) *
        (((invMinkowskiFourierCLM n).comp (SchwartzMap.smulLeftCLM ℂ g))
          (vladimirov_psi_schwartz n R hR_pos (zImPoint n 0 (τ • (-d))))) x)
      0 s := by
  let neg_d_c : Fin n → Fin 4 → ℂ := fun k μ => ((-d k μ : ℝ) : ℂ)
  let z_ray : ℝ → Fin n → Fin 4 → ℂ := fun τ => zImPoint n 0 (τ • (-d))
  let ψ_ray : ℝ → SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
    fun τ => vladimirov_psi_schwartz n R hR_pos (z_ray τ)
  let Φ_mul : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
    (invMinkowskiFourierCLM n).comp (SchwartzMap.smulLeftCLM ℂ g)
  let F_ode : ℝ → ℂ := fun τ =>
    ∫ x : Fin n → Fin 4 → ℝ, H (zImPoint n x (y₀ + τ • d)) * (Φ_mul (ψ_ray τ)) x
  change HasDerivAt F_ode 0 s
  obtain ⟨ρ, B_gap, hρ_pos, hB_nn, h_ball⟩ := exists_uniform_ball_in_forward_tube hys
  let d_c : Fin n → Fin 4 → ℂ := fun i μ => (d i μ : ℂ)
  let R₀ : ℝ := ρ / 4
  have hR₀_pos : 0 < R₀ := by dsimp [R₀]; positivity
  let δ_s : ℝ := min 1 (R₀ / (‖d‖ + 1))
  have hδs_pos : 0 < δ_s := lt_min zero_lt_one (div_pos hR₀_pos (by positivity))
  let ys : Fin n → Fin 4 → ℝ := y₀ + s • d
  let S_ys : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    zImPointIntegralCLM h_ana hCH h_bd hys
  let T_ys : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ := S_ys.comp Φ_mul
  have h1_deriv := hasDerivAt_zImPoint_schwartz h_ana hCH h_bd y₀ d
    (Φ_mul (ψ_ray s)) hys
  have hz_ray_deriv : HasDerivAt z_ray (Complex.I • neg_d_c) s := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro μ
    have hr : HasDerivAt (fun τ : ℝ => τ * (-d i μ)) (-d i μ) s := by
      simpa using (hasDerivAt_id s).mul_const (-d i μ)
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul Complex.I
    simpa [z_ray, zImPoint, neg_d_c] using hc
  have h2_fderiv := (vladimirov_hasFDerivAt_schwartz_family n R hR_pos (z_ray s)
    T_ys).restrictScalars ℝ
  have h2_deriv : HasDerivAt (fun τ : ℝ => T_ys (ψ_ray τ))
      (T_ys (vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c))) s :=
    h2_fderiv.comp_hasDerivAt s hz_ray_deriv
  have h_cancel : Complex.I * S_ys (schwartzDirDerivCLM n (-d) (Φ_mul (ψ_ray s))) +
      T_ys (vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c)) = 0 := by
    have h_arg_eq : Complex.I • schwartzDirDerivCLM n (-d) (Φ_mul (ψ_ray s)) +
        Φ_mul (vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c)) =
        0 := by
      apply minkowskiFourier_injective
      intro p
      have h0_f : minkowskiFourier (0 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) p = 0 := by
        rw [← minkowskiFourierCLM_apply, map_zero, _root_.zero_apply]
      rw [h0_f, ← minkowskiFourierCLM_apply, map_add, map_smul,
        _root_.add_apply, _root_.smul_apply,
        minkowskiFourierCLM_apply, minkowskiFourierCLM_apply,
        minkowskiFourier_schwartzDirDerivCLM]
      dsimp [Φ_mul]
      rw [minkowskiFourier_invMinkowskiFourierCLM_all,
        minkowskiFourier_invMinkowskiFourierCLM_all,
        SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
        SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
      simp only [smul_eq_mul]
      change Complex.I * ((Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (-d k) : ℝ) : ℂ)) *
          (g p * vladimirov_psi n R hR_pos (z_ray s) p)) +
        g p * ((vladimirov_phase_CLM n (Complex.I • neg_d_c) p) *
          vladimirov_psi n R hR_pos (z_ray s) p) = 0
      have h_neg_sum : (∑ k : Fin n, minkowskiInner (p k) (-d k)) =
          -(∑ k : Fin n, minkowskiInner (p k) (d k)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [minkowskiInner_explicit]
        ring
      have h_ph : vladimirov_phase_CLM n (Complex.I • neg_d_c) p =
          -((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ) : ℂ) := by
        change -Complex.I * (∑ k : Fin n,
            minkowskiInnerC (fun μ => (p k μ : ℂ)) ((Complex.I • neg_d_c) k)) =
          -((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ) : ℂ)
        have h_in : ∀ k : Fin n,
            minkowskiInnerC (fun μ => (p k μ : ℂ)) ((Complex.I • neg_d_c) k) =
            -(Complex.I * ((minkowskiInner (p k) (d k) : ℝ) : ℂ)) := by
          intro k
          dsimp [minkowskiInnerC, neg_d_c]
          rw [minkowskiInner_explicit]
          push_cast
          ring
        simp_rw [h_in]
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
        have hI : -Complex.I * -(Complex.I *
            ∑ x : Fin n, ((minkowskiInner (p x) (d x) : ℝ) : ℂ)) =
            (Complex.I * Complex.I) *
              ∑ x : Fin n, ((minkowskiInner (p x) (d x) : ℝ) : ℂ) := by ring
        rw [hI, Complex.I_mul_I]
        push_cast
        ring
      rw [h_neg_sum, h_ph]
      have hI2 : Complex.I * (Complex.I *
          ((-((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ)) : ℝ) : ℂ)) =
          ((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ) : ℂ) := by
        push_cast
        calc Complex.I * (Complex.I * -∑ k : Fin n, (minkowskiInner (p k) (d k) : ℂ))
            = -(Complex.I * Complex.I) * ∑ k : Fin n, (minkowskiInner (p k) (d k) : ℂ) := by
              ring
          _ = ∑ k : Fin n, (minkowskiInner (p k) (d k) : ℂ) := by
              rw [Complex.I_mul_I]; ring
      have h_reassoc : Complex.I * ((Complex.I *
          ((-((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ)) : ℝ) : ℂ)) *
          (g p * vladimirov_psi n R hR_pos (z_ray s) p)) =
          (Complex.I * (Complex.I *
            ((-((∑ k : Fin n, minkowskiInner (p k) (d k) : ℝ)) : ℝ) : ℂ))) *
            (g p * vladimirov_psi n R hR_pos (z_ray s) p) := by ring
      rw [h_reassoc, hI2]
      ring
    have hS := congrArg S_ys h_arg_eq
    rw [map_add, map_smul, map_zero, smul_eq_mul] at hS
    exact hS
  have h_sum_deriv : HasDerivAt
      (fun τ : ℝ => (∫ x, H (zImPoint n x (y₀ + τ • d)) * (Φ_mul (ψ_ray s)) x) +
        (T_ys (ψ_ray τ) - T_ys (ψ_ray s))) 0 s := by
    have h_add := h1_deriv.add (h2_deriv.sub_const (T_ys (ψ_ray s)))
    change HasDerivAt _
      (Complex.I * S_ys (schwartzDirDerivCLM n (-d) (Φ_mul (ψ_ray s))) +
        T_ys (vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c))) s
      at h_add
    rwa [h_cancel] at h_add
  rw [hasDerivAt_iff_isLittleO] at h_sum_deriv ⊢
  simp only [smul_zero, sub_zero] at h_sum_deriv ⊢
  let cross : ℝ → ℂ := fun τ =>
    ∫ x : Fin n → Fin 4 → ℝ,
      (H (zImPoint n x (y₀ + τ • d)) - H (zImPoint n x ys)) *
        (Φ_mul (ψ_ray τ - ψ_ray s)) x
  have h_decomp : (fun τ : ℝ => F_ode τ - F_ode s) =ᶠ[𝓝 s]
      fun τ : ℝ =>
        ((∫ x, H (zImPoint n x (y₀ + τ • d)) * (Φ_mul (ψ_ray s)) x) +
          (T_ys (ψ_ray τ) - T_ys (ψ_ray s)) -
          ((∫ x, H (zImPoint n x ys) * (Φ_mul (ψ_ray s)) x) +
            (T_ys (ψ_ray s) - T_ys (ψ_ray s)))) + cross τ := by
    have h_nhds : Set.Ioo (s - δ_s) (s + δ_s) ∈ 𝓝 s :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [h_nhds] with τ hτ
    have hτ_lt : |τ - s| < δ_s := abs_sub_lt_iff.mpr ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hτ_mem : zImPoint n 0 (y₀ + τ • d) ∈ forward_tube_n n := by
      refine (h_ball 0 ?_).1
      rw [Metric.mem_ball, dist_eq_norm]
      have h_sub_z : ‖zImPoint n 0 (y₀ + τ • d) - zImPoint n 0 ys‖ ≤ |τ - s| * ‖d‖ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
        refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
        simp only [Pi.sub_apply]
        have h_eq : zImPoint n 0 (y₀ + τ • d) i μ - zImPoint n 0 ys i μ =
            Complex.I * (((τ - s) * d i μ : ℝ) : ℂ) := by
          dsimp [zImPoint, ys]
          push_cast
          ring
        rw [h_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (d i μ)]
        exact mul_le_mul_of_nonneg_left
          ((norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)) (abs_nonneg _)
      have hδ_le : δ_s ≤ R₀ / (‖d‖ + 1) := min_le_right _ _
      have h1 : |τ - s| * ‖d‖ < R₀ := by
        calc |τ - s| * ‖d‖ ≤ |τ - s| * (‖d‖ + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ < (R₀ / (‖d‖ + 1)) * (‖d‖ + 1) :=
              mul_lt_mul_of_pos_right (hτ_lt.trans_le hδ_le) (by positivity)
          _ = R₀ := div_mul_cancel₀ R₀ (by positivity)
      dsimp [R₀] at h1
      linarith
    let S_τ := zImPointIntegralCLM h_ana hCH h_bd hτ_mem
    have hFτ : F_ode τ = S_τ (Φ_mul (ψ_ray τ)) := rfl
    have hFs : F_ode s = S_ys (Φ_mul (ψ_ray s)) := rfl
    have h1_τ : (∫ x, H (zImPoint n x (y₀ + τ • d)) * (Φ_mul (ψ_ray s)) x) =
        S_τ (Φ_mul (ψ_ray s)) := rfl
    have h1_s : (∫ x, H (zImPoint n x ys) * (Φ_mul (ψ_ray s)) x) =
        S_ys (Φ_mul (ψ_ray s)) := rfl
    have h_cross_eq : cross τ =
        S_τ (Φ_mul (ψ_ray τ - ψ_ray s)) - S_ys (Φ_mul (ψ_ray τ - ψ_ray s)) := by
      dsimp [cross, S_τ, S_ys]
      have hi1 := integrable_zImPoint_mul_schwartz h_ana hCH h_bd hτ_mem
        (Φ_mul (ψ_ray τ - ψ_ray s))
      have hi2 := integrable_zImPoint_mul_schwartz h_ana hCH h_bd hys
        (Φ_mul (ψ_ray τ - ψ_ray s))
      have h_sub_pt : (fun x =>
          (H (zImPoint n x (y₀ + τ • d)) - H (zImPoint n x ys)) *
            (Φ_mul (ψ_ray τ - ψ_ray s)) x) =
          fun x => H (zImPoint n x (y₀ + τ • d)) * (Φ_mul (ψ_ray τ - ψ_ray s)) x -
            H (zImPoint n x ys) * (Φ_mul (ψ_ray τ - ψ_ray s)) x := by
        ext x
        exact sub_mul _ _ _
      rw [h_sub_pt, MeasureTheory.integral_sub hi1 hi2]
    rw [hFτ, hFs, h1_τ, h1_s, h_cross_eq]
    dsimp [T_ys]
    rw [map_sub, map_sub, map_sub]
    ring
  suffices h_cross_o : cross =o[𝓝 s] fun τ : ℝ => τ - s by
    exact (h_sum_deriv.add h_cross_o).congr' h_decomp.symm EventuallyEq.rfl
  let B_H : ℝ := C_H * B_gap ^ N_H
  have hBH_nn : 0 ≤ B_H := mul_nonneg hCH (pow_nonneg hB_nn N_H)
  let K_der : ℝ := ((‖d_c‖ + 1) / R₀) * B_H * (1 + ‖ys‖ + 2 * R₀) ^ M
  let p_poly : Seminorm ℝ (SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :=
    (schwartzPolySeminorm n M).comp (Φ_mul.restrictScalars ℝ).toLinearMap
  have hp_poly_fn : (p_poly : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ → ℝ) =
      fun u => schwartzPolyIntegralBound n M (Φ_mul u) :=
    funext fun u => schwartzPolySeminorm_apply n M (Φ_mul u)
  have hp_cont : Continuous p_poly := by
    rw [hp_poly_fn]
    exact (continuous_schwartzPolyIntegralBound n M).comp Φ_mul.continuous
  obtain ⟨s_sem, C_sem, hC_sem_ne, hp_le⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (Fin n → Fin 4 → ℝ) ℂ) p_poly hp_cont
  obtain ⟨C_q, hCq_nn, hCq_ev⟩ :=
    schwartz_finset_seminorm_quadratic n R hR_pos (z_ray s) s_sem
  let C_d : ℝ := (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
    (vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c))
  have hz_ray_cont : Continuous z_ray :=
    continuous_pi fun i => continuous_pi fun μ =>
      continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)))
  have h_ev_q := hz_ray_cont.tendsto s |>.eventually hCq_ev
  have h_nhds : Set.Ioo (s - δ_s) (s + δ_s) ∈ 𝓝 s :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have h_tend_coef : Tendsto
      (fun τ : ℝ => K_der * (C_sem : ℝ) * (C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s|)
      (𝓝 s) (𝓝 0) := by
    have h_tend_abs : Tendsto (fun τ : ℝ => |τ - s|) (𝓝 s) (𝓝 0) := by
      have h_cont : Continuous (fun τ : ℝ => |τ - s|) :=
        continuous_abs.comp (continuous_id.sub continuous_const)
      simpa [sub_self] using h_cont.tendsto s
    simpa using h_tend_abs.const_mul (K_der * (C_sem : ℝ) * (C_q * ‖neg_d_c‖ ^ 2 + C_d))
  refine Asymptotics.isLittleO_iff.mpr fun c_eps hc_eps => ?_
  filter_upwards [h_nhds, h_ev_q, h_tend_coef.eventually (Iio_mem_nhds hc_eps)]
    with τ hτ hq_τ h_coef_lt
  have hτ_lt : |τ - s| < δ_s := abs_sub_lt_iff.mpr ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hτ_le1 : |τ - s| ≤ 1 := (hτ_lt.trans_le (min_le_left _ _)).le
  have h_zray_diff : z_ray τ - z_ray s = ((τ - s : ℝ) : ℂ) • (Complex.I • neg_d_c) := by
    ext i μ
    dsimp [z_ray, zImPoint, neg_d_c]
    push_cast
    ring
  have h_zray_norm : ‖z_ray τ - z_ray s‖ ≤ |τ - s| * ‖neg_d_c‖ := by
    rw [h_zray_diff, norm_smul, norm_smul, Complex.norm_real, Complex.norm_I, one_mul,
      Real.norm_eq_abs]
  have h_psi_lin : (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
      (ψ_ray τ - ψ_ray s) ≤ (C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s| := by
    let rem := ψ_ray τ - ψ_ray s -
      vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (z_ray τ - z_ray s)
    have h_split : ψ_ray τ - ψ_ray s = rem +
        (τ - s) •
          vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c) := by
      dsimp [rem]
      rw [h_zray_diff, vladimirov_deriv_psi_smul]
      exact (sub_add_cancel _ _).symm
    rw [h_split]
    refine (map_add_le_add _ _ _).trans ?_
    have h_rem_le : (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)) rem ≤
        C_q * ‖neg_d_c‖ ^ 2 * |τ - s| := by
      have h_sq_le : |τ - s| ^ 2 ≤ |τ - s| := by nlinarith [abs_nonneg (τ - s), hτ_le1]
      calc (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)) rem
          ≤ C_q * ‖z_ray τ - z_ray s‖ ^ 2 := hq_τ
        _ ≤ C_q * (|τ - s| * ‖neg_d_c‖) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (norm_nonneg _) h_zray_norm 2) hCq_nn
        _ = C_q * ‖neg_d_c‖ ^ 2 * |τ - s| ^ 2 := by ring
        _ ≤ C_q * ‖neg_d_c‖ ^ 2 * |τ - s| :=
            mul_le_mul_of_nonneg_left h_sq_le (by positivity)
    have h_der_le : (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
        ((τ - s) •
          vladimirov_deriv_psi_schwartz n R hR_pos (z_ray s) (Complex.I • neg_d_c)) =
        |τ - s| * C_d := by
      rw [map_smul_eq_mul, Real.norm_eq_abs]
    linarith
  have h_mvt_H : ∀ x : Fin n → Fin 4 → ℝ,
      ‖H (zImPoint n x (y₀ + τ • d)) - H (zImPoint n x ys)‖ ≤
        K_der * |τ - s| * (1 + ‖x‖) ^ M := by
    intro x
    let a_l : ℝ := min s τ
    let b_r : ℝ := max s τ
    have h_diff_seg : ∀ r ∈ Set.Icc a_l b_r,
        HasDerivWithinAt (fun u : ℝ => H (zImPoint n x (y₀ + u • d)))
          (Complex.I * fderiv ℂ H (zImPoint n x (y₀ + r • d)) d_c)
          (Set.Icc a_l b_r) r ∧
        ‖Complex.I * fderiv ℂ H (zImPoint n x (y₀ + r • d)) d_c‖ ≤
          K_der * (1 + ‖x‖) ^ M := by
      intro r hr
      have hr_lt : |r - s| < δ_s := by
        have h1 : a_l ≤ r := hr.1
        have h2 : r ≤ b_r := hr.2
        rcases le_total s τ with hst | hts
        · simp [a_l, b_r, hst] at h1 h2
          rw [abs_of_nonneg (by linarith)]
          rw [abs_of_nonneg (by linarith)] at hτ_lt
          linarith
        · simp [a_l, b_r, hts] at h1 h2
          rw [abs_of_nonpos (by linarith)]
          rw [abs_of_nonpos (by linarith)] at hτ_lt
          linarith
      have hz_lt : ‖zImPoint n x (y₀ + r • d) - zImPoint n x ys‖ < R₀ := by
        have h_sub_z : ‖zImPoint n x (y₀ + r • d) - zImPoint n x ys‖ ≤ |r - s| * ‖d‖ := by
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
          refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun μ => ?_
          simp only [Pi.sub_apply]
          have h_eq : zImPoint n x (y₀ + r • d) i μ - zImPoint n x ys i μ =
              Complex.I * (((r - s) * d i μ : ℝ) : ℂ) := by
            dsimp [zImPoint, ys]
            push_cast
            ring
          rw [h_eq, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, abs_mul, ← Real.norm_eq_abs (d i μ)]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (d i) μ).trans (norm_le_pi_norm d i)) (abs_nonneg _)
        have hδ_le : δ_s ≤ R₀ / (‖d‖ + 1) := min_le_right _ _
        calc ‖zImPoint n x (y₀ + r • d) - zImPoint n x ys‖
            ≤ |r - s| * (‖d‖ + 1) :=
              h_sub_z.trans (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _))
          _ < (R₀ / (‖d‖ + 1)) * (‖d‖ + 1) :=
              mul_lt_mul_of_pos_right (hr_lt.trans_le hδ_le) (by positivity)
          _ = R₀ := div_mul_cancel₀ R₀ (by positivity)
      have h_sub2 : Metric.ball (zImPoint n x (y₀ + r • d)) (2 * R₀) ⊆ forward_tube_n n := by
        intro u hu
        rw [Metric.mem_ball, dist_eq_norm] at hu
        refine (h_ball x ?_).1
        rw [Metric.mem_ball, dist_eq_norm]
        have h_tri : ‖u - zImPoint n x ys‖ ≤
            ‖u - zImPoint n x (y₀ + r • d)‖ +
              ‖zImPoint n x (y₀ + r • d) - zImPoint n x ys‖ := by
          simpa using norm_add_le (u - zImPoint n x (y₀ + r • d))
            (zImPoint n x (y₀ + r • d) - zImPoint n x ys)
        dsimp [R₀] at hu hz_lt
        linarith
      have h_bd2 : ∀ u ∈ Metric.ball (zImPoint n x (y₀ + r • d)) (2 * R₀),
          ‖H u‖ ≤ B_H * (1 + ‖u‖) ^ M := by
        intro u hu
        rw [Metric.mem_ball, dist_eq_norm] at hu
        have hu_ρ : u ∈ Metric.ball (zImPoint n x ys) ρ := by
          rw [Metric.mem_ball, dist_eq_norm]
          have h_tri : ‖u - zImPoint n x ys‖ ≤
              ‖u - zImPoint n x (y₀ + r • d)‖ +
                ‖zImPoint n x (y₀ + r • d) - zImPoint n x ys‖ := by
            simpa using norm_add_le (u - zImPoint n x (y₀ + r • d))
              (zImPoint n x (y₀ + r • d) - zImPoint n x ys)
          dsimp [R₀] at hu hz_lt
          linarith
        obtain ⟨hu_mem, hu_gap⟩ := h_ball x hu_ρ
        calc ‖H u‖ ≤ C_H * (1 + ‖u‖) ^ M * (tubeGapFactor n u) ^ N_H := h_bd u hu_mem
          _ ≤ C_H * (1 + ‖u‖) ^ M * B_gap ^ N_H := by
              gcongr
              exact tubeGapFactor_nonneg hu_mem
          _ = B_H * (1 + ‖u‖) ^ M := by dsimp [B_H]; ring
      have hz_mem : zImPoint n x (y₀ + r • d) ∈ forward_tube_n n :=
        h_sub2 (Metric.mem_ball_self (by positivity))
      have hdf : HasFDerivAt H (fderiv ℂ H (zImPoint n x (y₀ + r • d)))
          (zImPoint n x (y₀ + r • d)) :=
        (h_ana.differentiableOn.differentiableAt
          ((forward_tube_n_isOpen n).mem_nhds hz_mem)).hasFDerivAt
      have hd_line : HasDerivAt (fun u : ℝ => zImPoint n x (y₀ + u • d))
          (Complex.I • d_c) r := by
        rw [hasDerivAt_pi]
        intro i
        rw [hasDerivAt_pi]
        intro μ
        have h_r : HasDerivAt (fun u : ℝ => y₀ i μ + u * d i μ) (d i μ) r := by
          simpa using ((hasDerivAt_id r).mul_const (d i μ)).const_add (y₀ i μ)
        have h_c := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r h_r).const_mul
          Complex.I).const_add (x i μ : ℂ)
        simpa [zImPoint, d_c] using h_c
      have hd_H : HasDerivAt (fun u : ℝ => H (zImPoint n x (y₀ + u • d)))
          (Complex.I * fderiv ℂ H (zImPoint n x (y₀ + r • d)) d_c) r := by
        have hc := (hdf.restrictScalars ℝ).comp_hasDerivAt r hd_line
        rwa [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul] at hc
      refine ⟨hd_H.hasDerivWithinAt, ?_⟩
      rw [norm_mul, Complex.norm_I, one_mul]
      have h_est := norm_fderiv_tube_dir_le_of_ball_bound h_ana hR₀_pos hBH_nn
        h_sub2 h_bd2 d_c
      have hz_norm : ‖zImPoint n x (y₀ + r • d)‖ ≤ ‖x‖ + ‖ys‖ + R₀ := by
        have h1 : ‖zImPoint n x (y₀ + r • d)‖ ≤
            ‖zImPoint n x (y₀ + r • d) - zImPoint n x ys‖ + ‖zImPoint n x ys‖ := by
          simpa using norm_add_le (zImPoint n x (y₀ + r • d) - zImPoint n x ys)
            (zImPoint n x ys)
        linarith [norm_zImPoint_le n x ys]
      have h_prod : 1 + ‖zImPoint n x (y₀ + r • d)‖ + R₀ ≤
          (1 + ‖ys‖ + 2 * R₀) * (1 + ‖x‖) := by
        have hx0 : 0 ≤ (‖ys‖ + 2 * R₀) * ‖x‖ := by positivity
        linarith
      have h_pow : (1 + ‖zImPoint n x (y₀ + r • d)‖ + R₀) ^ M ≤
          (1 + ‖ys‖ + 2 * R₀) ^ M * (1 + ‖x‖) ^ M :=
        (pow_le_pow_left₀ (by positivity) h_prod M).trans_eq (mul_pow _ _ M)
      calc ‖fderiv ℂ H (zImPoint n x (y₀ + r • d)) d_c‖
          ≤ ((‖d_c‖ + 1) / R₀) * B_H *
              (1 + ‖zImPoint n x (y₀ + r • d)‖ + R₀) ^ M := h_est
        _ ≤ ((‖d_c‖ + 1) / R₀) * B_H *
              ((1 + ‖ys‖ + 2 * R₀) ^ M * (1 + ‖x‖) ^ M) :=
            mul_le_mul_of_nonneg_left h_pow (by positivity)
        _ = K_der * (1 + ‖x‖) ^ M := by dsimp [K_der]; ring
    have h_mvt := (convex_Icc a_l b_r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (h_diff_seg r hr).1)
      (fun r hr => (h_diff_seg r hr).2)
      ⟨min_le_left s τ, le_max_left s τ⟩
      ⟨min_le_right s τ, le_max_right s τ⟩
    have hb_sub : ‖τ - s‖ = |τ - s| := Real.norm_eq_abs _
    rw [hb_sub] at h_mvt
    calc ‖H (zImPoint n x (y₀ + τ • d)) - H (zImPoint n x ys)‖
        ≤ K_der * (1 + ‖x‖) ^ M * |τ - s| := h_mvt
      _ = K_der * |τ - s| * (1 + ‖x‖) ^ M := by ring
  have h_poly_le : schwartzPolyIntegralBound n M (Φ_mul (ψ_ray τ - ψ_ray s)) ≤
      (C_sem : ℝ) * (C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s| := by
    have h1 : schwartzPolyIntegralBound n M (Φ_mul (ψ_ray τ - ψ_ray s)) =
        p_poly (ψ_ray τ - ψ_ray s) :=
      (schwartzPolySeminorm_apply n M (Φ_mul (ψ_ray τ - ψ_ray s))).symm
    rw [h1]
    calc p_poly (ψ_ray τ - ψ_ray s)
        ≤ (C_sem • (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)))
            (ψ_ray τ - ψ_ray s) := hp_le (ψ_ray τ - ψ_ray s)
      _ = (C_sem : ℝ) *
            (s_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
              (ψ_ray τ - ψ_ray s) := rfl
      _ ≤ (C_sem : ℝ) * ((C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s|) :=
          mul_le_mul_of_nonneg_left h_psi_lin C_sem.coe_nonneg
      _ = (C_sem : ℝ) * (C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s| := by ring
  have hK_nn : 0 ≤ K_der := by dsimp [K_der]; positivity
  calc ‖cross τ‖
      ≤ ∫ x : Fin n → Fin 4 → ℝ,
          ‖(H (zImPoint n x (y₀ + τ • d)) - H (zImPoint n x ys)) *
            (Φ_mul (ψ_ray τ - ψ_ray s)) x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Fin n → Fin 4 → ℝ,
          (K_der * |τ - s|) * ((1 + ‖x‖) ^ M * ‖(Φ_mul (ψ_ray τ - ψ_ray s)) x‖) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          ((integrable_one_add_norm_pow_mul_schwartz n M
            (Φ_mul (ψ_ray τ - ψ_ray s))).const_mul (K_der * |τ - s|))
          (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        rw [norm_mul]
        calc ‖H (zImPoint n x (y₀ + τ • d)) - H (zImPoint n x ys)‖ *
              ‖(Φ_mul (ψ_ray τ - ψ_ray s)) x‖
            ≤ (K_der * |τ - s| * (1 + ‖x‖) ^ M) * ‖(Φ_mul (ψ_ray τ - ψ_ray s)) x‖ :=
              mul_le_mul_of_nonneg_right (h_mvt_H x) (norm_nonneg _)
          _ = (K_der * |τ - s|) * ((1 + ‖x‖) ^ M * ‖(Φ_mul (ψ_ray τ - ψ_ray s)) x‖) := by
              ring
    _ = (K_der * |τ - s|) *
          ∫ x : Fin n → Fin 4 → ℝ, (1 + ‖x‖) ^ M * ‖(Φ_mul (ψ_ray τ - ψ_ray s)) x‖ :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ (K_der * |τ - s|) * schwartzPolyIntegralBound n M (Φ_mul (ψ_ray τ - ψ_ray s)) :=
        mul_le_mul_of_nonneg_left
          (integral_one_add_norm_pow_mul_schwartz_le n M (Φ_mul (ψ_ray τ - ψ_ray s)))
          (mul_nonneg hK_nn (abs_nonneg _))
    _ ≤ (K_der * |τ - s|) * ((C_sem : ℝ) * (C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s|) :=
        mul_le_mul_of_nonneg_left h_poly_le (mul_nonneg hK_nn (abs_nonneg _))
    _ = (K_der * (C_sem : ℝ) * (C_q * ‖neg_d_c‖ ^ 2 + C_d) * |τ - s|) * ‖τ - s‖ := by
        rw [Real.norm_eq_abs]; ring
    _ ≤ c_eps * ‖τ - s‖ :=
        mul_le_mul_of_nonneg_right h_coef_lt.le (norm_nonneg _)

private lemma vladimirovFromTubeVal_invFourier_eq_zero_of_ball_cone {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (n : ℕ) (α : Fin n → κ) {q : Fin n → Fin 4 → ℝ} (hq_sum : ∑ i : Fin n, q i = 0)
    (m : Fin n) (hq_cone : partial_sum_p n q m ∉ closure forward_light_cone) :
    ∃ r_q : ℝ, 0 < r_q ∧ ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ Metric.ball q r_q →
      vladimirovFromTubeVal h_ana h_growth n α (invMinkowskiFourierCLM n g) = 0 := by
  have hm_lt : m.val + 1 < n := by
    by_contra h_ge
    push Not at h_ge
    have h_all : Finset.univ.filter (fun i : Fin n => i ≤ m) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have hi_lt := i.isLt
      exact Fin.le_iff_val_le_val.mpr (by omega)
    have h_eq0 : partial_sum_p n q m = 0 := by
      dsimp [partial_sum_p]
      rw [h_all, hq_sum]
    apply hq_cone
    rw [h_eq0, closure_forward_light_cone_eq]
    exact ⟨le_rfl, by simp [minkowskiInner_explicit]⟩
  obtain ⟨w, hw_cone, hw_neg⟩ := exists_cone_sep_of_notMem_closure hq_cone
  let L_w : (Fin 4 → ℝ) →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun u : Fin 4 → ℝ => minkowskiInner u w
        map_add' := fun u v => by simp [minkowskiInner_explicit]; ring
        map_smul' := fun r u => by simp [minkowskiInner_explicit]; ring }
      (∑ μ : Fin 4, |w μ|)
      (fun u => by
        change ‖minkowskiInner u w‖ ≤ (∑ μ : Fin 4, |w μ|) * ‖u‖
        rw [minkowskiInner_explicit, Real.norm_eq_abs]
        have h0 := norm_le_pi_norm u 0
        have h1 := norm_le_pi_norm u 1
        have h2 := norm_le_pi_norm u 2
        have h3 := norm_le_pi_norm u 3
        rw [Fin.sum_univ_four]
        have hw0 : |u 0 * w 0| ≤ ‖u‖ * |w 0| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
        have hw1 : |u 1 * w 1| ≤ ‖u‖ * |w 1| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        have hw2 : |u 2 * w 2| ≤ ‖u‖ * |w 2| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        have hw3 : |u 3 * w 3| ≤ ‖u‖ * |w 3| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        calc |u 0 * w 0 - u 1 * w 1 - u 2 * w 2 - u 3 * w 3|
            ≤ |u 0 * w 0| + |u 1 * w 1| + |u 2 * w 2| + |u 3 * w 3| := by
              have t1' := abs_sub (u 0 * w 0 - u 1 * w 1 - u 2 * w 2) (u 3 * w 3)
              have t2 := abs_sub (u 0 * w 0 - u 1 * w 1) (u 2 * w 2)
              have t3 := abs_sub (u 0 * w 0) (u 1 * w 1)
              linarith
          _ ≤ |w 0| * ‖u‖ + |w 1| * ‖u‖ + |w 2| * ‖u‖ + |w 3| * ‖u‖ := by linarith
          _ = (|w 0| + |w 1| + |w 2| + |w 3|) * ‖u‖ := by ring)
  let L_clm : (Fin n → Fin 4 → ℝ) →L[ℝ] ℝ := L_w.comp (partial_sum_p_CLM n m)
  have hLq : L_clm q = minkowskiInner (partial_sum_p n q m) w := rfl
  let δ : ℝ := -(L_clm q) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨r_q, hrq_pos, hrq⟩ := Metric.continuousAt_iff.mp L_clm.continuous.continuousAt δ hδ_pos
  refine ⟨r_q, hrq_pos, fun g hg_supp => ?_⟩
  have hL_ball : ∀ p ∈ Metric.ball q r_q, L_clm p ≤ -δ := by
    intro p hp
    have hd := hrq hp
    rw [Real.dist_eq] at hd
    have h1 := (abs_lt.mp hd).2
    dsimp [δ] at h1 ⊢
    linarith
  obtain ⟨C_H, M, N_H, hCH, h_bd⟩ := h_growth n α
  have h_lim := tendsto_vladimirovFromTubeVal_unit h_ana h_growth n α (invMinkowskiFourierCLM n g)
  suffices h_zero_t : ∀ t : ℝ, 0 < t →
      (∫ x : Fin n → Fin 4 → ℝ,
        H n α (tubeBoundaryLine n x unit_time_vector t) * (invMinkowskiFourierCLM n g) x) = 0 by
    have h_ev : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        H n α (tubeBoundaryLine n x unit_time_vector t) *
          (invMinkowskiFourierCLM n g) x) =ᶠ[𝓝[>] 0] fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact h_zero_t t ht
    haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
    exact tendsto_nhds_unique h_lim (tendsto_const_nhds.congr' h_ev.symm)
  intro t ht
  let R : ℝ := ‖q‖ + r_q + 1
  have hR_pos : 0 < R := by dsimp [R]; positivity
  have hg_in_R : ∀ p ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ), ‖p‖ ≤ R := by
    intro p hp
    have hb := hg_supp hp
    rw [Metric.mem_ball, dist_eq_norm] at hb
    have h1 : ‖p‖ ≤ ‖p - q‖ + ‖q‖ := by simpa using norm_add_le (p - q) q
    dsimp [R]
    linarith
  let y₀ : Fin n → Fin 4 → ℝ := t • tubeImDir n unit_time_vector
  let d : Fin n → Fin 4 → ℝ := fun k => if k ≤ m then -w else 0
  have hy_mem : ∀ τ : ℝ, 0 ≤ τ → zImPoint n 0 (y₀ + τ • d) ∈ forward_tube_n n := by
    intro τ hτ i hi
    change diff_im n (zImPoint n 0 (y₀ + τ • d)) i hi ∈ forward_light_cone
    rw [diff_im_zImPoint]
    let i1 : Fin n := ⟨i.val + 1, hi⟩
    have h_y0 : y₀ i1 - y₀ i = t • unit_time_vector := by
      ext μ
      dsimp [y₀, tubeImDir, i1]
      push_cast
      ring
    have h_diff : (y₀ + τ • d) i1 - (y₀ + τ • d) i =
        t • unit_time_vector + τ • (d i1 - d i) := by
      ext μ
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hy0_μ := congrFun h_y0 μ
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hy0_μ
      linarith
    change (y₀ + τ • d) i1 - (y₀ + τ • d) i ∈ forward_light_cone
    rw [h_diff]
    have ht_ut : t • unit_time_vector ∈ forward_light_cone :=
      forward_light_cone_smul t ht unit_time_vector unit_time_vector_mem_forward_light_cone
    by_cases him : i ≤ m
    · by_cases hi1m : i1 ≤ m
      · have hd0 : d i1 - d i = 0 := by simp [d, him, hi1m]
        rw [hd0, smul_zero, add_zero]
        exact ht_ut
      · have hd_w : d i1 - d i = w := by simp [d, him, hi1m]
        rw [hd_w]
        rcases eq_or_lt_of_le hτ with rfl | hτ_pos
        · simp [ht_ut]
        · exact forward_light_cone_add_mem ht_ut (forward_light_cone_smul τ hτ_pos w hw_cone)
    · have hi1m : ¬ i1 ≤ m := by
        intro hc
        exact him (le_trans (Fin.le_iff_val_le_val.mpr (Nat.le_succ _)) hc)
      have hd0 : d i1 - d i = 0 := by simp [d, him, hi1m]
      rw [hd0, smul_zero, add_zero]
      exact ht_ut
  have h_gap_le : ∀ τ : ℝ, 0 ≤ τ →
      tubeGapFactor n (zImPoint n 0 (y₀ + τ • d)) ≤ tubeGapFactor n (zImPoint n 0 y₀) := by
    intro τ hτ
    dsimp [tubeGapFactor]
    refine Finset.prod_le_prod (fun k _ => ?_) (fun k _ => ?_)
    · have hc := coneGap_pos _ (hy_mem τ hτ ⟨k.val, fin_sub_one_lt k⟩ (fin_sub_one_succ_lt k))
      exact add_nonneg zero_le_one (inv_nonneg.mpr hc.le)
    · refine add_le_add le_rfl ?_
      have hi := fin_sub_one_lt k
      have hk1 := fin_sub_one_succ_lt k
      let i0 : Fin n := ⟨k.val, hi⟩
      let i1 : Fin n := ⟨k.val + 1, hk1⟩
      have h_ut_pos : 0 < coneGap (diff_im n (zImPoint n 0 y₀) i0 hk1) := by
        have hy0_mem : zImPoint n 0 y₀ ∈ forward_tube_n n := by simpa using hy_mem 0 le_rfl
        exact coneGap_pos _ (hy0_mem i0 hk1)
      refine inv_anti₀ h_ut_pos ?_
      rw [diff_im_zImPoint, diff_im_zImPoint]
      have h_diff : (y₀ + τ • d) i1 - (y₀ + τ • d) i0 =
          (y₀ i1 - y₀ i0) + τ • (d i1 - d i0) := by
        ext μ
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      change coneGap (y₀ i1 - y₀ i0) ≤ coneGap ((y₀ + τ • d) i1 - (y₀ + τ • d) i0)
      rw [h_diff]
      by_cases him : i0 ≤ m
      · by_cases hi1m : i1 ≤ m
        · have hd0 : d i1 - d i0 = 0 := by simp [d, him, hi1m]
          rw [hd0, smul_zero, add_zero]
        · have hd_w : d i1 - d i0 = w := by simp [d, him, hi1m]
          rw [hd_w]
          have h1 := coneGap_add_ge (y₀ i1 - y₀ i0) (τ • w)
          have h2 : 0 ≤ coneGap (τ • w) := by
            rw [coneGap_smul_of_nonneg hτ w]
            exact mul_nonneg hτ (coneGap_pos w hw_cone).le
          linarith
      · have hi1m : ¬ i1 ≤ m := by
          intro hc
          exact him (le_trans (Fin.le_iff_val_le_val.mpr (Nat.le_succ _)) hc)
        have hd0 : d i1 - d i0 = 0 := by simp [d, him, hi1m]
        rw [hd0, smul_zero, add_zero]
  let z_ray : ℝ → Fin n → Fin 4 → ℂ := fun τ => zImPoint n 0 (τ • (-d))
  let ψ_ray : ℝ → SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
    fun τ => vladimirov_psi_schwartz n R hR_pos (z_ray τ)
  let Φ_mul : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
    (invMinkowskiFourierCLM n).comp (SchwartzMap.smulLeftCLM ℂ g)
  let F_ode : ℝ → ℂ := fun τ =>
    ∫ x : Fin n → Fin 4 → ℝ, H n α (zImPoint n x (y₀ + τ • d)) * (Φ_mul (ψ_ray τ)) x
  have hd_sum : ∀ p : Fin n → Fin 4 → ℝ,
      (∑ k : Fin n, minkowskiInner (p k) (d k)) = -(L_clm p) := by
    intro p
    have h_term : ∀ k : Fin n, minkowskiInner (p k) (d k) =
        if k ≤ m then -(minkowskiInner (p k) w) else 0 := by
      intro k
      by_cases hk : k ≤ m
      · simp only [d, hk, ↓reduceIte, minkowskiInner_explicit, Pi.neg_apply]
        ring
      · simp [d, hk, minkowskiInner_explicit]
    simp_rw [h_term]
    rw [← Finset.sum_filter, Finset.sum_neg_distrib]
    change -(∑ k ∈ Finset.univ.filter (· ≤ m), minkowskiInner (p k) w) =
      -(minkowskiInner (∑ k ∈ Finset.univ.filter (· ≤ m), p k) w)
    simp only [minkowskiInner_explicit, Finset.sum_apply, Finset.sum_mul, Finset.sum_sub_distrib]
  have hF_deriv : ∀ s : ℝ, 0 ≤ s → HasDerivAt F_ode 0 s := fun s hs =>
    hasDerivAt_vladimirov_cone_ray_eq_zero (h_ana n α) hCH h_bd hR_pos g y₀ d s (hy_mem s hs)
  have hF_const : ∀ Λ : ℝ, 0 ≤ Λ → F_ode Λ = F_ode 0 := by
    intro Λ hΛ
    have h_mvt := (convex_Icc 0 Λ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r hr => (hF_deriv r hr.1).hasDerivWithinAt)
      (fun _ _ => norm_zero.le)
      ⟨le_rfl, hΛ⟩ ⟨hΛ, le_rfl⟩
    simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at h_mvt
    exact h_mvt
  have hF0_eq : F_ode 0 = ∫ x : Fin n → Fin 4 → ℝ,
      H n α (tubeBoundaryLine n x unit_time_vector t) * (invMinkowskiFourierCLM n g) x := by
    have h_g0 : SchwartzMap.smulLeftCLM ℂ g (ψ_ray 0) = g := by
      ext p
      rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
      by_cases hp : p ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
      · have hp_R : p ∈ Metric.closedBall (0 : Fin n → Fin 4 → ℝ) R := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hg_in_R p hp
        change g p * (((vladimirovCutoffBump n R hR_pos p : ℝ) : ℂ) *
          vladimirov_kernel n (z_ray 0) p) = g p
        have h_bump1 : vladimirovCutoffBump n R hR_pos p = 1 :=
          (vladimirovCutoffBump n R hR_pos).one_of_mem_closedBall hp_R
        have h_ker1 : vladimirov_kernel n (z_ray 0) p = 1 := by
          have hz0 : z_ray 0 = 0 := by
            ext i μ
            simp [z_ray, zImPoint]
          rw [hz0]
          dsimp [vladimirov_kernel, minkowskiInnerC]
          simp
        rw [h_bump1, h_ker1, Complex.ofReal_one, mul_one, mul_one]
      · have hg0 : g p = 0 := by
          by_contra hne
          exact hp (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [hg0, zero_mul]
    dsimp [F_ode, Φ_mul]
    rw [h_g0]
    congr 1
    ext x
    rw [tubeBoundaryLine_eq_zImPoint, zero_smul, add_zero]
  suffices hF_tend : Tendsto F_ode Filter.atTop (𝓝 0) by
    have h_ev_c : F_ode =ᶠ[Filter.atTop] fun _ => F_ode 0 := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with Λ hΛ
      exact hF_const Λ hΛ
    exact hF0_eq ▸ tendsto_nhds_unique (tendsto_const_nhds.congr' h_ev_c.symm) hF_tend
  let p_inv : Seminorm ℝ (SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :=
    (schwartzPolySeminorm n M).comp ((invMinkowskiFourierCLM n).restrictScalars ℝ).toLinearMap
  have hp_inv_fn : (p_inv : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ → ℝ) =
      fun u => schwartzPolyIntegralBound n M (invMinkowskiFourierCLM n u) :=
    funext fun u => schwartzPolySeminorm_apply n M (invMinkowskiFourierCLM n u)
  have hp_inv_cont : Continuous p_inv := by
    rw [hp_inv_fn]
    exact (continuous_schwartzPolyIntegralBound n M).comp (invMinkowskiFourierCLM n).continuous
  obtain ⟨s_inv, C_inv, _, hp_inv_le⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ (Fin n → Fin 4 → ℝ) ℂ) p_inv
      hp_inv_cont
  let E_1 : (Fin n → Fin 4 → ℝ) → ℂ := fun v => Complex.exp ((L_clm v : ℝ) : ℂ)
  let B_sem : (ℕ × ℕ) → ℝ := fun kj =>
    R ^ kj.1 * ∑ i ∈ Finset.range (kj.2 + 1),
      (kj.2.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
        ‖iteratedFDeriv ℝ (kj.2 - i) E_1 0‖
  have hB_sem_nn : ∀ kj, 0 ≤ B_sem kj := fun kj =>
    mul_nonneg (pow_nonneg hR_pos.le _) (Finset.sum_nonneg fun _ _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (norm_nonneg _))
  have h_gexp_sem : ∀ (Λ : ℝ) (hΛ : 0 ≤ Λ) (kj : ℕ × ℕ),
      (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ kj)
        (SchwartzMap.smulLeftCLM ℂ g (ψ_ray Λ)) ≤
        B_sem kj * (1 + Λ) ^ kj.2 * Real.exp (-δ * Λ) := by
    intro Λ hΛ ⟨k_p, j_d⟩
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    have h_bd_nn : 0 ≤ B_sem (k_p, j_d) * (1 + Λ) ^ j_d * Real.exp (-δ * Λ) :=
      mul_nonneg (mul_nonneg (hB_sem_nn (k_p, j_d)) (pow_nonneg (by linarith) j_d))
        (Real.exp_nonneg _)
    refine SchwartzMap.seminorm_le_bound ℝ k_p j_d _ h_bd_nn fun p => ?_
    let E_Λ : (Fin n → Fin 4 → ℝ) → ℂ :=
      fun u => Complex.exp ((Λ : ℂ) * ((L_clm u : ℝ) : ℂ))
    have h_fn_eq : (SchwartzMap.smulLeftCLM ℂ g (ψ_ray Λ) : (Fin n → Fin 4 → ℝ) → ℂ) =
        fun u => g u * E_Λ u := by
      ext u
      rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
      by_cases hu : u ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
      · have hu_R : u ∈ Metric.closedBall (0 : Fin n → Fin 4 → ℝ) R := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hg_in_R u hu
        change g u * (((vladimirovCutoffBump n R hR_pos u : ℝ) : ℂ) *
          vladimirov_kernel n (z_ray Λ) u) = g u * E_Λ u
        have h_b1 : vladimirovCutoffBump n R hR_pos u = 1 :=
          (vladimirovCutoffBump n R hR_pos).one_of_mem_closedBall hu_R
        have h_ker : vladimirov_kernel n (z_ray Λ) u = E_Λ u := by
          have h_in : ∀ k : Fin n,
              minkowskiInnerC (fun μ => (u k μ : ℂ)) (zImPoint n 0 (Λ • (-d)) k) =
              -(Complex.I * (Λ : ℂ) * ((minkowskiInner (u k) (d k) : ℝ) : ℂ)) := by
            intro k
            dsimp [minkowskiInnerC, zImPoint]
            rw [minkowskiInner_explicit]
            push_cast
            ring
          dsimp [vladimirov_kernel, E_Λ, z_ray]
          congr 1
          simp_rw [h_in, Finset.sum_neg_distrib, ← Finset.mul_sum]
          have h_sum_c : (∑ x : Fin n, ((minkowskiInner (u x) (d x) : ℝ) : ℂ)) =
              ((∑ x : Fin n, minkowskiInner (u x) (d x) : ℝ) : ℂ) := by push_cast; rfl
          rw [h_sum_c, hd_sum u]
          push_cast
          calc -Complex.I * -(Complex.I * (Λ : ℂ) * -(L_clm u : ℂ))
              = -(Complex.I * Complex.I) * ((Λ : ℂ) * (L_clm u : ℂ)) := by ring
            _ = (Λ : ℂ) * (L_clm u : ℂ) := by rw [Complex.I_mul_I]; ring
        rw [h_b1, h_ker, Complex.ofReal_one, one_mul]
      · have hg0 : g u = 0 := by
          by_contra hne
          exact hu (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [hg0, zero_mul, zero_mul]
    rw [h_fn_eq]
    by_cases hp : p ∈ tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
    · have hp_norm : ‖p‖ ^ k_p ≤ R ^ k_p :=
        pow_le_pow_left₀ (norm_nonneg p) (hg_in_R p hp) k_p
      have hp_L : L_clm p ≤ -δ := hL_ball p (hg_supp hp)
      have hEΛ_sm : ContDiff ℝ (⊤ : ℕ∞) E_Λ :=
        Complex.contDiff_exp.comp
          (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp L_clm.contDiff))
      have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
        (f := (g : (Fin n → Fin 4 → ℝ) → ℂ)) (g := E_Λ) (n := j_d) (N := (⊤ : ℕ∞))
        (g.smooth ⊤) hEΛ_sm p (WithTop.coe_le_coe.mpr le_top)
      have h_sum_le : (∑ i ∈ Finset.range (j_d + 1),
          (j_d.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g : (Fin n → Fin 4 → ℝ) → ℂ) p‖ *
            ‖iteratedFDeriv ℝ (j_d - i) E_Λ p‖) ≤
          (∑ i ∈ Finset.range (j_d + 1),
            (j_d.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
              ‖iteratedFDeriv ℝ (j_d - i) E_1 0‖) *
            (1 + Λ) ^ j_d * Real.exp (-δ * Λ) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi_le : j_d - i ≤ j_d := Nat.sub_le j_d i
        have hg_i := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g i p
        have hE_i := norm_iteratedFDeriv_exp_scaled_linear_le L_clm hΛ p hp_L (j_d - i)
        have h_pow_le : (1 + Λ) ^ (j_d - i) ≤ (1 + Λ) ^ j_d :=
          pow_le_pow_right₀ (by linarith) hi_le
        calc (j_d.choose i : ℝ) * ‖iteratedFDeriv ℝ i (g : (Fin n → Fin 4 → ℝ) → ℂ) p‖ *
              ‖iteratedFDeriv ℝ (j_d - i) E_Λ p‖
            ≤ (j_d.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
                (Real.exp (-δ * Λ) * ((1 + Λ) ^ (j_d - i) *
                  ‖iteratedFDeriv ℝ (j_d - i) E_1 0‖)) :=
              mul_le_mul
                (mul_le_mul_of_nonneg_left hg_i (Nat.cast_nonneg _))
                hE_i (norm_nonneg _) (by positivity)
          _ ≤ (j_d.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
                (Real.exp (-δ * Λ) * ((1 + Λ) ^ j_d *
                  ‖iteratedFDeriv ℝ (j_d - i) E_1 0‖)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right h_pow_le (norm_nonneg _))
                  (Real.exp_nonneg _))
                (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
          _ = (j_d.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
                ‖iteratedFDeriv ℝ (j_d - i) E_1 0‖ * (1 + Λ) ^ j_d * Real.exp (-δ * Λ) := by
              ring
      calc ‖p‖ ^ k_p * ‖iteratedFDeriv ℝ j_d (fun u => g u * E_Λ u) p‖
          ≤ R ^ k_p * ((∑ i ∈ Finset.range (j_d + 1),
              (j_d.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
                ‖iteratedFDeriv ℝ (j_d - i) E_1 0‖) *
              (1 + Λ) ^ j_d * Real.exp (-δ * Λ)) :=
            mul_le_mul hp_norm (h_leib.trans h_sum_le) (norm_nonneg _) (pow_nonneg hR_pos.le _)
        _ = B_sem (k_p, j_d) * (1 + Λ) ^ j_d * Real.exp (-δ * Λ) := by dsimp [B_sem]; ring
    · have h_compl : (tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ))ᶜ ∈ 𝓝 p :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hp
      have h_ev0 : (fun u => g u * E_Λ u) =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
        filter_upwards [h_compl] with u hu
        have hg0 : g u = 0 := by
          by_contra hne
          exact hu (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [hg0, zero_mul]
      rw [(h_ev0.iteratedFDeriv ℝ j_d).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply,
        norm_zero, mul_zero]
      exact h_bd_nn
  let J_max : ℕ := s_inv.sup Prod.snd
  let C_sup : ℝ := ∑ kj ∈ s_inv, B_sem kj
  have hC_sup_nn : 0 ≤ C_sup := Finset.sum_nonneg fun kj _ => hB_sem_nn kj
  have h_sup_le : ∀ (Λ : ℝ) (hΛ : 0 ≤ Λ),
      (s_inv.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
        (SchwartzMap.smulLeftCLM ℂ g (ψ_ray Λ)) ≤
        C_sup * (1 + Λ) ^ J_max * Real.exp (-δ * Λ) := by
    intro Λ hΛ
    have h_sub : ∀ u : Finset (ℕ × ℕ), u ⊆ s_inv →
        (u.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
          (SchwartzMap.smulLeftCLM ℂ g (ψ_ray Λ)) ≤
          (∑ kj ∈ u, B_sem kj) * (1 + Λ) ^ J_max * Real.exp (-δ * Λ) := by
      intro u
      induction u using Finset.induction_on with
      | empty =>
        intro _
        simp
      | @insert a u ha ih =>
        intro hu
        rw [Finset.sup_insert, Seminorm.sup_apply, Finset.sum_insert ha]
        have ha_mem : a ∈ s_inv := hu (Finset.mem_insert_self a u)
        have ha_J : a.2 ≤ J_max := Finset.le_sup (f := Prod.snd) ha_mem
        have h_pow_J : (1 + Λ) ^ a.2 ≤ (1 + Λ) ^ J_max :=
          pow_le_pow_right₀ (by linarith) ha_J
        have h1 : (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ a)
            (SchwartzMap.smulLeftCLM ℂ g (ψ_ray Λ)) ≤
            B_sem a * (1 + Λ) ^ J_max * Real.exp (-δ * Λ) :=
          (h_gexp_sem Λ hΛ a).trans
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h_pow_J (hB_sem_nn a)) (Real.exp_nonneg _))
        have h2 := ih fun x hx => hu (Finset.mem_insert_of_mem hx)
        have h_sum_nn : 0 ≤ ∑ kj ∈ u, B_sem kj := Finset.sum_nonneg fun kj _ => hB_sem_nn kj
        refine max_le (h1.trans ?_) (h2.trans ?_)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (Real.exp_nonneg _)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [hB_sem_nn a]) (by positivity))
            (Real.exp_nonneg _)
    exact h_sub s_inv fun _ h => h
  have hy0_mem : zImPoint n 0 y₀ ∈ forward_tube_n n := by
    simpa using hy_mem 0 le_rfl
  let K_tot : ℝ := C_H * (1 + ‖y₀‖ + ‖d‖) ^ M *
    (tubeGapFactor n (zImPoint n 0 y₀)) ^ N_H * (C_inv : ℝ) * C_sup
  have h_F_le : ∀ Λ : ℝ, 1 ≤ Λ →
      ‖F_ode Λ‖ ≤ K_tot * ((2 / δ) ^ (M + J_max) *
        ((δ * Λ) ^ (M + J_max) * Real.exp (-(δ * Λ)))) := by
    intro Λ hΛ1
    have hΛ0 : 0 ≤ Λ := by linarith
    have hyΛ : zImPoint n 0 (y₀ + Λ • d) ∈ forward_tube_n n := hy_mem Λ hΛ0
    have hF_apply : F_ode Λ =
        zImPointIntegralCLM (h_ana n α) hCH h_bd hyΛ (Φ_mul (ψ_ray Λ)) := rfl
    have h_yΛ_le : 1 + ‖y₀ + Λ • d‖ ≤ (1 + ‖y₀‖ + ‖d‖) * (1 + Λ) := by
      have h1 : ‖y₀ + Λ • d‖ ≤ ‖y₀‖ + Λ * ‖d‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul Λ d, Real.norm_of_nonneg hΛ0]
      nlinarith [norm_nonneg y₀, norm_nonneg d]
    have h_yΛ_pow : (1 + ‖y₀ + Λ • d‖) ^ M ≤ (1 + ‖y₀‖ + ‖d‖) ^ M * (1 + Λ) ^ M :=
      (pow_le_pow_left₀ (by positivity) h_yΛ_le M).trans_eq (mul_pow _ _ M)
    have h_gap_pow : (tubeGapFactor n (zImPoint n 0 (y₀ + Λ • d))) ^ N_H ≤
        (tubeGapFactor n (zImPoint n 0 y₀)) ^ N_H :=
      pow_le_pow_left₀ (tubeGapFactor_nonneg hyΛ) (h_gap_le Λ hΛ0) N_H
    have h_int_bd : ‖F_ode Λ‖ ≤ C_H * (1 + ‖y₀ + Λ • d‖) ^ M *
        (tubeGapFactor n (zImPoint n 0 (y₀ + Λ • d))) ^ N_H *
        schwartzPolyIntegralBound n M (Φ_mul (ψ_ray Λ)) := by
      let K_Λ : ℝ := C_H * (1 + ‖y₀ + Λ • d‖) ^ M *
        (tubeGapFactor n (zImPoint n 0 (y₀ + Λ • d))) ^ N_H
      have hKΛ_nn : 0 ≤ K_Λ :=
        mul_nonneg (mul_nonneg hCH (by positivity)) (pow_nonneg (tubeGapFactor_nonneg hyΛ) N_H)
      calc ‖F_ode Λ‖
          ≤ ∫ x : Fin n → Fin 4 → ℝ,
              ‖H n α (zImPoint n x (y₀ + Λ • d)) * (Φ_mul (ψ_ray Λ)) x‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x : Fin n → Fin 4 → ℝ,
              K_Λ * ((1 + ‖x‖) ^ M * ‖(Φ_mul (ψ_ray Λ)) x‖) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              ((integrable_one_add_norm_pow_mul_schwartz n M (Φ_mul (ψ_ray Λ))).const_mul K_Λ)
              (Filter.Eventually.of_forall fun x => ?_)
            dsimp only
            rw [norm_mul]
            have hzx : zImPoint n x (y₀ + Λ • d) ∈ forward_tube_n n :=
              (zImPoint_mem_forward_tube_iff n x _).mpr hyΛ
            have hHz := h_bd _ hzx
            rw [tubeGapFactor_zImPoint_eq n x _] at hHz
            have h_zle : 1 + ‖zImPoint n x (y₀ + Λ • d)‖ ≤
                (1 + ‖y₀ + Λ • d‖) * (1 + ‖x‖) := by
              linarith [norm_zImPoint_le n x (y₀ + Λ • d),
                mul_nonneg (norm_nonneg (y₀ + Λ • d)) (norm_nonneg x)]
            have h_zp : (1 + ‖zImPoint n x (y₀ + Λ • d)‖) ^ M ≤
                (1 + ‖y₀ + Λ • d‖) ^ M * (1 + ‖x‖) ^ M :=
              (pow_le_pow_left₀ (by positivity) h_zle M).trans_eq (mul_pow _ _ M)
            calc ‖H n α (zImPoint n x (y₀ + Λ • d))‖ * ‖(Φ_mul (ψ_ray Λ)) x‖
                ≤ (C_H * ((1 + ‖y₀ + Λ • d‖) ^ M * (1 + ‖x‖) ^ M) *
                    (tubeGapFactor n (zImPoint n 0 (y₀ + Λ • d))) ^ N_H) *
                    ‖(Φ_mul (ψ_ray Λ)) x‖ :=
                  mul_le_mul_of_nonneg_right
                    (hHz.trans (mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left h_zp hCH)
                      (pow_nonneg (tubeGapFactor_nonneg hyΛ) N_H)))
                    (norm_nonneg _)
              _ = K_Λ * ((1 + ‖x‖) ^ M * ‖(Φ_mul (ψ_ray Λ)) x‖) := by dsimp [K_Λ]; ring
        _ = K_Λ * ∫ x : Fin n → Fin 4 → ℝ, (1 + ‖x‖) ^ M * ‖(Φ_mul (ψ_ray Λ)) x‖ :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ K_Λ * schwartzPolyIntegralBound n M (Φ_mul (ψ_ray Λ)) :=
            mul_le_mul_of_nonneg_left
              (integral_one_add_norm_pow_mul_schwartz_le n M (Φ_mul (ψ_ray Λ))) hKΛ_nn
    have h_pinv : schwartzPolyIntegralBound n M (Φ_mul (ψ_ray Λ)) ≤
        (C_inv : ℝ) * (C_sup * (1 + Λ) ^ J_max * Real.exp (-δ * Λ)) := by
      have h1 : schwartzPolyIntegralBound n M (Φ_mul (ψ_ray Λ)) =
          p_inv (SchwartzMap.smulLeftCLM ℂ g (ψ_ray Λ)) :=
        (schwartzPolySeminorm_apply n M (Φ_mul (ψ_ray Λ))).symm
      rw [h1]
      exact (hp_inv_le _).trans (mul_le_mul_of_nonneg_left (h_sup_le Λ hΛ0) C_inv.coe_nonneg)
    have h_1add : 1 + Λ ≤ (2 / δ) * (δ * Λ) := by
      have h2 : (2 / δ) * (δ * Λ) = 2 * Λ := by field_simp [hδ_pos.ne']
      linarith
    have h_pow_MJ : (1 + Λ) ^ (M + J_max) ≤ (2 / δ) ^ (M + J_max) * (δ * Λ) ^ (M + J_max) :=
      (pow_le_pow_left₀ (by positivity) h_1add (M + J_max)).trans_eq (mul_pow _ _ _)
    have h_neg_mul : -δ * Λ = -(δ * Λ) := by ring
    have h_lhs_nn1 : 0 ≤ C_H * ((1 + ‖y₀‖ + ‖d‖) ^ M * (1 + Λ) ^ M) :=
      mul_nonneg hCH (by positivity)
    have h_lhs_nn2 : 0 ≤ (C_H * ((1 + ‖y₀‖ + ‖d‖) ^ M * (1 + Λ) ^ M)) *
        (tubeGapFactor n (zImPoint n 0 y₀)) ^ N_H :=
      mul_nonneg h_lhs_nn1 (pow_nonneg (tubeGapFactor_nonneg hy0_mem) N_H)
    calc ‖F_ode Λ‖
        ≤ (C_H * ((1 + ‖y₀‖ + ‖d‖) ^ M * (1 + Λ) ^ M) *
            (tubeGapFactor n (zImPoint n 0 y₀)) ^ N_H) *
            ((C_inv : ℝ) * (C_sup * (1 + Λ) ^ J_max * Real.exp (-δ * Λ))) := by
          refine h_int_bd.trans (mul_le_mul ?_ h_pinv
            (schwartzPolyIntegralBound_nonneg n M _) h_lhs_nn2)
          exact mul_le_mul (mul_le_mul_of_nonneg_left h_yΛ_pow hCH) h_gap_pow
            (pow_nonneg (tubeGapFactor_nonneg hyΛ) N_H) h_lhs_nn1
      _ = K_tot * ((1 + Λ) ^ (M + J_max) * Real.exp (-(δ * Λ))) := by
          rw [pow_add, h_neg_mul]; dsimp [K_tot]; ring
      _ ≤ K_tot * ((2 / δ) ^ (M + J_max) *
            ((δ * Λ) ^ (M + J_max) * Real.exp (-(δ * Λ)))) := by
          have hK_nn : 0 ≤ K_tot := by
            dsimp [K_tot]
            exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCH (by positivity))
              (pow_nonneg (tubeGapFactor_nonneg hy0_mem) N_H)) C_inv.coe_nonneg) hC_sup_nn
          have h_rhs_re : (2 / δ) ^ (M + J_max) *
              ((δ * Λ) ^ (M + J_max) * Real.exp (-(δ * Λ))) =
              ((2 / δ) ^ (M + J_max) * (δ * Λ) ^ (M + J_max)) * Real.exp (-(δ * Λ)) := by ring
          rw [h_rhs_re]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h_pow_MJ (Real.exp_nonneg _)) hK_nn
  have h_exp_lim : Tendsto
      (fun Λ : ℝ => K_tot * ((2 / δ) ^ (M + J_max) *
        ((δ * Λ) ^ (M + J_max) * Real.exp (-(δ * Λ)))))
      Filter.atTop (𝓝 0) := by
    have h_u := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (M + J_max)).comp
      (Filter.tendsto_id.const_mul_atTop hδ_pos)
    simpa using (h_u.const_mul ((2 / δ) ^ (M + J_max))).const_mul K_tot
  refine squeeze_zero_norm' ?_ h_exp_lim
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  exact h_F_le Λ hΛ

theorem vladimirovFromTube_spectrumCondition {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (htrans : TubeTranslationInvariant (vladimirovFromTubeExtension h_ana h_growth)) :
    SpectrumCondition (vladimirovFromTubeWightmanFamily h_ana h_growth) := by
  let W := vladimirovFromTubeWightmanFamily h_ana h_growth
  have hW_trans : WightmanTranslationInvariant W :=
    wightmanTranslationInvariant_of_tubeTranslationInvariant
      (vladimirovFromTubeExtension h_ana h_growth) htrans
  rw [spectrumCondition_iff_tsupport]
  intro n α f h_disj
  let g_full : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := minkowskiFourierCLM n f
  have hf_eq : f = invMinkowskiFourierCLM n g_full :=
    (invMinkowskiFourierCLM_minkowskiFourierCLM n f).symm
  have h_loc_ball : ∀ q : Fin n → Fin 4 → ℝ, q ∉ spectralRegion n →
      ∃ r_q : ℝ, 0 < r_q ∧ ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
        tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ Metric.ball q r_q →
        W n α (invMinkowskiFourierCLM n g) = 0 := by
    intro q hq_not
    by_cases h_sum : ∑ i : Fin n, q i = 0
    · have h_ex : ∃ m : Fin n, partial_sum_p n q m ∉ closure forward_light_cone := by
        by_contra h_all
        push Not at h_all
        exact hq_not ⟨h_sum, h_all⟩
      obtain ⟨m, hm⟩ := h_ex
      exact vladimirovFromTubeVal_invFourier_eq_zero_of_ball_cone h_ana h_growth n α h_sum m hm
    · obtain ⟨r_q, hrq_pos, hrq⟩ := exists_div_exp_sub_one_schwartz n h_sum
      refine ⟨r_q, hrq_pos, fun g hg => ?_⟩
      obtain ⟨a, h, hh_eq⟩ := hrq g hg
      rw [hh_eq, map_sub]
      have h_tr := hW_trans n α a (invMinkowskiFourierCLM n h)
        (schwartzDiagTranslateN n a (invMinkowskiFourierCLM n h))
        (schwartzDiagTranslateN_shift n a (invMinkowskiFourierCLM n h))
      exact sub_eq_zero.mpr h_tr
  have h_compact : ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      HasCompactSupport (g : (Fin n → Fin 4 → ℝ) → ℂ) →
      Disjoint (tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)) (spectralRegion n) →
      W n α (invMinkowskiFourierCLM n g) = 0 := by
    intro g hg_comp hg_disj
    let K := tsupport (g : (Fin n → Fin 4 → ℝ) → ℂ)
    have hK_comp : IsCompact K := hg_comp
    have hK_not : ∀ q ∈ K, q ∉ spectralRegion n :=
      fun q hqK hqS => Set.disjoint_left.mp hg_disj hqK hqS
    let r_fn : K → ℝ := fun q => (h_loc_ball q.1 (hK_not q.1 q.2)).choose
    have hr_pos : ∀ q : K, 0 < r_fn q :=
      fun q => (h_loc_ball q.1 (hK_not q.1 q.2)).choose_spec.1
    have hr_van : ∀ (q : K) (u : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
        tsupport (u : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ Metric.ball q.1 (r_fn q) →
        W n α (invMinkowskiFourierCLM n u) = 0 :=
      fun q => (h_loc_ball q.1 (hK_not q.1 q.2)).choose_spec.2
    have h_cov : K ⊆ ⋃ q : K, Metric.ball q.1 (r_fn q / 3) := by
      intro p hp
      exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, Metric.mem_ball_self (by linarith [hr_pos ⟨p, hp⟩])⟩
    obtain ⟨t_fin, ht_cov⟩ := hK_comp.elim_finite_subcover
      (fun q : K => Metric.ball q.1 (r_fn q / 3))
      (fun _ => Metric.isOpen_ball) h_cov
    suffices h_ind : ∀ (S : Finset K) (u : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
        tsupport (u : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
          (⋃ q ∈ S, Metric.ball q.1 (r_fn q / 3)) →
        W n α (invMinkowskiFourierCLM n u) = 0 from h_ind t_fin g ht_cov
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro u hu
      have hu0 : u = 0 := by
        ext p
        by_contra hne
        have hp_mem : p ∈ tsupport (u : (Fin n → Fin 4 → ℝ) → ℂ) :=
          subset_tsupport _ (Function.mem_support.mpr hne)
        have hp_emp := hu hp_mem
        simp at hp_emp
      rw [hu0, map_zero, map_zero]
    | @insert q₀ S hq₀ ih =>
      intro u hu
      let b : ContDiffBump q₀.1 :=
        { rIn := r_fn q₀ / 3
          rOut := r_fn q₀ / 2
          rIn_pos := by linarith [hr_pos q₀]
          rIn_lt_rOut := by linarith [hr_pos q₀] }
      let b_c : (Fin n → Fin 4 → ℝ) → ℂ := fun p => (b p : ℂ)
      have hb_comp : HasCompactSupport b_c :=
        b.hasCompactSupport.comp_left Complex.ofReal_zero
      have hb_sm : ContDiff ℝ (⊤ : ℕ∞) b_c :=
        Complex.ofRealCLM.contDiff.comp b.contDiff
      let b_sch : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := hb_comp.toSchwartzMap hb_sm
      let u₁ : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := SchwartzMap.smulLeftCLM ℂ b_sch u
      let u₂ : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := u - u₁
      have hu_decomp : u = u₁ + u₂ := (add_sub_cancel u₁ u).symm
      have hu₁_supp : tsupport (u₁ : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
          Metric.ball q₀.1 (r_fn q₀) := by
        have h1 : tsupport (u₁ : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
            tsupport (u : (Fin n → Fin 4 → ℝ) → ℂ) ∩
              tsupport (b_sch : (Fin n → Fin 4 → ℝ) → ℂ) :=
          SchwartzMap.tsupport_smulLeftCLM_subset b_sch u
        intro p hp
        have hp_b : p ∈ tsupport b_c := (h1 hp).2
        have h_b_sub : Function.support b_c ⊆ Metric.closedBall q₀.1 (r_fn q₀ / 2) := by
          intro x hx
          rw [Function.mem_support] at hx
          by_contra hx_out
          rw [Metric.mem_closedBall, not_le] at hx_out
          have hb0 : b x = 0 := b.zero_of_le_dist hx_out.le
          exact hx (by dsimp [b_c]; rw [hb0, Complex.ofReal_zero])
        have hp_cb : p ∈ Metric.closedBall q₀.1 (r_fn q₀ / 2) :=
          closure_minimal h_b_sub Metric.isClosed_closedBall hp_b
        exact Metric.closedBall_subset_ball (by linarith [hr_pos q₀]) hp_cb
      have hu₂_supp : tsupport (u₂ : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
          ⋃ q ∈ S, Metric.ball q.1 (r_fn q / 3) := by
        have h_supp_u2 : Function.support (u₂ : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
            tsupport (u : (Fin n → Fin 4 → ℝ) → ℂ) \
              Metric.ball q₀.1 (r_fn q₀ / 3) := by
          intro p hp
          rw [Function.mem_support] at hp
          refine ⟨?_, ?_⟩
          · by_contra h_not
            have hu0 : u p = 0 := by
              by_contra hne
              exact h_not (subset_tsupport _ (Function.mem_support.mpr hne))
            have hu10 : u₁ p = 0 := by
              dsimp [u₁]
              rw [SchwartzMap.smulLeftCLM_apply_apply b_sch.hasTemperateGrowth,
                smul_eq_mul, hu0, mul_zero]
            exact hp (by dsimp [u₂]; rw [_root_.sub_apply, hu0, hu10, sub_zero])
          · intro hp_in
            have hb1 : b p = 1 :=
              b.one_of_mem_closedBall (Metric.ball_subset_closedBall hp_in)
            have hu1_eq : u₁ p = u p := by
              dsimp [u₁]
              rw [SchwartzMap.smulLeftCLM_apply_apply b_sch.hasTemperateGrowth, smul_eq_mul]
              change (b p : ℂ) * u p = u p
              rw [hb1, Complex.ofReal_one, one_mul]
            exact hp (by dsimp [u₂]; rw [_root_.sub_apply, hu1_eq, sub_self])
        have h_closed_diff : IsClosed (tsupport (u : (Fin n → Fin 4 → ℝ) → ℂ) \
            Metric.ball q₀.1 (r_fn q₀ / 3)) :=
          (isClosed_tsupport _).sdiff Metric.isOpen_ball
        intro p hp
        obtain ⟨hp_u, hp_not_q0⟩ := closure_minimal h_supp_u2 h_closed_diff hp
        have hp_ins := hu hp_u
        rw [Finset.set_biUnion_insert, Set.mem_union] at hp_ins
        rcases hp_ins with hp_q0 | hp_S
        · exact False.elim (hp_not_q0 hp_q0)
        · exact hp_S
      rw [hu_decomp, map_add, map_add, hr_van q₀ u₁ hu₁_supp, ih u₂ hu₂_supp, add_zero]
  rw [hf_eq]
  have h_seq_tend : Tendsto
      (fun k : ℕ => W n α (invMinkowskiFourierCLM n (schwartzCutoffSeq n g_full k)))
      Filter.atTop (𝓝 (W n α (invMinkowskiFourierCLM n g_full))) :=
    ((W n α).continuous.comp (invMinkowskiFourierCLM n).continuous).tendsto g_full |>.comp
      (schwartzCutoffSeq_tendsto n g_full)
  have h_seq_zero : ∀ k : ℕ,
      W n α (invMinkowskiFourierCLM n (schwartzCutoffSeq n g_full k)) = 0 := by
    intro k
    refine h_compact (schwartzCutoffSeq n g_full k)
      (schwartzCutoffSeq_hasCompactSupport n g_full k) ?_
    have h_sub : tsupport (schwartzCutoffSeq n g_full k : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
        tsupport (g_full : (Fin n → Fin 4 → ℝ) → ℂ) := by
      refine closure_minimal ?_ (isClosed_tsupport _)
      intro p hp
      rw [Function.mem_support, schwartzCutoffSeq_apply] at hp
      exact subset_tsupport _ (Function.mem_support.mpr fun hg0 => hp (by rw [hg0, mul_zero]))
    exact Set.disjoint_of_subset_left h_sub h_disj
  have h_ev0 : (fun k : ℕ => W n α (invMinkowskiFourierCLM n (schwartzCutoffSeq n g_full k))) =
      fun _ => (0 : ℂ) := funext h_seq_zero
  exact tendsto_nhds_unique h_seq_tend (h_ev0 ▸ tendsto_const_nhds)

theorem vladimirovFromTube_tubeTranslationInvariant {κ : Type*}
    {H : ∀ n : ℕ, (Fin n → κ) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (𝒮 : SchwingerFamily κ) (htrans : OSTranslationInvariant 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → κ) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = H n α (wickEmbedN n x)) :
    TubeTranslationInvariant (vladimirovFromTubeExtension h_ana h_growth) :=
  tubeTranslationInvariant_of_schwinger_eq_and_osTranslation
    (vladimirovFromTubeExtension h_ana h_growth) 𝒮 htrans h_schw

theorem vladimirovFromTube_poincareCovariant
    (R : HolomorphicLorentzRep ι)
    {H : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (𝒮 : SchwingerFamily ι) (htrans : OSTranslationInvariant 𝒮)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = H n α (wickEmbedN n x))
    (hcov : TubeCovariant R (vladimirovFromTubeExtension h_ana h_growth)) :
    PoincareCovariant R (vladimirovFromTubeWightmanFamily h_ana h_growth) :=
  poincareCovariant_of_tube_and_osTranslation R
    (vladimirovFromTubeExtension h_ana h_growth) 𝒮 htrans h_schw hcov

theorem vladimirovFromTube_tubePCT
    (R : HolomorphicLorentzRep ι) {η : ℂ}
    {H : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (𝒮 : SchwingerFamily ι)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = H n α (wickEmbedN n x))
    (h_sym : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      𝒮 n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) *
          ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * 𝒮 n (β ∘ Fin.rev) x) :
    TubePCT η R (vladimirovFromTubeExtension h_ana h_growth) :=
  tubePCT_of_schwinger_eq_and_osPCTSymmetry R
    (vladimirovFromTubeExtension h_ana h_growth) 𝒮 h_schw h_sym

theorem vladimirovFromTube_weakLocality
    (R : HolomorphicLorentzRep ι) {η : ℂ}
    {H : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (𝒮 : SchwingerFamily ι)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = H n α (wickEmbedN n x))
    (h_sym : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      𝒮 n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) *
          ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * 𝒮 n (β ∘ Fin.rev) x)
    (hcov : TubeCovariant R (vladimirovFromTubeExtension h_ana h_growth)) :
    WeakLocality η (vladimirovFromTubeWightmanFamily h_ana h_growth) :=
  weakLocality_of_tubePCT R (vladimirovFromTubeWightmanFamily h_ana h_growth)
    (vladimirovFromTubeExtension h_ana h_growth) hcov
    (vladimirovFromTube_tubePCT R h_ana h_growth 𝒮 h_schw h_sym)

noncomputable def osWavepacket (k : ℕ) (y : posOrderedEuclidN k) :
    SchwartzMap (Fin k → Fin 4 → ℝ) ℂ :=
  osToWightmanTest k (wickEmbedN k y.val) (wickEmbedN_mem_posTubeN y.property)

noncomputable def osWavepacketSubmodule (k : ℕ) :
    Submodule ℂ (SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :=
  Submodule.span ℂ (Set.range (osWavepacket k))

lemma borchersConcatSchwartz_zero_left (j k : ℕ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k 0 g = 0 := by
  ext x
  simp [borchersConcatSchwartz_apply]

lemma borchersConcatSchwartz_zero_right (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k f 0 = 0 := by
  ext x
  simp [borchersConcatSchwartz_apply]

lemma borchersConcatSchwartz_add_left (j k : ℕ)
    (f₁ f₂ : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k (f₁ + f₂) g =
      borchersConcatSchwartz j k f₁ g + borchersConcatSchwartz j k f₂ g := by
  ext x
  simp [borchersConcatSchwartz_apply, add_mul]

lemma borchersConcatSchwartz_add_right (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g₁ g₂ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k f (g₁ + g₂) =
      borchersConcatSchwartz j k f g₁ + borchersConcatSchwartz j k f g₂ := by
  ext x
  simp [borchersConcatSchwartz_apply, mul_add]

lemma borchersConcatSchwartz_sub_left (j k : ℕ)
    (f₁ f₂ : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k (f₁ - f₂) g =
      borchersConcatSchwartz j k f₁ g - borchersConcatSchwartz j k f₂ g := by
  ext x
  simp [borchersConcatSchwartz_apply, sub_mul]

lemma borchersConcatSchwartz_sub_right (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g₁ g₂ : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k f (g₁ - g₂) =
      borchersConcatSchwartz j k f g₁ - borchersConcatSchwartz j k f g₂ := by
  ext x
  simp [borchersConcatSchwartz_apply, mul_sub]

lemma borchersConcatSchwartz_smul_left (j k : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k (c • f) g =
      star c • borchersConcatSchwartz j k f g := by
  ext x
  simp only [borchersConcatSchwartz_apply, _root_.smul_apply, smul_eq_mul,
    map_mul, Complex.star_def]
  ring

lemma borchersConcatSchwartz_smul_right (j k : ℕ) (c : ℂ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k f (c • g) =
      c • borchersConcatSchwartz j k f g := by
  ext x
  simp only [borchersConcatSchwartz_apply, _root_.smul_apply, smul_eq_mul]
  ring

lemma borchersConcatSchwartz_sum_left {α_idx : Type*} (j k : ℕ)
    (s : Finset α_idx) (f : α_idx → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k (∑ a ∈ s, f a) g =
      ∑ a ∈ s, borchersConcatSchwartz j k (f a) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, borchersConcatSchwartz_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, borchersConcatSchwartz_add_left, ih]

lemma borchersConcatSchwartz_sum_right {α_idx : Type*} (j k : ℕ)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (s : Finset α_idx) (g : α_idx → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    borchersConcatSchwartz j k f (∑ b ∈ s, g b) =
      ∑ b ∈ s, borchersConcatSchwartz j k f (g b) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, borchersConcatSchwartz_zero_right]
  | @insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, borchersConcatSchwartz_add_right, ih]

lemma tendsto_borchersConcatSchwartz_seq (j k : ℕ)
    {u : ℕ → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ}
    {v : ℕ → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ}
    {f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ}
    {g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ}
    (hu : Tendsto u Filter.atTop (𝓝 f))
    (hv : Tendsto v Filter.atTop (𝓝 g)) :
    Tendsto (fun n => borchersConcatSchwartz j k (u n) (v n))
      Filter.atTop (𝓝 (borchersConcatSchwartz j k f g)) := by
  have hu0 : Tendsto (fun n => u n - f) Filter.atTop (𝓝 0) := by
    simpa [sub_self] using hu.sub (tendsto_const_nhds (x := f))
  have hv0 : Tendsto (fun n => v n - g) Filter.atTop (𝓝 0) := by
    simpa [sub_self] using hv.sub (tendsto_const_nhds (x := g))
  have h_diff0 : Tendsto
      (fun n => borchersConcatSchwartz j k (u n) (v n) - borchersConcatSchwartz j k f g)
      Filter.atTop (𝓝 0) := by
    rw [(schwartz_withSeminorms ℝ (Fin (j + k) → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0]
    rintro ⟨l, m⟩ ε hε
    have hu_sem := fun l' m' =>
      ((schwartz_withSeminorms ℝ (Fin j → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0).mp hu0 (l', m')
    have hv_sem := fun l' m' =>
      ((schwartz_withSeminorms ℝ (Fin k → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0).mp hv0 (l', m')
    have h_v_lim : ∀ l' m', Tendsto (fun n => SchwartzMap.seminorm ℝ l' m' (v n))
        Filter.atTop (𝓝 (SchwartzMap.seminorm ℝ l' m' g)) := by
      intro l' m'
      have hc : Continuous (SchwartzMap.seminorm ℝ l' m' :
          SchwartzMap (Fin k → Fin 4 → ℝ) ℂ → ℝ) :=
        ((schwartz_withSeminorms ℝ (Fin k → Fin 4 → ℝ) ℂ).continuous_seminorm (l', m'))
      exact hc.tendsto g |>.comp hv
    let B₁ : ℕ → ℝ := fun n =>
      ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
        (SchwartzMap.seminorm ℝ l q (u n - f) * SchwartzMap.seminorm ℝ 0 (m - q) (v n) +
          SchwartzMap.seminorm ℝ 0 q (u n - f) * SchwartzMap.seminorm ℝ l (m - q) (v n))
    let B₂ : ℕ → ℝ := fun n =>
      ∑ q ∈ Finset.range (m + 1), (m.choose q : ℝ) *
        (SchwartzMap.seminorm ℝ l q f * SchwartzMap.seminorm ℝ 0 (m - q) (v n - g) +
          SchwartzMap.seminorm ℝ 0 q f * SchwartzMap.seminorm ℝ l (m - q) (v n - g))
    have hB₁_lim : Tendsto B₁ Filter.atTop (𝓝 0) := by
      rw [← Finset.sum_const_zero (s := Finset.range (m + 1))]
      refine tendsto_finsetSum _ fun q _ => ?_
      have h1 : Tendsto (fun n => SchwartzMap.seminorm ℝ l q (u n - f)) Filter.atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro δ hδ
        filter_upwards [hu_sem l q δ hδ] with n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
        simpa [SchwartzMap.schwartzSeminormFamily_apply] using hn
      have h2 : Tendsto (fun n => SchwartzMap.seminorm ℝ 0 q (u n - f)) Filter.atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro δ hδ
        filter_upwards [hu_sem 0 q δ hδ] with n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
        simpa [SchwartzMap.schwartzSeminormFamily_apply] using hn
      simpa using tendsto_const_nhds.mul
        ((h1.mul (h_v_lim 0 (m - q))).add (h2.mul (h_v_lim l (m - q))))
    have hB₂_lim : Tendsto B₂ Filter.atTop (𝓝 0) := by
      rw [← Finset.sum_const_zero (s := Finset.range (m + 1))]
      refine tendsto_finsetSum _ fun q _ => ?_
      have h1 : Tendsto (fun n => SchwartzMap.seminorm ℝ 0 (m - q) (v n - g))
          Filter.atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro δ hδ
        filter_upwards [hv_sem 0 (m - q) δ hδ] with n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
        simpa [SchwartzMap.schwartzSeminormFamily_apply] using hn
      have h2 : Tendsto (fun n => SchwartzMap.seminorm ℝ l (m - q) (v n - g))
          Filter.atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro δ hδ
        filter_upwards [hv_sem l (m - q) δ hδ] with n hn
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
        simpa [SchwartzMap.schwartzSeminormFamily_apply] using hn
      simpa using tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul h1).add (tendsto_const_nhds.mul h2))
    have hB_lim : Tendsto (fun n => B₁ n + B₂ n) Filter.atTop (𝓝 0) := by
      simpa using hB₁_lim.add hB₂_lim
    filter_upwards [(tendsto_order.mp hB_lim).2 ε hε] with n hn
    rw [SchwartzMap.schwartzSeminormFamily_apply, sub_zero]
    have h_split : borchersConcatSchwartz j k (u n) (v n) - borchersConcatSchwartz j k f g =
        borchersConcatSchwartz j k (u n - f) (v n) +
          borchersConcatSchwartz j k f (v n - g) := by
      rw [borchersConcatSchwartz_sub_left, borchersConcatSchwartz_sub_right]
      abel
    rw [h_split]
    exact ((map_add_le_add _ _ _).trans
      (add_le_add (seminorm_borchersConcatSchwartz_le j k l m (u n - f) (v n))
        (seminorm_borchersConcatSchwartz_le j k l m f (v n - g)))).trans_lt hn
  simpa using h_diff0.add (tendsto_const_nhds (x := borchersConcatSchwartz j k f g))

theorem exists_fourier_eq_mem_closure_osWavepacketSubmodule (k : ℕ)
    (g : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    ∃ g_cut : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ,
      (∀ q ∈ tailOpenNhd k, minkowskiFourier g_cut q = minkowskiFourier g q) ∧
      g_cut ∈ closure (osWavepacketSubmodule k : Set (SchwartzMap (Fin k → Fin 4 → ℝ) ℂ)) := by
  by_cases hk : 0 < k
  · have hn : ¬ (k + 1 ≤ 1) := by omega
    obtain ⟨f_lift, hf_lift⟩ := exists_zeroSumLift_schwartz k g
    let g_cut : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ :=
      invMinkowskiFourierCLM k
        (pullbackTailSchwartzCLM k (cone_limit_schwartz (k + 1) f_lift))
    refine ⟨g_cut, fun q hq => ?_, ?_⟩
    · dsimp [g_cut]
      rw [minkowskiFourier_invMinkowskiFourierCLM_all, pullbackTailSchwartzCLM_apply,
        cone_limit_schwartz_apply,
        coneSpectralCutoff_eq_one_of_mem_coneOpenNhd (k + 1) hq,
        Complex.ofReal_one, one_mul, hf_lift q]
    · by_contra h_not_cl
      have h_conv : Convex ℝ
          (closure (osWavepacketSubmodule k : Set (SchwartzMap (Fin k → Fin 4 → ℝ) ℂ))) :=
        ((osWavepacketSubmodule k).restrictScalars ℝ).convex.closure
      obtain ⟨φ, u_sep, h_lt_u, h_u_lt⟩ :=
        RCLike.geometric_hahn_banach_point_closed (𝕜 := ℂ) h_conv isClosed_closure h_not_cl
      have hu_neg : u_sep < 0 := by
        have h0_mem : (0 : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) ∈
            closure (osWavepacketSubmodule k : Set _) :=
          subset_closure (Submodule.zero_mem _)
        have h0 := h_u_lt 0 h0_mem
        simpa using h0
      have hφ_van : ∀ y : posOrderedEuclidN k, φ (osWavepacket k y) = 0 := by
        intro y
        by_contra h_ne
        let c : ℂ := ((u_sep - 1 : ℝ) : ℂ) / φ (osWavepacket k y)
        have hc_mem : c • osWavepacket k y ∈ closure (osWavepacketSubmodule k : Set _) :=
          subset_closure (Submodule.smul_mem _ c (Submodule.subset_span ⟨y, rfl⟩))
        have h_ineq := h_u_lt (c • osWavepacket k y) hc_mem
        rw [map_smul, smul_eq_mul] at h_ineq
        have hc_mul : c * φ (osWavepacket k y) = ((u_sep - 1 : ℝ) : ℂ) :=
          div_mul_cancel₀ _ h_ne
        rw [hc_mul] at h_ineq
        change u_sep < (((u_sep - 1 : ℝ) : ℂ)).re at h_ineq
        rw [Complex.ofReal_re] at h_ineq
        linarith
      let T : SchwartzMap (Fin (k + 1) → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
        φ.comp ((invMinkowskiFourierCLM k).comp (pullbackTailSchwartzCLM k))
      have hT_ana : AnalyticOn ℂ (fun w => T (cone_psi_schwartz_total (k + 1) hn w))
          (forward_tube_n (k + 1)) :=
        AnalyticOnNhd.analyticOn fun w hw => cone_psi_schwartz_analyticAt hn hw T
      have hT_euclid : ∀ x ∈ posOrderedEuclidN (k + 1),
          T (cone_psi_schwartz_total (k + 1) hn (wickEmbedN (k + 1) x)) = 0 := by
        intro x hx
        have hx_tube : wickEmbedN (k + 1) x ∈ forward_tube_n (k + 1) :=
          wickEmbedN_mem_forward_tube_n (k + 1) hx.2
        rw [cone_psi_schwartz_total_eq hn hx_tube]
        let y_diff : Fin k → Fin 4 → ℝ := fun u => x (Fin.succ u) - x 0
        have hy_diff : y_diff ∈ posOrderedEuclidN k := by
          refine ⟨fun u => ?_, fun u hu => ?_⟩
          · have hlt := orderedEuclidN_time_lt_of_lt hx.2 (Fin.succ_pos u)
            dsimp [y_diff]
            linarith
          · have hlt := hx.2 (Fin.succ u) (Nat.succ_lt_succ hu)
            have h_idx : (⟨(Fin.succ u).val + 1, Nat.succ_lt_succ hu⟩ : Fin (k + 1)) =
                Fin.succ ⟨u.val + 1, hu⟩ := Fin.ext rfl
            rw [h_idx] at hlt
            change x (Fin.succ u) 0 - x 0 0 < x (Fin.succ ⟨u.val + 1, hu⟩) 0 - x 0 0
            linarith
        have h_pull_eq : pullbackTailSchwartzCLM k
            (cone_psi_schwartz (k + 1) hn (wickEmbedN (k + 1) x) hx_tube) =
            pullbackTailSchwartzCLM k
              (cone_psi_schwartz (k + 1) hn (posTubeExtendCLM k (wickEmbedN k y_diff))
                (wickEmbedN_mem_posTubeN hy_diff)) := by
          ext q
          change cone_psi (k + 1) (wickEmbedN (k + 1) x) (embedZeroSumMomentumCLM k q) =
            cone_psi (k + 1) (posTubeExtendCLM k (wickEmbedN k y_diff))
              (embedZeroSumMomentumCLM k q)
          dsimp [cone_psi]
          congr 1
          rw [vladimirov_kernel_embedZeroSumMomentum,
            vladimirov_kernel_posTubeExtend_embedZeroSumMomentum]
          have h_sub_w : (fun u : Fin k =>
              wickEmbedN (k + 1) x (Fin.succ u) - wickEmbedN (k + 1) x 0) =
              wickEmbedN k y_diff := by
            ext u μ
            by_cases hμ : μ = 0
            · subst hμ
              simp [wickEmbedN, wickEmbed, y_diff]
              ring
            · simp [wickEmbedN, wickEmbed, y_diff, hμ]
          rw [h_sub_w]
        have h_arg_eq : invMinkowskiFourierCLM k (pullbackTailSchwartzCLM k
            (cone_psi_schwartz (k + 1) hn (wickEmbedN (k + 1) x) hx_tube)) =
            osWavepacket k ⟨y_diff, hy_diff⟩ := by
          dsimp [osWavepacket, osToWightmanTest]
          rw [dif_pos hk, h_pull_eq]
        change φ (invMinkowskiFourierCLM k (pullbackTailSchwartzCLM k
          (cone_psi_schwartz (k + 1) hn (wickEmbedN (k + 1) x) hx_tube))) = 0
        rw [h_arg_eq]
        exact hφ_van ⟨y_diff, hy_diff⟩
      have hT_tube : ∀ w ∈ forward_tube_n (k + 1),
          T (cone_psi_schwartz_total (k + 1) hn w) = 0 :=
        analyticOn_forward_tube_eq_zero_of_posOrderedEuclidN_eq_zero (k + 1) hT_ana hT_euclid
      have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
      have h_conv_zero : ∀ (t : ℝ) (ht : 0 < t),
          T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht) = 0 := by
        intro t ht
        rw [clm_conv_schwartz_eq_integral (k + 1) hn T f_lift unit_time_vector hv t ht]
        refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
        dsimp only
        have hw_mem := tubeApproach_mem_forward_tube_n (k + 1) x unit_time_vector hv t ht
        have h0 := hT_tube _ hw_mem
        rw [cone_psi_schwartz_total_eq hn hw_mem] at h0
        rw [h0, mul_zero]
        rfl
      have h_tend : Tendsto (fun t : ℝ =>
          if ht : 0 < t then T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht) else 0)
          (𝓝[>] 0) (𝓝 (T (cone_limit_schwartz (k + 1) f_lift))) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        obtain ⟨s, C_T, hCT_pos, hT_bound⟩ := schwartz_clm_bound (k + 1) T
        have h_each : ∀ km ∈ s, ∀ᶠ t : ℝ in 𝓝[>] 0,
            (if ht : 0 < t then
              (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ km)
                (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht -
                  cone_limit_schwartz (k + 1) f_lift)
            else 0) < ε / C_T := fun km _ =>
          (conv_schwartz_tendsto_limit (k + 1) hn f_lift unit_time_vector hv km).eventually
            (Iio_mem_nhds (div_pos hε hCT_pos))
        filter_upwards [self_mem_nhdsWithin, (Filter.eventually_all_finset s).mpr h_each]
          with t ht h_km
        have ht_pos : 0 < t := ht
        rw [dif_pos ht_pos, dist_eq_norm, ← map_sub]
        have h_sup_lt : (s.sup (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ))
            (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
              cone_limit_schwartz (k + 1) f_lift) < ε / C_T := by
          classical
          have h_sub : ∀ u : Finset (ℕ × ℕ), u ⊆ s →
              (u.sup (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ))
                (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
                  cone_limit_schwartz (k + 1) f_lift) < ε / C_T := by
            intro u
            induction u using Finset.induction_on with
            | empty =>
              intro _
              rw [Finset.sup_empty, Seminorm.bot_eq_zero, _root_.zero_apply]
              exact div_pos hε hCT_pos
            | @insert a u ha ih =>
              intro hu
              rw [Finset.sup_insert, Seminorm.sup_apply]
              have ha_lt := h_km a (hu (Finset.mem_insert_self a u))
              rw [dif_pos ht_pos] at ha_lt
              exact max_lt ha_lt (ih fun km hkm => hu (Finset.mem_insert_of_mem hkm))
          exact h_sub s fun _ h => h
        calc ‖T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
                cone_limit_schwartz (k + 1) f_lift)‖
            ≤ C_T * (s.sup (schwartzSeminormFamily ℝ (Fin (k + 1) → Fin 4 → ℝ) ℂ))
                (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht_pos -
                  cone_limit_schwartz (k + 1) f_lift) := hT_bound _
          _ < C_T * (ε / C_T) := mul_lt_mul_of_pos_left h_sup_lt hCT_pos
          _ = ε := mul_div_cancel₀ ε hCT_pos.ne'
      have h_ev0 : (fun t : ℝ =>
          if ht : 0 < t then
            T (conv_schwartz (k + 1) hn f_lift unit_time_vector hv t ht)
          else 0) = fun _ => (0 : ℂ) := by
        ext t
        split_ifs with ht
        · exact h_conv_zero t ht
        · rfl
      rw [h_ev0] at h_tend
      haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
      have h_lim0 : T (cone_limit_schwartz (k + 1) f_lift) = 0 :=
        tendsto_nhds_unique h_tend tendsto_const_nhds
      have hφ_gcut : φ g_cut = 0 := h_lim0
      rw [hφ_gcut, map_zero] at h_lt_u
      linarith
  · have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨g, fun _ _ => rfl, subset_closure ?_⟩
    have hc_ne : momentumWavepacketSchwartz 0 0 0 ≠ 0 := by
      intro hc
      have h_int := integral_momentumWavepacketSchwartz_zero 0
      have h_fn0 : ∀ x : Fin 0 → Fin 4 → ℝ, momentumWavepacketSchwartz 0 0 x = 0 := fun x => by
        rw [Subsingleton.elim x 0, hc]
      have h_int0 : ∫ x : Fin 0 → Fin 4 → ℝ, momentumWavepacketSchwartz 0 0 x = 0 :=
        MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall h_fn0)
      rw [h_int0] at h_int
      exact zero_ne_one h_int
    let y₀ : posOrderedEuclidN 0 :=
      ⟨euclidOrderedBasePoint 0, euclidOrderedBasePoint_mem_posOrderedEuclidN 0⟩
    have hg_smul : g = (g 0 / momentumWavepacketSchwartz 0 0 0) • osWavepacket 0 y₀ := by
      change g = (g 0 / momentumWavepacketSchwartz 0 0 0) • momentumWavepacketSchwartz 0 0
      ext x
      rw [Subsingleton.elim x 0, _root_.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hc_ne]
    rw [hg_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y₀, rfl⟩)

theorem positivity_of_osAxioms_and_tube
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    {W : WightmanFamily ι} (E : TubeExtension W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    Positivity S W := by
  refine positivity_of_compactPositivity fun N F => ?_
  classical
  let D := hOS.toReflectionPositiveData
  have h_ex : ∀ (j : ℕ) (α : Fin j → ι),
      ∃ (g_cut : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
        (u : ℕ → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ),
        (∀ q ∈ tailOpenNhd j, minkowskiFourier g_cut q = minkowskiFourier (F j α).val q) ∧
        (∀ m : ℕ, u m ∈ osWavepacketSubmodule j) ∧
        Tendsto u Filter.atTop (𝓝 g_cut) := by
    intro j α
    obtain ⟨g_cut, hg_f, hg_cl⟩ := exists_fourier_eq_mem_closure_osWavepacketSubmodule j (F j α).val
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hg_cl
    exact ⟨g_cut, u, hg_f, hu_mem, hu_lim⟩
  let g_cut : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
    fun j α => (h_ex j α).choose
  let u_seq : ∀ j : ℕ, (Fin j → ι) → ℕ → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
    fun j α => (h_ex j α).choose_spec.choose
  have hg_fourier : ∀ (j : ℕ) (α : Fin j → ι) (q : Fin j → Fin 4 → ℝ),
      q ∈ tailOpenNhd j → minkowskiFourier (g_cut j α) q = minkowskiFourier (F j α).val q :=
    fun j α => (h_ex j α).choose_spec.choose_spec.1
  have hu_mem : ∀ (j : ℕ) (α : Fin j → ι) (m : ℕ), u_seq j α m ∈ osWavepacketSubmodule j :=
    fun j α => (h_ex j α).choose_spec.choose_spec.2.1
  have hu_lim : ∀ (j : ℕ) (α : Fin j → ι),
      Tendsto (u_seq j α) Filter.atTop (𝓝 (g_cut j α)) :=
    fun j α => (h_ex j α).choose_spec.choose_spec.2.2
  have h_term_eq : ∀ (j k : ℕ) (γ : Fin (j + k) → ι) (α : Fin j → ι) (α' : Fin k → ι),
      W (j + k) γ (wightmanConcatSchwartz j k (F j α) (F k α')) =
        W (j + k) γ (borchersConcatSchwartz j k (g_cut j α) (g_cut k α')) := by
    intro j k γ α α'
    rw [← borchersConcatSchwartz_eq_wightmanConcatSchwartz]
    let π_L : (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin j → Fin 4 → ℝ) :=
      -(concatProjLeftCLM j k)
    let π_R : (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) :=
      concatProjRightCLM j k
    let U := π_L ⁻¹' tailOpenNhd j ∩ π_R ⁻¹' tailOpenNhd k
    have hU_open : IsOpen U :=
      ((isOpen_tailOpenNhd j).preimage π_L.continuous).inter
        ((isOpen_tailOpenNhd k).preimage π_R.continuous)
    have hU_sub : spectralRegion (j + k) ⊆ U := fun p hp =>
      ⟨spectralRegion_subset_coneOpenNhd (j + 1)
        (embedZeroSumMomentum_left_mem_spectralRegion j k hp),
       spectralRegion_subset_coneOpenNhd (k + 1)
        (embedZeroSumMomentum_right_mem_spectralRegion j k hp)⟩
    refine W_eq_of_fourier_eq W hspec (j + k) γ
      (borchersConcatSchwartz j k (F j α).val (F k α').val)
      (borchersConcatSchwartz j k (g_cut j α) (g_cut k α'))
      U hU_open hU_sub fun p hp => ?_
    rw [minkowskiFourier_borchersProduct_eq j k (F j α).val (F k α').val _
        (borchersConcatSchwartz_apply j k _ _) p,
      minkowskiFourier_borchersProduct_eq j k (g_cut j α) (g_cut k α') _
        (borchersConcatSchwartz_apply j k _ _) p]
    have hL : (fun i => -p (Fin.castAdd k (Fin.rev i))) ∈ tailOpenNhd j := hp.1
    have hR : (fun i => p (Fin.natAdd j i)) ∈ tailOpenNhd k := hp.2
    rw [hg_fourier j α _ hL, hg_fourier k α' _ hR]
  let seq : ℕ → ℂ := fun m =>
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (borchersConcatSchwartz j k (u_seq j α m) (u_seq k α' m))
  let limVal : ℂ :=
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k (F j α) (F k α'))
  have h_tendsto : Tendsto seq Filter.atTop (𝓝 limVal) := by
    refine tendsto_finsetSum _ fun j _ =>
      tendsto_finsetSum _ fun k _ =>
        tendsto_finsetSum _ fun α _ =>
          tendsto_finsetSum _ fun α' _ =>
            tendsto_finsetSum _ fun β _ => ?_
    rw [h_term_eq j k (Fin.append (β ∘ Fin.rev) α') α α']
    have h_cat := tendsto_borchersConcatSchwartz_seq j k (hu_lim j α) (hu_lim k α')
    have h_W := (W (j + k) (Fin.append (β ∘ Fin.rev) α')).continuous.tendsto _ |>.comp h_cat
    exact tendsto_const_nhds.mul h_W
  have h_seq_nonneg : ∀ m : ℕ, 0 ≤ seq m := by
    intro m
    let c_fs : ∀ (j : ℕ) (α : Fin j → ι), posOrderedEuclidN j →₀ ℂ := fun j α =>
      (Finsupp.mem_span_range_iff_exists_finsupp.mp (hu_mem j α m)).choose
    have hc_sum : ∀ (j : ℕ) (α : Fin j → ι),
        (c_fs j α).sum (fun y c => c • osWavepacket j y) = u_seq j α m := fun j α =>
      (Finsupp.mem_span_range_iff_exists_finsupp.mp (hu_mem j α m)).choose_spec
    let cfg : ∀ (j : ℕ), (Fin j → ι) → posOrderedEuclidN j → OSConfig ι :=
      fun j α y => ⟨j, (α, y)⟩
    let Ψ_m : OSPreHilbertSpace D :=
      ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
        ∑ y ∈ (c_fs j α).support, (c_fs j α y) • osBasisPre D (cfg j α y)
    have hΨ_def : Ψ_m = ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
        ∑ y ∈ (c_fs j α).support, (c_fs j α y) • osBasisPre D (cfg j α y) := rfl
    have hseq_def : seq m =
        ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
            (∏ i : Fin j, S.C (α i) (β i)) *
              W (j + k) (Fin.append (β ∘ Fin.rev) α')
                (borchersConcatSchwartz j k (u_seq j α m) (u_seq k α' m)) := rfl
    have h_inner_eq : ⟪Ψ_m, Ψ_m⟫_ℂ = seq m := by
      rw [hΨ_def, hseq_def, sum_inner]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sum_inner]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun α' _ => ?_
      rw [← hc_sum j α, ← hc_sum k α', Finsupp.sum, Finsupp.sum]
      simp_rw [sum_inner, inner_smul_left, inner_sum, inner_smul_right, inner_osBasisPre]
      simp_rw [borchersConcatSchwartz_sum_left, borchersConcatSchwartz_sum_right,
        borchersConcatSchwartz_smul_left, borchersConcatSchwartz_smul_right,
        map_sum, map_smul, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.univ) (t := (c_fs j α).support)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_comm (s := Finset.univ) (t := (c_fs k α').support)]
      refine Finset.sum_congr rfl fun y' _ => ?_
      have h_ker_cfg : osKernel S D.𝒮 (cfg j α y) (cfg k α' y') =
          ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
            D.𝒮 (j + k) (Fin.append (β ∘ Fin.rev) α') (osConcatPoint j k y.val y'.val) := rfl
      rw [h_ker_cfg, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      have h_wp := wightman_borchersConcatSchwartz_osToWightmanTest_eq_schwinger
        R E hspec hP h_schw j k (Fin.append (β ∘ Fin.rev) α') y.property y'.property
      change star (c_fs j α y) * (c_fs k α' y' *
          ((∏ i : Fin j, S.C (α i) (β i)) *
            𝒮 (j + k) (Fin.append (β ∘ Fin.rev) α') (osConcatPoint j k y.val y'.val))) =
        (∏ i : Fin j, S.C (α i) (β i)) *
          (star (c_fs j α y) * (c_fs k α' y' *
            W (j + k) (Fin.append (β ∘ Fin.rev) α')
              (borchersConcatSchwartz j k
                (osToWightmanTest j (wickEmbedN j y.val) (wickEmbedN_mem_posTubeN y.property))
                (osToWightmanTest k (wickEmbedN k y'.val)
                  (wickEmbedN_mem_posTubeN y'.property)))))
      rw [h_wp]
      ring
    have h_re_nn : 0 ≤ (⟪Ψ_m, Ψ_m⟫_ℂ).re := D.positivity Ψ_m.toFinsupp
    have h_im_0 : (⟪Ψ_m, Ψ_m⟫_ℂ).im = 0 := by
      simpa using inner_self_im (𝕜 := ℂ) Ψ_m
    rw [← h_inner_eq]
    exact Complex.nonneg_iff.mpr ⟨h_re_nn, h_im_0.symm⟩
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · exact ge_of_tendsto (Complex.continuous_re.tendsto limVal |>.comp h_tendsto)
      (Filter.Eventually.of_forall fun m => (Complex.nonneg_iff.mp (h_seq_nonneg m)).1)
  · have h_im_seq : Complex.im ∘ seq = fun _ => (0 : ℝ) :=
      funext fun m => ((Complex.nonneg_iff.mp (h_seq_nonneg m)).2).symm
    have h_im_lim := Complex.continuous_im.tendsto limVal |>.comp h_tendsto
    rw [h_im_seq] at h_im_lim
    exact tendsto_nhds_unique tendsto_const_nhds h_im_lim

theorem vladimirovFromTube_positivity
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    {H : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ}
    (h_ana : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n))
    (h_growth : OSTubeGrowthBound H)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = H n α (wickEmbedN n x))
    (hcov : TubeCovariant R (vladimirovFromTubeExtension h_ana h_growth)) :
    Positivity S (vladimirovFromTubeWightmanFamily h_ana h_growth) :=
  positivity_of_osAxioms_and_tube hOS
    (vladimirovFromTubeExtension h_ana h_growth) h_schw
    (vladimirovFromTube_spectrumCondition h_ana h_growth
      (vladimirovFromTube_tubeTranslationInvariant h_ana h_growth 𝒮
        hOS.os1_translation h_schw))
    (vladimirovFromTube_poincareCovariant R h_ana h_growth 𝒮
      hOS.os1_translation h_schw hcov)

structure OSTubeExtensionData (R : HolomorphicLorentzRep ι) (𝒮 : SchwingerFamily ι) where
  H : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ
  analytic : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n)
  growth : OSTubeGrowthBound H
  schwinger_eq : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n → 𝒮 n α x = H n α (wickEmbedN n x)
  tube_covariant : ∀ (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n → spinorPhi (A, sl2c_conj A) • z ∈ forward_tube_n n →
    ∀ α : Fin n → ι,
      H n α (spinorPhi (A, sl2c_conj A) • z) =
        ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * H n β z

namespace OSTubeExtensionData

section

variable {R : HolomorphicLorentzRep ι} {𝒮 : SchwingerFamily ι}

noncomputable def W (T : OSTubeExtensionData R 𝒮) : WightmanFamily ι :=
  vladimirovFromTubeWightmanFamily T.analytic T.growth

noncomputable def E (T : OSTubeExtensionData R 𝒮) : TubeExtension T.W :=
  vladimirovFromTubeExtension T.analytic T.growth

@[simp]
lemma E_H (T : OSTubeExtensionData R 𝒮) : T.E.H = T.H := rfl

theorem schwingerFromTube_eq (T : OSTubeExtensionData R 𝒮)
    (n : ℕ) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    𝒮 n α x = schwingerFromTube T.E n α x :=
  T.schwinger_eq n α x hx

theorem tubeCovariant (T : OSTubeExtensionData R 𝒮) :
    TubeCovariant R T.E :=
  T.tube_covariant

theorem tubeTranslationInvariant (T : OSTubeExtensionData R 𝒮)
    (htrans : OSTranslationInvariant 𝒮) :
    TubeTranslationInvariant T.E :=
  vladimirovFromTube_tubeTranslationInvariant T.analytic T.growth 𝒮 htrans T.schwinger_eq

theorem spectrumCondition (T : OSTubeExtensionData R 𝒮)
    (htrans : OSTranslationInvariant 𝒮) :
    SpectrumCondition T.W :=
  vladimirovFromTube_spectrumCondition T.analytic T.growth
    (T.tubeTranslationInvariant htrans)

theorem poincareCovariant (T : OSTubeExtensionData R 𝒮)
    (htrans : OSTranslationInvariant 𝒮) :
    PoincareCovariant R T.W :=
  vladimirovFromTube_poincareCovariant R T.analytic T.growth 𝒮 htrans
    T.schwinger_eq T.tubeCovariant

theorem tubePCT (T : OSTubeExtensionData R 𝒮) {S : StarStructure R} {η : ℂ}
    (hOS : OSAxioms R S η 𝒮) :
    TubePCT η R T.E :=
  vladimirovFromTube_tubePCT R T.analytic T.growth 𝒮 T.schwinger_eq hOS.os3_symmetry

theorem weakLocality (T : OSTubeExtensionData R 𝒮) {S : StarStructure R} {η : ℂ}
    (hOS : OSAxioms R S η 𝒮) :
    WeakLocality η T.W :=
  vladimirovFromTube_weakLocality R T.analytic T.growth 𝒮
    T.schwinger_eq hOS.os3_symmetry T.tubeCovariant

theorem positivity (T : OSTubeExtensionData R 𝒮) {S : StarStructure R} {η : ℂ}
    (hOS : OSAxioms R S η 𝒮) :
    Positivity S T.W :=
  vladimirovFromTube_positivity hOS T.analytic T.growth T.schwinger_eq T.tubeCovariant

noncomputable def toForwardConeOSEuclideanTubeBridge (T : OSTubeExtensionData R 𝒮)
    {S : StarStructure R} {η : ℂ} (hOS : OSAxioms R S η 𝒮) :
    ForwardConeOSEuclideanTubeBridge R S η 𝒮 :=
  ForwardConeOSEuclideanTubeBridge.ofOSAxiomsTube hOS T.W T.E
    (fun n α _ hx => T.schwingerFromTube_eq n α hx)
    T.tubeCovariant
    (T.spectrumCondition hOS.os1_translation)
    (T.weakLocality hOS)
    (T.positivity hOS)

noncomputable def toForwardConeOSReconstructedWightman (T : OSTubeExtensionData R 𝒮)
    {S : StarStructure R} {η : ℂ} (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    ForwardConeOSReconstructedWightman R S η 𝒮 :=
  forwardConeOSReconstructedWightmanOfBridge R S η 𝒮 hOS hcluster
    (T.toForwardConeOSEuclideanTubeBridge hOS)

noncomputable def toForwardConeOSReconstructedWightmanOfDiagonalBounded
    (T : OSTubeExtensionData R 𝒮)
    {S : StarStructure R} {η : ℂ} (hOS : OSAxioms R S η 𝒮)
    (hdiag : OSDiagonalKernelBounded S 𝒮) :
    ForwardConeOSReconstructedWightman R S η 𝒮 :=
  forwardConeOSReconstructedWightmanOfDiagonalBoundedBridge R S η 𝒮 hOS hdiag
    (T.toForwardConeOSEuclideanTubeBridge hOS)

noncomputable def toWightmanAxioms (T : OSTubeExtensionData R 𝒮)
    {S : StarStructure R} {η : ℂ} (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    WightmanAxioms R S η :=
  (T.toForwardConeOSReconstructedWightman hOS hcluster).toWightmanAxioms

noncomputable def toGeneralWightmanAxiomsWithUniqueVacuum (T : OSTubeExtensionData R 𝒮)
    {S : StarStructure R} {η : ℂ} (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hnorm : OSVacuumNormalized 𝒮) :
    GeneralWightmanAxiomsWithUniqueVacuum R S η :=
  generalWightmanAxiomsWithUniqueVacuumOfBridge hOS hcluster hnorm
    (T.toForwardConeOSEuclideanTubeBridge hOS)

noncomputable def osToWightmanUnitaryEquiv (T : OSTubeExtensionData R 𝒮)
    {S : StarStructure R} {η : ℂ} (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    (T.toForwardConeOSReconstructedWightman hOS hcluster).Hilbert ≃ₗᵢ[ℂ]
      (T.toForwardConeOSReconstructedWightman hOS hcluster).WightmanHilbertSpace :=
  (T.toForwardConeOSReconstructedWightman hOS hcluster).osToWightmanLinearIsometryEquiv

end

end OSTubeExtensionData

def vacOSTubeExtensionData (R : HolomorphicLorentzRep ι) :
    OSTubeExtensionData R (vacS (ι := ι)) where
  H := vacH
  analytic n α := (vacTubeExtension (ι := ι)).analytic n α
  growth n α := by
    refine ⟨1, 0, 0, zero_le_one, fun z _ => ?_⟩
    cases n with
    | zero => simp [vacH_zero]
    | succ m => simp [vacH_succ]
  schwinger_eq n α x _ := by
    cases n <;> rfl
  tube_covariant := vacTubeCovariant R

def PositivityUpTo (N₀ : ℕ) {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) : Prop :=
  ∀ (N : ℕ), N ≤ N₀ →
  ∀ (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) → SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ),
    (∀ j k α α' x,
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i))) →
    0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')

theorem positivityUpTo_of_osAxioms_and_tube
    (N₀ : ℕ) {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    {W : WightmanFamily ι} (E : TubeExtension W)
    (h_schw : ∀ (n : ℕ), n ≤ 2 * N₀ → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    PositivityUpTo N₀ S W := by
  intro N hN F_in G_in hG_in
  have hcpos_N : ∀ F : ∀ j : ℕ, (Fin j → ι) →
      { f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ //
        HasCompactSupport (f : (Fin j → Fin 4 → ℝ) → ℂ) },
      0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i : Fin j, S.C (α i) (β i)) *
            W (j + k) (Fin.append (β ∘ Fin.rev) α')
              (wightmanConcatSchwartz j k (F j α) (F k α')) := by
    intro F
    classical
    let D := hOS.toReflectionPositiveData
    have h_ex : ∀ (j : ℕ) (α : Fin j → ι),
        ∃ (g_cut : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
          (u : ℕ → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ),
          (∀ q ∈ tailOpenNhd j, minkowskiFourier g_cut q = minkowskiFourier (F j α).val q) ∧
          (∀ m : ℕ, u m ∈ osWavepacketSubmodule j) ∧
          Tendsto u Filter.atTop (𝓝 g_cut) := by
      intro j α
      obtain ⟨g_cut, hg_f, hg_cl⟩ :=
        exists_fourier_eq_mem_closure_osWavepacketSubmodule j (F j α).val
      obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp hg_cl
      exact ⟨g_cut, u, hg_f, hu_mem, hu_lim⟩
    let g_cut : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
      fun j α => (h_ex j α).choose
    let u_seq : ∀ j : ℕ, (Fin j → ι) → ℕ → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
      fun j α => (h_ex j α).choose_spec.choose
    have hg_fourier : ∀ (j : ℕ) (α : Fin j → ι) (q : Fin j → Fin 4 → ℝ),
        q ∈ tailOpenNhd j → minkowskiFourier (g_cut j α) q = minkowskiFourier (F j α).val q :=
      fun j α => (h_ex j α).choose_spec.choose_spec.1
    have hu_mem : ∀ (j : ℕ) (α : Fin j → ι) (m : ℕ), u_seq j α m ∈ osWavepacketSubmodule j :=
      fun j α => (h_ex j α).choose_spec.choose_spec.2.1
    have hu_lim : ∀ (j : ℕ) (α : Fin j → ι),
        Tendsto (u_seq j α) Filter.atTop (𝓝 (g_cut j α)) :=
      fun j α => (h_ex j α).choose_spec.choose_spec.2.2
    have h_term_eq : ∀ (j k : ℕ) (γ : Fin (j + k) → ι) (α : Fin j → ι) (α' : Fin k → ι),
        W (j + k) γ (wightmanConcatSchwartz j k (F j α) (F k α')) =
          W (j + k) γ (borchersConcatSchwartz j k (g_cut j α) (g_cut k α')) := by
      intro j k γ α α'
      rw [← borchersConcatSchwartz_eq_wightmanConcatSchwartz]
      let π_L : (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin j → Fin 4 → ℝ) :=
        -(concatProjLeftCLM j k)
      let π_R : (Fin (j + k) → Fin 4 → ℝ) →L[ℝ] (Fin k → Fin 4 → ℝ) :=
        concatProjRightCLM j k
      let U := π_L ⁻¹' tailOpenNhd j ∩ π_R ⁻¹' tailOpenNhd k
      have hU_open : IsOpen U :=
        ((isOpen_tailOpenNhd j).preimage π_L.continuous).inter
          ((isOpen_tailOpenNhd k).preimage π_R.continuous)
      have hU_sub : spectralRegion (j + k) ⊆ U := fun p hp =>
        ⟨spectralRegion_subset_coneOpenNhd (j + 1)
          (embedZeroSumMomentum_left_mem_spectralRegion j k hp),
         spectralRegion_subset_coneOpenNhd (k + 1)
          (embedZeroSumMomentum_right_mem_spectralRegion j k hp)⟩
      refine W_eq_of_fourier_eq W hspec (j + k) γ
        (borchersConcatSchwartz j k (F j α).val (F k α').val)
        (borchersConcatSchwartz j k (g_cut j α) (g_cut k α'))
        U hU_open hU_sub fun p hp => ?_
      rw [minkowskiFourier_borchersProduct_eq j k (F j α).val (F k α').val _
          (borchersConcatSchwartz_apply j k _ _) p,
        minkowskiFourier_borchersProduct_eq j k (g_cut j α) (g_cut k α') _
          (borchersConcatSchwartz_apply j k _ _) p]
      have hL : (fun i => -p (Fin.castAdd k (Fin.rev i))) ∈ tailOpenNhd j := hp.1
      have hR : (fun i => p (Fin.natAdd j i)) ∈ tailOpenNhd k := hp.2
      rw [hg_fourier j α _ hL, hg_fourier k α' _ hR]
    let seq : ℕ → ℂ := fun m =>
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i : Fin j, S.C (α i) (β i)) *
            W (j + k) (Fin.append (β ∘ Fin.rev) α')
              (borchersConcatSchwartz j k (u_seq j α m) (u_seq k α' m))
    let limVal : ℂ :=
      ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i : Fin j, S.C (α i) (β i)) *
            W (j + k) (Fin.append (β ∘ Fin.rev) α')
              (wightmanConcatSchwartz j k (F j α) (F k α'))
    have h_tendsto : Tendsto seq Filter.atTop (𝓝 limVal) := by
      refine tendsto_finsetSum _ fun j _ =>
        tendsto_finsetSum _ fun k _ =>
          tendsto_finsetSum _ fun α _ =>
            tendsto_finsetSum _ fun α' _ =>
              tendsto_finsetSum _ fun β _ => ?_
      rw [h_term_eq j k (Fin.append (β ∘ Fin.rev) α') α α']
      have h_cat := tendsto_borchersConcatSchwartz_seq j k (hu_lim j α) (hu_lim k α')
      have h_W := (W (j + k) (Fin.append (β ∘ Fin.rev) α')).continuous.tendsto _ |>.comp h_cat
      exact tendsto_const_nhds.mul h_W
    have h_seq_nonneg : ∀ m : ℕ, 0 ≤ seq m := by
      intro m
      let c_fs : ∀ (j : ℕ) (α : Fin j → ι), posOrderedEuclidN j →₀ ℂ := fun j α =>
        (Finsupp.mem_span_range_iff_exists_finsupp.mp (hu_mem j α m)).choose
      have hc_sum : ∀ (j : ℕ) (α : Fin j → ι),
          (c_fs j α).sum (fun y c => c • osWavepacket j y) = u_seq j α m := fun j α =>
        (Finsupp.mem_span_range_iff_exists_finsupp.mp (hu_mem j α m)).choose_spec
      let cfg : ∀ (j : ℕ), (Fin j → ι) → posOrderedEuclidN j → OSConfig ι :=
        fun j α y => ⟨j, (α, y)⟩
      let Ψ_m : OSPreHilbertSpace D :=
        ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
          ∑ y ∈ (c_fs j α).support, (c_fs j α y) • osBasisPre D (cfg j α y)
      have hΨ_def : Ψ_m = ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
          ∑ y ∈ (c_fs j α).support, (c_fs j α y) • osBasisPre D (cfg j α y) := rfl
      have hseq_def : seq m =
          ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
            ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
              (∏ i : Fin j, S.C (α i) (β i)) *
                W (j + k) (Fin.append (β ∘ Fin.rev) α')
                  (borchersConcatSchwartz j k (u_seq j α m) (u_seq k α' m)) := rfl
      have h_inner_eq : ⟪Ψ_m, Ψ_m⟫_ℂ = seq m := by
        rw [hΨ_def, hseq_def, sum_inner]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [inner_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hjk_le : j + k ≤ 2 * N₀ := by
          have hj_lt := Finset.mem_range.mp hj
          have hk_lt := Finset.mem_range.mp hk
          omega
        rw [sum_inner]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [inner_sum]
        refine Finset.sum_congr rfl fun α' _ => ?_
        rw [← hc_sum j α, ← hc_sum k α', Finsupp.sum, Finsupp.sum]
        simp_rw [sum_inner, inner_smul_left, inner_sum, inner_smul_right, inner_osBasisPre]
        simp_rw [borchersConcatSchwartz_sum_left, borchersConcatSchwartz_sum_right,
          borchersConcatSchwartz_smul_left, borchersConcatSchwartz_smul_right,
          map_sum, map_smul, smul_eq_mul]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm (s := Finset.univ) (t := (c_fs j α).support)]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm (s := Finset.univ) (t := (c_fs k α').support)]
        refine Finset.sum_congr rfl fun y' _ => ?_
        have h_ker_cfg : osKernel S D.𝒮 (cfg j α y) (cfg k α' y') =
            ∑ β : Fin j → ι, (∏ i : Fin j, S.C (α i) (β i)) *
              D.𝒮 (j + k) (Fin.append (β ∘ Fin.rev) α') (osConcatPoint j k y.val y'.val) := rfl
        rw [h_ker_cfg, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        have h_wp := wightman_borchersConcatSchwartz_osToWightmanTest_eq_schwinger
          R E hspec hP (fun _ _ _ _ => rfl) j k (Fin.append (β ∘ Fin.rev) α')
          y.property y'.property
        have h_ord := osConcatPoint_mem_orderedEuclidN j k y.property y'.property
        rw [← h_schw (j + k) hjk_le (Fin.append (β ∘ Fin.rev) α') _ h_ord] at h_wp
        change star (c_fs j α y) * (c_fs k α' y' *
            ((∏ i : Fin j, S.C (α i) (β i)) *
              𝒮 (j + k) (Fin.append (β ∘ Fin.rev) α') (osConcatPoint j k y.val y'.val))) =
          (∏ i : Fin j, S.C (α i) (β i)) *
            (star (c_fs j α y) * (c_fs k α' y' *
              W (j + k) (Fin.append (β ∘ Fin.rev) α')
                (borchersConcatSchwartz j k
                  (osToWightmanTest j (wickEmbedN j y.val) (wickEmbedN_mem_posTubeN y.property))
                  (osToWightmanTest k (wickEmbedN k y'.val)
                    (wickEmbedN_mem_posTubeN y'.property)))))
        rw [h_wp]
        ring
      have h_re_nn : 0 ≤ (⟪Ψ_m, Ψ_m⟫_ℂ).re := D.positivity Ψ_m.toFinsupp
      have h_im_0 : (⟪Ψ_m, Ψ_m⟫_ℂ).im = 0 := by
        simpa using inner_self_im (𝕜 := ℂ) Ψ_m
      rw [← h_inner_eq]
      exact Complex.nonneg_iff.mpr ⟨h_re_nn, h_im_0.symm⟩
    rw [Complex.nonneg_iff]
    refine ⟨?_, ?_⟩
    · exact ge_of_tendsto (Complex.continuous_re.tendsto limVal |>.comp h_tendsto)
        (Filter.Eventually.of_forall fun m => (Complex.nonneg_iff.mp (h_seq_nonneg m)).1)
    · have h_im_seq : Complex.im ∘ seq = fun _ => (0 : ℝ) :=
        funext fun m => ((Complex.nonneg_iff.mp (h_seq_nonneg m)).2).symm
      have h_im_lim := Complex.continuous_im.tendsto limVal |>.comp h_tendsto
      rw [h_im_seq] at h_im_lim
      exact tendsto_nhds_unique tendsto_const_nhds h_im_lim
  let seq_cut : ℕ → ℂ := fun m =>
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α')
            (wightmanConcatSchwartz j k
              (compactCutoff j (F_in j α) m) (compactCutoff k (F_in k α') m))
  let lim_cut : ℂ :=
    ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G_in j k α α')
  have h_tend_cut : Tendsto seq_cut Filter.atTop (𝓝 lim_cut) := by
    refine tendsto_finsetSum _ fun j _ =>
      tendsto_finsetSum _ fun k _ =>
        tendsto_finsetSum _ fun α _ =>
          tendsto_finsetSum _ fun α' _ =>
            tendsto_finsetSum _ fun β _ => ?_
    have h_cat := tendsto_wightmanConcatSchwartz_compactCutoff j k
      (F_in j α) (F_in k α') (G_in j k α α') (hG_in j k α α')
    have h_W := (W (j + k) (Fin.append (β ∘ Fin.rev) α')).continuous.tendsto
      (G_in j k α α') |>.comp h_cat
    exact tendsto_const_nhds.mul h_W
  have h_nn_cut : ∀ m : ℕ, 0 ≤ seq_cut m := fun m =>
    hcpos_N (fun j α => compactCutoff j (F_in j α) m)
  rw [Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · exact ge_of_tendsto (Complex.continuous_re.tendsto lim_cut |>.comp h_tend_cut)
      (Filter.Eventually.of_forall fun m => (Complex.nonneg_iff.mp (h_nn_cut m)).1)
  · have h_im_seq : Complex.im ∘ seq_cut = fun _ => (0 : ℝ) :=
      funext fun m => ((Complex.nonneg_iff.mp (h_nn_cut m)).2).symm
    have h_im_lim := Complex.continuous_im.tendsto lim_cut |>.comp h_tend_cut
    rw [h_im_seq] at h_im_lim
    exact tendsto_nhds_unique tendsto_const_nhds h_im_lim

private def sl2cPairEntrySum (p : SL2C × SL2C) : ℝ :=
  ∑ r : Fin 2, ∑ s : Fin 2, (‖p.1.1 r s‖ + ‖p.2.1 r s‖)

private lemma sl2cPairEntrySum_nonneg (p : SL2C × SL2C) : 0 ≤ sl2cPairEntrySum p :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (norm_nonneg _) (norm_nonneg _)

private lemma norm_polyPt_le_one_add_sl2cPairEntrySum (p : SL2C × SL2C) (v : PolyVar) :
    ‖polyPt p v‖ ≤ 1 + sl2cPairEntrySum p := by
  rcases v with ⟨r, s⟩ | ⟨r, s⟩
  · have h1 : ‖p.1.1 r s‖ ≤ ‖p.1.1 r s‖ + ‖p.2.1 r s‖ :=
      le_add_of_nonneg_right (norm_nonneg _)
    have h2 : ‖p.1.1 r s‖ + ‖p.2.1 r s‖ ≤ ∑ s' : Fin 2, (‖p.1.1 r s'‖ + ‖p.2.1 r s'‖) :=
      Finset.single_le_sum (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_univ s)
    have h3 : (∑ s' : Fin 2, (‖p.1.1 r s'‖ + ‖p.2.1 r s'‖)) ≤ sl2cPairEntrySum p :=
      Finset.single_le_sum
        (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_univ r)
    change ‖p.1.1 r s‖ ≤ 1 + sl2cPairEntrySum p
    linarith
  · have h1 : ‖p.2.1 r s‖ ≤ ‖p.1.1 r s‖ + ‖p.2.1 r s‖ :=
      le_add_of_nonneg_left (norm_nonneg _)
    have h2 : ‖p.1.1 r s‖ + ‖p.2.1 r s‖ ≤ ∑ s' : Fin 2, (‖p.1.1 r s'‖ + ‖p.2.1 r s'‖) :=
      Finset.single_le_sum (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_univ s)
    have h3 : (∑ s' : Fin 2, (‖p.1.1 r s'‖ + ‖p.2.1 r s'‖)) ≤ sl2cPairEntrySum p :=
      Finset.single_le_sum
        (fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_univ r)
    change ‖p.2.1 r s‖ ≤ 1 + sl2cPairEntrySum p
    linarith

private lemma norm_mvPolynomial_eval_polyPt_le (P : MvPolynomial PolyVar ℂ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧
      ∀ p : SL2C × SL2C, ‖MvPolynomial.eval (polyPt p) P‖ ≤ C * (1 + sl2cPairEntrySum p) ^ K := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨‖a‖, 0, norm_nonneg a, fun p => ?_⟩
    simp
  | add P Q ihP ihQ =>
    rcases ihP with ⟨CP, KP, hCP, hP⟩
    rcases ihQ with ⟨CQ, KQ, hCQ, hQ⟩
    refine ⟨CP + CQ, max KP KQ, add_nonneg hCP hCQ, fun p => ?_⟩
    have hb1 : 1 ≤ 1 + sl2cPairEntrySum p := by linarith [sl2cPairEntrySum_nonneg p]
    have hKP : (1 + sl2cPairEntrySum p) ^ KP ≤ (1 + sl2cPairEntrySum p) ^ max KP KQ :=
      pow_le_pow_right₀ hb1 (le_max_left KP KQ)
    have hKQ : (1 + sl2cPairEntrySum p) ^ KQ ≤ (1 + sl2cPairEntrySum p) ^ max KP KQ :=
      pow_le_pow_right₀ hb1 (le_max_right KP KQ)
    rw [map_add]
    calc ‖MvPolynomial.eval (polyPt p) P + MvPolynomial.eval (polyPt p) Q‖
        ≤ ‖MvPolynomial.eval (polyPt p) P‖ + ‖MvPolynomial.eval (polyPt p) Q‖ := norm_add_le _ _
      _ ≤ CP * (1 + sl2cPairEntrySum p) ^ max KP KQ +
            CQ * (1 + sl2cPairEntrySum p) ^ max KP KQ :=
          add_le_add
            ((hP p).trans (mul_le_mul_of_nonneg_left hKP hCP))
            ((hQ p).trans (mul_le_mul_of_nonneg_left hKQ hCQ))
      _ = (CP + CQ) * (1 + sl2cPairEntrySum p) ^ max KP KQ := by ring
  | mul_X P v ihP =>
    rcases ihP with ⟨CP, KP, hCP, hP⟩
    refine ⟨CP, KP + 1, hCP, fun p => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (hP p) (norm_polyPt_le_one_add_sl2cPairEntrySum p v) (norm_nonneg _)
      (mul_nonneg hCP (pow_nonneg (by linarith [sl2cPairEntrySum_nonneg p]) KP))

private lemma continuous_isPoly {f : SL2C × SL2C → ℂ} (hf : IsPoly f) : Continuous f := by
  rcases hf with ⟨P, hP⟩
  suffices h : ∀ Q : MvPolynomial PolyVar ℂ, Continuous fun p => MvPolynomial.eval (polyPt p) Q by
    rw [funext hP]
    exact h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact continuous_const
  | add Q₁ Q₂ ih₁ ih₂ =>
    have h_eq : (fun p => MvPolynomial.eval (polyPt p) (Q₁ + Q₂)) =
        (fun p => MvPolynomial.eval (polyPt p) Q₁) +
          (fun p => MvPolynomial.eval (polyPt p) Q₂) :=
      funext fun p => map_add _ Q₁ Q₂
    rw [h_eq]
    exact ih₁.add ih₂
  | mul_X Q₁ v ih₁ =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine ih₁.mul ?_
    rcases v with ⟨r, s⟩ | ⟨r, s⟩
    · exact (continuous_apply s).comp ((continuous_apply r).comp
        (continuous_subtype_val.comp continuous_fst))
    · exact (continuous_apply s).comp ((continuous_apply r).comp
        (continuous_subtype_val.comp continuous_snd))

private lemma differentiable_isPoly_comp {f : SL2C × SL2C → ℂ} (hf : IsPoly f)
    {g : ℂ → SL2C × SL2C}
    (hg1 : ∀ r s : Fin 2, Differentiable ℂ fun z : ℂ => (g z).1.1 r s)
    (hg2 : ∀ r s : Fin 2, Differentiable ℂ fun z : ℂ => (g z).2.1 r s) :
    Differentiable ℂ fun z : ℂ => f (g z) := by
  rcases hf with ⟨P, hP⟩
  suffices h : ∀ Q : MvPolynomial PolyVar ℂ,
      Differentiable ℂ fun z : ℂ => MvPolynomial.eval (polyPt (g z)) Q by
    rw [funext fun z => hP (g z)]
    exact h P
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact differentiable_const a
  | add Q₁ Q₂ ih₁ ih₂ =>
    have h_eq : (fun z => MvPolynomial.eval (polyPt (g z)) (Q₁ + Q₂)) =
        (fun z => MvPolynomial.eval (polyPt (g z)) Q₁) +
          (fun z => MvPolynomial.eval (polyPt (g z)) Q₂) :=
      funext fun z => map_add _ Q₁ Q₂
    rw [h_eq]
    exact ih₁.add ih₂
  | mul_X Q₁ v ih₁ =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine ih₁.mul ?_
    rcases v with ⟨r, s⟩ | ⟨r, s⟩
    · exact hg1 r s
    · exact hg2 r s

def contragredientSL2C : SL2C →* SL2C where
  toFun B := ⟨(B⁻¹).1ᵀ, by rw [Matrix.det_transpose, (B⁻¹).2]⟩
  map_one' := by
    apply Subtype.ext
    change ((1 : SL2C)⁻¹).1ᵀ = 1
    rw [inv_one]
    exact Matrix.transpose_one
  map_mul' A B := by
    apply Subtype.ext
    change ((A * B)⁻¹).1ᵀ = (A⁻¹).1ᵀ * (B⁻¹).1ᵀ
    rw [_root_.mul_inv_rev]
    exact Matrix.transpose_mul (B⁻¹).1 (A⁻¹).1

lemma contragredientSL2C_entries (B : SL2C) :
    (contragredientSL2C B).1 0 0 = B.1 1 1 ∧
    (contragredientSL2C B).1 0 1 = -B.1 1 0 ∧
    (contragredientSL2C B).1 1 0 = -B.1 0 1 ∧
    (contragredientSL2C B).1 1 1 = B.1 0 0 := by
  simp [contragredientSL2C, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

@[simp]
lemma contragredientSL2C_involutive (B : SL2C) :
    contragredientSL2C (contragredientSL2C B) = B := by
  ext i j
  have h1 := contragredientSL2C_entries (contragredientSL2C B)
  have h2 := contragredientSL2C_entries B
  fin_cases i <;> fin_cases j <;> simp [h1, h2]

@[simp]
lemma contragredientSL2C_val_transpose (B : SL2C) :
    (contragredientSL2C B).1ᵀ = (B⁻¹).1 :=
  Matrix.transpose_transpose (B⁻¹).1

lemma contragredientSL2C_su2ToSL2C (U : SU2) :
    contragredientSL2C (su2ToSL2C U) = su2ToSL2C (su2Conj U) := by
  have h_inv : (su2ToSL2C U)⁻¹ = su2ToSL2C U⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    ext i j
    change ((su2ToSL2C U).1 * (su2ToSL2C U⁻¹).1) i j = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j
    have hU : U.val * (U⁻¹).val = 1 := congrArg Subtype.val (mul_inv_cancel U)
    exact congrFun (congrFun hU i) j
  ext i j
  change ((su2ToSL2C U)⁻¹).1ᵀ i j = (su2Conj U).val i j
  rw [h_inv]
  rfl

private lemma convex_re_gt (a : ℝ) : Convex ℝ { s : ℂ | a < s.re } := by
  intro x hx y hy u v hu hv huv
  change a < (u • x + v • y).re
  change a < x.re at hx
  change a < y.re at hy
  rcases eq_or_lt_of_le hu with rfl | hu_pos
  · have hv1 : v = 1 := by linarith
    rw [hv1, zero_smul, one_smul, zero_add]
    exact hy
  · have h1 : u * a < u * x.re := mul_lt_mul_of_pos_left hx hu_pos
    have h2 : v * a ≤ v * y.re := mul_le_mul_of_nonneg_left hy.le hv
    have ha : u * a + v * a = a := by linear_combination a * huv
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    linarith

private lemma eq_on_re_gt_of_real_gt_eq {a : ℝ} {f₁ f₂ : ℂ → ℂ}
    (hf₁ : DifferentiableOn ℂ f₁ { s : ℂ | a < s.re })
    (hf₂ : DifferentiableOn ℂ f₂ { s : ℂ | a < s.re })
    (h_real : ∀ t : ℝ, a < t → f₁ (t : ℂ) = f₂ (t : ℂ)) :
    ∀ s : ℂ, a < s.re → f₁ s = f₂ s := by
  let U : Set ℂ := { s : ℂ | a < s.re }
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_pre : IsPreconnected U := (convex_re_gt a).isPreconnected
  let g : ℂ → ℂ := fun s => f₁ s - f₂ s
  have hg_ana : AnalyticOnNhd ℂ g U :=
    hU_open.analyticOn_iff_analyticOnNhd.mp ((hf₁.sub hf₂).analyticOn hU_open)
  let s₀ : ℂ := ((a + 1 : ℝ) : ℂ)
  have hs₀_mem : s₀ ∈ U := by
    change a < (((a + 1 : ℝ) : ℂ)).re
    simp
  let w_seq : ℕ → ℂ := fun n => ((a + 1 + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)
  have hw_lim : Tendsto w_seq Filter.atTop (𝓝 s₀) := by
    have h_inv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have h_r : Tendsto (fun n : ℕ => a + 1 + ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 (a + 1)) := by
      simpa using (tendsto_const_nhds (x := a + 1)).add h_inv
    exact (Complex.continuous_ofReal.tendsto (a + 1)).comp h_r
  have hw_ne : ∀ n : ℕ, w_seq n ≠ s₀ := by
    intro n heq
    have hre := congrArg Complex.re heq
    dsimp [w_seq, s₀] at hre
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hw_nhds : Tendsto w_seq Filter.atTop (𝓝[≠] s₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hw_lim, Filter.Eventually.of_forall hw_ne⟩
  have hw_zero : ∀ n : ℕ, g (w_seq n) = 0 := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    dsimp [g, w_seq]
    exact sub_eq_zero.mpr (h_real (a + 1 + ((n : ℝ) + 1)⁻¹) (by linarith))
  have h_freq : ∃ᶠ w in 𝓝[≠] s₀, g w = 0 :=
    hw_nhds.frequently (Filter.Eventually.of_forall hw_zero).frequently
  have h_eq0 := hg_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero hU_pre hs₀_mem h_freq
  intro s hs
  exact sub_eq_zero.mp (h_eq0 hs)

private lemma eq_zero_of_differentiable_and_real_eq_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h_real : ∀ t : ℝ, f (t : ℂ) = 0) :
    ∀ z : ℂ, f z = 0 := by
  have hf_ana : AnalyticOnNhd ℂ f Set.univ :=
    isOpen_univ.analyticOn_iff_analyticOnNhd.mp (hf.differentiableOn.analyticOn isOpen_univ)
  have h_half : ∀ s : ℂ, -1 < s.re → f s = 0 :=
    eq_on_re_gt_of_real_gt_eq hf.differentiableOn (differentiableOn_const 0)
      (fun t _ => h_real t)
  have h_ev : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    have h_m1 : (-1 : ℝ) < (0 : ℂ).re := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h_m1] with s hs
    exact h_half s hs
  intro z
  exact hf_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ (0 : ℂ)) h_ev (Set.mem_univ z)

private def su2ExpDiag (t : ℝ) : SU2 :=
  ⟨!![Complex.exp (Complex.I * (t : ℂ)), 0; 0, Complex.exp (-Complex.I * (t : ℂ))], by
    let e₁ : ℂ := Complex.exp (Complex.I * (t : ℂ))
    let e₂ : ℂ := Complex.exp (-Complex.I * (t : ℂ))
    have h_conj1 : star e₁ = e₂ := by
      change (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ))) = _
      rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    have h_conj2 : star e₂ = e₁ := by
      change (starRingEnd ℂ) (Complex.exp (-Complex.I * (t : ℂ))) = _
      rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_I, neg_neg, Complex.conj_ofReal]
    have h_prod1 : e₁ * e₂ = 1 := by
      dsimp [e₁, e₂]
      rw [← Complex.exp_add]
      have h0 : Complex.I * (t : ℂ) + -Complex.I * (t : ℂ) = 0 := by ring
      rw [h0, Complex.exp_zero]
    have h_prod2 : e₂ * e₁ = 1 := by rw [mul_comm, h_prod1]
    change !![e₁, 0; 0, e₂] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> dsimp only
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change e₁ * star e₁ + 0 * star 0 = 1
        rw [h_conj1, h_prod1, zero_mul, add_zero]
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change e₁ * star 0 + 0 * star e₂ = 0
        simp
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change 0 * star e₁ + e₂ * star 0 = 0
        simp
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change 0 * star 0 + e₂ * star e₂ = 1
        rw [h_conj2, h_prod2, zero_mul, zero_add]
    · rw [Matrix.det_fin_two]
      change e₁ * e₂ - 0 * 0 = 1
      rw [h_prod1]
      ring⟩

private def su2RotReal (θ : ℝ) : SU2 :=
  ⟨!![(Real.cos θ : ℂ), -(Real.sin θ : ℂ); (Real.sin θ : ℂ), (Real.cos θ : ℂ)], by
    let c : ℂ := (Real.cos θ : ℂ)
    let s : ℂ := (Real.sin θ : ℂ)
    have hc_star : star c = c := Complex.conj_ofReal _
    have hs_star : star s = s := Complex.conj_ofReal _
    have h_cs : c * c + s * s = 1 := by
      dsimp [c, s]
      norm_cast
      simpa [sq] using Real.cos_sq_add_sin_sq θ
    change !![c, -s; s, c] ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> dsimp only
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change c * star c + (-s) * star (-s) = 1
        rw [star_neg, hc_star, hs_star]
        linear_combination h_cs
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change c * star s + (-s) * star c = 0
        rw [hc_star, hs_star]
        ring
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change s * star c + c * star (-s) = 0
        rw [star_neg, hc_star, hs_star]
        ring
      · rw [Matrix.mul_apply, Fin.sum_univ_two]
        change s * star s + c * star c = 1
        rw [hc_star, hs_star]
        linear_combination h_cs
    · rw [Matrix.det_fin_two]
      change c * c - (-s) * s = 1
      linear_combination h_cs⟩

private def sl2cExpDiag (z : ℂ) : SL2C :=
  ⟨!![Complex.exp (Complex.I * z), 0; 0, Complex.exp (-Complex.I * z)], by
    simp [Matrix.det_fin_two, ← Complex.exp_add]⟩

private def sl2cDiag (a : ℂ) (ha : a ≠ 0) : SL2C :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, mul_inv_cancel₀ ha]⟩

private def sl2cUpper (z : ℂ) : SL2C :=
  ⟨!![1, z; 0, 1], by simp [Matrix.det_fin_two]⟩

private def sl2cLower (z : ℂ) : SL2C :=
  ⟨!![1, 0; z, 1], by simp [Matrix.det_fin_two]⟩

private theorem su2_to_sl2c_stabilizer_lift {J : Type*} [Fintype J] [DecidableEq J]
    (Φ : SL2C →* Matrix J J ℂ)
    (h_cont : ∀ i j : J, Continuous fun B : SL2C => Φ B i j)
    (h_holo : ∀ γ : ℂ → SL2C,
      (∀ r s : Fin 2, Differentiable ℂ fun z : ℂ => (γ z).1 r s) →
      ∀ i j : J, Differentiable ℂ fun z : ℂ => Φ (γ z) i j)
    {v : J → ℂ} (h_su2 : ∀ U : SU2, Φ (su2ToSL2C U) *ᵥ v = v) :
    ∀ B : SL2C, Φ B *ᵥ v = v := by
  let H_set : Set SL2C := { B : SL2C | Φ B *ᵥ v = v }
  have h_mul : ∀ {B₁ B₂ : SL2C}, B₁ ∈ H_set → B₂ ∈ H_set → B₁ * B₂ ∈ H_set := by
    intro B₁ B₂ h₁ h₂
    change Φ (B₁ * B₂) *ᵥ v = v
    rw [map_mul, ← Matrix.mulVec_mulVec, h₂, h₁]
  have h_closed : IsClosed H_set := by
    have h_eq_set : H_set = ⋂ i : J, { B : SL2C | (∑ j : J, Φ B i j * v j) = v i } := by
      ext B
      simp [H_set, funext_iff, Matrix.mulVec, dotProduct]
    rw [h_eq_set]
    refine isClosed_iInter fun i => isClosed_eq ?_ continuous_const
    exact continuous_finsetSum _ fun j _ => (h_cont i j).mul continuous_const
  have h_curve : ∀ γ : ℂ → SL2C,
      (∀ r s : Fin 2, Differentiable ℂ fun z : ℂ => (γ z).1 r s) →
      (∀ t : ℝ, γ (t : ℂ) ∈ H_set) →
      ∀ z : ℂ, γ z ∈ H_set := by
    intro γ hγ_diff hγ_real z
    change Φ (γ z) *ᵥ v = v
    ext i
    simp only [Matrix.mulVec, dotProduct]
    apply sub_eq_zero.mp
    refine eq_zero_of_differentiable_and_real_eq_zero
      (f := fun w : ℂ => (∑ j : J, Φ (γ w) i j * v j) - v i) ?_ (fun t => ?_) z
    · refine (Differentiable.fun_sum fun j _ => ?_).sub (differentiable_const _)
      exact (h_holo γ hγ_diff i j).mul (differentiable_const _)
    · have ht := congrFun (hγ_real t) i
      simp only [Matrix.mulVec, dotProduct] at ht
      exact sub_eq_zero.mpr ht
  have h_expDiag : ∀ z : ℂ, sl2cExpDiag z ∈ H_set := by
    refine h_curve sl2cExpDiag (fun r s => ?_) (fun t => ?_)
    · fin_cases r <;> fin_cases s
      · exact Complex.differentiable_exp.comp
          ((differentiable_const Complex.I).mul differentiable_id)
      · exact differentiable_const 0
      · exact differentiable_const 0
      · exact Complex.differentiable_exp.comp
          ((differentiable_const (-Complex.I)).mul differentiable_id)
    · have h_eq : sl2cExpDiag (t : ℂ) = su2ToSL2C (su2ExpDiag t) := rfl
      rw [h_eq]
      exact h_su2 (su2ExpDiag t)
  have h_diag : ∀ (a : ℂ) (ha : a ≠ 0), sl2cDiag a ha ∈ H_set := by
    intro a ha
    have h_eq : sl2cDiag a ha = sl2cExpDiag (-Complex.I * Complex.log a) := by
      ext i j
      fin_cases i <;> fin_cases j
      · change a = Complex.exp (Complex.I * (-Complex.I * Complex.log a))
        have hz : Complex.I * (-Complex.I * Complex.log a) = Complex.log a := by
          rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
        rw [hz, Complex.exp_log ha]
      · rfl
      · rfl
      · change a⁻¹ = Complex.exp (-Complex.I * (-Complex.I * Complex.log a))
        have hz : -Complex.I * (-Complex.I * Complex.log a) = -Complex.log a := by
          rw [← mul_assoc, neg_mul_neg, Complex.I_mul_I, neg_one_mul]
        rw [hz, Complex.exp_neg, Complex.exp_log ha]
    rw [h_eq]
    exact h_expDiag _
  have h_upper_real : ∀ r : ℝ, sl2cUpper (r : ℂ) ∈ H_set := by
    intro r
    let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
    have hε_pos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
    have h_sqrt_ne : ∀ n, (Real.sqrt (ε n) : ℂ) ≠ 0 :=
      fun n => Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hε_pos n)).ne'
    have h_inv_ne : ∀ n, ((Real.sqrt (ε n) : ℂ)⁻¹) ≠ 0 :=
      fun n => inv_ne_zero (h_sqrt_ne n)
    let g_seq : ℕ → SL2C := fun n =>
      sl2cDiag ((Real.sqrt (ε n) : ℂ)⁻¹) (h_inv_ne n) *
        su2ToSL2C (su2RotReal (-(ε n * r))) *
        sl2cDiag (Real.sqrt (ε n) : ℂ) (h_sqrt_ne n)
    have hg_mem : ∀ n, g_seq n ∈ H_set := fun n =>
      h_mul (h_mul (h_diag _ _) (h_su2 _)) (h_diag _ _)
    have hε_lim : Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    have hεr_lim : Tendsto (fun n => ε n * r) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using hε_lim.mul (tendsto_const_nhds (x := r))
    have h_cos_lim : Tendsto (fun n => (Real.cos (ε n * r) : ℂ)) Filter.atTop (𝓝 (1 : ℂ)) := by
      have h1 := (Real.continuous_cos.tendsto 0).comp hεr_lim
      rw [Real.cos_zero] at h1
      have h2 := (Complex.continuous_ofReal.tendsto 1).comp h1
      rw [Complex.ofReal_one] at h2
      exact h2
    have h_sin_div : Tendsto (fun n => ((Real.sin (ε n * r) / ε n : ℝ) : ℂ))
        Filter.atTop (𝓝 (r : ℂ)) := by
      refine (Complex.continuous_ofReal.tendsto r).comp ?_
      by_cases hr : r = 0
      · subst hr
        simp
      · have h_nhds : Tendsto (fun n => ε n * r) Filter.atTop (𝓝[≠] (0 : ℝ)) :=
          tendsto_nhdsWithin_iff.mpr ⟨hεr_lim,
            Filter.Eventually.of_forall fun n => mul_ne_zero (hε_pos n).ne' hr⟩
        have h_sl : Tendsto (fun t : ℝ => t⁻¹ • (Real.sin (0 + t) - Real.sin 0))
            (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
          simpa using (Real.hasDerivAt_sin 0).tendsto_slope_zero
        have h_comp := (tendsto_const_nhds (x := r)).mul (h_sl.comp h_nhds)
        rw [mul_one] at h_comp
        refine h_comp.congr' (Filter.Eventually.of_forall fun n => ?_)
        dsimp only [Function.comp_apply, smul_eq_mul]
        rw [zero_add, Real.sin_zero, sub_zero]
        have hε_ne : ε n ≠ 0 := (hε_pos n).ne'
        field_simp [hr, hε_ne]
    have h_sin_mul : Tendsto (fun n => ((-(ε n * Real.sin (ε n * r)) : ℝ) : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) := by
      have h1 : Tendsto (fun n => -(ε n * Real.sin (ε n * r))) Filter.atTop (𝓝 (0 : ℝ)) := by
        simpa using (hε_lim.mul ((Real.continuous_sin.tendsto 0).comp hεr_lim)).neg
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have hg_lim : Tendsto g_seq Filter.atTop (𝓝 (sl2cUpper (r : ℂ))) := by
      refine tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_)
      fin_cases i <;> fin_cases j <;> dsimp only
      · refine h_cos_lim.congr' (Filter.Eventually.of_forall fun n => ?_)
        have hc_ne := h_sqrt_ne n
        simp only [g_seq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
        dsimp [sl2cDiag, su2ToSL2C, su2RotReal]
        rw [Real.cos_neg]
        field_simp [hc_ne]
        ring
      · refine h_sin_div.congr' (Filter.Eventually.of_forall fun n => ?_)
        have h_sq : (Real.sqrt (ε n) : ℂ) * (Real.sqrt (ε n) : ℂ) = (ε n : ℂ) := by
          norm_cast
          exact Real.mul_self_sqrt (hε_pos n).le
        simp only [g_seq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
        dsimp [sl2cDiag, su2ToSL2C, su2RotReal]
        rw [Real.sin_neg, Complex.ofReal_neg]
        push_cast
        rw [div_eq_mul_inv, ← h_sq, mul_inv]
        ring
      · refine h_sin_mul.congr' (Filter.Eventually.of_forall fun n => ?_)
        have h_sq : (Real.sqrt (ε n) : ℂ) * (Real.sqrt (ε n) : ℂ) = (ε n : ℂ) := by
          norm_cast
          exact Real.mul_self_sqrt (hε_pos n).le
        simp only [g_seq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
        dsimp [sl2cDiag, su2ToSL2C, su2RotReal]
        rw [Real.sin_neg, Complex.ofReal_neg, inv_inv]
        push_cast
        rw [← h_sq]
        ring
      · refine h_cos_lim.congr' (Filter.Eventually.of_forall fun n => ?_)
        have hc_ne := h_sqrt_ne n
        simp only [g_seq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
        dsimp [sl2cDiag, su2ToSL2C, su2RotReal]
        rw [Real.cos_neg, inv_inv]
        field_simp [hc_ne]
        ring
    exact h_closed.mem_of_tendsto hg_lim (Filter.Eventually.of_forall hg_mem)
  have h_upper : ∀ z : ℂ, sl2cUpper z ∈ H_set := by
    refine h_curve sl2cUpper (fun r s => ?_) h_upper_real
    fin_cases r <;> fin_cases s
    · exact differentiable_const 1
    · exact differentiable_id
    · exact differentiable_const 0
    · exact differentiable_const 1
  have h_lower : ∀ z : ℂ, sl2cLower z ∈ H_set := by
    intro z
    have h_eq : sl2cLower z =
        su2ToSL2C (su2RotReal (Real.pi / 2)) * sl2cUpper (-z) *
          su2ToSL2C (su2RotReal (-(Real.pi / 2))) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2cLower, sl2cUpper, su2ToSL2C, su2RotReal,
          Matrix.mul_apply, Fin.sum_univ_two, Real.cos_pi_div_two, Real.sin_pi_div_two]
    rw [h_eq]
    exact h_mul (h_mul (h_su2 _) (h_upper (-z))) (h_su2 _)
  intro B
  have hdet : B.1 0 0 * B.1 1 1 - B.1 0 1 * B.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact B.2
  by_cases hc : B.1 1 0 = 0
  · have ha : B.1 0 0 ≠ 0 := by
      intro ha0
      rw [ha0, hc, zero_mul, mul_zero, sub_self] at hdet
      exact zero_ne_one hdet
    have h_decomp : B = sl2cUpper (B.1 0 1 * B.1 0 0) * sl2cDiag (B.1 0 0) ha := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [sl2cUpper, sl2cDiag, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [sl2cUpper, sl2cDiag, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc,
          mul_inv_cancel₀ ha]
      · simp [sl2cUpper, sl2cDiag, Matrix.mul_apply, Fin.sum_univ_two, hc]
      · change B.1 1 1 = ((sl2cUpper (B.1 0 1 * B.1 0 0)).1 * (sl2cDiag (B.1 0 0) ha).1) 1 1
        rw [Matrix.mul_apply, Fin.sum_univ_two]
        dsimp [sl2cUpper, sl2cDiag]
        rw [zero_mul, zero_add, one_mul]
        rw [hc, mul_zero, sub_zero] at hdet
        exact eq_inv_of_mul_eq_one_right hdet
    rw [h_decomp]
    exact h_mul (h_upper _) (h_diag _ ha)
  · have h_decomp : B =
        sl2cUpper ((B.1 0 0 - 1) / B.1 1 0) * sl2cLower (B.1 1 0) *
          sl2cUpper ((B.1 1 1 - 1) / B.1 1 0) := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [sl2cUpper, sl2cLower, Matrix.mul_apply, Fin.sum_univ_two]
        field_simp [hc]
        ring
      · simp [sl2cUpper, sl2cLower, Matrix.mul_apply, Fin.sum_univ_two]
        field_simp [hc]
        linear_combination -hdet
      · simp [sl2cUpper, sl2cLower, Matrix.mul_apply, Fin.sum_univ_two]
      · simp [sl2cUpper, sl2cLower, Matrix.mul_apply, Fin.sum_univ_two]
        field_simp [hc]
        ring
    rw [h_decomp]
    exact h_mul (h_mul (h_upper _) (h_lower _)) (h_upper _)

def repTensorHom (R : HolomorphicLorentzRep ι) (n : ℕ) :
    (SL2C × SL2C) →* Matrix (Fin n → ι) (Fin n → ι) ℂ where
  toFun g α β := ∏ i : Fin n, R.σ g (α i) (β i)
  map_one' := by
    ext α β
    rw [map_one]
    by_cases h : α = β
    · subst h
      simp
    · rw [Matrix.one_apply_ne h]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
  map_mul' g₁ g₂ := by
    ext α γ
    simp only [Matrix.mul_apply, map_mul]
    simp_rw [← Finset.prod_mul_distrib]
    rw [Fintype.prod_sum]

private lemma isPoly_repTensorHom_entry (R : HolomorphicLorentzRep ι) (n : ℕ)
    (α β : Fin n → ι) :
    IsPoly fun p : SL2C × SL2C => repTensorHom R n p α β := by
  change IsPoly fun p : SL2C × SL2C => ∏ i ∈ (Finset.univ : Finset (Fin n)), R.σ p (α i) (β i)
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simpa using IsPoly.const 1) ?_
  intro i s hi ih
  simp only [Finset.prod_insert hi]
  exact IsPoly.mul (R.polynomial (α i) (β i)) ih

private lemma isPoly_contragredient_entry (R : HolomorphicLorentzRep ι) (n : ℕ)
    (α β : Fin n → ι) :
    IsPoly fun p : SL2C × SL2C =>
      repTensorHom R n (p.1, contragredientSL2C p.1) α β := by
  rcases isPoly_repTensorHom_entry R n α β with ⟨P, hP⟩
  have h_ind : ∀ Q : MvPolynomial PolyVar ℂ,
      IsPoly fun p : SL2C × SL2C =>
        MvPolynomial.eval (polyPt (p.1, contragredientSL2C p.1)) Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simpa using IsPoly.const a
    | add Q₁ Q₂ ih₁ ih₂ =>
      simpa only [map_add] using ih₁.add ih₂
    | mul_X Q₁ v ih₁ =>
      simp only [map_mul, MvPolynomial.eval_X]
      refine ih₁.mul ?_
      rcases v with ⟨r, s⟩ | ⟨r, s⟩
      · exact IsPoly.coordA r s
      · fin_cases r <;> fin_cases s
        · refine ⟨MvPolynomial.X (Sum.inl (1, 1)), fun p => ?_⟩
          simp [polyPt, (contragredientSL2C_entries p.1).1]
        · refine ⟨-MvPolynomial.X (Sum.inl (1, 0)), fun p => ?_⟩
          simp [polyPt, (contragredientSL2C_entries p.1).2.1]
        · refine ⟨-MvPolynomial.X (Sum.inl (0, 1)), fun p => ?_⟩
          simp [polyPt, (contragredientSL2C_entries p.1).2.2.1]
        · refine ⟨MvPolynomial.X (Sum.inl (0, 0)), fun p => ?_⟩
          simp [polyPt, (contragredientSL2C_entries p.1).2.2.2]
  rcases h_ind P with ⟨Q, hQ⟩
  exact ⟨Q, fun p => (hP (p.1, contragredientSL2C p.1)).trans (hQ p)⟩

def OSPositiveTimeTwoPointPowerBound (𝒮 : SchwingerFamily ι) : Prop :=
  ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧
    ∀ (α : Fin 2 → ι) (t : ℝ), 0 < t →
      ‖𝒮 2 α ![0, euclidTimeVec t]‖ ≤ C * (1 + t + t⁻¹) ^ K

private def posSingleTimeVec (ε : ℝ) (hε : 0 < ε) : posOrderedEuclidN 1 :=
  ⟨![euclidTimeVec ε], ⟨fun i => by
    fin_cases i
    simp [euclidTimeVec, hε], fun i hi => by omega⟩⟩

private def osSingleTimeConfig (γ : ι) (ε : ℝ) (hε : 0 < ε) : OSConfig ι :=
  ⟨1, (fun _ => γ, posSingleTimeVec ε hε)⟩

private noncomputable def osTwoPointRestSlice
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ε : ℝ) (hε : 0 < ε) (α : Fin 2 → ι) (s : ℂ) : ℂ :=
  let D := hOS.toReflectionPositiveData
  let hcontr := osContractionCondition_of_timeCluster D hOS.os1_translation hcluster
  let Z_tot := canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr hOS.os0_smooth
  ∑ β₀ : ι, star (S.C (α 0) β₀) *
    ⟪osBasis D (osSingleTimeConfig β₀ ε hε),
      Z_tot (s - ((2 * ε : ℝ) : ℂ)) (osBasis D (osSingleTimeConfig (α 1) ε hε))⟫_ℂ

private lemma differentiableOn_osTwoPointRestSlice
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ε : ℝ) (hε : 0 < ε) (α : Fin 2 → ι) :
    DifferentiableOn ℂ (osTwoPointRestSlice hOS hcluster ε hε α) { s : ℂ | 2 * ε < s.re } := by
  let D := hOS.toReflectionPositiveData
  let hcontr := osContractionCondition_of_timeCluster D hOS.os1_translation hcluster
  let Z_tot := canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr hOS.os0_smooth
  unfold osTwoPointRestSlice
  refine DifferentiableOn.fun_sum fun β₀ _ => ?_
  refine (differentiableOn_const _).mul ?_
  let L : (OSHilbert D →L[ℂ] OSHilbert D) →L[ℂ] ℂ :=
    (innerSL ℂ (osBasis D (osSingleTimeConfig β₀ ε hε))).comp
      (ContinuousLinearMap.apply ℂ (OSHilbert D) (osBasis D (osSingleTimeConfig (α 1) ε hε)))
  have h_sub : DifferentiableOn ℂ (fun s : ℂ => s - ((2 * ε : ℝ) : ℂ))
      { s : ℂ | 2 * ε < s.re } :=
    (differentiable_id.sub (differentiable_const _)).differentiableOn
  have h_maps : Set.MapsTo (fun s : ℂ => s - ((2 * ε : ℝ) : ℂ))
      { s : ℂ | 2 * ε < s.re } { z : ℂ | 0 < z.re } := by
    intro s hs
    change 2 * ε < s.re at hs
    change 0 < (s - ((2 * ε : ℝ) : ℂ)).re
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  exact L.differentiable.comp_differentiableOn
    ((differentiableOn_canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr
      hOS.os0_smooth).comp h_sub h_maps)

private lemma osTwoPointRestSlice_real_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ε : ℝ) (hε : 0 < ε) (α : Fin 2 → ι) {t : ℝ} (ht : 2 * ε < t) :
    osTwoPointRestSlice hOS hcluster ε hε α (t : ℂ) = 𝒮 2 α ![0, euclidTimeVec t] := by
  let D := hOS.toReflectionPositiveData
  let hcontr := osContractionCondition_of_timeCluster D hOS.os1_translation hcluster
  let τ : ℝ := t - 2 * ε
  have hτ : 0 ≤ τ := by dsimp [τ]; linarith
  have h_sub_eq : (t : ℂ) - ((2 * ε : ℝ) : ℂ) = (τ : ℂ) := by
    dsimp [τ]
    push_cast
    ring
  have hτ_rhp : (τ : ℂ) ∈ rightHalfPlane := by
    change 0 ≤ ((τ : ℝ) : ℂ).re
    simpa using hτ
  have hZ : canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr hOS.os0_smooth
      (τ : ℂ) = osContractionSemigroup D hcontr τ hτ := by
    rw [canonicalOSHolomorphicSemigroupTotal_eq D hOS.os1_translation hcontr hOS.os0_smooth hτ_rhp]
    exact (canonicalOSHolomorphicSemigroup D hOS.os1_translation hcontr hOS.os0_smooth).real_eq τ hτ
  have h_act : osContractionSemigroup D hcontr τ hτ
      (osBasis D (osSingleTimeConfig (α 1) ε hε)) =
      osBasis D (osConfigTimeShift τ hτ (osSingleTimeConfig (α 1) ε hε)) := by
    dsimp [osBasis]
    rw [osContractionSemigroup_toOSHilbert]
    dsimp [osTimeShiftLM]
    rw [osLiftConfigMap_osBasisPre]
  let B_cfg := osConfigTimeShift τ hτ (osSingleTimeConfig (α 1) ε hε)
  have h_sum_step : osTwoPointRestSlice hOS hcluster ε hε α (t : ℂ) =
      ∑ β₀ : ι, star (S.C (α 0) β₀) *
        osKernel S D.𝒮 (osSingleTimeConfig β₀ ε hε) B_cfg := by
    refine Finset.sum_congr rfl fun β₀ _ => ?_
    congr 1
    change ⟪osBasis D (osSingleTimeConfig β₀ ε hε),
      canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr hOS.os0_smooth
        ((t : ℂ) - ((2 * ε : ℝ) : ℂ)) (osBasis D (osSingleTimeConfig (α 1) ε hε))⟫_ℂ = _
    rw [h_sub_eq, hZ, h_act, inner_osBasis]
  have h_pt : (fun m : Fin 2 =>
      osConcatPoint 1 1 (posSingleTimeVec ε hε).val B_cfg.2.2.val m + euclidTimeVec ε) =
      ![0, euclidTimeVec t] := by
    ext m μ
    fin_cases m
    · change osConcatPoint 1 1 (posSingleTimeVec ε hε).val B_cfg.2.2.val
          (Fin.castAdd 1 (0 : Fin 1)) μ + euclidTimeVec ε μ = (0 : Fin 4 → ℝ) μ
      rw [osConcatPoint_castAdd]
      dsimp [posSingleTimeVec, euclidTimeReflectRev]
      rw [euclidTimeReflect_euclidTimeVec]
      simp
    · change osConcatPoint 1 1 (posSingleTimeVec ε hε).val B_cfg.2.2.val
          (Fin.natAdd 1 (0 : Fin 1)) μ + euclidTimeVec ε μ = euclidTimeVec t μ
      rw [osConcatPoint_natAdd]
      dsimp [B_cfg, osConfigTimeShift, osSingleTimeConfig, posSingleTimeVec]
      have h_sum : euclidTimeVec ε + euclidTimeVec τ + euclidTimeVec ε = euclidTimeVec t := by
        rw [← euclidTimeVec_add, ← euclidTimeVec_add]
        congr 1
        dsimp [τ]
        ring
      exact congrFun h_sum μ
  have h_ord : osConcatPoint 1 1 (posSingleTimeVec ε hε).val B_cfg.2.2.val ∈ orderedEuclidN 2 :=
    osConcatPoint_mem_orderedEuclidN 1 1 (posSingleTimeVec ε hε).property B_cfg.2.2.property
  have h_ker : ∀ β₀ : ι,
      osKernel S D.𝒮 (osSingleTimeConfig β₀ ε hε) B_cfg =
        ∑ γ₀ : ι, S.C β₀ γ₀ * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t] := by
    intro β₀
    dsimp [osKernel, osSingleTimeConfig]
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    refine Finset.sum_congr rfl fun γ₀ _ => ?_
    simp only [Fin.prod_univ_one]
    congr 1
    have h_tr := hOS.os1_translation 2
      (osConcatIdx 1 1 (fun _ => γ₀) (fun _ => α 1))
      (osConcatPoint 1 1 (posSingleTimeVec ε hε).val B_cfg.2.2.val) h_ord (euclidTimeVec ε)
    rw [h_pt] at h_tr
    change 𝒮 2 (osConcatIdx 1 1 (fun _ => γ₀) (fun _ => α 1))
      (osConcatPoint 1 1 (posSingleTimeVec ε hε).val B_cfg.2.2.val) = _
    rw [← h_tr]
    have h_idx : osConcatIdx 1 1 (fun _ : Fin 1 => γ₀) (fun _ : Fin 1 => α 1) = ![γ₀, α 1] := by
      ext m
      fin_cases m <;> rfl
    rw [h_idx]
  rw [h_sum_step]
  have h_ker_sum :
      (∑ β₀ : ι, star (S.C (α 0) β₀) * osKernel S D.𝒮 (osSingleTimeConfig β₀ ε hε) B_cfg) =
        ∑ β₀ : ι, ∑ γ₀ : ι,
          star (S.C (α 0) β₀) * (S.C β₀ γ₀ * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t]) := by
    refine Finset.sum_congr rfl fun β₀ _ => ?_
    rw [h_ker β₀, Finset.mul_sum]
  rw [h_ker_sum, Finset.sum_comm]
  have h_collapse : ∀ γ₀ : ι,
      (∑ β₀ : ι, star (S.C (α 0) β₀) * (S.C β₀ γ₀ * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t])) =
        (if α 0 = γ₀ then 1 else 0) * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t] := by
    intro γ₀
    have h_sum_eq : (∑ β₀ : ι, star (S.C (α 0) β₀) * S.C β₀ γ₀) =
        (S.C.map star * S.C) (α 0) γ₀ := by
      simp [Matrix.mul_apply]
    have h_id := congrFun (congrFun (starStructure_map_star_mul_self S) (α 0)) γ₀
    calc (∑ β₀ : ι, star (S.C (α 0) β₀) * (S.C β₀ γ₀ * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t]))
        = (∑ β₀ : ι, star (S.C (α 0) β₀) * S.C β₀ γ₀) *
            𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t] := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
      _ = (if α 0 = γ₀ then 1 else 0) * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t] := by
            rw [h_sum_eq, h_id]
            simp [Matrix.one_apply]
  have h_final :
      (∑ γ₀ : ι, ∑ β₀ : ι,
        star (S.C (α 0) β₀) * (S.C β₀ γ₀ * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t])) =
        𝒮 2 ![α 0, α 1] ![0, euclidTimeVec t] := by
    calc _ = ∑ γ₀ : ι, (if α 0 = γ₀ then 1 else 0) * 𝒮 2 ![γ₀, α 1] ![0, euclidTimeVec t] :=
          Finset.sum_congr rfl fun γ₀ _ => h_collapse γ₀
      _ = 𝒮 2 ![α 0, α 1] ![0, euclidTimeVec t] := by
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [h_final]
  have h_α : ![α 0, α 1] = α := by
    ext i
    fin_cases i <;> rfl
  rw [h_α]

private lemma osTwoPointRestSlice_congr
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (α : Fin 2 → ι)
    {s : ℂ} (hs : 2 * max ε₁ ε₂ < s.re) :
    osTwoPointRestSlice hOS hcluster ε₁ hε₁ α s =
      osTwoPointRestSlice hOS hcluster ε₂ hε₂ α s := by
  let a : ℝ := 2 * max ε₁ ε₂
  have h_sub₁ : { w : ℂ | a < w.re } ⊆ { w : ℂ | 2 * ε₁ < w.re } := fun w hw => by
    change a < w.re at hw
    change 2 * ε₁ < w.re
    linarith [le_max_left ε₁ ε₂]
  have h_sub₂ : { w : ℂ | a < w.re } ⊆ { w : ℂ | 2 * ε₂ < w.re } := fun w hw => by
    change a < w.re at hw
    change 2 * ε₂ < w.re
    linarith [le_max_right ε₁ ε₂]
  refine eq_on_re_gt_of_real_gt_eq
    ((differentiableOn_osTwoPointRestSlice hOS hcluster ε₁ hε₁ α).mono h_sub₁)
    ((differentiableOn_osTwoPointRestSlice hOS hcluster ε₂ hε₂ α).mono h_sub₂)
    (fun t ht => ?_) s hs
  have ht₁ : 2 * ε₁ < t := by dsimp [a] at ht; linarith [le_max_left ε₁ ε₂]
  have ht₂ : 2 * ε₂ < t := by dsimp [a] at ht; linarith [le_max_right ε₁ ε₂]
  rw [osTwoPointRestSlice_real_eq hOS hcluster ε₁ hε₁ α ht₁,
      osTwoPointRestSlice_real_eq hOS hcluster ε₂ hε₂ α ht₂]

noncomputable def osTwoPointRestH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (α : Fin 2 → ι) (s : ℂ) : ℂ :=
  if hs : 0 < s.re then
    osTwoPointRestSlice hOS hcluster (s.re / 4) (by linarith) α s
  else 0

theorem differentiableOn_osTwoPointRestH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (α : Fin 2 → ι) :
    DifferentiableOn ℂ (osTwoPointRestH hOS hcluster α) { s : ℂ | 0 < s.re } := by
  intro s₀ hs₀
  change 0 < s₀.re at hs₀
  let ε₀ : ℝ := s₀.re / 3
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; linarith
  let V : Set ℂ := { s : ℂ | 2 * ε₀ < s.re }
  have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hs₀_V : s₀ ∈ V := by
    change 2 * (s₀.re / 3) < s₀.re
    linarith
  have h_diff_slice : DifferentiableAt ℂ (osTwoPointRestSlice hOS hcluster ε₀ hε₀ α) s₀ :=
    (differentiableOn_osTwoPointRestSlice hOS hcluster ε₀ hε₀ α).differentiableAt
      (hV_open.mem_nhds hs₀_V)
  have h_ev : osTwoPointRestH hOS hcluster α =ᶠ[𝓝 s₀]
      osTwoPointRestSlice hOS hcluster ε₀ hε₀ α := by
    filter_upwards [hV_open.mem_nhds hs₀_V] with s hs
    change 2 * ε₀ < s.re at hs
    have hs_pos : 0 < s.re := by linarith
    unfold osTwoPointRestH
    rw [dif_pos hs_pos]
    refine osTwoPointRestSlice_congr hOS hcluster (by linarith) hε₀ α ?_
    have h_max : 2 * max (s.re / 4) ε₀ < s.re := by
      rcases max_choice (s.re / 4) ε₀ with h_eq | h_eq <;> rw [h_eq] <;> linarith
    exact h_max
  exact (h_diff_slice.congr_of_eventuallyEq h_ev).differentiableWithinAt

theorem analyticOn_osTwoPointRestH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (α : Fin 2 → ι) :
    AnalyticOn ℂ (osTwoPointRestH hOS hcluster α) { s : ℂ | 0 < s.re } :=
  (differentiableOn_osTwoPointRestH hOS hcluster α).analyticOn
    (isOpen_lt continuous_const Complex.continuous_re)

theorem osTwoPointRestH_real_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (α : Fin 2 → ι) {t : ℝ} (ht : 0 < t) :
    osTwoPointRestH hOS hcluster α (t : ℂ) = 𝒮 2 α ![0, euclidTimeVec t] := by
  have ht_re : 0 < ((t : ℝ) : ℂ).re := by simpa using ht
  unfold osTwoPointRestH
  rw [dif_pos ht_re]
  have hε_pos : 0 < ((t : ℝ) : ℂ).re / 4 := by
    simp only [Complex.ofReal_re]
    linarith
  have ht_gt : 2 * (((t : ℝ) : ℂ).re / 4) < t := by
    simp only [Complex.ofReal_re]
    linarith
  exact osTwoPointRestSlice_real_eq hOS hcluster (((t : ℝ) : ℂ).re / 4) hε_pos α ht_gt

private def contragredientProdHom : SL2C →* (SL2C × SL2C) where
  toFun B := (B, contragredientSL2C B)
  map_one' := by simp
  map_mul' A B := by simp

theorem osTwoPointRestH_stabilizer
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (B : SL2C) {s : ℂ} (hs : 0 < s.re) :
    repTensorHom R 2 (B, contragredientSL2C B) *ᵥ
        (fun β : Fin 2 → ι => osTwoPointRestH hOS hcluster β s) =
      fun α : Fin 2 → ι => osTwoPointRestH hOS hcluster α s := by
  let Φ : SL2C →* Matrix (Fin 2 → ι) (Fin 2 → ι) ℂ :=
    (repTensorHom R 2).comp contragredientProdHom
  refine su2_to_sl2c_stabilizer_lift Φ
    (fun α β => ?_) (fun γ hγ α β => ?_) (fun U => ?_) B
  · have h_eq : (fun X : SL2C => Φ X α β) =
        (fun p : SL2C × SL2C => repTensorHom R 2 (p.1, contragredientSL2C p.1) α β) ∘
          (fun X : SL2C => (X, (1 : SL2C))) := rfl
    rw [h_eq]
    exact (continuous_isPoly (isPoly_contragredient_entry R 2 α β)).comp
      (continuous_id.prodMk continuous_const)
  · have h_eq : (fun z : ℂ => Φ (γ z) α β) =
        fun z : ℂ => repTensorHom R 2 ((γ z, (1 : SL2C)).1,
          contragredientSL2C (γ z, (1 : SL2C)).1) α β := rfl
    rw [h_eq]
    exact differentiable_isPoly_comp (isPoly_contragredient_entry R 2 α β)
      (g := fun z => (γ z, (1 : SL2C))) hγ (fun _ _ => differentiable_const _)
  · ext α
    simp only [Φ, MonoidHom.comp_apply, contragredientProdHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Matrix.mulVec, dotProduct]
    refine eq_on_re_gt_of_real_gt_eq
      (f₁ := fun w : ℂ => ∑ β : Fin 2 → ι,
        repTensorHom R 2 (su2ToSL2C U, contragredientSL2C (su2ToSL2C U)) α β *
          osTwoPointRestH hOS hcluster β w)
      (f₂ := osTwoPointRestH hOS hcluster α) ?_
      (differentiableOn_osTwoPointRestH hOS hcluster α) (fun t ht => ?_) s hs
    · exact DifferentiableOn.fun_sum fun β _ =>
        (differentiableOn_const _).mul (differentiableOn_osTwoPointRestH hOS hcluster β)
    · rw [osTwoPointRestH_real_eq hOS hcluster α ht, contragredientSL2C_su2ToSL2C U]
      have h_rhs_eq : ∀ β : Fin 2 → ι,
          osTwoPointRestH hOS hcluster β (t : ℂ) = 𝒮 2 β ![0, euclidTimeVec t] :=
        fun β => osTwoPointRestH_real_eq hOS hcluster β ht
      simp_rw [h_rhs_eq]
      have h_ord : (![0, euclidTimeVec t] : Fin 2 → Fin 4 → ℝ) ∈ orderedEuclidN 2 := by
        intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simpa [euclidTimeVec] using ht
      have h_fix : euclidRotN 2 U (su2Conj U) ![0, euclidTimeVec t] = ![0, euclidTimeVec t] := by
        ext i μ
        fin_cases i
        · change ((euclidRotOfSU2 U (su2Conj U)).mulVec 0) μ = (0 : Fin 4 → ℝ) μ
          simp
        · change ((euclidRotOfSU2 U (su2Conj U)).mulVec (euclidTimeVec t)) μ = euclidTimeVec t μ
          rw [euclidRotOfSU2_mulVec, euclidRotApply_su2Conj_euclidTimeVec]
      have h_rot := hOS.os1_rotation 2 U (su2Conj U) ![0, euclidTimeVec t] h_ord
        (by rwa [h_fix]) α
      rw [h_fix] at h_rot
      exact h_rot.symm

private lemma osOnePoint_sl2c_covariant
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮) (A B : SL2C) :
    repTensorHom R 1 (A, B) *ᵥ (fun β : Fin 1 → ι => 𝒮 1 β 0) =
      fun α : Fin 1 → ι => 𝒮 1 α 0 := by
  have h_ord0 : (0 : Fin 1 → Fin 4 → ℝ) ∈ orderedEuclidN 1 := fun _ hi => by omega
  have h_rot0 : ∀ U V : SU2, euclidRotN 1 U V 0 = (0 : Fin 1 → Fin 4 → ℝ) := by
    intro U V
    ext i μ
    change ((euclidRotOfSU2 U V).mulVec 0) μ = 0
    simp
  let ΦL : SL2C →* Matrix (Fin 1 → ι) (Fin 1 → ι) ℂ :=
    (repTensorHom R 1).comp (MonoidHom.inl SL2C SL2C)
  let ΦR : SL2C →* Matrix (Fin 1 → ι) (Fin 1 → ι) ℂ :=
    (repTensorHom R 1).comp (MonoidHom.inr SL2C SL2C)
  have hL : ΦL A *ᵥ (fun β : Fin 1 → ι => 𝒮 1 β 0) = fun α : Fin 1 → ι => 𝒮 1 α 0 := by
    refine su2_to_sl2c_stabilizer_lift ΦL
      (fun α β => (continuous_isPoly (isPoly_repTensorHom_entry R 1 α β)).comp
        (continuous_id.prodMk continuous_const))
      (fun γ hγ α β => differentiable_isPoly_comp (isPoly_repTensorHom_entry R 1 α β)
        (g := fun z => (γ z, (1 : SL2C))) hγ (fun _ _ => differentiable_const _))
      (fun U => ?_) A
    ext α
    have h := hOS.os1_rotation 1 U 1 0 h_ord0 (by rw [h_rot0]; exact h_ord0) α
    rw [h_rot0] at h
    have h1 : su2ToSL2C 1 = (1 : SL2C) := by ext r s; rfl
    rw [h1] at h
    exact h.symm
  have hR : ΦR B *ᵥ (fun β : Fin 1 → ι => 𝒮 1 β 0) = fun α : Fin 1 → ι => 𝒮 1 α 0 := by
    refine su2_to_sl2c_stabilizer_lift ΦR
      (fun α β => (continuous_isPoly (isPoly_repTensorHom_entry R 1 α β)).comp
        (continuous_const.prodMk continuous_id))
      (fun γ hγ α β => differentiable_isPoly_comp (isPoly_repTensorHom_entry R 1 α β)
        (g := fun z => ((1 : SL2C), γ z)) (fun _ _ => differentiable_const _) hγ)
      (fun V => ?_) B
    ext α
    have h := hOS.os1_rotation 1 1 V 0 h_ord0 (by rw [h_rot0]; exact h_ord0) α
    rw [h_rot0] at h
    have h1 : su2ToSL2C 1 = (1 : SL2C) := by ext r s; rfl
    rw [h1] at h
    exact h.symm
  have h_prod : (A, B) = (A, (1 : SL2C)) * ((1 : SL2C), B) := by simp
  rw [h_prod, map_mul, ← Matrix.mulVec_mulVec]
  change ΦL A *ᵥ (ΦR B *ᵥ fun β : Fin 1 → ι => 𝒮 1 β 0) = _
  rw [hR, hL]

theorem norm_osTwoPointRestH_le_of_powerBound
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮) :
    ∃ (C_r : ℝ) (K : ℕ), 0 ≤ C_r ∧
      ∀ (α : Fin 2 → ι) {s : ℂ}, 0 < s.re →
        ‖osTwoPointRestH hOS hcluster α s‖ ≤
          C_r * (1 + ‖s‖) ^ K * (1 + (s.re)⁻¹) ^ K := by
  rcases hpow with ⟨C, K, hC_nn, hC_bd⟩
  let D := hOS.toReflectionPositiveData
  let hcontr := osContractionCondition_of_timeCluster D hOS.os1_translation hcluster
  let C_star : ℝ := ∑ a : ι, ∑ b : ι, ‖S.C a b‖
  have hC_star_nn : 0 ≤ C_star :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C_star * C_star * C * 2 ^ K, K, by positivity, fun α {s} hs => ?_⟩
  let ε : ℝ := s.re / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have h2ε : 0 < 2 * ε := by linarith
  have h_norm_sq : ∀ γ : ι,
      ‖osBasis D (osSingleTimeConfig γ ε hε)‖ ^ 2 ≤
        C_star * (C * (1 + 2 * ε + (2 * ε)⁻¹) ^ K) := by
    intro γ
    have h_sq_re : ‖osBasis D (osSingleTimeConfig γ ε hε)‖ ^ 2 =
        (osKernel S D.𝒮 (osSingleTimeConfig γ ε hε) (osSingleTimeConfig γ ε hε)).re := by
      have h := norm_sq_eq_re_inner (𝕜 := ℂ) (osBasis D (osSingleTimeConfig γ ε hε))
      rwa [inner_osBasis] at h
    rw [h_sq_re]
    have h_re_le : (osKernel S D.𝒮 (osSingleTimeConfig γ ε hε) (osSingleTimeConfig γ ε hε)).re ≤
        ‖osKernel S D.𝒮 (osSingleTimeConfig γ ε hε) (osSingleTimeConfig γ ε hε)‖ :=
      Complex.re_le_norm _
    refine h_re_le.trans ?_
    have h_pt : (fun m : Fin 2 =>
        osConcatPoint 1 1 (posSingleTimeVec ε hε).val (posSingleTimeVec ε hε).val m +
          euclidTimeVec ε) = ![0, euclidTimeVec (2 * ε)] := by
      ext m μ
      fin_cases m
      · change osConcatPoint 1 1 (posSingleTimeVec ε hε).val (posSingleTimeVec ε hε).val
            (Fin.castAdd 1 (0 : Fin 1)) μ + euclidTimeVec ε μ = (0 : Fin 4 → ℝ) μ
        rw [osConcatPoint_castAdd]
        dsimp [posSingleTimeVec, euclidTimeReflectRev]
        rw [euclidTimeReflect_euclidTimeVec]
        simp
      · change osConcatPoint 1 1 (posSingleTimeVec ε hε).val (posSingleTimeVec ε hε).val
            (Fin.natAdd 1 (0 : Fin 1)) μ + euclidTimeVec ε μ = euclidTimeVec (2 * ε) μ
        rw [osConcatPoint_natAdd]
        dsimp [posSingleTimeVec]
        have h_sum : euclidTimeVec ε + euclidTimeVec ε = euclidTimeVec (2 * ε) := by
          rw [← euclidTimeVec_add]
          congr 1
          ring
        exact congrFun h_sum μ
    have h_ord := osConcatPoint_mem_orderedEuclidN 1 1
      (posSingleTimeVec ε hε).property (posSingleTimeVec ε hε).property
    have h_ker_eq : osKernel S D.𝒮 (osSingleTimeConfig γ ε hε) (osSingleTimeConfig γ ε hε) =
        ∑ δ : ι, S.C γ δ * 𝒮 2 ![δ, γ] ![0, euclidTimeVec (2 * ε)] := by
      dsimp [osKernel, osSingleTimeConfig]
      rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
      refine Finset.sum_congr rfl fun δ _ => ?_
      simp only [Fin.prod_univ_one]
      congr 1
      have h_tr := hOS.os1_translation 2
        (osConcatIdx 1 1 (fun _ => δ) (fun _ => γ))
        (osConcatPoint 1 1 (posSingleTimeVec ε hε).val (posSingleTimeVec ε hε).val) h_ord
        (euclidTimeVec ε)
      rw [h_pt] at h_tr
      change 𝒮 2 (osConcatIdx 1 1 (fun _ => δ) (fun _ => γ))
        (osConcatPoint 1 1 (posSingleTimeVec ε hε).val (posSingleTimeVec ε hε).val) = _
      rw [← h_tr]
      have h_idx : osConcatIdx 1 1 (fun _ : Fin 1 => δ) (fun _ : Fin 1 => γ) = ![δ, γ] := by
        ext m
        fin_cases m <;> rfl
      rw [h_idx]
    rw [h_ker_eq]
    have h_sum_norm : ‖∑ δ : ι, S.C γ δ * 𝒮 2 ![δ, γ] ![0, euclidTimeVec (2 * ε)]‖ ≤
        (∑ δ : ι, ‖S.C γ δ‖) * (C * (1 + 2 * ε + (2 * ε)⁻¹) ^ K) := by
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun δ _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC_bd ![δ, γ] (2 * ε) h2ε) (norm_nonneg _)
    have h_le_Cstar : (∑ δ : ι, ‖S.C γ δ‖) ≤ C_star :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ γ)
    exact h_sum_norm.trans
      (mul_le_mul_of_nonneg_right h_le_Cstar (by positivity))
  unfold osTwoPointRestH
  rw [dif_pos hs]
  change ‖osTwoPointRestSlice hOS hcluster ε hε α s‖ ≤ _
  unfold osTwoPointRestSlice
  have hs_rhp : s - ((2 * ε : ℝ) : ℂ) ∈ rightHalfPlane := by
    change 0 ≤ (s - ((2 * ε : ℝ) : ℂ)).re
    simp only [Complex.sub_re, Complex.ofReal_re]
    dsimp [ε]
    linarith
  let M_bd : ℝ := C_star * (C * (1 + 2 * ε + (2 * ε)⁻¹) ^ K)
  have hM_nn : 0 ≤ M_bd := by dsimp [M_bd]; positivity
  have h_inner_le : ∀ β₀ : ι,
      ‖⟪osBasis D (osSingleTimeConfig β₀ ε hε),
          canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr hOS.os0_smooth
            (s - ((2 * ε : ℝ) : ℂ)) (osBasis D (osSingleTimeConfig (α 1) ε hε))⟫_ℂ‖ ≤ M_bd := by
    intro β₀
    rw [canonicalOSHolomorphicSemigroupTotal_eq D hOS.os1_translation hcontr hOS.os0_smooth hs_rhp]
    have h_cs := norm_inner_le_norm (𝕜 := ℂ) (osBasis D (osSingleTimeConfig β₀ ε hε))
      ((canonicalOSHolomorphicSemigroup D hOS.os1_translation hcontr hOS.os0_smooth).Z
        (s - ((2 * ε : ℝ) : ℂ)) hs_rhp (osBasis D (osSingleTimeConfig (α 1) ε hε)))
    have h_ct := (canonicalOSHolomorphicSemigroup D hOS.os1_translation hcontr
      hOS.os0_smooth).contraction (s - ((2 * ε : ℝ) : ℂ)) hs_rhp
      (osBasis D (osSingleTimeConfig (α 1) ε hε))
    have h_prod_le :
        ‖osBasis D (osSingleTimeConfig β₀ ε hε)‖ *
          ‖osBasis D (osSingleTimeConfig (α 1) ε hε)‖ ≤ M_bd := by
      have hA := h_norm_sq β₀
      have hB := h_norm_sq (α 1)
      have h_amgm := sq_nonneg (‖osBasis D (osSingleTimeConfig β₀ ε hε)‖ -
        ‖osBasis D (osSingleTimeConfig (α 1) ε hε)‖)
      nlinarith
    exact h_cs.trans ((mul_le_mul_of_nonneg_left h_ct (norm_nonneg _)).trans h_prod_le)
  have h_sum1 : ‖∑ β₀ : ι, star (S.C (α 0) β₀) *
      ⟪osBasis D (osSingleTimeConfig β₀ ε hε),
        canonicalOSHolomorphicSemigroupTotal D hOS.os1_translation hcontr hOS.os0_smooth
          (s - ((2 * ε : ℝ) : ℂ)) (osBasis D (osSingleTimeConfig (α 1) ε hε))⟫_ℂ‖ ≤
      C_star * M_bd := by
    have h_le1 : (∑ β₀ : ι, ‖S.C (α 0) β₀‖) ≤ C_star :=
      Finset.single_le_sum (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ (α 0))
    refine (norm_sum_le _ _).trans
      ((Finset.sum_le_sum (g := fun β₀ => ‖S.C (α 0) β₀‖ * M_bd) fun β₀ _ => ?_).trans ?_)
    · rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (h_inner_le β₀) (norm_nonneg _)
    · rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right h_le1 hM_nn
  have h_base : 1 + 2 * ε + (2 * ε)⁻¹ ≤ 2 * ((1 + ‖s‖) * (1 + (s.re)⁻¹)) := by
    have h_eq1 : 2 * ε = s.re / 2 := by dsimp [ε]; ring
    have h_eq2 : (2 * ε)⁻¹ = 2 * (s.re)⁻¹ := by
      rw [h_eq1, inv_div, div_eq_mul_inv]
    rw [h_eq2, h_eq1]
    have h_re_le : s.re ≤ ‖s‖ := Complex.re_le_norm s
    have h_s_nn : 0 ≤ ‖s‖ := norm_nonneg s
    have h_inv_nn : 0 ≤ (s.re)⁻¹ := inv_nonneg.mpr hs.le
    nlinarith
  have h_pow_le : (1 + 2 * ε + (2 * ε)⁻¹) ^ K ≤
      2 ^ K * (1 + ‖s‖) ^ K * (1 + (s.re)⁻¹) ^ K := by
    calc (1 + 2 * ε + (2 * ε)⁻¹) ^ K
        ≤ (2 * ((1 + ‖s‖) * (1 + (s.re)⁻¹))) ^ K :=
          pow_le_pow_left₀ (by positivity) h_base K
      _ = 2 ^ K * (1 + ‖s‖) ^ K * (1 + (s.re)⁻¹) ^ K := by
          rw [mul_pow, mul_pow, mul_assoc]
  calc _ ≤ C_star * M_bd := h_sum1
    _ = C_star * C_star * C * (1 + 2 * ε + (2 * ε)⁻¹) ^ K := by dsimp [M_bd]; ring
    _ ≤ C_star * C_star * C * (2 ^ K * (1 + ‖s‖) ^ K * (1 + (s.re)⁻¹) ^ K) :=
        mul_le_mul_of_nonneg_left h_pow_le (by positivity)
    _ = C_star * C_star * C * 2 ^ K * (1 + ‖s‖) ^ K * (1 + (s.re)⁻¹) ^ K := by ring

private lemma minkowskiInner_mul_le_sq_of_mem_forward_cone
    {y : Fin 4 → ℝ} (hy : y ∈ forward_light_cone) (x : Fin 4 → ℝ) :
    minkowskiInner y y * minkowskiInner x x ≤ (minkowskiInner x y) ^ 2 := by
  have hy0 : 0 < y 0 := hy.1
  have hyy : 0 < minkowskiInner y y := hy.2
  let u : Fin 4 → ℝ := minkowskiInner y y • x - minkowskiInner x y • y
  have huy : minkowskiInner u y = 0 := by
    dsimp [u]
    simp only [minkowskiInner_explicit, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hu0_eq : u 0 * y 0 = u 1 * y 1 + u 2 * y 2 + u 3 * y 3 := by
    rw [minkowskiInner_explicit] at huy
    linarith
  have h_cs := cauchy_schwarz_3 (u 1) (u 2) (u 3) (y 1) (y 2) (y 3)
  have hy_sp : (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 ≤ (y 0) ^ 2 := by
    have h := hy.2
    rw [minkowskiInner_explicit] at h
    linarith
  have hu0_sq : (u 0) ^ 2 * (y 0) ^ 2 ≤ ((u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2) * (y 0) ^ 2 := by
    calc (u 0) ^ 2 * (y 0) ^ 2
        = (u 0 * y 0) ^ 2 := by ring
      _ = (u 1 * y 1 + u 2 * y 2 + u 3 * y 3) ^ 2 := by rw [hu0_eq]
      _ ≤ ((u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2) * ((y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2) := h_cs
      _ ≤ ((u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2) * (y 0) ^ 2 :=
          mul_le_mul_of_nonneg_left hy_sp (by positivity)
  have huu_le : minkowskiInner u u ≤ 0 := by
    rw [minkowskiInner_explicit]
    have hy0_sq_pos : 0 < (y 0) ^ 2 := sq_pos_of_pos hy0
    nlinarith
  have huu_expand : minkowskiInner u u =
      minkowskiInner y y *
        (minkowskiInner y y * minkowskiInner x x - (minkowskiInner x y) ^ 2) := by
    dsimp [u]
    simp only [minkowskiInner_explicit, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [huu_expand] at huu_le
  nlinarith

private def negMinkowskiSqC (ζ : Fin 4 → ℂ) : ℂ :=
  -minkowskiInnerC ζ ζ

private lemma negMinkowskiSqC_re_im (ζ : Fin 4 → ℂ) :
    (negMinkowskiSqC ζ).re =
      minkowskiInner (fun μ => (ζ μ).im) (fun μ => (ζ μ).im) -
        minkowskiInner (fun μ => (ζ μ).re) (fun μ => (ζ μ).re) ∧
    (negMinkowskiSqC ζ).im =
      -2 * minkowskiInner (fun μ => (ζ μ).re) (fun μ => (ζ μ).im) := by
  have hζ_decomp : ∀ μ : Fin 4, ζ μ = ((ζ μ).re : ℂ) + ((ζ μ).im : ℂ) * Complex.I :=
    fun μ => (Complex.re_add_im (ζ μ)).symm
  dsimp [negMinkowskiSqC, minkowskiInnerC]
  rw [minkowskiInner_explicit, minkowskiInner_explicit, minkowskiInner_explicit]
  conv_lhs =>
    rw [hζ_decomp 0, hζ_decomp 1, hζ_decomp 2, hζ_decomp 3]
  constructor
  · simp
    ring
  · simp
    ring

private lemma two_mul_minkowskiInner_im_le_norm_add_re {ζ : Fin 4 → ℂ}
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) :
    2 * minkowskiInner (fun μ => (ζ μ).im) (fun μ => (ζ μ).im) ≤
      ‖negMinkowskiSqC ζ‖ + (negMinkowskiSqC ζ).re := by
  let x : Fin 4 → ℝ := fun μ => (ζ μ).re
  let y : Fin 4 → ℝ := fun μ => (ζ μ).im
  have h_re_im := negMinkowskiSqC_re_im ζ
  have h_rev_cs := minkowskiInner_mul_le_sq_of_mem_forward_cone hζ x
  have h_norm_sq : ‖negMinkowskiSqC ζ‖ ^ 2 =
      (negMinkowskiSqC ζ).re ^ 2 + (negMinkowskiSqC ζ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h_sq_le : (minkowskiInner y y + minkowskiInner x x) ^ 2 ≤ ‖negMinkowskiSqC ζ‖ ^ 2 := by
    rw [h_norm_sq, h_re_im.1, h_re_im.2]
    dsimp [x, y]
    nlinarith
  have h_le_norm : minkowskiInner y y + minkowskiInner x x ≤ ‖negMinkowskiSqC ζ‖ := by
    have h_abs : |minkowskiInner y y + minkowskiInner x x| ≤ ‖negMinkowskiSqC ζ‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h_sq_le
    exact (le_abs_self _).trans h_abs
  rw [h_re_im.1]
  dsimp [x, y] at h_le_norm
  linarith

private lemma negMinkowskiSqC_mem_slitPlane {ζ : Fin 4 → ℂ}
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) :
    negMinkowskiSqC ζ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra h_not
  push Not at h_not
  rcases h_not with ⟨hre_le, him_eq⟩
  have hw_eq : negMinkowskiSqC ζ = ((negMinkowskiSqC ζ).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him_eq
  have h_norm : ‖negMinkowskiSqC ζ‖ = -(negMinkowskiSqC ζ).re := by
    conv_lhs => rw [hw_eq]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hre_le]
  have h_pos : 0 < 2 * minkowskiInner (fun μ => (ζ μ).im) (fun μ => (ζ μ).im) :=
    mul_pos two_pos hζ.2
  have h_le := two_mul_minkowskiInner_im_le_norm_add_re hζ
  linarith

noncomputable def tubeProperTime (ζ : Fin 4 → ℂ) : ℂ :=
  Complex.exp (Complex.log (negMinkowskiSqC ζ) / 2)

private lemma tubeProperTime_sq {ζ : Fin 4 → ℂ}
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) :
    tubeProperTime ζ ^ 2 = negMinkowskiSqC ζ := by
  have hw_ne : negMinkowskiSqC ζ ≠ 0 :=
    Complex.slitPlane_ne_zero (negMinkowskiSqC_mem_slitPlane hζ)
  unfold tubeProperTime
  rw [sq, ← Complex.exp_add, add_halves, Complex.exp_log hw_ne]

private lemma re_tubeProperTime_pos {ζ : Fin 4 → ℂ}
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) :
    0 < (tubeProperTime ζ).re := by
  have hw_slit := negMinkowskiSqC_mem_slitPlane hζ
  have h_gt : -Real.pi < (Complex.log (negMinkowskiSqC ζ)).im :=
    Complex.neg_pi_lt_log_im _
  have h_lt : (Complex.log (negMinkowskiSqC ζ)).im < Real.pi :=
    lt_of_le_of_ne (Complex.log_im_le_pi _) (by
      rw [Complex.log_im]
      exact Complex.slitPlane_arg_ne_pi hw_slit)
  have h_mem : (Complex.log (negMinkowskiSqC ζ) / 2).im ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h_im_div : (Complex.log (negMinkowskiSqC ζ) / 2).im =
        (Complex.log (negMinkowskiSqC ζ)).im / 2 := by
      simp [div_eq_mul_inv]
    rw [Set.mem_Ioo, h_im_div]
    constructor <;> linarith
  unfold tubeProperTime
  rw [Complex.exp_re]
  exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo h_mem)

private lemma coneGap_le_re_tubeProperTime {ζ : Fin 4 → ℂ}
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) :
    coneGap (fun μ => (ζ μ).im) ≤ (tubeProperTime ζ).re := by
  let y : Fin 4 → ℝ := fun μ => (ζ μ).im
  have hgap_pos : 0 < coneGap y := coneGap_pos y hζ
  have hre_pos : 0 < (tubeProperTime ζ).re := re_tubeProperTime_pos hζ
  have h_gap_sq : (coneGap y) ^ 2 ≤ minkowskiInner y y := by
    dsimp [coneGap]
    rw [minkowskiInner_explicit]
    let r : ℝ := Real.sqrt ((y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2)
    have hr_nn : 0 ≤ r := Real.sqrt_nonneg _
    have hr_sq : r ^ 2 = (y 1) ^ 2 + (y 2) ^ 2 + (y 3) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hy0_gt : r < y 0 := by
      have h : 0 < coneGap y := hgap_pos
      dsimp [coneGap, r] at h ⊢
      linarith
    nlinarith
  have h_sq_eq := tubeProperTime_sq hζ
  have h_w_re : (negMinkowskiSqC ζ).re =
      (tubeProperTime ζ).re ^ 2 - (tubeProperTime ζ).im ^ 2 := by
    rw [← h_sq_eq, sq, Complex.mul_re]
    ring
  have h_w_norm : ‖negMinkowskiSqC ζ‖ =
      (tubeProperTime ζ).re ^ 2 + (tubeProperTime ζ).im ^ 2 := by
    rw [← h_sq_eq, norm_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have h_two_le := two_mul_minkowskiInner_im_le_norm_add_re hζ
  have h_re_sq : (coneGap y) ^ 2 ≤ (tubeProperTime ζ).re ^ 2 := by
    dsimp [y] at h_gap_sq
    linarith
  nlinarith

private lemma norm_tubeProperTime_le (ζ : Fin 4 → ℂ) :
    ‖tubeProperTime ζ‖ ≤ 2 * (1 + ‖ζ‖) := by
  by_cases hw : negMinkowskiSqC ζ = 0
  · unfold tubeProperTime
    rw [hw, Complex.log_zero, zero_div, Complex.exp_zero, norm_one]
    have h_nn : 0 ≤ ‖ζ‖ := norm_nonneg ζ
    linarith
  · have h_sq : ‖tubeProperTime ζ‖ ^ 2 = ‖negMinkowskiSqC ζ‖ := by
      have h1 : tubeProperTime ζ ^ 2 = negMinkowskiSqC ζ := by
        unfold tubeProperTime
        rw [sq, ← Complex.exp_add, add_halves, Complex.exp_log hw]
      rw [← norm_pow, h1]
    have h_c : ∀ μ : Fin 4, ‖ζ μ‖ ≤ ‖ζ‖ := fun μ => norm_le_pi_norm ζ μ
    have h_w_le : ‖negMinkowskiSqC ζ‖ ≤ 4 * ‖ζ‖ ^ 2 := by
      dsimp [negMinkowskiSqC, minkowskiInnerC]
      rw [norm_neg]
      have h0 := h_c 0
      have h1 := h_c 1
      have h2 := h_c 2
      have h3 := h_c 3
      have h0_nn := norm_nonneg (ζ 0)
      have h1_nn := norm_nonneg (ζ 1)
      have h2_nn := norm_nonneg (ζ 2)
      have h3_nn := norm_nonneg (ζ 3)
      calc ‖ζ 0 * ζ 0 - ζ 1 * ζ 1 - ζ 2 * ζ 2 - ζ 3 * ζ 3‖
          ≤ ‖ζ 0 * ζ 0 - ζ 1 * ζ 1 - ζ 2 * ζ 2‖ + ‖ζ 3 * ζ 3‖ := norm_sub_le _ _
        _ ≤ (‖ζ 0 * ζ 0 - ζ 1 * ζ 1‖ + ‖ζ 2 * ζ 2‖) + ‖ζ 3 * ζ 3‖ :=
            add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ ((‖ζ 0 * ζ 0‖ + ‖ζ 1 * ζ 1‖) + ‖ζ 2 * ζ 2‖) + ‖ζ 3 * ζ 3‖ :=
            add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
        _ = ‖ζ 0‖ ^ 2 + ‖ζ 1‖ ^ 2 + ‖ζ 2‖ ^ 2 + ‖ζ 3‖ ^ 2 := by
            simp only [norm_mul, sq]
        _ ≤ 4 * ‖ζ‖ ^ 2 := by nlinarith
    have h_sq2 : ‖tubeProperTime ζ‖ ^ 2 ≤ (2 * (1 + ‖ζ‖)) ^ 2 := by
      rw [h_sq]
      have hζ_nn := norm_nonneg ζ
      nlinarith
    have ht_nn := norm_nonneg (tubeProperTime ζ)
    have hζ_nn := norm_nonneg ζ
    nlinarith

private lemma analyticAt_negMinkowskiSqC (ζ : Fin 4 → ℂ) :
    AnalyticAt ℂ negMinkowskiSqC ζ := by
  let e : ∀ μ : Fin 4, (Fin 4 → ℂ) →L[ℂ] ℂ := fun μ => ContinuousLinearMap.proj μ
  have h_eq : negMinkowskiSqC = fun w : Fin 4 → ℂ =>
      -(e 0 w * e 0 w - e 1 w * e 1 w - e 2 w * e 2 w - e 3 w * e 3 w) := rfl
  rw [h_eq]
  exact ((((((e 0).analyticAt ζ).mul ((e 0).analyticAt ζ)).sub
    (((e 1).analyticAt ζ).mul ((e 1).analyticAt ζ))).sub
    (((e 2).analyticAt ζ).mul ((e 2).analyticAt ζ))).sub
    (((e 3).analyticAt ζ).mul ((e 3).analyticAt ζ))).neg

private lemma analyticAt_tubeProperTime {ζ : Fin 4 → ℂ}
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) :
    AnalyticAt ℂ tubeProperTime ζ := by
  let f_sqrt : ℂ → ℂ := fun w => Complex.exp (Complex.log w / 2)
  have hf_diff : DifferentiableOn ℂ f_sqrt Complex.slitPlane := by
    intro w hw
    exact (Complex.differentiableAt_exp.comp w
      ((Complex.differentiableAt_log hw).div_const 2)).differentiableWithinAt
  have hf_ana : AnalyticOnNhd ℂ f_sqrt Complex.slitPlane :=
    Complex.isOpen_slitPlane.analyticOn_iff_analyticOnNhd.mp
      (hf_diff.analyticOn Complex.isOpen_slitPlane)
  exact (hf_ana (negMinkowskiSqC ζ) (negMinkowskiSqC_mem_slitPlane hζ)).comp
    (analyticAt_negMinkowskiSqC ζ)

noncomputable def tubeSpinorBoost (ζ : Fin 4 → ℂ)
    (hζ : (fun μ => (ζ μ).im) ∈ forward_light_cone) : SL2C :=
  ⟨(-(Complex.I / tubeProperTime ζ)) • vec_to_spinor ζ, by
    have hτ_ne : tubeProperTime ζ ≠ 0 := by
      intro h0
      have hre := re_tubeProperTime_pos hζ
      rw [h0, Complex.zero_re] at hre
      exact lt_irrefl 0 hre
    have hτ_sq := tubeProperTime_sq hζ
    have hw_ne : negMinkowskiSqC ζ ≠ 0 :=
      Complex.slitPlane_ne_zero (negMinkowskiSqC_mem_slitPlane hζ)
    rw [Matrix.det_smul, Fintype.card_fin, vec_to_spinor_det]
    have h_mink : (ζ 0) ^ 2 - (ζ 1) ^ 2 - (ζ 2) ^ 2 - (ζ 3) ^ 2 = -negMinkowskiSqC ζ := by
      dsimp [negMinkowskiSqC, minkowskiInnerC]
      ring
    rw [h_mink, neg_sq, div_pow, Complex.I_sq, hτ_sq]
    field_simp [hw_ne]⟩

private lemma analyticAt_vec_to_spinor_entry (r s : Fin 2) (ζ : Fin 4 → ℂ) :
    AnalyticAt ℂ (fun w : Fin 4 → ℂ => vec_to_spinor w r s) ζ := by
  let e : ∀ μ : Fin 4, (Fin 4 → ℂ) →L[ℂ] ℂ := fun μ => ContinuousLinearMap.proj μ
  fin_cases r <;> fin_cases s <;> simp only [Fin.zero_eta, Fin.mk_one]
  · have h_eq : (fun w : Fin 4 → ℂ => vec_to_spinor w 0 0) =
        fun w => e 0 w + e 3 w := by
      ext w
      simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, e]
    rw [h_eq]
    exact ((e 0).analyticAt ζ).add ((e 3).analyticAt ζ)
  · have h_eq : (fun w : Fin 4 → ℂ => vec_to_spinor w 0 1) =
        fun w => e 1 w + (-Complex.I) * e 2 w := by
      ext w
      simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, e]
      ring
    rw [h_eq]
    exact ((e 1).analyticAt ζ).add (analyticAt_const.mul ((e 2).analyticAt ζ))
  · have h_eq : (fun w : Fin 4 → ℂ => vec_to_spinor w 1 0) =
        fun w => e 1 w + Complex.I * e 2 w := by
      ext w
      simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, e]
      ring
    rw [h_eq]
    exact ((e 1).analyticAt ζ).add (analyticAt_const.mul ((e 2).analyticAt ζ))
  · have h_eq : (fun w : Fin 4 → ℂ => vec_to_spinor w 1 1) =
        fun w => e 0 w - e 3 w := by
      ext w
      simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3, e]
      ring
    rw [h_eq]
    exact ((e 0).analyticAt ζ).sub ((e 3).analyticAt ζ)

open Classical in
noncomputable def osTwoPointTruncH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData) :
    ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ
  | 0 => fun α _ => 𝒮 0 α 0
  | 1 => fun α _ => 𝒮 1 α 0
  | 2 => fun α z =>
      if hz : (fun μ => ((z 1 - z 0) μ).im) ∈ forward_light_cone then
        (repTensorHom R 2 (tubeSpinorBoost (z 1 - z 0) hz, 1) *ᵥ
          fun γ => osTwoPointRestH hOS hcluster γ (tubeProperTime (z 1 - z 0))) α
      else 0
  | _ + 3 => fun _ _ => 0

private lemma osTwoPointTruncH_two_of_mem
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (α : Fin 2 → ι) {z : Fin 2 → Fin 4 → ℂ}
    (hz : (fun μ => ((z 1 - z 0) μ).im) ∈ forward_light_cone) :
    osTwoPointTruncH hOS hcluster 2 α z =
      (repTensorHom R 2 (tubeSpinorBoost (z 1 - z 0) hz, 1) *ᵥ
        fun γ => osTwoPointRestH hOS hcluster γ (tubeProperTime (z 1 - z 0))) α := by
  unfold osTwoPointTruncH
  exact dif_pos hz

private lemma diff_im_two_zero_eq (z : Fin 2 → Fin 4 → ℂ) :
    diff_im 2 z 0 (by decide) = fun μ => ((z 1 - z 0) μ).im := by
  ext μ
  simp [diff_im, diff_z]

private lemma sub_two_im_mem_forward_light_cone {z : Fin 2 → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n 2) :
    (fun μ => ((z 1 - z 0) μ).im) ∈ forward_light_cone := by
  rw [← diff_im_two_zero_eq z]
  exact hz 0 (by decide)

theorem analyticOn_osTwoPointTruncH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (n : ℕ) (α : Fin n → ι) :
    AnalyticOn ℂ (osTwoPointTruncH hOS hcluster n α) (forward_tube_n n) := by
  rw [(forward_tube_n_isOpen n).analyticOn_iff_analyticOnNhd]
  intro z₀ hz₀
  match n with
  | 0 => exact analyticAt_const
  | 1 => exact analyticAt_const
  | 2 =>
    let dCLM : (Fin 2 → Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) :=
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 4 → ℂ) (1 : Fin 2) -
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => Fin 4 → ℂ) (0 : Fin 2)
    have hz₀_cone : (fun μ => ((dCLM z₀) μ).im) ∈ forward_light_cone :=
      sub_two_im_mem_forward_light_cone hz₀
    let ζ₀ := dCLM z₀
    have hτ₀_re : 0 < (tubeProperTime ζ₀).re := re_tubeProperTime_pos hz₀_cone
    have hτ₀_ne : tubeProperTime ζ₀ ≠ 0 := by
      intro h0
      rw [h0, Complex.zero_re] at hτ₀_re
      exact lt_irrefl 0 hτ₀_re
    have h_inv_ana : AnalyticAt ℂ (fun w : ℂ => (-(Complex.I / w))) (tubeProperTime ζ₀) := by
      have h_open_ne : IsOpen { w : ℂ | w ≠ 0 } := isOpen_ne
      have h_diff : DifferentiableOn ℂ (fun w : ℂ => -(Complex.I / w)) { w : ℂ | w ≠ 0 } := by
        intro w hw
        exact ((differentiableAt_const Complex.I).div
          differentiableAt_id hw).neg.differentiableWithinAt
      exact (h_open_ne.analyticOn_iff_analyticOnNhd.mp
        (h_diff.analyticOn h_open_ne)) (tubeProperTime ζ₀) hτ₀_ne
    have h_inv_tau : AnalyticAt ℂ ((fun w : ℂ => -(Complex.I / w)) ∘ tubeProperTime) (dCLM z₀) :=
      h_inv_ana.comp (analyticAt_tubeProperTime hz₀_cone)
    have h_scal_ana0 := h_inv_tau.comp (dCLM.analyticAt z₀)
    have h_scal_ana : AnalyticAt ℂ
        (fun z : Fin 2 → Fin 4 → ℂ => -(Complex.I / tubeProperTime (dCLM z))) z₀ := h_scal_ana0
    let f_explicit : (Fin 2 → Fin 4 → ℂ) → ℂ := fun z =>
      ∑ γ : Fin 2 → ι,
        (∏ i : Fin 2, MvPolynomial.eval
          (Sum.elim
            (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
              vec_to_spinor (dCLM z) rs.1 rs.2)
            (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2))
          (R.polynomial (α i) (γ i)).choose) *
          osTwoPointRestH hOS hcluster γ (tubeProperTime (dCLM z))
    have h_poly_ana : ∀ P : MvPolynomial PolyVar ℂ,
        AnalyticAt ℂ (fun z : Fin 2 → Fin 4 → ℂ =>
          MvPolynomial.eval
            (Sum.elim
              (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
                vec_to_spinor (dCLM z) rs.1 rs.2)
              (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2)) P) z₀ := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C a => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ => a) z₀)
      | add P Q ihP ihQ =>
        have h_eq :
            (fun z : Fin 2 → Fin 4 → ℂ =>
              MvPolynomial.eval
                (Sum.elim
                  (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
                    vec_to_spinor (dCLM z) rs.1 rs.2)
                  (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2)) (P + Q)) =
              (fun z : Fin 2 → Fin 4 → ℂ =>
                MvPolynomial.eval
                  (Sum.elim
                    (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
                      vec_to_spinor (dCLM z) rs.1 rs.2)
                    (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2)) P) +
                (fun z : Fin 2 → Fin 4 → ℂ =>
                  MvPolynomial.eval
                    (Sum.elim
                      (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
                        vec_to_spinor (dCLM z) rs.1 rs.2)
                      (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2)) Q) :=
          funext fun _ => map_add _ P Q
        rw [h_eq]
        exact ihP.add ihQ
      | mul_X P v ihP =>
        simp only [map_mul, MvPolynomial.eval_X]
        refine ihP.mul ?_
        rcases v with ⟨r, s⟩ | ⟨r, s⟩
        · have hvts := (analyticAt_vec_to_spinor_entry r s ζ₀).comp (dCLM.analyticAt z₀)
          exact h_scal_ana.mul hvts
        · exact analyticAt_const
    have hf_ana : AnalyticAt ℂ f_explicit z₀ := by
      have h_sum : ∀ s : Finset (Fin 2 → ι),
          AnalyticAt ℂ (fun z : Fin 2 → Fin 4 → ℂ =>
            ∑ γ ∈ s,
              (∏ i : Fin 2, MvPolynomial.eval
                (Sum.elim
                  (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
                    vec_to_spinor (dCLM z) rs.1 rs.2)
                  (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2))
                (R.polynomial (α i) (γ i)).choose) *
                osTwoPointRestH hOS hcluster γ (tubeProperTime (dCLM z))) z₀ := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ => (0 : ℂ)) z₀)
        | insert γ s hγ ih =>
          simp only [Finset.sum_insert hγ]
          have h_prod : AnalyticAt ℂ (fun z : Fin 2 → Fin 4 → ℂ =>
              ∏ i : Fin 2, MvPolynomial.eval
                (Sum.elim
                  (fun rs => (-(Complex.I / tubeProperTime (dCLM z))) *
                    vec_to_spinor (dCLM z) rs.1 rs.2)
                  (fun rs => (1 : Matrix (Fin 2) (Fin 2) ℂ) rs.1 rs.2))
                (R.polynomial (α i) (γ i)).choose) z₀ := by
            simp only [Fin.prod_univ_two]
            exact (h_poly_ana _).mul (h_poly_ana _)
          have h_rest : AnalyticAt ℂ (fun z : Fin 2 → Fin 4 → ℂ =>
              osTwoPointRestH hOS hcluster γ (tubeProperTime (dCLM z))) z₀ := by
            have h_open_re : IsOpen { s : ℂ | 0 < s.re } :=
              isOpen_lt continuous_const Complex.continuous_re
            have h_rest_nhd := (h_open_re.analyticOn_iff_analyticOnNhd.mp
              (analyticOn_osTwoPointRestH hOS hcluster γ)) (tubeProperTime ζ₀) hτ₀_re
            have h_rest_tau :
                AnalyticAt ℂ (osTwoPointRestH hOS hcluster γ ∘ tubeProperTime) (dCLM z₀) :=
              h_rest_nhd.comp (analyticAt_tubeProperTime hz₀_cone)
            have h_rest_comp := h_rest_tau.comp (dCLM.analyticAt z₀)
            exact h_rest_comp
          exact (h_prod.mul h_rest).add ih
      exact h_sum Finset.univ
    have h_ev : osTwoPointTruncH hOS hcluster 2 α =ᶠ[𝓝 z₀] f_explicit := by
      filter_upwards [(forward_tube_n_isOpen 2).mem_nhds hz₀] with z hz
      have hz_cone := sub_two_im_mem_forward_light_cone hz
      rw [osTwoPointTruncH_two_of_mem hOS hcluster α hz_cone]
      dsimp [f_explicit, dCLM]
      simp only [Matrix.mulVec, dotProduct, repTensorHom, MonoidHom.coe_mk, OneHom.coe_mk]
      refine Finset.sum_congr rfl fun γ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      have h_poly_spec := (R.polynomial (α i) (γ i)).choose_spec
        (tubeSpinorBoost (z 1 - z 0) hz_cone, 1)
      rw [h_poly_spec]
      rfl
    exact hf_ana.congr h_ev.symm
  | m + 3 => exact analyticAt_const

lemma inv_coneGap_le_tubeGapFactor {n : ℕ} {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n)
    (i : Fin n) (hi : i.val + 1 < n) :
    (coneGap (diff_im n z i hi))⁻¹ ≤ tubeGapFactor n z := by
  let j₀ : Fin (n - 1) := ⟨i.val, by omega⟩
  have h1 : (coneGap (diff_im n z i hi))⁻¹ ≤
      1 + (coneGap (diff_im n z ⟨j₀.val, fin_sub_one_lt j₀⟩ (fin_sub_one_succ_lt j₀)))⁻¹ := by
    have h_eq : diff_im n z ⟨j₀.val, fin_sub_one_lt j₀⟩ (fin_sub_one_succ_lt j₀) =
        diff_im n z i hi := by
      ext μ
      simp [diff_im, diff_z, j₀]
    rw [h_eq]
    linarith
  refine h1.trans ?_
  unfold tubeGapFactor
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
  have hf_ge1 : ∀ j ∈ Finset.univ.erase j₀,
      1 ≤ 1 + (coneGap (diff_im n z ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j)))⁻¹ := by
    intro j _
    have hg := coneGap_pos
      (diff_im n z ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))
      (hz ⟨j.val, fin_sub_one_lt j⟩ (fin_sub_one_succ_lt j))
    linarith [inv_nonneg.mpr hg.le]
  have h_prod := one_le_prod_real (Finset.univ.erase j₀) _ hf_ge1
  have h_j0_nn :
      0 ≤ 1 + (coneGap (diff_im n z ⟨j₀.val, fin_sub_one_lt j₀⟩ (fin_sub_one_succ_lt j₀)))⁻¹ := by
    have hg := coneGap_pos
      (diff_im n z ⟨j₀.val, fin_sub_one_lt j₀⟩ (fin_sub_one_succ_lt j₀))
      (hz ⟨j₀.val, fin_sub_one_lt j₀⟩ (fin_sub_one_succ_lt j₀))
    linarith [inv_nonneg.mpr hg.le]
  nlinarith

theorem ostubeGrowthBound_osTwoPointTruncH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮) :
    OSTubeGrowthBound (osTwoPointTruncH hOS hcluster) := by
  intro n α
  match n with
  | 0 =>
    refine ⟨‖𝒮 0 α 0‖, 0, 0, norm_nonneg _, fun z _ => ?_⟩
    simp [osTwoPointTruncH]
  | 1 =>
    refine ⟨‖𝒮 1 α 0‖, 0, 0, norm_nonneg _, fun z _ => ?_⟩
    simp [osTwoPointTruncH]
  | 2 =>
    rcases norm_osTwoPointRestH_le_of_powerBound hOS hcluster hpow with ⟨C_r, K_r, hCr_nn, h_rest⟩
    have h_poly_ex : ∀ γ : Fin 2 → ι,
        ∃ (C_p : ℝ) (K_p : ℕ), 0 ≤ C_p ∧
          ∀ p : SL2C × SL2C,
            ‖repTensorHom R 2 p α γ‖ ≤ C_p * (1 + sl2cPairEntrySum p) ^ K_p := by
      intro γ
      rcases isPoly_repTensorHom_entry R 2 α γ with ⟨P, hP⟩
      rcases norm_mvPolynomial_eval_polyPt_le P with ⟨C_p, K_p, hCp_nn, hP_bd⟩
      exact ⟨C_p, K_p, hCp_nn, fun p => by
        have heq := hP p
        dsimp only at heq
        rw [heq]
        exact hP_bd p⟩
    let C_p : (Fin 2 → ι) → ℝ := fun γ => (h_poly_ex γ).choose
    let K_p : (Fin 2 → ι) → ℕ := fun γ => (h_poly_ex γ).choose_spec.choose
    have hCp_nn : ∀ γ, 0 ≤ C_p γ := fun γ => (h_poly_ex γ).choose_spec.choose_spec.1
    have hCp_bd : ∀ γ p, ‖repTensorHom R 2 p α γ‖ ≤ C_p γ * (1 + sl2cPairEntrySum p) ^ K_p γ :=
      fun γ => (h_poly_ex γ).choose_spec.choose_spec.2
    let K_max : ℕ := Finset.univ.sup K_p
    let C_sum : ℝ := ∑ γ : Fin 2 → ι, C_p γ
    have hCsum_nn : 0 ≤ C_sum := Finset.sum_nonneg fun γ _ => hCp_nn γ
    refine ⟨C_sum * C_r * 20 ^ K_max * 10 ^ K_r, K_max + K_r, K_max + K_r, by positivity,
      fun z hz => ?_⟩
    have hz_cone := sub_two_im_mem_forward_light_cone hz
    let ζ : Fin 4 → ℂ := z 1 - z 0
    have hζ_norm0 : ‖ζ‖ ≤ 2 * ‖z‖ := by
      have h0 : ‖z 0‖ ≤ ‖z‖ := norm_le_pi_norm z 0
      have h1 : ‖z 1‖ ≤ ‖z‖ := norm_le_pi_norm z 1
      have h_sub : ‖ζ‖ ≤ ‖z 1‖ + ‖z 0‖ := norm_sub_le (z 1) (z 0)
      linarith
    have hζ_norm : ‖ζ‖ ≤ 2 * (1 + ‖z‖) := by linarith
    have h_gap_le : (coneGap (fun μ => (ζ μ).im))⁻¹ ≤ tubeGapFactor 2 z := by
      rw [← diff_im_two_zero_eq z]
      exact inv_coneGap_le_tubeGapFactor hz 0 (by decide)
    have hτ_re_pos : 0 < (tubeProperTime ζ).re := re_tubeProperTime_pos hz_cone
    have h_re_inv : ((tubeProperTime ζ).re)⁻¹ ≤ tubeGapFactor 2 z := by
      have h1 := inv_anti₀ (coneGap_pos _ hz_cone) (coneGap_le_re_tubeProperTime hz_cone)
      exact h1.trans h_gap_le
    have h_tau_inv : ‖tubeProperTime ζ‖⁻¹ ≤ tubeGapFactor 2 z := by
      have h1 := inv_anti₀ hτ_re_pos (Complex.re_le_norm (tubeProperTime ζ))
      exact h1.trans h_re_inv
    have h_tau_one : 1 + ‖tubeProperTime ζ‖ ≤ 5 * (1 + ‖z‖) := by
      have h1 := norm_tubeProperTime_le ζ
      have hz_nn := norm_nonneg z
      linarith
    have h_gap_ge1 : 1 ≤ tubeGapFactor 2 z := one_le_tubeGapFactor hz
    have h_vts_entry : ∀ r s : Fin 2, ‖vec_to_spinor ζ r s‖ ≤ 2 * ‖ζ‖ := by
      intro r s
      have hc : ∀ μ : Fin 4, ‖ζ μ‖ ≤ ‖ζ‖ := fun μ => norm_le_pi_norm ζ μ
      fin_cases r <;> fin_cases s <;> simp only [Fin.zero_eta, Fin.mk_one]
      · dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
        simp only [mul_one, mul_zero, add_zero]
        exact (norm_add_le _ _).trans (by linarith [hc 0, hc 3])
      · have h_eq : vec_to_spinor ζ 0 1 = ζ 1 - Complex.I * ζ 2 := by
          simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
          ring
        rw [h_eq]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith [hc 1, hc 2]
      · have h_eq : vec_to_spinor ζ 1 0 = ζ 1 + Complex.I * ζ 2 := by
          simp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
          ring
        rw [h_eq]
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith [hc 1, hc 2]
      · dsimp [vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]
        simp only [mul_one, mul_zero, mul_neg, add_zero]
        exact (norm_add_le _ _).trans (by rw [norm_neg]; linarith [hc 0, hc 3])
    let p_boost : SL2C × SL2C := (tubeSpinorBoost ζ hz_cone, 1)
    have h_entry_sum : 1 + sl2cPairEntrySum p_boost ≤ 20 * (1 + ‖z‖) * tubeGapFactor 2 z := by
      have h_b_entry : ∀ r s : Fin 2,
          ‖(tubeSpinorBoost ζ hz_cone).1 r s‖ ≤ 4 * (1 + ‖z‖) * tubeGapFactor 2 z := by
        intro r s
        change ‖(-(Complex.I / tubeProperTime ζ)) * vec_to_spinor ζ r s‖ ≤ _
        rw [norm_mul, norm_neg, norm_div, Complex.norm_I, one_div]
        calc ‖tubeProperTime ζ‖⁻¹ * ‖vec_to_spinor ζ r s‖
            ≤ tubeGapFactor 2 z * (2 * (2 * (1 + ‖z‖))) :=
              mul_le_mul h_tau_inv
                ((h_vts_entry r s).trans (mul_le_mul_of_nonneg_left hζ_norm zero_le_two))
                (norm_nonneg _) (by linarith)
          _ = 4 * (1 + ‖z‖) * tubeGapFactor 2 z := by ring
      have h_1_sum : (∑ r : Fin 2, ∑ s : Fin 2, ‖(1 : SL2C).1 r s‖) = 2 := by
        simp [Fin.sum_univ_two]
        norm_num
      have h_sum_split : sl2cPairEntrySum p_boost =
          (∑ r : Fin 2, ∑ s : Fin 2, ‖(tubeSpinorBoost ζ hz_cone).1 r s‖) +
            (∑ r : Fin 2, ∑ s : Fin 2, ‖(1 : SL2C).1 r s‖) := by
        dsimp [sl2cPairEntrySum, p_boost]
        simp_rw [Finset.sum_add_distrib]
      have h_b_sum : (∑ r : Fin 2, ∑ s : Fin 2, ‖(tubeSpinorBoost ζ hz_cone).1 r s‖) ≤
          16 * (1 + ‖z‖) * tubeGapFactor 2 z := by
        have h00 := h_b_entry 0 0
        have h01 := h_b_entry 0 1
        have h10 := h_b_entry 1 0
        have h11 := h_b_entry 1 1
        simp only [Fin.sum_univ_two]
        linarith
      rw [h_sum_split, h_1_sum]
      have hz_nn : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    rw [osTwoPointTruncH_two_of_mem hOS hcluster α hz_cone]
    simp only [Matrix.mulVec, dotProduct]
    have h_term : ∀ γ : Fin 2 → ι,
        ‖repTensorHom R 2 p_boost α γ * osTwoPointRestH hOS hcluster γ (tubeProperTime ζ)‖ ≤
          C_p γ * (C_r * 20 ^ K_max * 10 ^ K_r *
            (1 + ‖z‖) ^ (K_max + K_r) * (tubeGapFactor 2 z) ^ (K_max + K_r)) := by
      intro γ
      rw [norm_mul]
      have h_K_le : K_p γ ≤ K_max := Finset.le_sup (f := K_p) (Finset.mem_univ γ)
      have h_poly_γ : ‖repTensorHom R 2 p_boost α γ‖ ≤
          C_p γ * (20 ^ K_max * (1 + ‖z‖) ^ K_max * (tubeGapFactor 2 z) ^ K_max) := by
        have h1 := hCp_bd γ p_boost
        have h_b1 : 1 ≤ 1 + sl2cPairEntrySum p_boost := by
          linarith [sl2cPairEntrySum_nonneg p_boost]
        have h2 := pow_le_pow_right₀ h_b1 h_K_le
        have h3 : (1 + sl2cPairEntrySum p_boost) ^ K_max ≤
            (20 * (1 + ‖z‖) * tubeGapFactor 2 z) ^ K_max :=
          pow_le_pow_left₀ (by linarith) h_entry_sum K_max
        calc ‖repTensorHom R 2 p_boost α γ‖
            ≤ C_p γ * (1 + sl2cPairEntrySum p_boost) ^ K_p γ := h1
          _ ≤ C_p γ * (20 * (1 + ‖z‖) * tubeGapFactor 2 z) ^ K_max :=
              mul_le_mul_of_nonneg_left (h2.trans h3) (hCp_nn γ)
          _ = C_p γ * (20 ^ K_max * (1 + ‖z‖) ^ K_max * (tubeGapFactor 2 z) ^ K_max) := by
              rw [mul_pow, mul_pow]
      have h_rest_γ : ‖osTwoPointRestH hOS hcluster γ (tubeProperTime ζ)‖ ≤
          C_r * 10 ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r := by
        have h1 := h_rest γ hτ_re_pos
        have h_p1 : (1 + ‖tubeProperTime ζ‖) ^ K_r ≤ 5 ^ K_r * (1 + ‖z‖) ^ K_r := by
          calc (1 + ‖tubeProperTime ζ‖) ^ K_r
              ≤ (5 * (1 + ‖z‖)) ^ K_r := pow_le_pow_left₀ (by positivity) h_tau_one K_r
            _ = 5 ^ K_r * (1 + ‖z‖) ^ K_r := mul_pow _ _ _
        have h_p2 : (1 + ((tubeProperTime ζ).re)⁻¹) ^ K_r ≤
            2 ^ K_r * (tubeGapFactor 2 z) ^ K_r := by
          calc (1 + ((tubeProperTime ζ).re)⁻¹) ^ K_r
              ≤ (2 * tubeGapFactor 2 z) ^ K_r :=
                pow_le_pow_left₀ (by positivity) (by linarith) K_r
            _ = 2 ^ K_r * (tubeGapFactor 2 z) ^ K_r := mul_pow _ _ _
        have h_prod :
            (1 + ‖tubeProperTime ζ‖) ^ K_r * (1 + ((tubeProperTime ζ).re)⁻¹) ^ K_r ≤
              10 ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r := by
          calc (1 + ‖tubeProperTime ζ‖) ^ K_r * (1 + ((tubeProperTime ζ).re)⁻¹) ^ K_r
              ≤ (5 ^ K_r * (1 + ‖z‖) ^ K_r) * (2 ^ K_r * (tubeGapFactor 2 z) ^ K_r) :=
                mul_le_mul h_p1 h_p2 (by positivity) (by positivity)
            _ = (5 * 2) ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r := by
                rw [mul_pow]
                ring
            _ = 10 ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r := by norm_num
        calc ‖osTwoPointRestH hOS hcluster γ (tubeProperTime ζ)‖
            ≤ C_r * (1 + ‖tubeProperTime ζ‖) ^ K_r *
                (1 + ((tubeProperTime ζ).re)⁻¹) ^ K_r := h1
          _ = C_r * ((1 + ‖tubeProperTime ζ‖) ^ K_r *
                (1 + ((tubeProperTime ζ).re)⁻¹) ^ K_r) := mul_assoc _ _ _
          _ ≤ C_r * (10 ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r) :=
              mul_le_mul_of_nonneg_left h_prod hCr_nn
          _ = C_r * 10 ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r := by ring
      have h_gap_nn : 0 ≤ tubeGapFactor 2 z := by linarith
      have h_cp_nn : 0 ≤ C_p γ := hCp_nn γ
      calc ‖repTensorHom R 2 p_boost α γ‖ *
              ‖osTwoPointRestH hOS hcluster γ (tubeProperTime ζ)‖
          ≤ (C_p γ * (20 ^ K_max * (1 + ‖z‖) ^ K_max * (tubeGapFactor 2 z) ^ K_max)) *
              (C_r * 10 ^ K_r * (1 + ‖z‖) ^ K_r * (tubeGapFactor 2 z) ^ K_r) :=
            mul_le_mul h_poly_γ h_rest_γ (norm_nonneg _) (by positivity)
        _ = C_p γ * (C_r * 20 ^ K_max * 10 ^ K_r *
              ((1 + ‖z‖) ^ K_max * (1 + ‖z‖) ^ K_r) *
              ((tubeGapFactor 2 z) ^ K_max * (tubeGapFactor 2 z) ^ K_r)) := by ring
        _ = C_p γ * (C_r * 20 ^ K_max * 10 ^ K_r *
              (1 + ‖z‖) ^ (K_max + K_r) * (tubeGapFactor 2 z) ^ (K_max + K_r)) := by
            rw [← pow_add, ← pow_add]
    calc ‖∑ γ : Fin 2 → ι,
            repTensorHom R 2 p_boost α γ * osTwoPointRestH hOS hcluster γ (tubeProperTime ζ)‖
        ≤ ∑ γ : Fin 2 → ι,
            ‖repTensorHom R 2 p_boost α γ * osTwoPointRestH hOS hcluster γ (tubeProperTime ζ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ γ : Fin 2 → ι,
            C_p γ * (C_r * 20 ^ K_max * 10 ^ K_r *
              (1 + ‖z‖) ^ (K_max + K_r) * (tubeGapFactor 2 z) ^ (K_max + K_r)) :=
          Finset.sum_le_sum fun γ _ => h_term γ
      _ = C_sum * C_r * 20 ^ K_max * 10 ^ K_r *
            (1 + ‖z‖) ^ (K_max + K_r) * (tubeGapFactor 2 z) ^ (K_max + K_r) := by
          rw [← Finset.sum_mul]
          dsimp [C_sum]
          ring
  | m + 3 =>
    refine ⟨0, 0, 0, le_rfl, fun z _ => ?_⟩
    simp [osTwoPointTruncH]

theorem osTwoPointTruncH_sl2c_covariant
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (n : ℕ) (A B : SL2C) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n)
    (hz' : spinorPhi (A, B) • z ∈ forward_tube_n n)
    (α : Fin n → ι) :
    osTwoPointTruncH hOS hcluster n α (spinorPhi (A, B) • z) =
      ∑ β : Fin n → ι,
        (∏ i : Fin n, R.σ (A, B) (α i) (β i)) * osTwoPointTruncH hOS hcluster n β z := by
  change osTwoPointTruncH hOS hcluster n α (spinorPhi (A, B) • z) =
    (repTensorHom R n (A, B) *ᵥ fun β => osTwoPointTruncH hOS hcluster n β z) α
  match n with
  | 0 =>
    have h1 : repTensorHom R 0 (A, B) = 1 := by
      ext u w
      have huw : u = w := funext fun i => Fin.elim0 i
      subst huw
      simp [repTensorHom]
    dsimp [osTwoPointTruncH]
    rw [h1, Matrix.one_mulVec]
  | 1 =>
    dsimp [osTwoPointTruncH]
    exact congrFun (osOnePoint_sl2c_covariant hOS A B).symm α
  | 2 =>
    let z' : Fin 2 → Fin 4 → ℂ := spinorPhi (A, B) • z
    let ζ : Fin 4 → ℂ := z 1 - z 0
    let ζ' : Fin 4 → ℂ := z' 1 - z' 0
    have hz_cone : (fun μ => (ζ μ).im) ∈ forward_light_cone :=
      sub_two_im_mem_forward_light_cone hz
    have hz'_cone : (fun μ => (ζ' μ).im) ∈ forward_light_cone :=
      sub_two_im_mem_forward_light_cone hz'
    have hζ'_act : vec_to_spinor ζ' = A.1 * vec_to_spinor ζ * B.1ᵀ := by
      have h_sub : ζ' = (spinorPhi_matrix A B).mulVec ζ := by
        change (spinorPhi_matrix A B).mulVec (z 1) - (spinorPhi_matrix A B).mulVec (z 0) = _
        exact (Matrix.mulVec_sub (spinorPhi_matrix A B) (z 1) (z 0)).symm
      rw [h_sub, spinorPhi_matrix_mulVec]
      dsimp [spinor_action]
      exact vec_to_spinor_right_inv _
    have h_det_eq : ∀ w : Fin 4 → ℂ, negMinkowskiSqC w = -(vec_to_spinor w).det := by
      intro w
      rw [vec_to_spinor_det]
      dsimp [negMinkowskiSqC, minkowskiInnerC]
      ring
    have h_neg_sq : negMinkowskiSqC ζ' = negMinkowskiSqC ζ := by
      rw [h_det_eq ζ', h_det_eq ζ, hζ'_act, Matrix.det_mul, Matrix.det_mul,
        Matrix.det_transpose, A.2, B.2, one_mul, mul_one]
    have h_tau : tubeProperTime ζ' = tubeProperTime ζ := by
      unfold tubeProperTime
      rw [h_neg_sq]
    have h_boost_mul :
        tubeSpinorBoost ζ' hz'_cone * contragredientSL2C B =
          A * tubeSpinorBoost ζ hz_cone := by
      apply Subtype.ext
      change (tubeSpinorBoost ζ' hz'_cone).1 * (contragredientSL2C B).1 =
        A.1 * (tubeSpinorBoost ζ hz_cone).1
      have h_c_val : (contragredientSL2C B).1 = (B⁻¹).1ᵀ := rfl
      have h_b1 : (tubeSpinorBoost ζ' hz'_cone).1 =
          (-(Complex.I / tubeProperTime ζ')) • vec_to_spinor ζ' := rfl
      have h_b2 : (tubeSpinorBoost ζ hz_cone).1 =
          (-(Complex.I / tubeProperTime ζ)) • vec_to_spinor ζ := rfl
      have hB : B.1ᵀ * (B⁻¹).1ᵀ = 1 := by
        rw [← Matrix.transpose_mul]
        have hinv : (B⁻¹).1 * B.1 = 1 := congrArg Subtype.val (inv_mul_cancel B)
        rw [hinv, Matrix.transpose_one]
      rw [h_b1, h_b2, h_c_val, h_tau, hζ'_act, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.mul_assoc, hB, Matrix.mul_one]
    let C₀ : SL2C := (contragredientSL2C B)⁻¹
    have h_boost_eq : tubeSpinorBoost ζ' hz'_cone = A * tubeSpinorBoost ζ hz_cone * C₀ :=
      eq_mul_inv_of_mul_eq h_boost_mul
    have hC₀_contra : contragredientSL2C C₀ = B⁻¹ := by
      dsimp [C₀]
      rw [map_inv, contragredientSL2C_involutive]
    have h_pair : (tubeSpinorBoost ζ' hz'_cone, (1 : SL2C)) =
        (A, B) * ((tubeSpinorBoost ζ hz_cone, (1 : SL2C)) * (C₀, contragredientSL2C C₀)) := by
      refine Prod.ext ?_ ?_
      · change tubeSpinorBoost ζ' hz'_cone = A * (tubeSpinorBoost ζ hz_cone * C₀)
        rw [h_boost_eq, mul_assoc]
      · change (1 : SL2C) = B * (1 * contragredientSL2C C₀)
        rw [hC₀_contra, one_mul, mul_inv_cancel]
    rw [osTwoPointTruncH_two_of_mem hOS hcluster α hz'_cone]
    change (repTensorHom R 2 (tubeSpinorBoost ζ' hz'_cone, 1) *ᵥ
      fun γ => osTwoPointRestH hOS hcluster γ (tubeProperTime ζ')) α = _
    have h_rhs_fn :
        (fun β => osTwoPointTruncH hOS hcluster 2 β z) =
          repTensorHom R 2 (tubeSpinorBoost ζ hz_cone, 1) *ᵥ
            fun γ => osTwoPointRestH hOS hcluster γ (tubeProperTime ζ) :=
      funext fun β => osTwoPointTruncH_two_of_mem hOS hcluster β hz_cone
    rw [h_rhs_fn]
    simp_rw [h_tau]
    rw [h_pair, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      osTwoPointRestH_stabilizer hOS hcluster C₀ (re_tubeProperTime_pos hz_cone)]
  | m + 3 =>
    have h0 : (fun β : Fin (m + 3) → ι => osTwoPointTruncH hOS hcluster (m + 3) β z) = 0 := rfl
    rw [h0, Matrix.mulVec_zero]
    rfl

theorem tubeCovariant_osTwoPointTruncH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮) :
    TubeCovariant R
      (vladimirovFromTubeExtension
        (analyticOn_osTwoPointTruncH hOS hcluster)
        (ostubeGrowthBound_osTwoPointTruncH hOS hcluster hpow)) := by
  intro n A z hz hz' α
  exact osTwoPointTruncH_sl2c_covariant hOS hcluster n A (sl2c_conj A) z hz hz' α

private lemma osTwoPointTruncH_wickEmbedN_euclidTimeVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (β : Fin 2 → ι) {r : ℝ} (hr : 0 < r) :
    osTwoPointTruncH hOS hcluster 2 β (wickEmbedN 2 ![0, euclidTimeVec r]) =
      𝒮 2 β ![0, euclidTimeVec r] := by
  let x_r : Fin 2 → Fin 4 → ℝ := ![0, euclidTimeVec r]
  have hx_r : x_r ∈ orderedEuclidN 2 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [x_r, euclidTimeVec] using hr
  have hz_r : wickEmbedN 2 x_r ∈ forward_tube_n 2 :=
    wickEmbedN_mem_forward_tube_n 2 hx_r
  have hz_cone := sub_two_im_mem_forward_light_cone hz_r
  have h_diff_r : wickEmbedN 2 x_r 1 - wickEmbedN 2 x_r 0 = wickEmbed (euclidTimeVec r) := by
    ext μ
    simp [wickEmbedN, x_r, wickEmbed]
  let ζ_r : Fin 4 → ℂ := wickEmbed (euclidTimeVec r)
  have hζ_cone : (fun μ => (ζ_r μ).im) ∈ forward_light_cone := by
    rwa [h_diff_r] at hz_cone
  have h_neg_sq : negMinkowskiSqC ζ_r = (r : ℂ) ^ 2 := by
    dsimp [negMinkowskiSqC, minkowskiInnerC, ζ_r]
    simp only [wickEmbed, euclidTimeVec, ↓reduceIte, Fin.isValue, Fin.reduceEq,
      Complex.ofReal_zero, mul_zero, sub_zero]
    calc -((r : ℂ) * Complex.I * ((r : ℂ) * Complex.I))
        = -(Complex.I ^ 2) * (r : ℂ) ^ 2 := by ring
      _ = (r : ℂ) ^ 2 := by
          rw [Complex.I_sq]
          ring
  have h_tau_r : tubeProperTime ζ_r = (r : ℂ) := by
    have hsq : tubeProperTime ζ_r ^ 2 = (r : ℂ) ^ 2 :=
      (tubeProperTime_sq hζ_cone).trans h_neg_sq
    have hfac : (tubeProperTime ζ_r - (r : ℂ)) * (tubeProperTime ζ_r + (r : ℂ)) = 0 := by
      linear_combination hsq
    have hsum_ne : tubeProperTime ζ_r + (r : ℂ) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith [re_tubeProperTime_pos hζ_cone]
    rcases mul_eq_zero.mp hfac with hsub | hsum
    · exact sub_eq_zero.mp hsub
    · exact False.elim (hsum_ne hsum)
  have h_boost_one : tubeSpinorBoost ζ_r hζ_cone = 1 := by
    apply Subtype.ext
    change (-(Complex.I / tubeProperTime ζ_r)) • vec_to_spinor ζ_r = 1
    rw [h_tau_r, vec_to_spinor_wickEmbed_euclidTimeVec, smul_smul]
    have hr_c : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hc : -(Complex.I / (r : ℂ)) * (Complex.I * (r : ℂ)) = 1 := by
      field_simp [hr_c]
      rw [Complex.I_sq]
      ring
    rw [hc, one_smul]
  rw [osTwoPointTruncH_two_of_mem hOS hcluster β hz_cone]
  have h_eq_rhs :
      (repTensorHom R 2
        (tubeSpinorBoost (wickEmbedN 2 x_r 1 - wickEmbedN 2 x_r 0) hz_cone, 1) *ᵥ
        fun γ => osTwoPointRestH hOS hcluster γ
          (tubeProperTime (wickEmbedN 2 x_r 1 - wickEmbedN 2 x_r 0))) =
      (repTensorHom R 2 (tubeSpinorBoost ζ_r hζ_cone, 1) *ᵥ
        fun γ => osTwoPointRestH hOS hcluster γ (tubeProperTime ζ_r)) := by
    congr 1
    · congr 1
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      change (-(Complex.I / tubeProperTime (wickEmbedN 2 x_r 1 - wickEmbedN 2 x_r 0))) •
          vec_to_spinor (wickEmbedN 2 x_r 1 - wickEmbedN 2 x_r 0) =
        (-(Complex.I / tubeProperTime ζ_r)) • vec_to_spinor ζ_r
      rw [h_diff_r]
    · ext γ
      rw [h_diff_r]
  rw [h_eq_rhs, h_boost_one]
  have h_one_pair : ((1 : SL2C), (1 : SL2C)) = (1 : SL2C × SL2C) := rfl
  rw [h_one_pair, map_one, Matrix.one_mulVec, h_tau_r]
  exact osTwoPointRestH_real_eq hOS hcluster β hr

theorem schwinger_eq_osTwoPointTruncH
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    {n : ℕ} (hn : n ≤ 2) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    𝒮 n α x = osTwoPointTruncH hOS hcluster n α (wickEmbedN n x) := by
  match n with
  | 0 =>
    have hx0 : x = 0 := Subsingleton.elim x 0
    rw [hx0]
    rfl
  | 1 =>
    have hx_shift : x = fun i => (0 : Fin 1 → Fin 4 → ℝ) i + x 0 := by
      ext i μ
      fin_cases i
      simp
    rw [hx_shift, hOS.os1_translation 1 α 0 (fun _ hi => by omega) (x 0)]
    rfl
  | 2 =>
    let v : Fin 4 → ℝ := x 1 - x 0
    have hv0 : 0 < v 0 := by
      simpa [v] using hx 0 (by decide)
    have hv_ne : v ≠ 0 := by
      intro h0
      have h := congrFun h0 0
      simp only [Pi.zero_apply] at h
      linarith
    have hv_pos : 0 < euclidInner v v :=
      lt_of_le_of_ne (euclidInner_self_nonneg v)
        (Ne.symm ((euclidInner_self_eq_zero_iff v).not.mpr hv_ne))
    let r : ℝ := Real.sqrt (euclidInner v v)
    have hr : 0 < r := Real.sqrt_pos.mpr hv_pos
    let U : SU2 := alignPosTimeSU2 v
    have h_align : euclidRotApply U 1 v = euclidTimeVec r := by
      rw [euclidRotApply_alignPosTimeSU2]
      ext μ
      fin_cases μ <;> rfl
    have h_inv_apply : euclidRotApply U⁻¹ 1 (euclidTimeVec r) = v := by
      rw [← h_align]
      simpa using euclidRotApply_inv_self U 1 v
    have h_rot_pair : euclidRotN 2 U⁻¹ 1 ![0, euclidTimeVec r] = ![0, v] := by
      ext i μ
      fin_cases i
      · change ((euclidRotOfSU2 U⁻¹ 1).mulVec 0) μ = (0 : Fin 4 → ℝ) μ
        simp
      · change ((euclidRotOfSU2 U⁻¹ 1).mulVec (euclidTimeVec r)) μ = v μ
        rw [euclidRotOfSU2_mulVec, h_inv_apply]
    have h_ord_r : (![0, euclidTimeVec r] : Fin 2 → Fin 4 → ℝ) ∈ orderedEuclidN 2 := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa [euclidTimeVec] using hr
    have h_ord_v : (![0, v] : Fin 2 → Fin 4 → ℝ) ∈ orderedEuclidN 2 := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      simpa using hv0
    have h_shift_x : x = fun i => (![0, v] : Fin 2 → Fin 4 → ℝ) i + x 0 := by
      ext i μ
      fin_cases i
      · simp
      · simp [v]
    have h_lhs_tr : 𝒮 2 α x = 𝒮 2 α ![0, v] := by
      rw [h_shift_x]
      exact hOS.os1_translation 2 α ![0, v] h_ord_v (x 0)
    have h_rhs_tr :
        osTwoPointTruncH hOS hcluster 2 α (wickEmbedN 2 x) =
          osTwoPointTruncH hOS hcluster 2 α (wickEmbedN 2 ![0, v]) := by
      have h_diff_eq :
          wickEmbedN 2 x 1 - wickEmbedN 2 x 0 =
            wickEmbedN 2 ![0, v] 1 - wickEmbedN 2 ![0, v] 0 := by
        ext μ
        fin_cases μ <;>
          · simp [wickEmbedN, wickEmbed, v]
            try ring
      have hz1 := sub_two_im_mem_forward_light_cone (wickEmbedN_mem_forward_tube_n 2 hx)
      have hz2 := sub_two_im_mem_forward_light_cone (wickEmbedN_mem_forward_tube_n 2 h_ord_v)
      rw [osTwoPointTruncH_two_of_mem hOS hcluster α hz1,
        osTwoPointTruncH_two_of_mem hOS hcluster α hz2]
      have h_vec_eq :
          (repTensorHom R 2
            (tubeSpinorBoost (wickEmbedN 2 x 1 - wickEmbedN 2 x 0) hz1, 1) *ᵥ
            fun γ => osTwoPointRestH hOS hcluster γ
              (tubeProperTime (wickEmbedN 2 x 1 - wickEmbedN 2 x 0))) =
          (repTensorHom R 2
            (tubeSpinorBoost (wickEmbedN 2 ![0, v] 1 - wickEmbedN 2 ![0, v] 0) hz2, 1) *ᵥ
            fun γ => osTwoPointRestH hOS hcluster γ
              (tubeProperTime (wickEmbedN 2 ![0, v] 1 - wickEmbedN 2 ![0, v] 0))) := by
        congr 1
        · congr 1
          refine Prod.ext ?_ rfl
          apply Subtype.ext
          change (-(Complex.I / tubeProperTime (wickEmbedN 2 x 1 - wickEmbedN 2 x 0))) •
              vec_to_spinor (wickEmbedN 2 x 1 - wickEmbedN 2 x 0) =
            (-(Complex.I / tubeProperTime
              (wickEmbedN 2 ![0, v] 1 - wickEmbedN 2 ![0, v] 0))) •
              vec_to_spinor (wickEmbedN 2 ![0, v] 1 - wickEmbedN 2 ![0, v] 0)
          rw [h_diff_eq]
        · ext γ
          rw [h_diff_eq]
      exact congrFun h_vec_eq α
    rw [h_lhs_tr, h_rhs_tr, ← h_rot_pair,
      hOS.os1_rotation 2 U⁻¹ 1 ![0, euclidTimeVec r] h_ord_r (by rwa [h_rot_pair]) α,
      wickEmbedN_euclidRotN,
      osTwoPointTruncH_sl2c_covariant hOS hcluster 2 (su2ToSL2C U⁻¹) (su2ToSL2C 1)
        (wickEmbedN 2 ![0, euclidTimeVec r]) (wickEmbedN_mem_forward_tube_n 2 h_ord_r)
        (by rw [← wickEmbedN_euclidRotN, h_rot_pair]
            exact wickEmbedN_mem_forward_tube_n 2 h_ord_v) α]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [osTwoPointTruncH_wickEmbedN_euclidTimeVec hOS hcluster β hr]
  | m + 3 => omega

noncomputable def osTwoPointTruncSchwinger (𝒮 : SchwingerFamily ι) : SchwingerFamily ι :=
  fun n α x => if n ≤ 2 then 𝒮 n α x else 0

noncomputable def osTwoPointWightmanFamily
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮) :
    WightmanFamily ι :=
  vladimirovFromTubeWightmanFamily
    (analyticOn_osTwoPointTruncH hOS hcluster)
    (ostubeGrowthBound_osTwoPointTruncH hOS hcluster hpow)

noncomputable def osTwoPointExtension
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮) :
    TubeExtension (osTwoPointWightmanFamily hOS hcluster hpow) :=
  vladimirovFromTubeExtension
    (analyticOn_osTwoPointTruncH hOS hcluster)
    (ostubeGrowthBound_osTwoPointTruncH hOS hcluster hpow)

theorem os_two_point_wightman_reconstruction
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮) :
    let W₂ := osTwoPointWightmanFamily hOS hcluster hpow
    let E₂ := osTwoPointExtension hOS hcluster hpow
    (∀ (n : ℕ), n ≤ 2 → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E₂ n α x) ∧
    TubeCovariant R E₂ ∧
    TubeTranslationInvariant E₂ ∧
    SpectrumCondition W₂ ∧
    PoincareCovariant R W₂ ∧
    TubePCT η R E₂ ∧
    WeakLocality η W₂ ∧
    PositivityUpTo 1 S W₂ := by
  let h_ana := analyticOn_osTwoPointTruncH hOS hcluster
  let h_growth := ostubeGrowthBound_osTwoPointTruncH hOS hcluster hpow
  let 𝒮_tr := osTwoPointTruncSchwinger 𝒮
  have h_schw_tr : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮_tr n α x = osTwoPointTruncH hOS hcluster n α (wickEmbedN n x) := by
    intro n α x hx
    dsimp [𝒮_tr, osTwoPointTruncSchwinger]
    split_ifs with hn
    · exact schwinger_eq_osTwoPointTruncH hOS hcluster hn α hx
    · match n with
      | 0 => omega
      | 1 => omega
      | 2 => omega
      | m + 3 => rfl
  have h_trans_tr : OSTranslationInvariant 𝒮_tr := by
    intro n α x hx a
    dsimp [𝒮_tr, osTwoPointTruncSchwinger]
    split_ifs with hn
    · exact hOS.os1_translation n α x hx a
    · rfl
  have h_sym_tr : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      𝒮_tr n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) *
          ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * 𝒮_tr n (β ∘ Fin.rev) x := by
    intro n α x hx
    dsimp [𝒮_tr, osTwoPointTruncSchwinger]
    split_ifs with hn
    · exact hOS.os3_symmetry n α x hx
    · simp
  have hcov : TubeCovariant R (osTwoPointExtension hOS hcluster hpow) :=
    tubeCovariant_osTwoPointTruncH hOS hcluster hpow
  have htrans : TubeTranslationInvariant (osTwoPointExtension hOS hcluster hpow) :=
    vladimirovFromTube_tubeTranslationInvariant h_ana h_growth 𝒮_tr h_trans_tr h_schw_tr
  have hspec : SpectrumCondition (osTwoPointWightmanFamily hOS hcluster hpow) :=
    vladimirovFromTube_spectrumCondition h_ana h_growth htrans
  have hP : PoincareCovariant R (osTwoPointWightmanFamily hOS hcluster hpow) :=
    vladimirovFromTube_poincareCovariant R h_ana h_growth 𝒮_tr h_trans_tr h_schw_tr hcov
  have hpct : TubePCT η R (osTwoPointExtension hOS hcluster hpow) :=
    vladimirovFromTube_tubePCT R h_ana h_growth 𝒮_tr h_schw_tr h_sym_tr
  have hwloc : WeakLocality η (osTwoPointWightmanFamily hOS hcluster hpow) :=
    vladimirovFromTube_weakLocality R h_ana h_growth 𝒮_tr h_schw_tr h_sym_tr hcov
  have h_schw_le2 : ∀ (n : ℕ), n ≤ 2 → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      𝒮 n α x = schwingerFromTube (osTwoPointExtension hOS hcluster hpow) n α x :=
    fun n hn α _ hx => schwinger_eq_osTwoPointTruncH hOS hcluster hn α hx
  have hpos1 : PositivityUpTo 1 S (osTwoPointWightmanFamily hOS hcluster hpow) :=
    positivityUpTo_of_osAxioms_and_tube 1 hOS (osTwoPointExtension hOS hcluster hpow)
      (fun n hn α x hx => h_schw_le2 n (by omega) α x hx) hspec hP
  exact ⟨h_schw_le2, hcov, htrans, hspec, hP, hpct, hwloc, hpos1⟩

theorem osTwoPointWightmanFamily_eq_of_tubeExtensionData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hpow : OSPositiveTimeTwoPointPowerBound 𝒮)
    (T : OSTubeExtensionData R 𝒮) {n : ℕ} (hn : n ≤ 2) :
    osTwoPointWightmanFamily hOS hcluster hpow n = T.W n := by
  let E₁ := osTwoPointExtension hOS hcluster hpow
  let E₂ := T.E
  have hH_eq : ∀ (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → E₁.H n α z = E₂.H n α z := by
    intro α z hz
    refine analyticOn_forward_tube_eq_of_wickEmbedN_eq n
      (E₁.analytic n α) (E₂.analytic n α) (fun x hx => ?_) hz
    change osTwoPointTruncH hOS hcluster n α (wickEmbedN n x) = T.H n α (wickEmbedN n x)
    rw [← schwinger_eq_osTwoPointTruncH hOS hcluster hn α hx, T.schwinger_eq n α x hx]
  ext α f
  have hv : euclidTimeVec 1 ∈ forward_light_cone := timeUnitVec_mem_forward_light_cone
  have hb₁ := E₁.boundary n α f (euclidTimeVec 1) hv
  have hb₂ := E₂.boundary n α f (euclidTimeVec 1) hv
  have h_ev : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
      E₁.H n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) *
        f x) =ᶠ[𝓝[>] (0 : ℝ)]
    (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
      E₂.H n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) *
        f x) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    congr 1
    ext x
    congr 1
    apply hH_eq α
    intro i hi
    have h_im : (fun k : Fin 4 => -((((fun j m => (x j m : ℂ) +
          Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) i -
        (fun j m => (x j m : ℂ) +
          Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) ⟨i.val + 1, hi⟩) k).im)) =
        fun k : Fin 4 => if k = 0 then t else 0 := by
      ext k
      fin_cases k <;> · simp [euclidTimeVec, Complex.sub_im, Complex.add_im]; try ring
    change (fun k : Fin 4 => -((((fun j m => (x j m : ℂ) +
        Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) i -
      (fun j m => (x j m : ℂ) +
        Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) ⟨i.val + 1, hi⟩) k).im)) ∈
      forward_light_cone
    rw [h_im]
    dsimp [forward_light_cone]
    rw [minkowskiInner_explicit]
    simp only [↓reduceIte, Fin.isValue, Fin.reduceEq, mul_zero, sub_zero]
    exact ⟨ht, mul_pos ht ht⟩
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique (hb₁.congr' h_ev) hb₂

theorem os_to_wightman_full_synthesis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (hnorm : OSVacuumNormalized 𝒮)
    (T : OSTubeExtensionData R 𝒮) :
    let P := T.toForwardConeOSReconstructedWightman hOS hcluster
    let G := T.toGeneralWightmanAxiomsWithUniqueVacuum hOS hcluster hnorm
    let U := T.osToWightmanUnitaryEquiv hOS hcluster
    G.WData.W = T.W ∧
    (∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube T.E n α x) ∧
    U P.vacuum = P.wightmanVacuumVec ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : P.Hilbert),
      U (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (euclidTimeReflect a) Ψ) =
        wightmanTranslate P.toWightmanPositiveData
          (wightmanTranslationInvariant_of_poincare R P.poincare) a (U Ψ)) ∧
    ((∀ {ε : ℂ}, R.HasSpinParity ε → (∃ β : Fin 2 → ι, T.W 2 β ≠ 0) → η = ε) ∧
      (∀ {ε : ℂ}, R.HasSpinParity ε →
        (∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
          x ∈ orderedEuclidN n ∧ 𝒮 n α x ≠ 0) → η = ε)) ∧
    ((η = 1 ∨ η = -1) → LocalCommutativity η T.W →
      FullEuclidOSAxioms R S η P.permutedSchwinger ∧
      ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
        x ∈ orderedEuclidN n → P.permutedSchwinger n α x = 𝒮 n α x) := by
  let P := T.toForwardConeOSReconstructedWightman hOS hcluster
  have h_holo : P.semigroup.IsWeaklyHolomorphic :=
    hOS.isWeaklyHolomorphic_canonicalHolomorphicSemigroup_of_timeCluster hcluster
  refine ⟨rfl, fun n α _ hx => T.schwingerFromTube_eq n α hx,
    P.osToWightmanLinearIsometryEquiv_vacuum,
    P.osToWightmanLinearIsometryEquiv_spacetimeTranslate h_holo,
    ⟨fun hε h_nondeg => P.spin_statistics hε h_nondeg,
     fun hε h_nondeg => osAxioms_spin_statistics hOS hε h_nondeg⟩,
    fun hη hloc =>
      ⟨P.toFullEuclidOSAxioms hη hloc,
       fun n α _ hx => P.permutedSchwinger_eq_on_orderedEuclidN hη hloc n α hx⟩⟩

end

end QFT
