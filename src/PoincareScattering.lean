import ScatteringTheory

open scoped ComplexConjugate Topology BigOperators Matrix InnerProductSpace
open Geometry Geometry.MatrixAnalysis MeasureTheory Filter Complex Matrix

namespace QFT

noncomputable section

section MatrixIdentities

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma starStructure_conj_mul_self {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    S.C.map star * S.C = 1 :=
  mul_eq_one_comm.mp S.involutive

lemma starStructure_intertwine_rep {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A : SL2C) :
    S.C * R.rep A = (R.rep A).map star * S.C := by
  have h := S.intertwine A (sl2c_conj A)
  rw [sl2c_conj_conj] at h
  exact h

lemma starStructure_rep_inv_bra_ket {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A : SL2C) (α δ : ι) :
    (∑ γ : ι, ∑ β : ι, star (R.rep A⁻¹ α γ) * S.C γ β * R.rep A β δ) = S.C α δ := by
  have hmap_eq : ∀ M : Matrix ι ι ℂ, M.map star = M.map (starRingEnd ℂ) := fun _ => rfl
  have hmat : (R.rep A⁻¹).map (starRingEnd ℂ) * (S.C * R.rep A) = S.C := by
    rw [starStructure_intertwine_rep S A, hmap_eq, ← Matrix.mul_assoc]
    have hmul : (R.rep A⁻¹).map (starRingEnd ℂ) * (R.rep A).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [hmul, Matrix.one_mul]
  have hentry := congrArg (fun M : Matrix ι ι ℂ => M α δ) hmat
  dsimp only [Matrix.mul_apply, Matrix.map_apply] at hentry
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Complex.star_def] at hentry
  exact hentry

lemma pctMatrix_conj_mul_C {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {ε : ℂ} (hε : R.HasSpinParity ε) :
    (pctMatrix S).map star * S.C = ε • R.σ (-1, 1) := by
  unfold pctMatrix
  have hmap : (S.C * R.σ (-1, 1)).map star = S.C.map star * (R.σ (-1, 1)).map star := by
    change (S.C * R.σ (-1, 1)).map (starRingEnd ℂ) =
      S.C.map (starRingEnd ℂ) * (R.σ (-1, 1)).map (starRingEnd ℂ)
    exact Matrix.map_mul
  rw [hmap, Matrix.mul_assoc]
  have hint : (R.σ (-1, 1)).map star * S.C = S.C * R.σ (1, -1) := by
    have h := S.intertwine 1 (-1)
    have hcm1 : sl2c_conj (-1 : SL2C) = -1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
    rw [sl2c_conj_one, hcm1] at h
    exact h.symm
  rw [hint, ← Matrix.mul_assoc, starStructure_conj_mul_self S, Matrix.one_mul]
  have h1m1 : ((1 : SL2C), (-1 : SL2C)) = ((-1 : SL2C), (-1 : SL2C)) * (-1, 1) := by
    ext <;> simp
  rw [h1m1, map_mul, hε.1, Algebra.smul_mul_assoc, Matrix.one_mul]

lemma pctMatrix_conj_mul_self {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {ε : ℂ} (hε : R.HasSpinParity ε) :
    (pctMatrix S).map star * pctMatrix S = ε • (1 : Matrix ι ι ℂ) := by
  have h_assoc : (pctMatrix S).map star * pctMatrix S =
      ((pctMatrix S).map star * S.C) * R.σ (-1, 1) := by
    unfold pctMatrix
    rw [Matrix.mul_assoc]
  rw [h_assoc, pctMatrix_conj_mul_C S hε, Algebra.smul_mul_assoc, ← map_mul]
  have hsq : ((-1 : SL2C), (1 : SL2C)) * (-1, 1) = 1 := by
    ext <;> simp
  rw [hsq, map_one]

lemma pctMatrix_comm_rep {R : HolomorphicLorentzRep ι} (S : StarStructure R) (A : SL2C) :
    (R.rep A).map star * pctMatrix S = pctMatrix S * R.rep A := by
  unfold pctMatrix
  rw [← Matrix.mul_assoc, ← starStructure_intertwine_rep S A, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  change R.σ (A, sl2c_conj A) * R.σ (-1, 1) = R.σ (-1, 1) * R.σ (A, sl2c_conj A)
  rw [← map_mul, ← map_mul]
  have hcomm : (A, sl2c_conj A) * (-1, (1 : SL2C)) = (-1, (1 : SL2C)) * (A, sl2c_conj A) := by
    ext <;> simp
  rw [hcomm]

lemma rep_neg_one_of_hasSpinParity {R : HolomorphicLorentzRep ι} {ε : ℂ}
    (hε : R.HasSpinParity ε) :
    R.rep (-1 : SL2C) = ε • (1 : Matrix ι ι ℂ) := by
  have hcm1 : sl2c_conj (-1 : SL2C) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
  change R.σ (-1, sl2c_conj (-1)) = ε • 1
  rw [hcm1, hε.1]

lemma lorentzOfSL2C_neg_one : lorentzOfSL2C (-1 : SL2C) = 1 := by
  have hstd : stdRep.rep (-1 : SL2C) = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
    simpa using rep_neg_one_of_hasSpinParity stdRep_spinParity
  rw [stdRep_rep] at hstd
  ext μ ν
  have hentry := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => (M μ ν).re) hstd
  rw [Matrix.one_apply] at hentry ⊢
  by_cases hμν : μ = ν
  · rw [if_pos hμν] at hentry ⊢
    simpa using hentry
  · rw [if_neg hμν] at hentry ⊢
    simpa using hentry

theorem wightman_eq_zero_of_odd_of_spinParity_neg_one
    {R : HolomorphicLorentzRep ι} {W : WightmanFamily ι}
    (hP : PoincareCovariant R W) (hε : R.HasSpinParity (-1))
    {n : ℕ} (hn : Odd n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 := by
  have h_act : ∀ x : Fin n → Fin 4 → ℝ,
      f (fun i => poincareAct 0 (-1) (x i)) = f x := by
    intro x
    congr 1
    ext i μ
    simp [poincareAct, lorentzOfSL2C_neg_one]
  have hcov := hP n 0 (-1) f f h_act α
  have hrep := rep_neg_one_of_hasSpinParity hε
  have hsum : (∑ β : Fin n → ι, (∏ i : Fin n, R.rep (-1) (α i) (β i)) * W n β f) =
      ((-1 : ℂ) ^ n) * W n α f := by
    have hterm : ∀ β : Fin n → ι,
        (∏ i : Fin n, R.rep (-1) (α i) (β i)) =
          if α = β then (-1 : ℂ) ^ n else 0 := by
      intro β
      simp_rw [hrep]
      by_cases hαβ : α = β
      · subst hαβ
        simp
      · rw [if_neg hαβ]
        obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
          by_contra hc
          push Not at hc
          exact hαβ (funext hc)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply_ne hi])
    simp_rw [hterm, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hsum, hn.neg_one_pow, neg_one_mul] at hcov
  linear_combination (1 / 2 : ℂ) * hcov

end MatrixIdentities

section SpinorLorentzHilbert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wightmanSpinorLorentzBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) (C : WightmanConfig ι) :
    WightmanPreHilbertSpace WData :=
  ∑ γ : Fin C.1 → ι,
    (∏ i : Fin C.1, R.rep A⁻¹ (C.2.1 i) (γ i)) •
      wightmanBasisPre WData ⟨C.1, (γ, compactSchwartzLorentz C.1 A C.2.2)⟩

def wightmanSpinorLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) :
    WightmanPreHilbertSpace WData →ₗ[ℂ] WightmanPreHilbertSpace WData :=
  (Finsupp.linearCombination ℂ (wightmanSpinorLorentzBasis WData A)).comp
    (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap

@[simp]
lemma wightmanSpinorLorentzLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) (C : WightmanConfig ι) :
    wightmanSpinorLorentzLM WData A (wightmanBasisPre WData C) =
      wightmanSpinorLorentzBasis WData A C := by
  unfold wightmanSpinorLorentzLM
  change Finsupp.linearCombination ℂ (wightmanSpinorLorentzBasis WData A)
      (Finsupp.single C 1) = wightmanSpinorLorentzBasis WData A C
  simp

omit [Fintype ι] in
lemma prod_one_matrix_eq_ite {n : ℕ} (α γ : Fin n → ι) :
    (∏ i : Fin n, (1 : Matrix ι ι ℂ) (α i) (γ i)) = if α = γ then 1 else 0 := by
  by_cases hαγ : α = γ
  · subst hαγ
    simp
  · rw [if_neg hαγ]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ γ i := by
      by_contra hc
      push Not at hc
      exact hαγ (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)

omit [DecidableEq ι] in
lemma sum_prod_matrix_mul {n : ℕ} (M N : Matrix ι ι ℂ) (α δ : Fin n → ι) :
    (∑ γ : Fin n → ι, (∏ i : Fin n, M (α i) (γ i)) * (∏ i : Fin n, N (γ i) (δ i))) =
      ∏ i : Fin n, (M * N) (α i) (δ i) := by
  simp_rw [← Finset.prod_mul_distrib, Matrix.mul_apply]
  exact (Fintype.prod_sum fun (i : Fin n) (c : ι) => M (α i) c * N c (δ i)).symm

@[simp]
lemma wightmanSpinorLorentzLM_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) :
    wightmanSpinorLorentzLM WData 1 = LinearMap.id := by
  apply LinearMap.ext
  intro Ψ
  conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  conv_rhs => rw [LinearMap.id_apply, wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  unfold Finsupp.sum
  rw [map_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [map_smul, wightmanSpinorLorentzLM_wightmanBasisPre]
  congr 1
  rcases C with ⟨n, α, f⟩
  unfold wightmanSpinorLorentzBasis
  have h1 : R.rep (1 : SL2C)⁻¹ = (1 : Matrix ι ι ℂ) := by rw [inv_one, map_one]
  change (∑ γ : Fin n → ι,
      (∏ i : Fin n, R.rep (1 : SL2C)⁻¹ (α i) (γ i)) •
        wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n 1 f)⟩) =
    wightmanBasisPre WData ⟨n, (α, f)⟩
  rw [Finset.sum_eq_single α]
  · rw [h1, prod_one_matrix_eq_ite (ι := ι) α α, if_pos rfl, one_smul, compactSchwartzLorentz_one]
  · intro γ _ hγα
    rw [h1, prod_one_matrix_eq_ite (ι := ι) α γ, if_neg hγα.symm, zero_smul]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))

lemma wightmanSpinorLorentzLM_basis_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : SL2C) (C : WightmanConfig ι) :
    wightmanSpinorLorentzBasis WData (A * B) C =
      wightmanSpinorLorentzLM WData A (wightmanSpinorLorentzBasis WData B C) := by
  rcases C with ⟨n, α, f⟩
  have h_lhs : wightmanSpinorLorentzBasis WData (A * B) ⟨n, (α, f)⟩ =
      ∑ δ : Fin n → ι,
        (∏ i : Fin n, R.rep (A * B)⁻¹ (α i) (δ i)) •
          wightmanBasisPre WData ⟨n, (δ, compactSchwartzLorentz n (A * B) f)⟩ := rfl
  have h_rhs : wightmanSpinorLorentzBasis WData B ⟨n, (α, f)⟩ =
      ∑ γ : Fin n → ι,
        (∏ i : Fin n, R.rep B⁻¹ (α i) (γ i)) •
          wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n B f)⟩ := rfl
  rw [h_lhs, h_rhs, map_sum]
  have hstep : ∀ γ : Fin n → ι,
      wightmanSpinorLorentzLM WData A
          ((∏ i : Fin n, R.rep B⁻¹ (α i) (γ i)) •
            wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n B f)⟩) =
        ∑ δ : Fin n → ι,
          ((∏ i : Fin n, R.rep B⁻¹ (α i) (γ i)) *
            (∏ i : Fin n, R.rep A⁻¹ (γ i) (δ i))) •
            wightmanBasisPre WData ⟨n, (δ, compactSchwartzLorentz n (A * B) f)⟩ := by
    intro γ
    rw [map_smul, wightmanSpinorLorentzLM_wightmanBasisPre]
    change (∏ i : Fin n, R.rep B⁻¹ (α i) (γ i)) •
        (∑ δ : Fin n → ι,
          (∏ i : Fin n, R.rep A⁻¹ (γ i) (δ i)) •
            wightmanBasisPre WData
              ⟨n, (δ, compactSchwartzLorentz n A (compactSchwartzLorentz n B f))⟩) = _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [smul_smul, ← compactSchwartzLorentz_mul n A B f]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [← Finset.sum_smul, sum_prod_matrix_mul]
  have hmul : R.rep (A * B)⁻¹ = R.rep B⁻¹ * R.rep A⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul]
  rw [hmul]

lemma wightmanSpinorLorentzLM_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A B : SL2C) :
    wightmanSpinorLorentzLM WData (A * B) =
      (wightmanSpinorLorentzLM WData A).comp (wightmanSpinorLorentzLM WData B) := by
  apply LinearMap.ext
  intro Ψ
  rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ,
      map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun C _ => ?_
  rw [map_smul, LinearMap.comp_apply, map_smul, wightmanSpinorLorentzLM_wightmanBasisPre,
      wightmanSpinorLorentzLM_wightmanBasisPre, map_smul, wightmanSpinorLorentzLM_basis_mul]

@[simp]
lemma wightmanSpinorLorentzLM_vacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) :
    wightmanSpinorLorentzLM WData A (wightmanVacuumPre WData) =
      wightmanVacuumPre WData := by
  unfold wightmanVacuumPre
  rw [wightmanSpinorLorentzLM_wightmanBasisPre]
  change (∑ γ : Fin 0 → ι,
      (∏ i : Fin 0, R.rep A⁻¹ (Fin.elim0 i) (γ i)) •
        wightmanBasisPre WData
          ⟨0, (γ, compactSchwartzLorentz 0 A (momentumWavepacketCompactSchwartz 0 0))⟩) =
    wightmanBasisPre WData (wightmanVacuumConfig ι)
  rw [Fintype.sum_eq_single Fin.elim0 fun γ hne => False.elim (hne (Subsingleton.elim _ _))]
  simp [wightmanVacuumConfig, wightmanBaseConfig, compactSchwartzLorentz_fin0]

lemma wightmanSpinorLorentzLM_comp_translateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C) (a : Fin 4 → ℝ) :
    (wightmanSpinorLorentzLM WData A).comp (wightmanTranslateLM WData a) =
      (wightmanTranslateLM WData ((lorentzOfSL2C A).mulVec a)).comp
        (wightmanSpinorLorentzLM WData A) := by
  apply LinearMap.ext
  intro Ψ
  rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ,
      map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun C _ => ?_
  simp only [LinearMap.comp_apply, map_smul, wightmanTranslateLM_wightmanBasisPre,
    wightmanSpinorLorentzLM_wightmanBasisPre]
  congr 1
  rcases C with ⟨n, α, f⟩
  change (∑ γ : Fin n → ι,
      (∏ i : Fin n, R.rep A⁻¹ (α i) (γ i)) •
        wightmanBasisPre WData
          ⟨n, (γ, compactSchwartzLorentz n A (compactSchwartzTranslate n a f))⟩) =
    wightmanTranslateLM WData ((lorentzOfSL2C A).mulVec a)
      (∑ γ : Fin n → ι,
        (∏ i : Fin n, R.rep A⁻¹ (α i) (γ i)) •
          wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n A f)⟩)
  rw [map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_smul, wightmanTranslateLM_wightmanBasisPre]
  dsimp only [wightmanConfigTranslate]
  rw [compactSchwartzLorentz_translate n A a f]

lemma wightmanKernel_pair
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι)
    (j k : ℕ) (α : Fin j → ι) (f : CompactSchwartz j)
    (α' : Fin k → ι) (g : CompactSchwartz k) :
    wightmanKernel S W ⟨j, (α, f)⟩ ⟨k, (α', g)⟩ =
      ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (osConcatIdx j k β α') (wightmanConcatSchwartz j k f g) := rfl

private lemma wightmanSpinorLorentzBasis_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (A : SL2C)
    (n : ℕ) (α : Fin n → ι) (f : CompactSchwartz n) :
    wightmanSpinorLorentzBasis WData A ⟨n, (α, f)⟩ =
      ∑ γ : Fin n → ι,
        (∏ i : Fin n, R.rep A⁻¹ (α i) (γ i)) •
          wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n A f)⟩ := rfl

lemma inner_wightmanSpinorLorentzBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (C₁ C₂ : WightmanConfig ι) :
    ⟪wightmanSpinorLorentzBasis WData A C₁,
      wightmanSpinorLorentzBasis WData A C₂⟫_ℂ =
      wightmanKernel S WData.W C₁ C₂ := by
  rcases C₁ with ⟨j, α, f⟩
  rcases C₂ with ⟨k, α', g⟩
  rw [wightmanSpinorLorentzBasis_eq, wightmanSpinorLorentzBasis_eq, sum_inner]
  simp_rw [inner_smul_left, ← Complex.star_def, inner_sum, inner_smul_right,
    inner_wightmanBasisPre, wightmanKernel_pair]
  have h_poinc : ∀ (β : Fin j → ι) (γ' : Fin k → ι),
      WData.W (j + k) (osConcatIdx j k β γ')
          (wightmanConcatSchwartz j k (compactSchwartzLorentz j A f)
            (compactSchwartzLorentz k A g)) =
        ∑ δ₁ : Fin j → ι, ∑ δ₂ : Fin k → ι,
          (∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
            (∏ i : Fin k, R.rep A (γ' i) (δ₂ i)) *
            WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g) := by
    intro β γ'
    have hrel : ∀ x : Fin (j + k) → Fin 4 → ℝ,
        wightmanConcatSchwartz j k (compactSchwartzLorentz j A f)
          (compactSchwartzLorentz k A g) (fun i => poincareAct 0 A (x i)) =
          wightmanConcatSchwartz j k f g x := by
      intro x
      simpa [poincareAct] using wightmanConcatSchwartz_lorentz_rel j k A f g x
    rw [hP (j + k) 0 A _ _ hrel (osConcatIdx j k β γ'),
        ← (osConcatIdxEquiv j k).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun δ₁ _ => Finset.sum_congr rfl fun δ₂ _ => ?_
    dsimp only [osConcatIdxEquiv, Equiv.coe_fn_mk]
    have hprod : (∏ i : Fin (j + k),
        R.rep A (osConcatIdx j k β γ' i) (osConcatIdx j k δ₁ δ₂ i)) =
        (∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
          (∏ i : Fin k, R.rep A (γ' i) (δ₂ i)) := by
      rw [Fin.prod_univ_add]
      congr 1
      · rw [← Equiv.prod_comp (finRevPerm j)]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [osConcatIdx, finRevPerm]
      · refine Finset.prod_congr rfl fun i _ => ?_
        simp [osConcatIdx]
    rw [hprod]
  simp_rw [h_poinc]
  have hinv_mat : R.rep A⁻¹ * R.rep A = (1 : Matrix ι ι ℂ) := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h_ket : ∀ (γ : Fin j → ι) (β : Fin j → ι),
      (∑ γ' : Fin k → ι, (∏ i : Fin k, R.rep A⁻¹ (α' i) (γ' i)) *
        ∑ δ₁ : Fin j → ι, ∑ δ₂ : Fin k → ι,
          (∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
            (∏ i : Fin k, R.rep A (γ' i) (δ₂ i)) *
            WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g)) =
      ∑ δ₁ : Fin j → ι,
        (∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
          WData.W (j + k) (osConcatIdx j k δ₁ α') (wightmanConcatSchwartz j k f g) := by
    intro _ β
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ₁ _ => ?_
    rw [Finset.sum_comm]
    have h_inner_k : ∀ δ₂ : Fin k → ι,
        (∑ γ' : Fin k → ι, (∏ i : Fin k, R.rep A⁻¹ (α' i) (γ' i)) *
          ((∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
            (∏ i : Fin k, R.rep A (γ' i) (δ₂ i)) *
            WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g))) =
        (if α' = δ₂ then 1 else 0) *
          ((∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
            WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g)) := by
      intro δ₂
      have h_factor : ∀ γ' : Fin k → ι,
          (∏ i : Fin k, R.rep A⁻¹ (α' i) (γ' i)) *
            ((∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
              (∏ i : Fin k, R.rep A (γ' i) (δ₂ i)) *
              WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g)) =
          ((∏ i : Fin k, R.rep A⁻¹ (α' i) (γ' i)) * (∏ i : Fin k, R.rep A (γ' i) (δ₂ i))) *
            ((∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
              WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g)) :=
        fun _ => by ring
      simp_rw [h_factor, ← Finset.sum_mul, sum_prod_matrix_mul, hinv_mat,
        prod_one_matrix_eq_ite (ι := ι) α' δ₂]
    simp_rw [h_inner_k, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h_ket_full : ∀ γ : Fin j → ι,
      (∑ γ' : Fin k → ι,
        (∏ i : Fin k, R.rep A⁻¹ (α' i) (γ' i)) *
          ∑ β : Fin j → ι,
            (∏ i : Fin j, S.C (γ i) (β i)) *
              ∑ δ₁ : Fin j → ι, ∑ δ₂ : Fin k → ι,
                (∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
                  (∏ i : Fin k, R.rep A (γ' i) (δ₂ i)) *
                    WData.W (j + k) (osConcatIdx j k δ₁ δ₂) (wightmanConcatSchwartz j k f g)) =
      ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (γ i) (β i)) *
          ∑ δ₁ : Fin j → ι,
            (∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
              WData.W (j + k) (osConcatIdx j k δ₁ α') (wightmanConcatSchwartz j k f g) := by
    intro γ
    rw [Finset.sum_congr rfl fun γ' _ => Finset.mul_sum _ _ _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_congr rfl fun γ' _ => mul_left_comm _ _ _, ← Finset.mul_sum, h_ket γ β]
  simp_rw [h_ket_full]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun β _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ₁ _ => ?_
  have h_rearr : ∀ (β γ : Fin j → ι),
      star (∏ i : Fin j, R.rep A⁻¹ (α i) (γ i)) *
        ((∏ i : Fin j, S.C (γ i) (β i)) *
          ((∏ i : Fin j, R.rep A (β i) (δ₁ i)) *
            WData.W (j + k) (osConcatIdx j k δ₁ α') (wightmanConcatSchwartz j k f g))) =
      ((∏ i : Fin j, star (R.rep A⁻¹ (α i) (γ i))) *
        (∏ i : Fin j, S.C (γ i) (β i)) *
        (∏ i : Fin j, R.rep A (β i) (δ₁ i))) *
        WData.W (j + k) (osConcatIdx j k δ₁ α') (wightmanConcatSchwartz j k f g) := by
    intro β γ
    rw [star_prod]
    ring
  simp_rw [h_rearr]
  rw [Finset.sum_congr rfl fun β _ => (Finset.sum_mul _ _ _).symm, ← Finset.sum_mul]
  congr 1
  have h_prod3 : ∀ (β γ : Fin j → ι),
      (∏ i : Fin j, star (R.rep A⁻¹ (α i) (γ i))) *
        (∏ i : Fin j, S.C (γ i) (β i)) *
        (∏ i : Fin j, R.rep A (β i) (δ₁ i)) =
      ∏ i : Fin j, (star (R.rep A⁻¹ (α i) (γ i)) * S.C (γ i) (β i) * R.rep A (β i) (δ₁ i)) := by
    intro β γ
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => h_prod3 β γ]
  rw [Finset.sum_comm]
  have h_fub :
      (∑ γ : Fin j → ι, ∑ β : Fin j → ι,
        ∏ i : Fin j,
          (star (R.rep A⁻¹ (α i) (γ i)) * S.C (γ i) (β i) * R.rep A (β i) (δ₁ i))) =
      ∏ i : Fin j, ∑ γ : ι, ∑ β : ι,
        (star (R.rep A⁻¹ (α i) γ) * S.C γ β * R.rep A β (δ₁ i)) := by
    rw [Finset.sum_congr rfl fun γ _ => (Fintype.prod_sum fun (i : Fin j) (β : ι) =>
      star (R.rep A⁻¹ (α i) (γ i)) * S.C (γ i) β * R.rep A β (δ₁ i)).symm]
    exact (Fintype.prod_sum fun (i : Fin j) (γ : ι) =>
      ∑ β : ι, star (R.rep A⁻¹ (α i) γ) * S.C γ β * R.rep A β (δ₁ i)).symm
  rw [h_fub]
  exact Finset.prod_congr rfl fun i _ => starStructure_rep_inv_bra_ket S A (α i) (δ₁ i)

theorem inner_wightmanSpinorLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanSpinorLorentzLM WData A Ψ,
      wightmanSpinorLorentzLM WData A Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  conv_lhs =>
    rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ,
        wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Φ]
  rw [map_finsuppSum, map_finsuppSum]
  unfold Finsupp.sum
  rw [sum_inner]
  simp_rw [map_smul, inner_smul_left, inner_sum, inner_smul_right,
    wightmanSpinorLorentzLM_wightmanBasisPre,
    inner_wightmanSpinorLorentzBasis WData hP A, Finset.mul_sum, ← mul_assoc]
  rw [WightmanPreHilbertSpace.inner_def]
  unfold wightmanPreInner Finsupp.sum
  refine Finset.sum_congr rfl fun C₁ _ => Finset.sum_congr rfl fun C₂ _ => ?_
  rfl

theorem norm_wightmanSpinorLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (Ψ : WightmanPreHilbertSpace WData) :
    ‖wightmanSpinorLorentzLM WData A Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanSpinorLorentzLM WData hP A Ψ Ψ]

def wightmanSpinorLorentzPreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C) :
    WightmanPreHilbertSpace WData →L[ℂ] WightmanPreHilbertSpace WData :=
  (wightmanSpinorLorentzLM WData A).mkContinuous 1 fun Ψ => by
    rw [one_mul, norm_wightmanSpinorLorentzLM WData hP A Ψ]

def wightmanSpinorLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C) :
    WightmanHilbert WData →L[ℂ] WightmanHilbert WData :=
  (wightmanSpinorLorentzPreCLM WData hP A).completion

@[simp]
lemma wightmanSpinorLorentz_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanSpinorLorentz WData hP A (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData (wightmanSpinorLorentzLM WData A Ψ) :=
  ContinuousLinearMap.completion_apply_coe (wightmanSpinorLorentzPreCLM WData hP A) Ψ

@[simp]
theorem wightmanSpinorLorentz_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) :
    wightmanSpinorLorentz WData hP 1 = ContinuousLinearMap.id ℂ (WightmanHilbert WData) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanSpinorLorentz WData hP 1 (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData Ψ
    rw [wightmanSpinorLorentz_toWightmanHilbert, wightmanSpinorLorentzLM_one, LinearMap.id_apply]

theorem wightmanSpinorLorentz_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A B : SL2C) :
    wightmanSpinorLorentz WData hP (A * B) =
      (wightmanSpinorLorentz WData hP A).comp (wightmanSpinorLorentz WData hP B) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanSpinorLorentz WData hP (A * B) (toWightmanHilbert WData Ψ) =
      wightmanSpinorLorentz WData hP A
        (wightmanSpinorLorentz WData hP B (toWightmanHilbert WData Ψ))
    rw [wightmanSpinorLorentz_toWightmanHilbert, wightmanSpinorLorentz_toWightmanHilbert,
        wightmanSpinorLorentz_toWightmanHilbert, wightmanSpinorLorentzLM_mul,
        LinearMap.comp_apply]

@[simp]
theorem wightmanSpinorLorentz_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C) :
    wightmanSpinorLorentz WData hP A (wightmanVacuum WData) = wightmanVacuum WData := by
  dsimp [wightmanVacuum]
  rw [wightmanSpinorLorentz_toWightmanHilbert, wightmanSpinorLorentzLM_vacuumPre]

theorem inner_wightmanSpinorLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C)
    (x y : WightmanHilbert WData) :
    ⟪wightmanSpinorLorentz WData hP A x, wightmanSpinorLorentz WData hP A y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪wightmanSpinorLorentz WData hP A (toWightmanHilbert WData Ψ),
        wightmanSpinorLorentz WData hP A (toWightmanHilbert WData Φ)⟫_ℂ =
      ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ
    rw [wightmanSpinorLorentz_toWightmanHilbert, wightmanSpinorLorentz_toWightmanHilbert,
        inner_toWightmanHilbert, inner_toWightmanHilbert,
        inner_wightmanSpinorLorentzLM WData hP A Ψ Φ]

@[simp]
theorem norm_wightmanSpinorLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C)
    (x : WightmanHilbert WData) :
    ‖wightmanSpinorLorentz WData hP A x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanSpinorLorentz WData hP A x x]

theorem wightmanSpinorLorentz_comp_wightmanTranslate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (a : Fin 4 → ℝ) :
    (wightmanSpinorLorentz WData hP A).comp
        (wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) a) =
      (wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP)
          ((lorentzOfSL2C A).mulVec a)).comp
        (wightmanSpinorLorentz WData hP A) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanSpinorLorentz WData hP A
        (wightmanTranslate WData _ a (toWightmanHilbert WData Ψ)) =
      wightmanTranslate WData _ ((lorentzOfSL2C A).mulVec a)
        (wightmanSpinorLorentz WData hP A (toWightmanHilbert WData Ψ))
    rw [wightmanTranslate_toWightmanHilbert, wightmanSpinorLorentz_toWightmanHilbert,
        wightmanSpinorLorentz_toWightmanHilbert, wightmanTranslate_toWightmanHilbert,
        ← LinearMap.comp_apply, wightmanSpinorLorentzLM_comp_translateLM, LinearMap.comp_apply]

def wightmanSpinorLorentzEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C) :
    WightmanHilbert WData ≃ₗᵢ[ℂ] WightmanHilbert WData where
  toLinearEquiv := LinearEquiv.ofLinear
    (wightmanSpinorLorentz WData hP A).toLinearMap
    (wightmanSpinorLorentz WData hP A⁻¹).toLinearMap
    (by
      ext x
      change (wightmanSpinorLorentz WData hP A).comp (wightmanSpinorLorentz WData hP A⁻¹) x = x
      rw [← wightmanSpinorLorentz_mul, mul_inv_cancel, wightmanSpinorLorentz_one,
          ContinuousLinearMap.id_apply])
    (by
      ext x
      change (wightmanSpinorLorentz WData hP A⁻¹).comp (wightmanSpinorLorentz WData hP A) x = x
      rw [← wightmanSpinorLorentz_mul, inv_mul_cancel, wightmanSpinorLorentz_one,
          ContinuousLinearMap.id_apply])
  norm_map' x := norm_wightmanSpinorLorentz WData hP A x

@[simp]
lemma wightmanSpinorLorentzEquiv_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C)
    (x : WightmanHilbert WData) :
    wightmanSpinorLorentzEquiv WData hP A x = wightmanSpinorLorentz WData hP A x := rfl

@[simp]
lemma wightmanSpinorLorentzEquiv_symm
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C) :
    (wightmanSpinorLorentzEquiv WData hP A).symm = wightmanSpinorLorentzEquiv WData hP A⁻¹ := by
  ext x
  rfl

@[simp]
theorem wightmanSpinorLorentzEquiv_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) :
    wightmanSpinorLorentzEquiv WData hP 1 = LinearIsometryEquiv.refl ℂ (WightmanHilbert WData) := by
  ext x
  simp

theorem wightmanSpinorLorentzEquiv_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A B : SL2C)
    (x : WightmanHilbert WData) :
    wightmanSpinorLorentzEquiv WData hP (A * B) x =
      wightmanSpinorLorentzEquiv WData hP A (wightmanSpinorLorentzEquiv WData hP B x) := by
  change wightmanSpinorLorentz WData hP (A * B) x =
    (wightmanSpinorLorentz WData hP A).comp (wightmanSpinorLorentz WData hP B) x
  rw [wightmanSpinorLorentz_mul]

@[simp]
theorem wightmanSpinorLorentzEquiv_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) (A : SL2C) :
    wightmanSpinorLorentzEquiv WData hP A (wightmanVacuum WData) = wightmanVacuum WData :=
  wightmanSpinorLorentz_vacuum WData hP A

theorem wightmanSpinorLorentzEquiv_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (a : Fin 4 → ℝ) (x : WightmanHilbert WData) :
    wightmanSpinorLorentzEquiv WData hP A
        (wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) a x) =
      wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP)
        ((lorentzOfSL2C A).mulVec a) (wightmanSpinorLorentzEquiv WData hP A x) := by
  change (wightmanSpinorLorentz WData hP A).comp
      (wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) a) x = _
  rw [wightmanSpinorLorentz_comp_wightmanTranslate]
  rfl

def wightmanPoincareEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (a : Fin 4 → ℝ) (A : SL2C) :
    WightmanHilbert WData ≃ₗᵢ[ℂ] WightmanHilbert WData :=
  (wightmanSpinorLorentzEquiv WData hP A).trans
    (wightmanTranslateLinearIsometryEquiv WData
      (wightmanTranslationInvariant_of_poincare R hP) a)

@[simp]
lemma wightmanPoincareEquiv_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (a : Fin 4 → ℝ) (A : SL2C) (x : WightmanHilbert WData) :
    wightmanPoincareEquiv WData hP a A x =
      wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) a
        (wightmanSpinorLorentzEquiv WData hP A x) := rfl

@[simp]
theorem wightmanPoincareEquiv_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W) :
    wightmanPoincareEquiv WData hP 0 1 = LinearIsometryEquiv.refl ℂ (WightmanHilbert WData) := by
  ext x
  simp [wightmanTranslate_zero]

@[simp]
theorem wightmanPoincareEquiv_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (a : Fin 4 → ℝ) (A : SL2C) :
    wightmanPoincareEquiv WData hP a A (wightmanVacuum WData) = wightmanVacuum WData := by
  simp [wightmanTranslate_vacuum]

theorem wightmanPoincareEquiv_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (a₁ a₂ : Fin 4 → ℝ) (A₁ A₂ : SL2C) (x : WightmanHilbert WData) :
    wightmanPoincareEquiv WData hP a₁ A₁ (wightmanPoincareEquiv WData hP a₂ A₂ x) =
      wightmanPoincareEquiv WData hP (a₁ + (lorentzOfSL2C A₁).mulVec a₂) (A₁ * A₂) x := by
  simp only [wightmanPoincareEquiv_apply]
  rw [wightmanSpinorLorentzEquiv_translate, wightmanSpinorLorentzEquiv_mul,
      ← ContinuousLinearMap.comp_apply, ← wightmanTranslate_add]

theorem wightmanSpinorLorentz_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (C : WightmanConfig ι) :
    wightmanSpinorLorentz WData hP A (wightmanBasis WData C) =
      ∑ γ : Fin C.1 → ι,
        (∏ i : Fin C.1, R.rep A⁻¹ (C.2.1 i) (γ i)) •
          wightmanBasis WData ⟨C.1, (γ, compactSchwartzLorentz C.1 A C.2.2)⟩ := by
  dsimp [wightmanBasis]
  rw [wightmanSpinorLorentz_toWightmanHilbert, wightmanSpinorLorentzLM_wightmanBasisPre]
  unfold wightmanSpinorLorentzBasis
  rw [map_sum]
  refine Finset.sum_congr rfl fun γ _ => map_smul _ _ _

theorem wightmanSpinorLorentz_wightmanSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (j : ℕ) (α : Fin j → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    wightmanSpinorLorentz WData hP A (wightmanSchwartzVec WData j α f) =
      ∑ γ : Fin j → ι,
        (∏ i : Fin j, R.rep A⁻¹ (α i) (γ i)) •
          wightmanSchwartzVec WData j γ (schwartzLorentzCLM j A⁻¹ f) := by
  have h_lhs : Tendsto
      (fun m : ℕ => wightmanSpinorLorentz WData hP A
        (wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩))
      atTop (𝓝 (wightmanSpinorLorentz WData hP A (wightmanSchwartzVec WData j α f))) :=
    ((wightmanSpinorLorentz WData hP A).continuous.tendsto _).comp
      (tendsto_wightmanBasis_compactCutoff WData j α f)
  have h_rhs : Tendsto
      (fun m : ℕ => ∑ γ : Fin j → ι,
        (∏ i : Fin j, R.rep A⁻¹ (α i) (γ i)) •
          wightmanSchwartzVec WData j γ
            (schwartzLorentzCLM j A⁻¹ (schwartzCutoffSeq j f m)))
      atTop (𝓝 (∑ γ : Fin j → ι,
        (∏ i : Fin j, R.rep A⁻¹ (α i) (γ i)) •
          wightmanSchwartzVec WData j γ (schwartzLorentzCLM j A⁻¹ f))) := by
    refine tendsto_finsetSum Finset.univ fun γ _ => ?_
    exact (((wightmanSchwartzVec WData j γ).continuous.tendsto _).comp
      (((schwartzLorentzCLM j A⁻¹).continuous.tendsto _).comp
        (schwartzCutoffSeq_tendsto j f))).const_smul _
  have h_eq : (fun m : ℕ => wightmanSpinorLorentz WData hP A
        (wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩)) =
      fun m : ℕ => ∑ γ : Fin j → ι,
        (∏ i : Fin j, R.rep A⁻¹ (α i) (γ i)) •
          wightmanSchwartzVec WData j γ
            (schwartzLorentzCLM j A⁻¹ (schwartzCutoffSeq j f m)) := by
    ext m
    rw [wightmanSpinorLorentz_wightmanBasis]
    dsimp only
    refine Finset.sum_congr rfl fun γ _ => ?_
    congr 1
    rw [← wightmanSchwartzVec_compact WData j γ
      (compactSchwartzLorentz j A (compactCutoff j f m))]
    rfl
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

def lorentzIndexedSchwartz (R : HolomorphicLorentzRep ι) (k : ℕ) (A : SL2C)
    (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι k :=
  fun γ => ∑ α : Fin k → ι,
    (∏ i : Fin k, R.rep A⁻¹ (α i) (γ i)) • schwartzLorentzCLM k A⁻¹ (Φ α)

theorem wightmanSpinorLorentz_wightmanIndexedVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (k : ℕ) (Φ : IndexedSchwartz ι k) :
    wightmanSpinorLorentz WData hP A (wightmanIndexedVec WData k Φ) =
      wightmanIndexedVec WData k (lorentzIndexedSchwartz R k A Φ) := by
  unfold wightmanIndexedVec lorentzIndexedSchwartz
  rw [map_sum]
  simp_rw [wightmanSpinorLorentz_wightmanSchwartzVec WData hP A k, map_sum, map_smul]
  exact Finset.sum_comm

end SpinorLorentzHilbert

section AntiunitaryPCTHilbert

def schwartzPTConjLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →ₗ⋆[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ where
  toFun f := schwartzConj (schwartzNeg n f)
  map_add' f g := by rw [map_add, schwartzConj_add]
  map_smul' c f := by rw [map_smul, schwartzConj_smul]; rfl

lemma continuous_schwartzPTConjLM (n : ℕ) : Continuous (schwartzPTConjLM n) := by
  have h_with : WithSeminorms (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ) :=
    schwartz_withSeminorms ℝ _ _
  refine continuous_of_continuousAt_zero (schwartzPTConjLM n).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, h_with.tendsto_nhds _ 0]
  intro p ε hε
  let K : ℝ := ‖Complex.conjCLE.toContinuousLinearMap‖
  have h_bd : ∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      SchwartzMap.seminorm ℝ p.1 p.2 (schwartzPTConjLM n f) ≤
        K * SchwartzMap.seminorm ℝ p.1 p.2 (schwartzNeg n f) :=
    fun f => seminorm_schwartzConj_le p.1 p.2 (schwartzNeg n f)
  have h_zero : Tendsto
      (fun f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ =>
        K * SchwartzMap.seminorm ℝ p.1 p.2 (schwartzNeg n f))
      (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ =>
        SchwartzMap.seminorm ℝ p.1 p.2 (schwartzNeg n f)) :=
      (h_with.continuous_seminorm p).comp (schwartzNeg n).continuous
    simpa [map_zero, mul_zero] using (hcont.tendsto 0).const_mul K
  have ht := squeeze_zero (fun f => apply_nonneg _ _) h_bd h_zero
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with f hf
  rw [sub_zero]
  exact hf

def schwartzPTConj (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →SL[starRingEnd ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  { schwartzPTConjLM n with cont := continuous_schwartzPTConjLM n }

@[simp]
lemma schwartzPTConj_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzPTConj n f x = star (f (-x)) := rfl

@[simp]
lemma schwartzPTConj_involutive (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzPTConj n (schwartzPTConj n f) = f := by
  ext x
  simp

lemma hasCompactSupport_schwartzPTConj (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :
    HasCompactSupport (schwartzPTConj n f : (Fin n → Fin 4 → ℝ) → ℂ) := by
  have hK : IsCompact ((fun y : Fin n → Fin 4 → ℝ => -y) ''
      tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :=
    hf.isCompact.image continuous_neg
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  rw [Function.mem_support] at hx
  have hne : f (-x) ≠ 0 := by
    intro h0
    apply hx
    simp [h0]
  exact ⟨-x, subset_tsupport _ (Function.mem_support.mpr hne), neg_neg x⟩

def compactSchwartzPTConj (n : ℕ) (f : CompactSchwartz n) : CompactSchwartz n :=
  ⟨schwartzPTConj n f.val, hasCompactSupport_schwartzPTConj n f.val f.property⟩

@[simp]
lemma compactSchwartzPTConj_val (n : ℕ) (f : CompactSchwartz n) :
    (compactSchwartzPTConj n f).val = schwartzPTConj n f.val := rfl

@[simp]
lemma compactSchwartzPTConj_involutive (n : ℕ) (f : CompactSchwartz n) :
    compactSchwartzPTConj n (compactSchwartzPTConj n f) = f := by
  apply Subtype.ext
  exact schwartzPTConj_involutive n f.val

@[simp]
lemma compactSchwartzPTConj_vacuum :
    compactSchwartzPTConj 0 (momentumWavepacketCompactSchwartz 0 0) =
      momentumWavepacketCompactSchwartz 0 0 := by
  apply Subtype.ext
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  change star (momentumWavepacketSchwartz 0 0 (-x)) = momentumWavepacketSchwartz 0 0 x
  rw [hx, neg_zero, momentumWavepacketSchwartz_zero_eval_zero, star_one]

lemma compactSchwartzPTConj_translate (n : ℕ) (a : Fin 4 → ℝ) (f : CompactSchwartz n) :
    compactSchwartzPTConj n (compactSchwartzTranslate n a f) =
      compactSchwartzTranslate n (-a) (compactSchwartzPTConj n f) := by
  ext x
  change star (f.val (fun i => (-x) i - a)) = star (f.val (-fun i => x i - (-a)))
  congr 2
  ext i μ
  simp only [Pi.neg_apply, Pi.sub_apply]
  ring

lemma compactSchwartzPTConj_lorentz (n : ℕ) (A : SL2C) (f : CompactSchwartz n) :
    compactSchwartzPTConj n (compactSchwartzLorentz n A f) =
      compactSchwartzLorentz n A (compactSchwartzPTConj n f) := by
  ext x
  change star (f.val (fun i => (lorentzOfSL2C A⁻¹).mulVec ((-x) i))) =
    star (f.val (-fun i => (lorentzOfSL2C A⁻¹).mulVec (x i)))
  congr 2
  ext i μ
  change ((lorentzOfSL2C A⁻¹).mulVec (-x i)) μ = -((lorentzOfSL2C A⁻¹).mulVec (x i)) μ
  rw [Matrix.mulVec_neg]
  rfl

lemma chooseTwo_add (j k : ℕ) :
    (j + k) * (j + k - 1) / 2 = j * (j - 1) / 2 + k * (k - 1) / 2 + j * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (j + (k + 1)) * (j + (k + 1) - 1) / 2 =
        (j + k) * (j + k - 1) / 2 + j + k := by
      have hmul : (j + (k + 1)) * (j + k) = (j + k) * (j + k - 1) + 2 * (j + k) := by
        cases h : j + k with
        | zero => omega
        | succ m =>
          have h1' : j + (k + 1) = m + 2 := by omega
          rw [h1']
          simp
          ring
      have hexpr : j + (k + 1) - 1 = j + k := by omega
      rw [hexpr, hmul]
      omega
    have h2 : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
      have hmul : (k + 1) * k = k * (k - 1) + 2 * k := by
        cases k with
        | zero => simp
        | succ m => simp; ring
      rw [hmul]
      omega
    have h3 : (k + 1) * ((k + 1) - 1) / 2 = (k + 1) * k / 2 := rfl
    rw [h1, h3, h2, ih]
    ring

lemma neg_one_pow_chooseTwo_even {j k : ℕ} (heven : Even (j + k)) :
    (-1 : ℂ) ^ (k * (k - 1) / 2) * (-1 : ℂ) ^ (j * (j - 1) / 2) * (-1 : ℂ) ^ k =
      (-1 : ℂ) ^ ((j + k) * (j + k - 1) / 2) := by
  rw [chooseTwo_add j k, pow_add, pow_add]
  have hjk : (-1 : ℂ) ^ (j * k) = (-1 : ℂ) ^ k := by
    rcases Nat.even_or_odd k with hk | hk
    · rw [(hk.mul_left j).neg_one_pow, hk.neg_one_pow]
    · have hj : Odd j := by
        rcases Nat.even_or_odd j with hj_ev | hj_odd
        · exfalso
          exact Nat.not_even_iff_odd.mpr (hk.add_even hj_ev) (Nat.add_comm j k ▸ heven)
        · exact hj_odd
      rw [(hj.mul hk).neg_one_pow, hk.neg_one_pow]
  rw [hjk]
  ring

def schwartzIndexCast (n₁ n₂ : ℕ) (h : n₁ = n₂) :
    SchwartzMap (Fin n₂ → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n₁ → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => Fin 4 → ℝ) (finCongr h))

@[simp]
lemma schwartzIndexCast_apply (n₁ n₂ : ℕ) (h : n₁ = n₂)
    (f : SchwartzMap (Fin n₂ → Fin 4 → ℝ) ℂ) (x : Fin n₁ → Fin 4 → ℝ) :
    schwartzIndexCast n₁ n₂ h f x = f (fun i => x (Fin.cast h.symm i)) := by
  subst h
  change f (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ => Fin 4 → ℝ) (Equiv.refl _) x) = f x
  congr 1

lemma wightmanConcatSchwartz_pt_rev_rel (j k : ℕ)
    (f : CompactSchwartz j) (g : CompactSchwartz k) (x : Fin (j + k) → Fin 4 → ℝ) :
    schwartzIndexCast (j + k) (k + j) (Nat.add_comm j k)
        (wightmanConcatSchwartz k j (compactSchwartzPTConj k g) (compactSchwartzPTConj j f))
        (fun t => -x (Fin.rev t)) =
      wightmanConcatSchwartz j k f g x := by
  rw [schwartzIndexCast_apply, wightmanConcatSchwartz_apply, wightmanConcatSchwartz_apply]
  simp only [compactSchwartzPTConj_val, schwartzPTConj_apply]
  have h1 : (-fun i : Fin k =>
      -x (Fin.rev (Fin.cast (Nat.add_comm j k).symm (Fin.castAdd j (Fin.rev i))))) =
      fun i : Fin k => x (Fin.natAdd j i) := by
    ext i μ
    simp only [Pi.neg_apply, neg_neg]
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have h2 : (-fun i : Fin j =>
      -x (Fin.rev (Fin.cast (Nat.add_comm j k).symm (Fin.natAdd k i)))) =
      fun i : Fin j => x (Fin.castAdd k (Fin.rev i)) := by
    ext i μ
    simp only [Pi.neg_apply, neg_neg]
    congr 1
    ext
    simp only [Fin.val_rev, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
    omega
  rw [h1, h2, ← Complex.star_def, star_star, mul_comm]

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wightmanPCTBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ) (C : WightmanConfig ι) :
    WightmanPreHilbertSpace WData :=
  (η ^ (C.1 * (C.1 - 1) / 2)) •
    ∑ μ : Fin C.1 → ι,
      (∏ i : Fin C.1, pctMatrix S (C.2.1 i) (μ i)) •
        wightmanBasisPre WData ⟨C.1, (μ, compactSchwartzPTConj C.1 C.2.2)⟩

def finsuppConj (ι : Type*) : (WightmanConfig ι →₀ ℂ) →ₗ⋆[ℂ] (WightmanConfig ι →₀ ℂ) where
  toFun Ψ := Ψ.mapRange (starRingEnd ℂ) (map_zero _)
  map_add' Ψ Φ := Finsupp.mapRange_add (map_add _) Ψ Φ
  map_smul' c Ψ := by
    ext A
    simp

def wightmanPCTPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ) :
    WightmanPreHilbertSpace WData →ₗ⋆[ℂ] WightmanPreHilbertSpace WData :=
  (Finsupp.linearCombination ℂ (wightmanPCTBasis WData η)).comp
    ((finsuppConj ι).comp (WightmanPreHilbertSpace.equivFinsupp WData).toLinearMap)

@[simp]
lemma wightmanPCTPreLM_wightmanBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ) (C : WightmanConfig ι) :
    wightmanPCTPreLM WData η (wightmanBasisPre WData C) = wightmanPCTBasis WData η C := by
  unfold wightmanPCTPreLM finsuppConj
  change Finsupp.linearCombination ℂ (wightmanPCTBasis WData η)
      ((Finsupp.single C (1 : ℂ)).mapRange (starRingEnd ℂ) (map_zero _)) =
    wightmanPCTBasis WData η C
  simp

@[simp]
lemma wightmanPCTPreLM_vacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ) :
    wightmanPCTPreLM WData η (wightmanVacuumPre WData) = wightmanVacuumPre WData := by
  unfold wightmanVacuumPre
  rw [wightmanPCTPreLM_wightmanBasisPre]
  change (η ^ (0 * (0 - 1) / 2)) •
      (∑ μ : Fin 0 → ι,
        (∏ i : Fin 0, pctMatrix S (Fin.elim0 i) (μ i)) •
          wightmanBasisPre WData
            ⟨0, (μ, compactSchwartzPTConj 0 (momentumWavepacketCompactSchwartz 0 0))⟩) =
    wightmanBasisPre WData (wightmanVacuumConfig ι)
  rw [Fintype.sum_eq_single Fin.elim0 fun μ hne => False.elim (hne (Subsingleton.elim _ _))]
  simp only [Nat.zero_mul, Nat.zero_div, pow_zero, one_smul, Finset.univ_eq_empty,
    Finset.prod_empty, compactSchwartzPTConj_vacuum]
  rfl

lemma wightmanPCTPreLM_basis_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {η : ℂ} (hε : R.HasSpinParity η)
    (C : WightmanConfig ι) :
    wightmanPCTPreLM WData η (wightmanPCTBasis WData η C) =
      wightmanSpinorLorentzBasis WData (-1) C := by
  rcases C with ⟨n, α, f⟩
  have h1 : wightmanPCTBasis WData η ⟨n, (α, f)⟩ =
      (η ^ (n * (n - 1) / 2)) •
        ∑ μ : Fin n → ι,
          (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
            wightmanBasisPre WData ⟨n, (μ, compactSchwartzPTConj n f)⟩ := rfl
  rw [h1, map_smulₛₗ, ← Complex.star_def, map_sum]
  have hη_real : star (η ^ (n * (n - 1) / 2)) * (η ^ (n * (n - 1) / 2)) = 1 := by
    rcases hε.2 with rfl | rfl <;> simp [← mul_pow]
  have hstep : ∀ μ : Fin n → ι,
      wightmanPCTPreLM WData η
          ((∏ i : Fin n, pctMatrix S (α i) (μ i)) •
            wightmanBasisPre WData ⟨n, (μ, compactSchwartzPTConj n f)⟩) =
        (η ^ (n * (n - 1) / 2)) •
          ∑ ν : Fin n → ι,
            ((∏ i : Fin n, star (pctMatrix S (α i) (μ i))) *
              (∏ i : Fin n, pctMatrix S (μ i) (ν i))) •
              wightmanBasisPre WData ⟨n, (ν, f)⟩ := by
    intro μ
    rw [map_smulₛₗ, ← Complex.star_def, wightmanPCTPreLM_wightmanBasisPre]
    change star (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
        ((η ^ (n * (n - 1) / 2)) •
          ∑ ν : Fin n → ι,
            (∏ i : Fin n, pctMatrix S (μ i) (ν i)) •
              wightmanBasisPre WData
                ⟨n, (ν, compactSchwartzPTConj n (compactSchwartzPTConj n f))⟩) = _
    rw [star_prod, smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul, compactSchwartzPTConj_involutive]
  simp_rw [hstep, ← Finset.smul_sum, smul_smul]
  rw [hη_real, one_smul, Finset.sum_comm]
  change _ = ∑ ν : Fin n → ι,
      (∏ i : Fin n, R.rep (-1 : SL2C)⁻¹ (α i) (ν i)) •
        wightmanBasisPre WData ⟨n, (ν, compactSchwartzLorentz n (-1) f)⟩
  have hinv_m1 : (-1 : SL2C)⁻¹ = -1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hfl : compactSchwartzLorentz n (-1) f = f := by
    ext x
    change f.val (fun i => (lorentzOfSL2C (-1 : SL2C)⁻¹).mulVec (x i)) = f.val x
    rw [hinv_m1, lorentzOfSL2C_neg_one]
    simp
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul, hfl, hinv_m1, rep_neg_one_of_hasSpinParity hε]
  congr 1
  have hmat := pctMatrix_conj_mul_self S hε
  have hprod := sum_prod_matrix_mul ((pctMatrix S).map star) (pctMatrix S) α ν
  simp only [Matrix.map_apply] at hprod
  rw [hprod, hmat]

theorem wightmanPCTPreLM_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) {η : ℂ} (hε : R.HasSpinParity η)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanPCTPreLM WData η (wightmanPCTPreLM WData η Ψ) =
      wightmanSpinorLorentzLM WData (-1) Ψ := by
  conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  conv_rhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  unfold Finsupp.sum
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [map_smulₛₗ, map_smulₛₗ, map_smul, RingHomCompTriple.comp_apply, RingHom.id_apply,
      wightmanPCTPreLM_wightmanBasisPre, wightmanSpinorLorentzLM_wightmanBasisPre,
      wightmanPCTPreLM_basis_sq WData hε C]

lemma wightmanPCTPreLM_translateLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ) (a : Fin 4 → ℝ)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanPCTPreLM WData η (wightmanTranslateLM WData a Ψ) =
      wightmanTranslateLM WData (-a) (wightmanPCTPreLM WData η Ψ) := by
  conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  conv_rhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  unfold Finsupp.sum
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul]
  congr 1
  rcases C with ⟨n, α, f⟩
  rw [wightmanTranslateLM_wightmanBasisPre, wightmanPCTPreLM_wightmanBasisPre,
      wightmanPCTPreLM_wightmanBasisPre]
  dsimp only [wightmanConfigTranslate]
  change (η ^ (n * (n - 1) / 2)) •
      (∑ μ : Fin n → ι,
        (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
          wightmanBasisPre WData
            ⟨n, (μ, compactSchwartzPTConj n (compactSchwartzTranslate n a f))⟩) =
    wightmanTranslateLM WData (-a)
      ((η ^ (n * (n - 1) / 2)) •
        ∑ μ : Fin n → ι,
          (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
            wightmanBasisPre WData ⟨n, (μ, compactSchwartzPTConj n f)⟩)
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, wightmanTranslateLM_wightmanBasisPre, compactSchwartzPTConj_translate]
  rfl

lemma wightmanPCTPreLM_spinorLorentzLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ) (A : SL2C)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanPCTPreLM WData η (wightmanSpinorLorentzLM WData A Ψ) =
      wightmanSpinorLorentzLM WData A (wightmanPCTPreLM WData η Ψ) := by
  conv_lhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  conv_rhs => rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ]
  unfold Finsupp.sum
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul]
  congr 1
  rcases C with ⟨n, α, f⟩
  rw [wightmanSpinorLorentzLM_wightmanBasisPre, wightmanPCTPreLM_wightmanBasisPre]
  change wightmanPCTPreLM WData η
      (∑ γ : Fin n → ι,
        (∏ i : Fin n, R.rep A⁻¹ (α i) (γ i)) •
          wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n A f)⟩) =
    wightmanSpinorLorentzLM WData A
      ((η ^ (n * (n - 1) / 2)) •
        ∑ μ : Fin n → ι,
          (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
            wightmanBasisPre WData ⟨n, (μ, compactSchwartzPTConj n f)⟩)
  rw [map_sum, map_smul, map_sum]
  have hL : ∀ γ : Fin n → ι,
      wightmanPCTPreLM WData η
          ((∏ i : Fin n, R.rep A⁻¹ (α i) (γ i)) •
            wightmanBasisPre WData ⟨n, (γ, compactSchwartzLorentz n A f)⟩) =
        (η ^ (n * (n - 1) / 2)) •
          ∑ ν : Fin n → ι,
            ((∏ i : Fin n, star (R.rep A⁻¹ (α i) (γ i))) *
              (∏ i : Fin n, pctMatrix S (γ i) (ν i))) •
              wightmanBasisPre WData
                ⟨n, (ν, compactSchwartzLorentz n A (compactSchwartzPTConj n f))⟩ := by
    intro γ
    rw [map_smulₛₗ, ← Complex.star_def, wightmanPCTPreLM_wightmanBasisPre]
    change star (∏ i : Fin n, R.rep A⁻¹ (α i) (γ i)) •
        ((η ^ (n * (n - 1) / 2)) •
          ∑ ν : Fin n → ι,
            (∏ i : Fin n, pctMatrix S (γ i) (ν i)) •
              wightmanBasisPre WData
                ⟨n, (ν, compactSchwartzPTConj n (compactSchwartzLorentz n A f))⟩) = _
    rw [star_prod, smul_comm, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul, compactSchwartzPTConj_lorentz]
  have hR : ∀ μ : Fin n → ι,
      wightmanSpinorLorentzLM WData A
          ((∏ i : Fin n, pctMatrix S (α i) (μ i)) •
            wightmanBasisPre WData ⟨n, (μ, compactSchwartzPTConj n f)⟩) =
        ∑ ν : Fin n → ι,
          ((∏ i : Fin n, pctMatrix S (α i) (μ i)) *
            (∏ i : Fin n, R.rep A⁻¹ (μ i) (ν i))) •
            wightmanBasisPre WData
              ⟨n, (ν, compactSchwartzLorentz n A (compactSchwartzPTConj n f))⟩ := by
    intro μ
    rw [map_smul, wightmanSpinorLorentzLM_wightmanBasisPre]
    change (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
        (∑ ν : Fin n → ι,
          (∏ i : Fin n, R.rep A⁻¹ (μ i) (ν i)) •
            wightmanBasisPre WData
              ⟨n, (ν, compactSchwartzLorentz n A (compactSchwartzPTConj n f))⟩) = _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => smul_smul _ _ _
  simp_rw [hL, ← Finset.smul_sum, hR]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_smul, ← Finset.sum_smul]
  congr 1
  have h1 := sum_prod_matrix_mul ((R.rep A⁻¹).map star) (pctMatrix S) α ν
  have h2 := sum_prod_matrix_mul (pctMatrix S) (R.rep A⁻¹) α ν
  simp only [Matrix.map_apply] at h1
  rw [h1, h2, pctMatrix_comm_rep S A⁻¹]

private lemma wightmanPCTBasis_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (η : ℂ)
    (n : ℕ) (α : Fin n → ι) (f : CompactSchwartz n) :
    wightmanPCTBasis WData η ⟨n, (α, f)⟩ =
      (η ^ (n * (n - 1) / 2)) •
        ∑ μ : Fin n → ι,
          (∏ i : Fin n, pctMatrix S (α i) (μ i)) •
            wightmanBasisPre WData ⟨n, (μ, compactSchwartzPTConj n f)⟩ := rfl

lemma inner_wightmanPCTBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (C₁ C₂ : WightmanConfig ι) :
    ⟪wightmanPCTBasis WData η C₁, wightmanPCTBasis WData η C₂⟫_ℂ =
      star (wightmanKernel S WData.W C₁ C₂) := by
  rw [WData.hermiticity C₂ C₁]
  rcases C₁ with ⟨j, α, f⟩
  rcases C₂ with ⟨k, α', g⟩
  let W_jk : (Fin j → ι) → (Fin k → ι) → ℂ := fun δ₂ δ₁ =>
    WData.W (j + k) (osConcatIdx j k δ₂ δ₁)
      (wightmanConcatSchwartz j k (compactSchwartzPTConj j f) (compactSchwartzPTConj k g))
  have h_pct_W : ∀ β' : Fin k → ι,
      WData.W (k + j) (osConcatIdx k j β' α) (wightmanConcatSchwartz k j g f) =
        η ^ ((k + j) * (k + j - 1) / 2) *
          ∑ δ₁ : Fin k → ι, ∑ δ₂ : Fin j → ι,
            (∏ i : Fin k, R.σ (-1, 1) (β' i) (δ₁ i)) *
              (∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) * W_jk δ₂ δ₁ := by
    intro β'
    let f_ptrev := schwartzIndexCast (k + j) (j + k) (Nat.add_comm k j)
      (wightmanConcatSchwartz j k (compactSchwartzPTConj j f) (compactSchwartzPTConj k g))
    have hrel : ∀ x : Fin (k + j) → Fin 4 → ℝ,
        f_ptrev (fun t => -x (Fin.rev t)) = wightmanConcatSchwartz k j g f x :=
      wightmanConcatSchwartz_pt_rev_rel k j g f
    rw [hpct (k + j) (osConcatIdx k j β' α) (wightmanConcatSchwartz k j g f) f_ptrev hrel,
        ← (osConcatIdxEquiv k j).sum_comp, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun δ₁ _ => Finset.sum_congr rfl fun δ₂ _ => ?_
    dsimp only [osConcatIdxEquiv, Equiv.coe_fn_mk]
    have hprod : (∏ i : Fin (k + j),
        R.σ (-1, 1) (osConcatIdx k j β' α i) (osConcatIdx k j δ₁ δ₂ i)) =
        (∏ i : Fin k, R.σ (-1, 1) (β' i) (δ₁ i)) *
          (∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) := by
      rw [Fin.prod_univ_add]
      congr 1
      · rw [← Equiv.prod_comp (finRevPerm k)]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [osConcatIdx, finRevPerm]
      · refine Finset.prod_congr rfl fun i _ => ?_
        simp [osConcatIdx]
    have hcongr : WData.W (k + j) (osConcatIdx k j δ₁ δ₂ ∘ Fin.rev) f_ptrev = W_jk δ₂ δ₁ := by
      refine wightman_congr_eq (Nat.add_comm k j) WData.W _ _ _ _ (fun s => ?_) (fun y => ?_)
      · dsimp only [Function.comp_apply, osConcatIdx]
        by_cases hs : s.val < j
        · let v : Fin j := ⟨s.val, hs⟩
          have hcs : Fin.cast (Nat.add_comm k j) s = Fin.castAdd k v := by ext; rfl
          have hrs : Fin.rev s = Fin.natAdd k (Fin.rev v) := by
            ext
            simp only [Fin.val_rev, Fin.val_natAdd, v]
            omega
          rw [hrs, hcs, Fin.append_right, Fin.append_left]
          rfl
        · let u : Fin k := ⟨s.val - j, by omega⟩
          have hcs : Fin.cast (Nat.add_comm k j) s = Fin.natAdd j u := by
            ext
            simp only [Fin.val_cast, Fin.val_natAdd, u]
            omega
          have hrs : Fin.rev s = Fin.castAdd j (Fin.rev u) := by
            ext
            simp only [Fin.val_rev, Fin.val_castAdd, u]
            omega
          rw [hrs, hcs, Fin.append_left, Fin.append_right]
          simp [Function.comp_apply, Fin.rev_rev]
      · simp only [f_ptrev, schwartzIndexCast_apply]
        congr 1
    rw [hprod, hcongr]
  have h_rhs : wightmanKernel S WData.W ⟨k, (α', g)⟩ ⟨j, (α, f)⟩ =
      η ^ ((k + j) * (k + j - 1) / 2) *
        ∑ δ₂ : Fin j → ι, ∑ δ₁ : Fin k → ι,
          (∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) *
            (∏ i : Fin k, pctMatrix S (α' i) (δ₁ i)) * W_jk δ₂ δ₁ := by
    rw [wightmanKernel_pair]
    simp_rw [h_pct_W, ← mul_assoc]
    have hpull : ∀ β' : Fin k → ι,
        (∏ i : Fin k, S.C (α' i) (β' i)) * η ^ ((k + j) * (k + j - 1) / 2) *
          (∑ δ₁ : Fin k → ι, ∑ δ₂ : Fin j → ι,
            (∏ i : Fin k, R.σ (-1, 1) (β' i) (δ₁ i)) *
              (∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) * W_jk δ₂ δ₁) =
        η ^ ((k + j) * (k + j - 1) / 2) *
          ∑ δ₂ : Fin j → ι, ∑ δ₁ : Fin k → ι,
            ((∏ i : Fin k, S.C (α' i) (β' i)) * (∏ i : Fin k, R.σ (-1, 1) (β' i) (δ₁ i))) *
              ((∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) * W_jk δ₂ δ₁) := by
      intro β'
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ₂ _ => Finset.sum_congr rfl fun δ₁ _ => by ring
    simp_rw [hpull, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ₂ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ₁ _ => ?_
    rw [← Finset.sum_mul, sum_prod_matrix_mul]
    have hpct_def : S.C * R.σ (-1, 1) = pctMatrix S := rfl
    rw [hpct_def]
    ring
  have h_lhs : ⟪wightmanPCTBasis WData η ⟨j, (α, f)⟩,
      wightmanPCTBasis WData η ⟨k, (α', g)⟩⟫_ℂ =
      (star (η ^ (j * (j - 1) / 2)) * η ^ (k * (k - 1) / 2) * η ^ j) *
        ∑ δ₂ : Fin j → ι, ∑ δ₁ : Fin k → ι,
          (∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) *
            (∏ i : Fin k, pctMatrix S (α' i) (δ₁ i)) * W_jk δ₂ δ₁ := by
    rw [wightmanPCTBasis_eq, wightmanPCTBasis_eq, inner_smul_left, inner_smul_right, sum_inner]
    simp_rw [inner_smul_left, ← Complex.star_def, inner_sum, inner_smul_right,
      inner_wightmanBasisPre, wightmanKernel_pair]
    have h_inner_sum :
        (∑ μ : Fin j → ι, star (∏ i : Fin j, pctMatrix S (α i) (μ i)) *
          ∑ δ₁ : Fin k → ι, (∏ i : Fin k, pctMatrix S (α' i) (δ₁ i)) *
            ∑ δ₂ : Fin j → ι, (∏ i : Fin j, S.C (μ i) (δ₂ i)) * W_jk δ₂ δ₁) =
        η ^ j * ∑ δ₂ : Fin j → ι, ∑ δ₁ : Fin k → ι,
          (∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i)) *
            (∏ i : Fin k, pctMatrix S (α' i) (δ₁ i)) * W_jk δ₂ δ₁ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_congr rfl fun δ₁ _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ₂ _ => ?_
      refine Finset.sum_congr rfl fun δ₁ _ => ?_
      have h_factor : ∀ μ : Fin j → ι,
          star (∏ i : Fin j, pctMatrix S (α i) (μ i)) *
            ((∏ i : Fin k, pctMatrix S (α' i) (δ₁ i)) *
              ((∏ i : Fin j, S.C (μ i) (δ₂ i)) * W_jk δ₂ δ₁)) =
          ((∏ i : Fin j, ((pctMatrix S).map star) (α i) (μ i)) *
            (∏ i : Fin j, S.C (μ i) (δ₂ i))) *
            ((∏ i : Fin k, pctMatrix S (α' i) (δ₁ i)) * W_jk δ₂ δ₁) := by
        intro μ
        rw [star_prod]
        simp only [Matrix.map_apply]
        ring
      simp_rw [h_factor, ← Finset.sum_mul, sum_prod_matrix_mul, pctMatrix_conj_mul_C S hε]
      have h_smul_prod : (∏ i : Fin j, (η • R.σ (-1, 1)) (α i) (δ₂ i)) =
          η ^ j * ∏ i : Fin j, R.σ (-1, 1) (α i) (δ₂ i) := by
        rw [Finset.prod_congr rfl fun i _ => Matrix.smul_apply _ _ _ _,
            Finset.prod_congr rfl fun i _ => smul_eq_mul _ _,
            Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
      rw [h_smul_prod]
      ring
    dsimp only [W_jk] at h_inner_sum
    rw [h_inner_sum]
    ring
  rw [h_lhs, h_rhs]
  rcases hε.2 with rfl | rfl
  · simp
  · rcases Nat.even_or_odd (j + k) with heven | hodd
    · have hsign : star ((-1 : ℂ) ^ (j * (j - 1) / 2)) * (-1 : ℂ) ^ (k * (k - 1) / 2) *
          (-1 : ℂ) ^ j = (-1 : ℂ) ^ ((k + j) * (k + j - 1) / 2) := by
        have hst : star ((-1 : ℂ) ^ (j * (j - 1) / 2)) = (-1 : ℂ) ^ (j * (j - 1) / 2) := by
          simp
        rw [hst]
        exact neg_one_pow_chooseTwo_even (j := k) (k := j) (Nat.add_comm j k ▸ heven)
      rw [hsign]
    · have hW0 : ∀ (δ₂ : Fin j → ι) (δ₁ : Fin k → ι), W_jk δ₂ δ₁ = 0 := fun δ₂ δ₁ =>
        wightman_eq_zero_of_odd_of_spinParity_neg_one hP hε hodd _ _
      simp [hW0]

theorem inner_wightmanPCTPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (Ψ Φ : WightmanPreHilbertSpace WData) :
    ⟪wightmanPCTPreLM WData η Ψ, wightmanPCTPreLM WData η Φ⟫_ℂ = star ⟪Ψ, Φ⟫_ℂ := by
  conv_lhs =>
    rw [wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Ψ,
        wightmanPreHilbert_eq_finsupp_sum_wightmanBasisPre WData Φ]
  unfold Finsupp.sum
  rw [map_sum, map_sum, sum_inner]
  simp_rw [map_smulₛₗ, inner_smul_left, inner_sum, inner_smul_right,
    RingHomCompTriple.comp_apply, RingHom.id_apply, ← Complex.star_def,
    wightmanPCTPreLM_wightmanBasisPre,
    inner_wightmanPCTBasis WData hP hpct hε, Finset.mul_sum]
  rw [WightmanPreHilbertSpace.inner_def]
  unfold wightmanPreInner Finsupp.sum
  rw [star_sum]
  refine Finset.sum_congr rfl fun C₁ _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun C₂ _ => ?_
  simp only [star_mul', star_star]
  ring

theorem norm_wightmanPCTPreLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (Ψ : WightmanPreHilbertSpace WData) :
    ‖wightmanPCTPreLM WData η Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanPCTPreLM WData hP hpct hε Ψ Ψ, Complex.star_def, RCLike.conj_re]

def wightmanPCTPreCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η) :
    WightmanPreHilbertSpace WData →SL[starRingEnd ℂ] WightmanPreHilbertSpace WData :=
  (wightmanPCTPreLM WData η).mkContinuous 1 fun Ψ => by
    rw [one_mul, norm_wightmanPCTPreLM WData hP hpct hε Ψ]

def wightmanPCTCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η) :
    WightmanHilbert WData →SL[starRingEnd ℂ] WightmanHilbert WData :=
  (wightmanPCTPreCLM WData hP hpct hε).completion

@[simp]
lemma wightmanPCTCLM_toWightmanHilbert
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (Ψ : WightmanPreHilbertSpace WData) :
    wightmanPCTCLM WData hP hpct hε (toWightmanHilbert WData Ψ) =
      toWightmanHilbert WData (wightmanPCTPreLM WData η Ψ) :=
  ContinuousLinearMap.completion_apply_coe (wightmanPCTPreCLM WData hP hpct hε) Ψ

theorem inner_wightmanPCTCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (x y : WightmanHilbert WData) :
    ⟪wightmanPCTCLM WData hP hpct hε x, wightmanPCTCLM WData hP hpct hε y⟫_ℂ = star ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪wightmanPCTCLM WData hP hpct hε (toWightmanHilbert WData Ψ),
        wightmanPCTCLM WData hP hpct hε (toWightmanHilbert WData Φ)⟫_ℂ =
      star ⟪toWightmanHilbert WData Ψ, toWightmanHilbert WData Φ⟫_ℂ
    rw [wightmanPCTCLM_toWightmanHilbert, wightmanPCTCLM_toWightmanHilbert,
        inner_toWightmanHilbert, inner_toWightmanHilbert,
        inner_wightmanPCTPreLM WData hP hpct hε Ψ Φ]

@[simp]
theorem norm_wightmanPCTCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (x : WightmanHilbert WData) :
    ‖wightmanPCTCLM WData hP hpct hε x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_wightmanPCTCLM WData hP hpct hε x x, Complex.star_def, RCLike.conj_re]

theorem wightmanPCTCLM_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (x : WightmanHilbert WData) :
    wightmanPCTCLM WData hP hpct hε (wightmanPCTCLM WData hP hpct hε x) =
      wightmanSpinorLorentz WData hP (-1) x := by
  revert x
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanPCTCLM WData hP hpct hε
        (wightmanPCTCLM WData hP hpct hε (toWightmanHilbert WData Ψ)) =
      wightmanSpinorLorentz WData hP (-1) (toWightmanHilbert WData Ψ)
    rw [wightmanPCTCLM_toWightmanHilbert, wightmanPCTCLM_toWightmanHilbert,
        wightmanSpinorLorentz_toWightmanHilbert, wightmanPCTPreLM_sq WData hε Ψ]

@[simp]
theorem wightmanPCTCLM_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η) :
    wightmanPCTCLM WData hP hpct hε (wightmanVacuum WData) = wightmanVacuum WData := by
  dsimp [wightmanVacuum]
  rw [wightmanPCTCLM_toWightmanHilbert, wightmanPCTPreLM_vacuumPre]

theorem wightmanPCTCLM_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (a : Fin 4 → ℝ) (x : WightmanHilbert WData) :
    wightmanPCTCLM WData hP hpct hε
        (wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) a x) =
      wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) (-a)
        (wightmanPCTCLM WData hP hpct hε x) := by
  revert x
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanPCTCLM WData hP hpct hε
        (wightmanTranslate WData _ a (toWightmanHilbert WData Ψ)) =
      wightmanTranslate WData _ (-a)
        (wightmanPCTCLM WData hP hpct hε (toWightmanHilbert WData Ψ))
    rw [wightmanTranslate_toWightmanHilbert, wightmanPCTCLM_toWightmanHilbert,
        wightmanPCTCLM_toWightmanHilbert, wightmanTranslate_toWightmanHilbert,
        wightmanPCTPreLM_translateLM]

theorem wightmanPCTCLM_spinorLorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (A : SL2C) (x : WightmanHilbert WData) :
    wightmanPCTCLM WData hP hpct hε (wightmanSpinorLorentz WData hP A x) =
      wightmanSpinorLorentz WData hP A (wightmanPCTCLM WData hP hpct hε x) := by
  revert x
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change wightmanPCTCLM WData hP hpct hε
        (wightmanSpinorLorentz WData hP A (toWightmanHilbert WData Ψ)) =
      wightmanSpinorLorentz WData hP A
        (wightmanPCTCLM WData hP hpct hε (toWightmanHilbert WData Ψ))
    rw [wightmanSpinorLorentz_toWightmanHilbert, wightmanPCTCLM_toWightmanHilbert,
        wightmanPCTCLM_toWightmanHilbert, wightmanSpinorLorentz_toWightmanHilbert,
        wightmanPCTPreLM_spinorLorentzLM]

def wightmanPCTEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η) :
    WightmanHilbert WData ≃ₗᵢ⋆[ℂ] WightmanHilbert WData where
  toFun := wightmanPCTCLM WData hP hpct hε
  invFun x := wightmanSpinorLorentz WData hP (-1) (wightmanPCTCLM WData hP hpct hε x)
  left_inv x := by
    dsimp only
    rw [wightmanPCTCLM_sq, ← ContinuousLinearMap.comp_apply, ← wightmanSpinorLorentz_mul]
    have hsq : (-1 : SL2C) * (-1 : SL2C) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hsq, wightmanSpinorLorentz_one, ContinuousLinearMap.id_apply]
  right_inv x := by
    dsimp only
    rw [wightmanPCTCLM_spinorLorentz, wightmanPCTCLM_sq, ← ContinuousLinearMap.comp_apply,
        ← wightmanSpinorLorentz_mul]
    have hsq : (-1 : SL2C) * (-1 : SL2C) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hsq, wightmanSpinorLorentz_one, ContinuousLinearMap.id_apply]
  map_add' := map_add (wightmanPCTCLM WData hP hpct hε)
  map_smul' := map_smulₛₗ (wightmanPCTCLM WData hP hpct hε)
  norm_map' := norm_wightmanPCTCLM WData hP hpct hε

@[simp]
lemma wightmanPCTEquiv_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (x : WightmanHilbert WData) :
    wightmanPCTEquiv WData hP hpct hε x = wightmanPCTCLM WData hP hpct hε x := rfl

theorem inner_wightmanPCTEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (x y : WightmanHilbert WData) :
    ⟪wightmanPCTEquiv WData hP hpct hε x, wightmanPCTEquiv WData hP hpct hε y⟫_ℂ =
      star ⟪x, y⟫_ℂ :=
  inner_wightmanPCTCLM WData hP hpct hε x y

@[simp]
theorem wightmanPCTEquiv_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η) :
    wightmanPCTEquiv WData hP hpct hε (wightmanVacuum WData) = wightmanVacuum WData :=
  wightmanPCTCLM_vacuum WData hP hpct hε

theorem wightmanPCTEquiv_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (x : WightmanHilbert WData) :
    wightmanPCTEquiv WData hP hpct hε (wightmanPCTEquiv WData hP hpct hε x) =
      wightmanSpinorLorentzEquiv WData hP (-1) x :=
  wightmanPCTCLM_sq WData hP hpct hε x

theorem wightmanPCTEquiv_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (a : Fin 4 → ℝ) (x : WightmanHilbert WData) :
    wightmanPCTEquiv WData hP hpct hε
        (wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) a x) =
      wightmanTranslate WData (wightmanTranslationInvariant_of_poincare R hP) (-a)
        (wightmanPCTEquiv WData hP hpct hε x) :=
  wightmanPCTCLM_translate WData hP hpct hε a x

theorem wightmanPCTEquiv_lorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (A : SL2C) (x : WightmanHilbert WData) :
    wightmanPCTEquiv WData hP hpct hε (wightmanSpinorLorentzEquiv WData hP A x) =
      wightmanSpinorLorentzEquiv WData hP A (wightmanPCTEquiv WData hP hpct hε x) :=
  wightmanPCTCLM_spinorLorentz WData hP hpct hε A x

theorem wightmanPCTEquiv_poincare
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (a : Fin 4 → ℝ) (A : SL2C) (x : WightmanHilbert WData) :
    wightmanPCTEquiv WData hP hpct hε (wightmanPoincareEquiv WData hP a A x) =
      wightmanPoincareEquiv WData hP (-a) A (wightmanPCTEquiv WData hP hpct hε x) := by
  simp only [wightmanPoincareEquiv_apply]
  rw [wightmanPCTEquiv_translate, wightmanPCTEquiv_lorentz]

theorem wightmanPCTCLM_wightmanBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (C : WightmanConfig ι) :
    wightmanPCTCLM WData hP hpct hε (wightmanBasis WData C) =
      (η ^ (C.1 * (C.1 - 1) / 2)) •
        ∑ μ : Fin C.1 → ι,
          (∏ i : Fin C.1, pctMatrix S (C.2.1 i) (μ i)) •
            wightmanBasis WData ⟨C.1, (μ, compactSchwartzPTConj C.1 C.2.2)⟩ := by
  dsimp [wightmanBasis]
  rw [wightmanPCTCLM_toWightmanHilbert, wightmanPCTPreLM_wightmanBasisPre]
  unfold wightmanPCTBasis
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => map_smul _ _ _

theorem wightmanPCTEquiv_wightmanSchwartzVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (j : ℕ) (α : Fin j → ι)
    (f : SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) :
    wightmanPCTEquiv WData hP hpct hε (wightmanSchwartzVec WData j α f) =
      (η ^ (j * (j - 1) / 2)) •
        ∑ μ : Fin j → ι,
          (∏ i : Fin j, pctMatrix S (α i) (μ i)) •
            wightmanSchwartzVec WData j μ (schwartzPTConj j f) := by
  have h_lhs : Tendsto
      (fun m : ℕ => wightmanPCTCLM WData hP hpct hε
        (wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩))
      atTop (𝓝 (wightmanPCTCLM WData hP hpct hε (wightmanSchwartzVec WData j α f))) :=
    ((wightmanPCTCLM WData hP hpct hε).continuous.tendsto _).comp
      (tendsto_wightmanBasis_compactCutoff WData j α f)
  have h_rhs : Tendsto
      (fun m : ℕ => (η ^ (j * (j - 1) / 2)) •
        ∑ μ : Fin j → ι,
          (∏ i : Fin j, pctMatrix S (α i) (μ i)) •
            wightmanSchwartzVec WData j μ (schwartzPTConj j (schwartzCutoffSeq j f m)))
      atTop (𝓝 ((η ^ (j * (j - 1) / 2)) •
        ∑ μ : Fin j → ι,
          (∏ i : Fin j, pctMatrix S (α i) (μ i)) •
            wightmanSchwartzVec WData j μ (schwartzPTConj j f))) := by
    refine (tendsto_finsetSum Finset.univ fun μ _ => ?_).const_smul _
    exact (((wightmanSchwartzVec WData j μ).continuous.tendsto _).comp
      (((schwartzPTConj j).continuous.tendsto _).comp
        (schwartzCutoffSeq_tendsto j f))).const_smul _
  have h_eq : (fun m : ℕ => wightmanPCTCLM WData hP hpct hε
        (wightmanBasis WData ⟨j, (α, compactCutoff j f m)⟩)) =
      fun m : ℕ => (η ^ (j * (j - 1) / 2)) •
        ∑ μ : Fin j → ι,
          (∏ i : Fin j, pctMatrix S (α i) (μ i)) •
            wightmanSchwartzVec WData j μ (schwartzPTConj j (schwartzCutoffSeq j f m)) := by
    ext m
    rw [wightmanPCTCLM_wightmanBasis]
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    rw [← wightmanSchwartzVec_compact WData j μ
      (compactSchwartzPTConj j (compactCutoff j f m))]
    rfl
  rw [h_eq] at h_lhs
  exact tendsto_nhds_unique h_lhs h_rhs

def pctIndexedSchwartz {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (η : ℂ) (k : ℕ) (Φ : IndexedSchwartz ι k) : IndexedSchwartz ι k :=
  fun μ => (η ^ (k * (k - 1) / 2)) •
    ∑ α : Fin k → ι, (∏ i : Fin k, pctMatrix S (α i) (μ i)) • schwartzPTConj k (Φ α)

theorem wightmanPCTEquiv_wightmanIndexedVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (k : ℕ) (Φ : IndexedSchwartz ι k) :
    wightmanPCTEquiv WData hP hpct hε (wightmanIndexedVec WData k Φ) =
      wightmanIndexedVec WData k (pctIndexedSchwartz S η k Φ) := by
  change wightmanPCTEquiv WData hP hpct hε
      (∑ α : Fin k → ι, wightmanSchwartzVec WData k α (Φ α)) =
    ∑ μ : Fin k → ι, wightmanSchwartzVec WData k μ
      ((η ^ (k * (k - 1) / 2)) •
        ∑ α : Fin k → ι, (∏ i : Fin k, pctMatrix S (α i) (μ i)) • schwartzPTConj k (Φ α))
  rw [map_sum]
  simp_rw [wightmanPCTEquiv_wightmanSchwartzVec WData hP hpct hε k,
    map_smul, map_sum, map_smul, Finset.smul_sum]
  exact Finset.sum_comm

def WightmanAxioms.lorentzEquiv {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} (WAx : WightmanAxioms R S η) (A : SL2C) :
    WightmanHilbert WAx.WData ≃ₗᵢ[ℂ] WightmanHilbert WAx.WData :=
  wightmanSpinorLorentzEquiv WAx.WData WAx.poincare A

def WightmanAxioms.poincareEquiv {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} (WAx : WightmanAxioms R S η) (a : Fin 4 → ℝ) (A : SL2C) :
    WightmanHilbert WAx.WData ≃ₗᵢ[ℂ] WightmanHilbert WAx.WData :=
  wightmanPoincareEquiv WAx.WData WAx.poincare a A

theorem WightmanAxioms.wightmanPCT {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} (WAx : WightmanAxioms R S η) :
    WightmanPCT η R WAx.WData.W :=
  wightman_pct_of_spectrumCondition R WAx.WData.W WAx.spectrum WAx.poincare WAx.weakLocality

def WightmanAxioms.pctEquiv {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} (WAx : WightmanAxioms R S η) (hε : R.HasSpinParity η) :
    WightmanHilbert WAx.WData ≃ₗᵢ⋆[ℂ] WightmanHilbert WAx.WData :=
  wightmanPCTEquiv WAx.WData WAx.poincare WAx.wightmanPCT hε

end

end AntiunitaryPCTHilbert

section ModeMatrixAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma contDiff_massShellBoost {m : ℝ} (hm : 0 < m) (A : SL2C) :
    ContDiff ℝ (⊤ : ℕ∞) (massShellBoost m A) :=
  ((massShellSpatialProjCLM.comp (lorentzSingleCLM A)).contDiff).comp (contDiff_massShellVec hm)

lemma massShellBoost_neg_one (m : ℝ) (p : Fin 3 → ℝ) :
    massShellBoost m (-1) p = p := by
  ext j
  fin_cases j <;> simp [massShellBoost, lorentzOfSL2C_neg_one, massShellVec]

structure LorentzModeData
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (m : ℝ) (η : ℂ) (C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) where
  hm : 0 < m
  mode : MassShellModeData R S m η C_shell
  contDiff_w : ∀ (s : Fin mode.ν) (α : ι),
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => mode.w s p α)
  dual_w : Fin mode.ν → (Fin 3 → ℝ) → ι → ℂ
  contDiff_dual_w : ∀ (s : Fin mode.ν) (α : ι),
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => dual_w s p α)
  dual_orthonormal : ∀ (s₁ s₂ : Fin mode.ν) (p : Fin 3 → ℝ),
    ∑ α : ι, mode.w s₁ p α * dual_w s₂ p α = if s₁ = s₂ then 1 else 0
  hC_cov : ∀ (A : SL2C) (p : Fin 3 → ℝ) (α : Fin 2 → ι),
    C_shell α ((lorentzOfSL2C A).mulVec (massShellVec m p)) =
      ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C_shell β (massShellVec m p)

abbrev OnShellPCT
    (R : HolomorphicLorentzRep ι) (m : ℝ) (η : ℂ)
    (C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ (p : Fin 3 → ℝ) (α : Fin 2 → ι),
    C_shell α (massShellVec m p) =
      η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C_shell (β ∘ Fin.rev) (massShellVec m p)

def modeProj {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R S m η C_shell) (p : Fin 3 → ℝ) (ξ : ι → ℂ)
    (s' : Fin M_mode.ν) : ℂ :=
  ∑ γ : ι, M_mode.w s' p γ * ξ γ

omit [Fintype ι] [DecidableEq ι] in
lemma eq_zero_of_sum_star_mul_self_eq_zero {ν : ℕ} {u : Fin ν → ℂ}
    (h : ∑ s : Fin ν, star (u s) * u s = 0) (s : Fin ν) : u s = 0 := by
  have hre : ∑ s' : Fin ν, ‖u s'‖ ^ 2 = 0 := by
    have h0 := congrArg Complex.re h
    rw [Complex.zero_re] at h0
    have hsum : (∑ s' : Fin ν, star (u s') * u s').re = ∑ s' : Fin ν, ‖u s'‖ ^ 2 := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rwa [hsum] at h0
  have hsq : ‖u s‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun s' _ => sq_nonneg (‖u s'‖)).mp hre s
      (Finset.mem_univ s)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

lemma sum_star_mul_modeProj
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R S m η C_shell) (p : Fin 3 → ℝ) (ξ₁ ξ₂ : ι → ℂ) :
    (∑ s' : Fin M_mode.ν, star (modeProj M_mode p ξ₁ s') * modeProj M_mode p ξ₂ s') =
      ∑ γ₁ : ι, ∑ γ₂ : ι, star (ξ₁ γ₁) * ξ₂ γ₂ *
        (∑ δ : ι, S.C γ₁ δ * massShellWeight m C_shell ![δ, γ₂] p) := by
  have hexp : ∀ s' : Fin M_mode.ν,
      star (modeProj M_mode p ξ₁ s') * modeProj M_mode p ξ₂ s' =
        ∑ γ₁ : ι, ∑ γ₂ : ι,
          star (ξ₁ γ₁) * ξ₂ γ₂ * (star (M_mode.w s' p γ₁) * M_mode.w s' p γ₂) := by
    intro s'
    dsimp [modeProj]
    rw [← Complex.star_def, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ₂ _ => ?_
    rw [star_mul']
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun γ₁ _ => Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ₂ _ => ?_
  rw [← Finset.mul_sum, M_mode.factor_weight p γ₁ γ₂]

lemma finTwo_eq_cons {α : Type*} (β : Fin 2 → α) : ![β 0, β 1] = β := by
  ext i
  fin_cases i <;> rfl

lemma finTwo_cons_rev {α : Type*} (a b : α) : (![a, b] ∘ Fin.rev) = ![b, a] := by
  ext i
  fin_cases i <;> rfl

lemma sum_star_mul_modeProj_rep
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (p : Fin 3 → ℝ) (ξ₁ ξ₂ : ι → ℂ) :
    (∑ s' : Fin L.mode.ν,
        star (modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ₁ α) s') *
          modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ₂ α) s') =
      ((massShellEnergy m (massShellBoost m A⁻¹ p) / massShellEnergy m p : ℝ) : ℂ) *
        ∑ s' : Fin L.mode.ν,
          star (modeProj L.mode (massShellBoost m A⁻¹ p) ξ₁ s') *
            modeProj L.mode (massShellBoost m A⁻¹ p) ξ₂ s' := by
  let p' := massShellBoost m A⁻¹ p
  rw [sum_star_mul_modeProj, sum_star_mul_modeProj]
  have hp_eq : massShellVec m p = (lorentzOfSL2C A).mulVec (massShellVec m p') := by
    rw [lorentzOfSL2C_mulVec_massShellVec L.hm A p']
    dsimp [p']
    rw [massShellBoost_comp_inv L.hm A p]
  have hwt : ∀ δ γ₂ : ι,
      massShellWeight m C_shell ![δ, γ₂] p =
        ((massShellEnergy m p' / massShellEnergy m p : ℝ) : ℂ) *
          ∑ β : Fin 2 → ι, (R.rep A δ (β 0) * R.rep A γ₂ (β 1)) *
            massShellWeight m C_shell β p' := by
    intro δ γ₂
    dsimp [massShellWeight]
    rw [hp_eq, L.hC_cov A p' ![δ, γ₂], Finset.mul_sum]
    have hω1 : (massShellEnergy m p : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (massShellEnergy_pos L.hm p).ne'
    have hω2 : (massShellEnergy m p' : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (massShellEnergy_pos L.hm p').ne'
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Fin.prod_univ_two]
    dsimp [Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    field_simp [hω1, hω2]
  have hL :
      (∑ γ₁ : ι, ∑ γ₂ : ι,
        star (∑ α₁ : ι, R.rep A⁻¹ α₁ γ₁ * ξ₁ α₁) *
          (∑ α₂ : ι, R.rep A⁻¹ α₂ γ₂ * ξ₂ α₂) *
          (∑ δ : ι, S.C γ₁ δ * massShellWeight m C_shell ![δ, γ₂] p)) =
      ((massShellEnergy m p' / massShellEnergy m p : ℝ) : ℂ) *
        ∑ α₁ : ι, ∑ α₂ : ι, star (ξ₁ α₁) * ξ₂ α₂ *
          ∑ β : Fin 2 → ι,
            (∑ γ₁ : ι, ∑ δ : ι, star (R.rep A⁻¹ α₁ γ₁) * S.C γ₁ δ * R.rep A δ (β 0)) *
              (∑ γ₂ : ι, R.rep A⁻¹ α₂ γ₂ * R.rep A γ₂ (β 1)) *
                massShellWeight m C_shell β p' := by
    have h_mul1 :
        (∑ γ₁ : ι, ∑ γ₂ : ι,
          star (∑ α₁ : ι, R.rep A⁻¹ α₁ γ₁ * ξ₁ α₁) *
            (∑ α₂ : ι, R.rep A⁻¹ α₂ γ₂ * ξ₂ α₂) *
            (∑ δ : ι, S.C γ₁ δ * massShellWeight m C_shell ![δ, γ₂] p)) =
        ∑ α₁ : ι, ∑ α₂ : ι, star (ξ₁ α₁) * ξ₂ α₂ *
          ∑ γ₁ : ι, ∑ γ₂ : ι, ∑ δ : ι,
            star (R.rep A⁻¹ α₁ γ₁) * S.C γ₁ δ * R.rep A⁻¹ α₂ γ₂ *
              massShellWeight m C_shell ![δ, γ₂] p := by
      have hterm1 : ∀ γ₁ γ₂ : ι,
          star (∑ α₁ : ι, R.rep A⁻¹ α₁ γ₁ * ξ₁ α₁) *
              (∑ α₂ : ι, R.rep A⁻¹ α₂ γ₂ * ξ₂ α₂) *
              (∑ δ : ι, S.C γ₁ δ * massShellWeight m C_shell ![δ, γ₂] p) =
            ∑ α₁ : ι, ∑ α₂ : ι, ∑ δ : ι,
              star (ξ₁ α₁) * ξ₂ α₂ *
                (star (R.rep A⁻¹ α₁ γ₁) * S.C γ₁ δ * R.rep A⁻¹ α₂ γ₂ *
                  massShellWeight m C_shell ![δ, γ₂] p) := by
        intro γ₁ γ₂
        rw [star_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α₁ _ => ?_
        conv_lhs =>
          arg 1
          rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun α₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [star_mul']
        ring
      rw [Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ₂ _ => hterm1 γ₁ γ₂]
      rw [Finset.sum_congr rfl fun γ₁ _ => Finset.sum_comm, Finset.sum_comm]
      rw [Finset.sum_congr rfl fun α₁ _ => Finset.sum_congr rfl fun γ₁ _ => Finset.sum_comm]
      rw [Finset.sum_congr rfl fun α₁ _ => Finset.sum_comm]
      refine Finset.sum_congr rfl fun α₁ _ => Finset.sum_congr rfl fun α₂ _ => ?_
      simp_rw [Finset.mul_sum]
    rw [h_mul1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α₂ _ => ?_
    rw [mul_left_comm ((massShellEnergy m p' / massShellEnergy m p : ℝ) : ℂ) _ _]
    congr 1
    have hterm2 : ∀ γ₁ γ₂ δ : ι,
        star (R.rep A⁻¹ α₁ γ₁) * S.C γ₁ δ * R.rep A⁻¹ α₂ γ₂ *
            massShellWeight m C_shell ![δ, γ₂] p =
          ((massShellEnergy m p' / massShellEnergy m p : ℝ) : ℂ) *
            ∑ β : Fin 2 → ι,
              (star (R.rep A⁻¹ α₁ γ₁) * S.C γ₁ δ * R.rep A δ (β 0)) *
                (R.rep A⁻¹ α₂ γ₂ * R.rep A γ₂ (β 1)) * massShellWeight m C_shell β p' := by
      intro γ₁ γ₂ δ
      rw [hwt δ γ₂, mul_left_comm _ ((massShellEnergy m p' / massShellEnergy m p : ℝ) : ℂ) _]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => by ring
    rw [Finset.sum_congr rfl fun γ₁ _ =>
      Finset.sum_congr rfl fun γ₂ _ => Finset.sum_congr rfl fun δ _ => hterm2 γ₁ γ₂ δ]
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ₂ _ => Finset.sum_comm]
    rw [Finset.sum_congr rfl fun γ₁ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ₁ _ => ?_
    rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hL]
  congr 1
  refine Finset.sum_congr rfl fun α₁ _ => Finset.sum_congr rfl fun α₂ _ => ?_
  congr 1
  have hinv_mat : R.rep A⁻¹ * R.rep A = (1 : Matrix ι ι ℂ) := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have h_bra : ∀ β₀ : ι,
      (∑ γ₁ : ι, ∑ δ : ι, star (R.rep A⁻¹ α₁ γ₁) * S.C γ₁ δ * R.rep A δ β₀) = S.C α₁ β₀ :=
    fun β₀ => starStructure_rep_inv_bra_ket S A α₁ β₀
  have h_ket : ∀ β₁ : ι,
      (∑ γ₂ : ι, R.rep A⁻¹ α₂ γ₂ * R.rep A γ₂ β₁) = if α₂ = β₁ then 1 else 0 := fun β₁ => by
    have hmul : (∑ γ₂ : ι, R.rep A⁻¹ α₂ γ₂ * R.rep A γ₂ β₁) = (R.rep A⁻¹ * R.rep A) α₂ β₁ := by
      rfl
    rw [hmul, hinv_mat, Matrix.one_apply]
  let e : (ι × ι) ≃ (Fin 2 → ι) :=
    { toFun := fun q => ![q.1, q.2]
      invFun := fun β => (β 0, β 1)
      left_inv := fun _ => rfl
      right_inv := fun β => finTwo_eq_cons β }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Finset.sum_eq_single α₂]
  · dsimp [e]
    rw [← Complex.star_def, h_bra δ, h_ket α₂, if_pos rfl, mul_one]
  · intro β₁ _ hne
    dsimp [e]
    rw [h_ket β₁, if_neg hne.symm, mul_zero, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ α₂))

lemma sum_star_mul_modeProj_pct
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (p : Fin 3 → ℝ) (ξ₁ ξ₂ : ι → ℂ) :
    (∑ s' : Fin L.mode.ν,
        star (modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ₁ α)) s') *
          modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ₂ α)) s') =
      ∑ s' : Fin L.mode.ν, star (modeProj L.mode p ξ₂ s') * modeProj L.mode p ξ₁ s' := by
  rw [sum_star_mul_modeProj, sum_star_mul_modeProj]
  have h_mulC : ∀ α₁ δ : ι,
      (∑ μ₁ : ι, star (pctMatrix S α₁ μ₁) * S.C μ₁ δ) = η * R.σ (-1, 1) α₁ δ := by
    intro α₁ δ
    have hmat := pctMatrix_conj_mul_C S hε
    have hent := congrArg (fun M : Matrix ι ι ℂ => M α₁ δ) hmat
    dsimp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent
    exact hent
  have h_pct_w : ∀ α₁ β₂ : ι,
      (∑ δ : ι, ∑ μ₂ : ι,
        R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ * massShellWeight m C_shell ![δ, μ₂] p) =
      η * massShellWeight m C_shell ![β₂, α₁] p := by
    intro α₁ β₂
    have hp := hC_pct p ![β₂, α₁]
    have hη_sq : η * η = 1 := by
      rcases hε.2 with rfl | rfl <;> simp
    dsimp [massShellWeight]
    have hω_pull :
        (∑ δ : ι, ∑ μ₂ : ι,
          R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ *
            (((2 * massShellEnergy m p)⁻¹ : ℂ) * C_shell ![δ, μ₂] (massShellVec m p))) =
        ((2 * massShellEnergy m p)⁻¹ : ℂ) *
          ∑ μ₂ : ι, ∑ δ : ι,
            (R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ) * C_shell ![δ, μ₂] (massShellVec m p) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ₂ _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun δ _ => by ring
    let e : (ι × ι) ≃ (Fin 2 → ι) :=
      { toFun := fun q => ![q.1, q.2]
        invFun := fun ρ => (ρ 0, ρ 1)
        left_inv := fun _ => rfl
        right_inv := fun ρ => finTwo_eq_cons ρ }
    have hsum_eq :
        (∑ μ₂ : ι, ∑ δ : ι,
          (R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ) * C_shell ![δ, μ₂] (massShellVec m p)) =
        ∑ ρ : Fin 2 → ι,
          (∏ i : Fin 2, R.σ (-1, 1) (![β₂, α₁] i) (ρ i)) *
            C_shell (ρ ∘ Fin.rev) (massShellVec m p) := by
      rw [← e.sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun μ₂ _ => Finset.sum_congr rfl fun δ _ => ?_
      dsimp [e]
      rw [Fin.prod_univ_two, finTwo_cons_rev]
      simp
    rw [hω_pull, hsum_eq]
    have hC_rel : η * ∑ ρ : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (![β₂, α₁] i) (ρ i)) *
          C_shell (ρ ∘ Fin.rev) (massShellVec m p) =
        C_shell ![β₂, α₁] (massShellVec m p) := hp.symm
    calc ((2 * massShellEnergy m p)⁻¹ : ℂ) *
          ∑ ρ : Fin 2 → ι,
            (∏ i : Fin 2, R.σ (-1, 1) (![β₂, α₁] i) (ρ i)) *
              C_shell (ρ ∘ Fin.rev) (massShellVec m p)
        = η * (((2 * massShellEnergy m p)⁻¹ : ℂ) *
            (η * ∑ ρ : Fin 2 → ι,
              (∏ i : Fin 2, R.σ (-1, 1) (![β₂, α₁] i) (ρ i)) *
                C_shell (ρ ∘ Fin.rev) (massShellVec m p))) := by
          calc _ = (η * η) * (((2 * massShellEnergy m p)⁻¹ : ℂ) *
              ∑ ρ : Fin 2 → ι,
                (∏ i : Fin 2, R.σ (-1, 1) (![β₂, α₁] i) (ρ i)) *
                  C_shell (ρ ∘ Fin.rev) (massShellVec m p)) := by rw [hη_sq, one_mul]
            _ = _ := by ring
      _ = η * (((2 * massShellEnergy m p)⁻¹ : ℂ) * C_shell ![β₂, α₁] (massShellVec m p)) := by
          rw [hC_rel]
  have hη_sq : η * η = 1 := by
    rcases hε.2 with rfl | rfl <;> simp
  have hpct_entry : ∀ α₂ μ₂ : ι,
      pctMatrix S α₂ μ₂ = ∑ β₂ : ι, S.C α₂ β₂ * R.σ (-1, 1) β₂ μ₂ := fun α₂ μ₂ => rfl
  have h_lhs :
      (∑ μ₁ : ι, ∑ μ₂ : ι,
        star (∑ α₁ : ι, pctMatrix S α₁ μ₁ * star (ξ₁ α₁)) *
          (∑ α₂ : ι, pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) *
            (∑ δ : ι, S.C μ₁ δ * massShellWeight m C_shell ![δ, μ₂] p)) =
      ∑ α₂ : ι, ∑ α₁ : ι, star (ξ₂ α₂) * ξ₁ α₁ *
        (η * ∑ β₂ : ι, S.C α₂ β₂ *
          ∑ δ : ι, ∑ μ₂ : ι,
            R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ * massShellWeight m C_shell ![δ, μ₂] p) := by
    have h_split :
        (∑ μ₁ : ι, ∑ μ₂ : ι,
          star (∑ α₁ : ι, pctMatrix S α₁ μ₁ * star (ξ₁ α₁)) *
            (∑ α₂ : ι, pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) *
              (∑ δ : ι, S.C μ₁ δ * massShellWeight m C_shell ![δ, μ₂] p)) =
        ∑ α₂ : ι, ∑ α₁ : ι,
          ∑ μ₂ : ι, ∑ μ₁ : ι, ∑ δ : ι,
            star (pctMatrix S α₁ μ₁) * ξ₁ α₁ * (pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) *
              (S.C μ₁ δ * massShellWeight m C_shell ![δ, μ₂] p) := by
      have hterm' : ∀ μ₁ μ₂ : ι,
          star (∑ α₁ : ι, pctMatrix S α₁ μ₁ * star (ξ₁ α₁)) *
              (∑ α₂ : ι, pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) *
              (∑ δ : ι, S.C μ₁ δ * massShellWeight m C_shell ![δ, μ₂] p) =
            ∑ α₂ : ι, ∑ α₁ : ι, ∑ δ : ι,
              star (pctMatrix S α₁ μ₁) * ξ₁ α₁ * (pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) *
                (S.C μ₁ δ * massShellWeight m C_shell ![δ, μ₂] p) := by
        intro μ₁ μ₂
        rw [star_sum]
        have h1 :
            (∑ α₁ : ι, star (pctMatrix S α₁ μ₁ * star (ξ₁ α₁))) *
              (∑ α₂ : ι, pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) =
            ∑ α₂ : ι, ∑ α₁ : ι,
              star (pctMatrix S α₁ μ₁) * ξ₁ α₁ * (pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) := by
          rw [Finset.sum_mul, Finset.sum_comm]
          refine Finset.sum_congr rfl fun α₂ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun α₁ _ => ?_
          rw [star_mul', star_star]
        rw [h1, Finset.sum_mul]
        refine Finset.sum_congr rfl fun α₂ _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun α₁ _ => ?_
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl fun μ₁ _ => Finset.sum_congr rfl fun μ₂ _ => hterm' μ₁ μ₂]
      rw [Finset.sum_congr rfl fun μ₁ _ => Finset.sum_comm, Finset.sum_comm]
      rw [Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun μ₁ _ => Finset.sum_comm]
      rw [Finset.sum_congr rfl fun α₂ _ => Finset.sum_comm]
      refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun α₁ _ => Finset.sum_comm
    rw [h_split]
    refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun α₁ _ => ?_
    have h_inner :
        (∑ μ₂ : ι, ∑ μ₁ : ι, ∑ δ : ι,
          star (pctMatrix S α₁ μ₁) * ξ₁ α₁ * (pctMatrix S α₂ μ₂ * star (ξ₂ α₂)) *
            (S.C μ₁ δ * massShellWeight m C_shell ![δ, μ₂] p)) =
        star (ξ₂ α₂) * ξ₁ α₁ *
          (∑ μ₂ : ι, ∑ δ : ι,
            (∑ μ₁ : ι, star (pctMatrix S α₁ μ₁) * S.C μ₁ δ) *
              (pctMatrix S α₂ μ₂ * massShellWeight m C_shell ![δ, μ₂] p)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ₂ _ => ?_
      rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ₁ _ => by ring
    rw [h_inner]
    congr 1
    have h_step : ∀ μ₂ δ : ι,
        (∑ μ₁ : ι, star (pctMatrix S α₁ μ₁) * S.C μ₁ δ) *
            (pctMatrix S α₂ μ₂ * massShellWeight m C_shell ![δ, μ₂] p) =
          η * ∑ β₂ : ι,
            S.C α₂ β₂ *
              (R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ * massShellWeight m C_shell ![δ, μ₂] p) := by
      intro μ₂ δ
      rw [h_mulC α₁ δ, hpct_entry α₂ μ₂, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β₂ _ => by ring
    rw [Finset.sum_congr rfl fun μ₂ _ => Finset.sum_congr rfl fun δ _ => h_step μ₂ δ]
    simp_rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun μ₂ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun β₂ _ => ?_
    simp_rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  rw [h_lhs]
  refine Finset.sum_congr rfl fun α₂ _ => Finset.sum_congr rfl fun α₁ _ => ?_
  congr 1
  have h_re_w :
      (η * ∑ β₂ : ι, S.C α₂ β₂ *
        ∑ δ : ι, ∑ μ₂ : ι,
          R.σ (-1, 1) β₂ μ₂ * R.σ (-1, 1) α₁ δ * massShellWeight m C_shell ![δ, μ₂] p) =
      ∑ δ : ι, S.C α₂ δ * massShellWeight m C_shell ![δ, α₁] p := by
    rw [Finset.sum_congr rfl fun β₂ _ => congrArg (S.C α₂ β₂ * ·) (h_pct_w α₁ β₂),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun β₂ _ => ?_
    calc
      η * (S.C α₂ β₂ * (η * massShellWeight m C_shell ![β₂, α₁] p))
        = (η * η) * (S.C α₂ β₂ * massShellWeight m C_shell ![β₂, α₁] p) := by ring
      _ = S.C α₂ β₂ * massShellWeight m C_shell ![β₂, α₁] p := by rw [hη_sq, one_mul]
  exact h_re_w

def wignerModeMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (p : Fin 3 → ℝ)
    (s' s : Fin L.mode.ν) : ℂ :=
  ∑ α : ι, ∑ γ : ι, L.mode.w s' p γ * R.rep A⁻¹ α γ * L.dual_w s (massShellBoost m A⁻¹ p) α

lemma wignerModeMatrix_eq_modeProj
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (p : Fin 3 → ℝ)
    (s' s : Fin L.mode.ν) :
    wignerModeMatrix L A p s' s =
      modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * L.dual_w s (massShellBoost m A⁻¹ p) α)
        s' := by
  dsimp [wignerModeMatrix, modeProj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => by ring

lemma contDiff_wignerModeMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (s' s : Fin L.mode.ν) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => wignerModeMatrix L A p s' s) := by
  unfold wignerModeMatrix
  refine ContDiff.sum fun α _ => ContDiff.sum fun γ _ => ?_
  exact ((L.contDiff_w s' γ).mul contDiff_const).mul
    ((L.contDiff_dual_w s α).comp (contDiff_massShellBoost L.hm A⁻¹))

lemma wignerModeMatrix_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (p : Fin 3 → ℝ) (s' s : Fin L.mode.ν) :
    wignerModeMatrix L 1 p s' s = if s' = s then 1 else 0 := by
  unfold wignerModeMatrix
  have h1 : R.rep (1 : SL2C)⁻¹ = (1 : Matrix ι ι ℂ) := by rw [inv_one, map_one]
  have hb : massShellBoost m (1 : SL2C)⁻¹ p = p := by rw [inv_one, massShellBoost_one]
  simp_rw [h1, hb]
  rw [Finset.sum_comm]
  have h_eq :
      (∑ γ : ι, ∑ α : ι, L.mode.w s' p γ * (1 : Matrix ι ι ℂ) α γ * L.dual_w s p α) =
      ∑ α : ι, L.mode.w s' p α * L.dual_w s p α := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_eq_single α]
    · simp
    · intro γ _ hne
      simp [Matrix.one_apply_ne hne.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ α))
  rw [h_eq, L.dual_orthonormal s' s p]

lemma wignerModeMatrix_neg_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (p : Fin 3 → ℝ) (s' s : Fin L.mode.ν) :
    wignerModeMatrix L (-1) p s' s = if s' = s then η else 0 := by
  unfold wignerModeMatrix
  have hinv : (-1 : SL2C)⁻¹ = -1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hinv, massShellBoost_neg_one, rep_neg_one_of_hasSpinParity hε, Finset.sum_comm]
  have h_eq :
      (∑ γ : ι, ∑ α : ι, L.mode.w s' p γ * (η • (1 : Matrix ι ι ℂ)) α γ * L.dual_w s p α) =
      η * ∑ α : ι, L.mode.w s' p α * L.dual_w s p α := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_eq_single α]
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one]
      ring
    · intro γ _ hne
      simp [Matrix.one_apply_ne hne.symm]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ α))
  rw [h_eq, L.dual_orthonormal s' s p]
  split_ifs <;> simp

lemma sum_star_mul_wignerModeMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (p : Fin 3 → ℝ)
    (s₁ s₂ : Fin L.mode.ν) :
    (∑ s' : Fin L.mode.ν,
        star (wignerModeMatrix L A p s' s₁) * wignerModeMatrix L A p s' s₂) =
      ((massShellEnergy m (massShellBoost m A⁻¹ p) / massShellEnergy m p : ℝ) : ℂ) *
        if s₁ = s₂ then 1 else 0 := by
  simp_rw [wignerModeMatrix_eq_modeProj]
  rw [sum_star_mul_modeProj_rep L A p]
  congr 1
  have h_proj : ∀ s₀ s' : Fin L.mode.ν,
      modeProj L.mode (massShellBoost m A⁻¹ p) (L.dual_w s₀ (massShellBoost m A⁻¹ p)) s' =
        if s' = s₀ then 1 else 0 := fun s₀ s' => L.dual_orthonormal s' s₀ _
  simp_rw [h_proj]
  by_cases hs : s₁ = s₂
  · subst hs
    rw [if_pos rfl, Finset.sum_eq_single s₁]
    · simp
    · intro s' _ hne
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s₁))
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun s' _ => ?_
    by_cases h1 : s' = s₁
    · subst h1
      simp [hs]
    · simp [h1]

lemma wignerModeMatrix_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A B : SL2C) (p : Fin 3 → ℝ)
    (s' s : Fin L.mode.ν) :
    (∑ s'' : Fin L.mode.ν,
        wignerModeMatrix L A p s' s'' * wignerModeMatrix L B (massShellBoost m A⁻¹ p) s'' s) =
      wignerModeMatrix L (A * B) p s' s := by
  let p' := massShellBoost m A⁻¹ p
  let p'' := massShellBoost m B⁻¹ p'
  let ξ : ι → ℂ := fun α =>
    (∑ s'' : Fin L.mode.ν, L.dual_w s'' p' α * wignerModeMatrix L B p' s'' s) -
      ∑ β : ι, R.rep B⁻¹ β α * L.dual_w s p'' β
  have h_zero_p' : ∀ s'' : Fin L.mode.ν, modeProj L.mode p' ξ s'' = 0 := by
    intro s''
    dsimp [modeProj, ξ]
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 :
        (∑ x : Fin L.mode.ν, ∑ α : ι,
          L.mode.w s'' p' α * (L.dual_w x p' α * wignerModeMatrix L B p' x s)) =
        wignerModeMatrix L B p' s'' s := by
      have hterm : ∀ x : Fin L.mode.ν,
          (∑ α : ι, L.mode.w s'' p' α * (L.dual_w x p' α * wignerModeMatrix L B p' x s)) =
            (if s'' = x then 1 else 0) * wignerModeMatrix L B p' x s := by
        intro x
        have hmul :
            (∑ α : ι, L.mode.w s'' p' α * (L.dual_w x p' α * wignerModeMatrix L B p' x s)) =
              (∑ α : ι, L.mode.w s'' p' α * L.dual_w x p' α) * wignerModeMatrix L B p' x s := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => by ring
        rw [hmul, L.dual_orthonormal s'' x p']
      simp_rw [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 :
        (∑ α : ι, ∑ β : ι, L.mode.w s'' p' α * (R.rep B⁻¹ β α * L.dual_w s p'' β)) =
        wignerModeMatrix L B p' s'' s := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring
    rw [h1, h2, sub_self]
  have h_sum_zero :
      (∑ s₀ : Fin L.mode.ν,
        star (modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ α) s₀) *
          modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ α) s₀) = 0 := by
    have h_p' : (∑ s₀ : Fin L.mode.ν,
        star (modeProj L.mode p' ξ s₀) * modeProj L.mode p' ξ s₀) = 0 := by
      simp [h_zero_p']
    rw [sum_star_mul_modeProj_rep L A p ξ ξ, h_p', mul_zero]
  have h_pt := eq_zero_of_sum_star_mul_self_eq_zero h_sum_zero s'
  have h_diff_eq :
      modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ α) s' =
        (∑ s'' : Fin L.mode.ν,
          wignerModeMatrix L A p s' s'' * wignerModeMatrix L B p' s'' s) -
          wignerModeMatrix L (A * B) p s' s := by
    dsimp [modeProj, ξ]
    have h_term_diff : ∀ γ : ι,
        L.mode.w s' p γ * ∑ α : ι, R.rep A⁻¹ α γ *
            ((∑ s'' : Fin L.mode.ν, L.dual_w s'' p' α * wignerModeMatrix L B p' s'' s) -
              ∑ β : ι, R.rep B⁻¹ β α * L.dual_w s p'' β) =
          (∑ α : ι, ∑ s'' : Fin L.mode.ν,
            L.mode.w s' p γ * R.rep A⁻¹ α γ * L.dual_w s'' p' α *
              wignerModeMatrix L B p' s'' s) -
          ∑ α : ι, ∑ β : ι,
            L.mode.w s' p γ * R.rep A⁻¹ α γ * (R.rep B⁻¹ β α * L.dual_w s p'' β) := by
      intro γ
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [mul_sub, mul_sub]
      simp_rw [Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [Finset.sum_congr rfl fun γ _ => h_term_diff γ, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_congr rfl fun γ _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun s'' _ => ?_
      dsimp [wignerModeMatrix]
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_mul]
    · have hp_inv : massShellBoost m (A * B)⁻¹ p = p'' := by
        rw [_root_.mul_inv_rev, massShellBoost_mul L.hm]
      have hrep_inv : R.rep (A * B)⁻¹ = R.rep B⁻¹ * R.rep A⁻¹ := by
        rw [_root_.mul_inv_rev, map_mul]
      dsimp [wignerModeMatrix]
      rw [hp_inv, hrep_inv]
      have h_inner : ∀ γ α : ι,
          (∑ β : ι, L.mode.w s' p γ * R.rep A⁻¹ α γ * (R.rep B⁻¹ β α * L.dual_w s p'' β)) =
          ∑ β : ι, L.mode.w s' p γ * (R.rep B⁻¹ β α * R.rep A⁻¹ α γ) * L.dual_w s p'' β :=
        fun γ α => Finset.sum_congr rfl fun β _ => by ring
      rw [Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun α _ => h_inner γ α]
      rw [Finset.sum_congr rfl fun γ _ => Finset.sum_comm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun γ _ => ?_
      rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [h_diff_eq] at h_pt
  exact sub_eq_zero.mp h_pt

def wignerUnitaryMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (p : Fin 3 → ℝ) :
    Matrix (Fin L.mode.ν) (Fin L.mode.ν) ℂ :=
  fun s' s =>
    ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) : ℝ) : ℂ) *
      wignerModeMatrix L A p s' s

theorem wignerUnitaryMatrix_conjTranspose_mul_self
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (p : Fin 3 → ℝ) :
    (wignerUnitaryMatrix L A p)ᴴ * wignerUnitaryMatrix L A p = 1 := by
  ext s₁ s₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply, wignerUnitaryMatrix]
  have hpos : 0 ≤ massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p) :=
    div_nonneg (massShellEnergy_pos L.hm p).le (massShellEnergy_pos L.hm _).le
  have h_conj :
      star ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) : ℝ) :
        ℂ) *
        ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) : ℝ) :
          ℂ) =
      ((massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos]
  have h_sum :
      (∑ s' : Fin L.mode.ν,
        star
          (((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) : ℝ) :
            ℂ) * wignerModeMatrix L A p s' s₁) *
          (((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) : ℝ) :
            ℂ) * wignerModeMatrix L A p s' s₂)) =
      ((massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p) : ℝ) : ℂ) *
        ∑ s' : Fin L.mode.ν,
          star (wignerModeMatrix L A p s' s₁) * wignerModeMatrix L A p s' s₂ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    calc
      star (((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) :
          ℝ) : ℂ) * wignerModeMatrix L A p s' s₁) *
        (((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) :
          ℝ) : ℂ) * wignerModeMatrix L A p s' s₂)
        = (star ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) :
              ℝ) : ℂ) *
            ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) :
              ℝ) : ℂ)) *
            (star (wignerModeMatrix L A p s' s₁) * wignerModeMatrix L A p s' s₂) := by
            rw [star_mul']
            ring
      _ = _ := by rw [h_conj]
  rw [h_sum, sum_star_mul_wignerModeMatrix L A p s₁ s₂]
  have hω1 : (massShellEnergy m p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (massShellEnergy_pos L.hm p).ne'
  have hω2 : (massShellEnergy m (massShellBoost m A⁻¹ p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (massShellEnergy_pos L.hm _).ne'
  push_cast
  split_ifs <;> field_simp [hω1, hω2]

theorem wignerUnitaryMatrix_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A B : SL2C) (p : Fin 3 → ℝ) :
    wignerUnitaryMatrix L A p * wignerUnitaryMatrix L B (massShellBoost m A⁻¹ p) =
      wignerUnitaryMatrix L (A * B) p := by
  ext s' s
  rw [Matrix.mul_apply]
  dsimp [wignerUnitaryMatrix]
  have h_fac :
      Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) *
        Real.sqrt
          (massShellEnergy m (massShellBoost m A⁻¹ p) /
            massShellEnergy m (massShellBoost m B⁻¹ (massShellBoost m A⁻¹ p))) =
      Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m (A * B)⁻¹ p)) := by
    have hω1 : 0 < massShellEnergy m p := massShellEnergy_pos L.hm p
    have hω2 : 0 < massShellEnergy m (massShellBoost m A⁻¹ p) := massShellEnergy_pos L.hm _
    have hω3 :
        0 < massShellEnergy m (massShellBoost m B⁻¹ (massShellBoost m A⁻¹ p)) :=
      massShellEnergy_pos L.hm _
    rw [← Real.sqrt_mul (div_nonneg hω1.le hω2.le), div_mul_div_cancel₀ hω2.ne',
      ← massShellBoost_mul L.hm B⁻¹ A⁻¹, ← _root_.mul_inv_rev]
  have h_sum :
      (∑ x : Fin L.mode.ν,
        ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m A⁻¹ p)) : ℝ) :
          ℂ) * wignerModeMatrix L A p s' x *
        (((Real.sqrt
            (massShellEnergy m (massShellBoost m A⁻¹ p) /
              massShellEnergy m (massShellBoost m B⁻¹ (massShellBoost m A⁻¹ p))) : ℝ) : ℂ) *
          wignerModeMatrix L B (massShellBoost m A⁻¹ p) x s)) =
      ((Real.sqrt (massShellEnergy m p / massShellEnergy m (massShellBoost m (A * B)⁻¹ p)) : ℝ) :
        ℂ) * ∑ x : Fin L.mode.ν,
          wignerModeMatrix L A p s' x * wignerModeMatrix L B (massShellBoost m A⁻¹ p) x s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← h_fac, Complex.ofReal_mul]
    ring
  rw [h_sum, wignerModeMatrix_mul L A B p s' s]

def pctModeMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (p : Fin 3 → ℝ) (s' s : Fin L.mode.ν) : ℂ :=
  ∑ α : ι, ∑ μ : ι, L.mode.w s' p μ * pctMatrix S α μ * star (L.dual_w s p α)

lemma pctModeMatrix_eq_modeProj
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (p : Fin 3 → ℝ) (s' s : Fin L.mode.ν) :
    pctModeMatrix L p s' s =
      modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (L.dual_w s p α)) s' := by
  dsimp [pctModeMatrix, modeProj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => by ring

lemma contDiff_pctModeMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (s' s : Fin L.mode.ν) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => pctModeMatrix L p s' s) := by
  unfold pctModeMatrix
  refine ContDiff.sum fun α _ => ContDiff.sum fun μ _ => ?_
  exact ((L.contDiff_w s' μ).mul contDiff_const).mul
    (Complex.conjCLE.contDiff.comp (L.contDiff_dual_w s α))

lemma sum_star_mul_pctModeMatrix
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (p : Fin 3 → ℝ) (s₁ s₂ : Fin L.mode.ν) :
    (∑ s' : Fin L.mode.ν, star (pctModeMatrix L p s' s₁) * pctModeMatrix L p s' s₂) =
      if s₁ = s₂ then 1 else 0 := by
  simp_rw [pctModeMatrix_eq_modeProj]
  rw [sum_star_mul_modeProj_pct L hε hC_pct p]
  have h_proj : ∀ s₀ s' : Fin L.mode.ν,
      modeProj L.mode p (L.dual_w s₀ p) s' = if s' = s₀ then 1 else 0 :=
    fun s₀ s' => L.dual_orthonormal s' s₀ p
  simp_rw [h_proj]
  by_cases hs : s₁ = s₂
  · subst hs
    rw [if_pos rfl, Finset.sum_eq_single s₁]
    · simp
    · intro s' _ hne
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s₁))
  · rw [if_neg hs]
    refine Finset.sum_eq_zero fun s' _ => ?_
    by_cases h2 : s' = s₂
    · subst h2
      simp [Ne.symm hs]
    · simp [h2]

lemma pctModeMatrix_mul_conj
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (p : Fin 3 → ℝ) (s'' s : Fin L.mode.ν) :
    (∑ s' : Fin L.mode.ν, pctModeMatrix L p s'' s' * star (pctModeMatrix L p s' s)) =
      if s'' = s then η else 0 := by
  let ξ : ι → ℂ := fun α =>
    (∑ s' : Fin L.mode.ν, L.dual_w s' p α * pctModeMatrix L p s' s) -
      ∑ β : ι, pctMatrix S β α * star (L.dual_w s p β)
  have h_zero : ∀ s' : Fin L.mode.ν, modeProj L.mode p ξ s' = 0 := by
    intro s'
    dsimp [modeProj, ξ]
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 :
        (∑ x : Fin L.mode.ν, ∑ α : ι,
          L.mode.w s' p α * (L.dual_w x p α * pctModeMatrix L p x s)) =
        pctModeMatrix L p s' s := by
      have hterm : ∀ x : Fin L.mode.ν,
          (∑ α : ι, L.mode.w s' p α * (L.dual_w x p α * pctModeMatrix L p x s)) =
            (if s' = x then 1 else 0) * pctModeMatrix L p x s := by
        intro x
        have hmul :
            (∑ α : ι, L.mode.w s' p α * (L.dual_w x p α * pctModeMatrix L p x s)) =
              (∑ α : ι, L.mode.w s' p α * L.dual_w x p α) * pctModeMatrix L p x s := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => by ring
        rw [hmul, L.dual_orthonormal s' x p]
      simp_rw [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h2 :
        (∑ α : ι, ∑ β : ι, L.mode.w s' p α * (pctMatrix S β α * star (L.dual_w s p β))) =
        pctModeMatrix L p s' s := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring
    rw [h1, ← Complex.star_def, h2, sub_self]
  have h_sum_zero :
      (∑ s₀ : Fin L.mode.ν,
        star (modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ α)) s₀) *
          modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ α)) s₀) = 0 := by
    rw [sum_star_mul_modeProj_pct L hε hC_pct p ξ ξ]
    simp [h_zero]
  have h_pt := eq_zero_of_sum_star_mul_self_eq_zero h_sum_zero s''
  have h_diff_eq :
      modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ α)) s'' =
        (∑ s' : Fin L.mode.ν, pctModeMatrix L p s'' s' * star (pctModeMatrix L p s' s)) -
          if s'' = s then η else 0 := by
    dsimp [modeProj, ξ]
    simp_rw [← Complex.star_def]
    have h_term_diff : ∀ μ : ι,
        L.mode.w s'' p μ * ∑ α : ι, pctMatrix S α μ *
            star ((∑ s' : Fin L.mode.ν, L.dual_w s' p α * pctModeMatrix L p s' s) -
              ∑ β : ι, pctMatrix S β α * star (L.dual_w s p β)) =
          (∑ s' : Fin L.mode.ν, ∑ α : ι,
            L.mode.w s'' p μ * pctMatrix S α μ * star (L.dual_w s' p α) *
              star (pctModeMatrix L p s' s)) -
          ∑ β : ι, ∑ α : ι,
            L.mode.w s'' p μ * (star (pctMatrix S β α) * pctMatrix S α μ) * L.dual_w s p β := by
      intro μ
      rw [Finset.mul_sum]
      have h_alpha : ∀ α : ι,
          L.mode.w s'' p μ * (pctMatrix S α μ *
              star ((∑ s' : Fin L.mode.ν, L.dual_w s' p α * pctModeMatrix L p s' s) -
                ∑ β : ι, pctMatrix S β α * star (L.dual_w s p β))) =
            (∑ s' : Fin L.mode.ν,
              L.mode.w s'' p μ * pctMatrix S α μ * star (L.dual_w s' p α) *
                star (pctModeMatrix L p s' s)) -
            ∑ β : ι,
              L.mode.w s'' p μ * (star (pctMatrix S β α) * pctMatrix S α μ) * L.dual_w s p β := by
        intro α
        rw [star_sub, mul_sub, mul_sub, star_sum, star_sum, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_
        · rw [star_mul']
          ring
        · rw [star_mul', star_star]
          ring
      rw [Finset.sum_congr rfl fun α _ => h_alpha α, Finset.sum_sub_distrib]
      congr 1 <;> exact Finset.sum_comm
    rw [Finset.sum_congr rfl fun μ _ => h_term_diff μ, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      dsimp [pctModeMatrix]
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_mul]
    · have h_self : ∀ β μ : ι,
          (∑ α : ι, star (pctMatrix S β α) * pctMatrix S α μ) =
            if β = μ then η else 0 := by
        intro β μ
        have hmat := pctMatrix_conj_mul_self S hε
        have hent := congrArg (fun M : Matrix ι ι ℂ => M β μ) hmat
        dsimp only [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent
        rw [hent, Matrix.one_apply]
        split_ifs <;> simp
      rw [Finset.sum_comm]
      have h_fact : ∀ β μ : ι,
          (∑ α : ι, L.mode.w s'' p μ * (star (pctMatrix S β α) * pctMatrix S α μ) *
            L.dual_w s p β) =
          L.mode.w s'' p μ * (if β = μ then η else 0) * L.dual_w s p β := by
        intro β μ
        have hmul :
            (∑ α : ι, L.mode.w s'' p μ * (star (pctMatrix S β α) * pctMatrix S α μ) *
              L.dual_w s p β) =
            L.mode.w s'' p μ * (∑ α : ι, star (pctMatrix S β α) * pctMatrix S α μ) *
              L.dual_w s p β := by
          rw [Finset.mul_sum, Finset.sum_mul]
        rw [hmul, h_self β μ]
      rw [Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun μ _ => h_fact β μ]
      have h_collapse :
          (∑ β : ι, ∑ μ : ι,
            L.mode.w s'' p μ * (if β = μ then η else 0) * L.dual_w s p β) =
          η * ∑ μ : ι, L.mode.w s'' p μ * L.dual_w s p μ := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_eq_single μ]
        · rw [if_pos rfl]
          ring
        · intro β _ hne
          rw [if_neg hne]
          simp
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ μ))
      rw [h_collapse, L.dual_orthonormal s'' s p]
      split_ifs <;> simp
  rw [h_diff_eq] at h_pt
  exact sub_eq_zero.mp h_pt

lemma pctModeMatrix_mul_conj_wigner
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (A : SL2C) (p : Fin 3 → ℝ)
    (s'' s : Fin L.mode.ν) :
    (∑ s' : Fin L.mode.ν,
        pctModeMatrix L p s'' s' * star (wignerModeMatrix L A p s' s)) =
      ∑ s' : Fin L.mode.ν,
        wignerModeMatrix L A p s'' s' * pctModeMatrix L (massShellBoost m A⁻¹ p) s' s := by
  let p' := massShellBoost m A⁻¹ p
  let ξ₁ : ι → ℂ := fun α =>
    (∑ s' : Fin L.mode.ν, L.dual_w s' p α * wignerModeMatrix L A p s' s) -
      ∑ β : ι, R.rep A⁻¹ β α * L.dual_w s p' β
  have h1_zero : ∀ s' : Fin L.mode.ν, modeProj L.mode p ξ₁ s' = 0 := by
    intro s'
    dsimp [modeProj, ξ₁]
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have ha :
        (∑ x : Fin L.mode.ν, ∑ α : ι,
          L.mode.w s' p α * (L.dual_w x p α * wignerModeMatrix L A p x s)) =
        wignerModeMatrix L A p s' s := by
      have hterm : ∀ x : Fin L.mode.ν,
          (∑ α : ι, L.mode.w s' p α * (L.dual_w x p α * wignerModeMatrix L A p x s)) =
            (if s' = x then 1 else 0) * wignerModeMatrix L A p x s := by
        intro x
        have hmul :
            (∑ α : ι, L.mode.w s' p α * (L.dual_w x p α * wignerModeMatrix L A p x s)) =
              (∑ α : ι, L.mode.w s' p α * L.dual_w x p α) * wignerModeMatrix L A p x s := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => by ring
        rw [hmul, L.dual_orthonormal s' x p]
      simp_rw [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hb :
        (∑ α : ι, ∑ β : ι, L.mode.w s' p α * (R.rep A⁻¹ β α * L.dual_w s p' β)) =
        wignerModeMatrix L A p s' s := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring
    rw [ha, hb, sub_self]
  have h1_sum :
      (∑ s₀ : Fin L.mode.ν,
        star (modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ₁ α)) s₀) *
          modeProj L.mode p (fun μ => ∑ α : ι, pctMatrix S α μ * star (ξ₁ α)) s₀) = 0 := by
    rw [sum_star_mul_modeProj_pct L hε hC_pct p ξ₁ ξ₁]
    simp [h1_zero]
  have h1_pt := eq_zero_of_sum_star_mul_self_eq_zero h1_sum s''
  have h1_eq :
      (∑ s' : Fin L.mode.ν,
        pctModeMatrix L p s'' s' * star (wignerModeMatrix L A p s' s)) =
      modeProj L.mode p
        (fun μ => ∑ α : ι, ∑ β : ι,
          pctMatrix S α μ * star (R.rep A⁻¹ β α) * star (L.dual_w s p' β)) s'' := by
    apply sub_eq_zero.mp
    rw [← h1_pt]
    dsimp [modeProj, ξ₁]
    simp_rw [← Complex.star_def]
    have h_term_diff : ∀ μ : ι,
        L.mode.w s'' p μ * ∑ α : ι, pctMatrix S α μ *
            star ((∑ s' : Fin L.mode.ν, L.dual_w s' p α * wignerModeMatrix L A p s' s) -
              ∑ β : ι, R.rep A⁻¹ β α * L.dual_w s p' β) =
          (∑ s' : Fin L.mode.ν, ∑ α : ι,
            L.mode.w s'' p μ * pctMatrix S α μ * star (L.dual_w s' p α) *
              star (wignerModeMatrix L A p s' s)) -
          ∑ α : ι, ∑ β : ι,
            L.mode.w s'' p μ *
              (pctMatrix S α μ * star (R.rep A⁻¹ β α) * star (L.dual_w s p' β)) := by
      intro μ
      rw [Finset.mul_sum]
      have h_alpha : ∀ α : ι,
          L.mode.w s'' p μ * (pctMatrix S α μ *
              star ((∑ s' : Fin L.mode.ν, L.dual_w s' p α * wignerModeMatrix L A p s' s) -
                ∑ β : ι, R.rep A⁻¹ β α * L.dual_w s p' β)) =
            (∑ s' : Fin L.mode.ν,
              L.mode.w s'' p μ * pctMatrix S α μ * star (L.dual_w s' p α) *
                star (wignerModeMatrix L A p s' s)) -
            ∑ β : ι,
              L.mode.w s'' p μ *
                (pctMatrix S α μ * star (R.rep A⁻¹ β α) * star (L.dual_w s p' β)) := by
        intro α
        rw [star_sub, mul_sub, mul_sub, star_sum, star_sum, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum, Finset.mul_sum]
        congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_
        · rw [star_mul']
          ring
        · rw [star_mul']
          ring
      rw [Finset.sum_congr rfl fun α _ => h_alpha α, Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl fun μ _ => h_term_diff μ, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      dsimp [pctModeMatrix]
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_mul]
    · refine Finset.sum_congr rfl fun μ _ => ?_
      simp_rw [Finset.mul_sum]
  have h_comm :
      modeProj L.mode p
        (fun μ => ∑ α : ι, ∑ β : ι,
          pctMatrix S α μ * star (R.rep A⁻¹ β α) * star (L.dual_w s p' β)) s'' =
      modeProj L.mode p
        (fun μ => ∑ α : ι, R.rep A⁻¹ α μ *
          ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β)) s'' := by
    dsimp [modeProj]
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    have h_entry : ∀ β : ι,
        (∑ α : ι, star (R.rep A⁻¹ β α) * pctMatrix S α μ) =
          ∑ α : ι, pctMatrix S β α * R.rep A⁻¹ α μ := by
      intro β
      have hent := congrArg (fun M : Matrix ι ι ℂ => M β μ) (pctMatrix_comm_rep S A⁻¹)
      dsimp only [Matrix.mul_apply, Matrix.map_apply] at hent
      exact hent
    calc (∑ α : ι, ∑ β : ι, pctMatrix S α μ * star (R.rep A⁻¹ β α) * star (L.dual_w s p' β))
        = ∑ β : ι, (∑ α : ι, star (R.rep A⁻¹ β α) * pctMatrix S α μ) * star (L.dual_w s p' β) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => by ring
      _ = ∑ β : ι, (∑ α : ι, pctMatrix S β α * R.rep A⁻¹ α μ) * star (L.dual_w s p' β) := by
          refine Finset.sum_congr rfl fun β _ => by rw [h_entry β]
      _ = ∑ α : ι, R.rep A⁻¹ α μ * ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β) := by
          have h1 :
              (∑ β : ι, (∑ α : ι, pctMatrix S β α * R.rep A⁻¹ α μ) * star (L.dual_w s p' β)) =
              ∑ β : ι, ∑ α : ι, R.rep A⁻¹ α μ * (pctMatrix S β α * star (L.dual_w s p' β)) := by
            refine Finset.sum_congr rfl fun β _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun α _ => by ring
          rw [h1, Finset.sum_comm]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [← Finset.mul_sum]
  let ξ₂ : ι → ℂ := fun α =>
    (∑ s' : Fin L.mode.ν, L.dual_w s' p' α * pctModeMatrix L p' s' s) -
      ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β)
  have h2_zero : ∀ s' : Fin L.mode.ν, modeProj L.mode p' ξ₂ s' = 0 := by
    intro s'
    dsimp [modeProj, ξ₂]
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    have ha :
        (∑ x : Fin L.mode.ν, ∑ α : ι,
          L.mode.w s' p' α * (L.dual_w x p' α * pctModeMatrix L p' x s)) =
        pctModeMatrix L p' s' s := by
      have hterm : ∀ x : Fin L.mode.ν,
          (∑ α : ι, L.mode.w s' p' α * (L.dual_w x p' α * pctModeMatrix L p' x s)) =
            (if s' = x then 1 else 0) * pctModeMatrix L p' x s := by
        intro x
        have hmul :
            (∑ α : ι, L.mode.w s' p' α * (L.dual_w x p' α * pctModeMatrix L p' x s)) =
              (∑ α : ι, L.mode.w s' p' α * L.dual_w x p' α) * pctModeMatrix L p' x s := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => by ring
        rw [hmul, L.dual_orthonormal s' x p']
      simp_rw [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hb :
        (∑ α : ι, ∑ β : ι, L.mode.w s' p' α * (pctMatrix S β α * star (L.dual_w s p' β))) =
        pctModeMatrix L p' s' s := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => by ring
    rw [ha, ← Complex.star_def, hb, sub_self]
  have h2_sum :
      (∑ s₀ : Fin L.mode.ν,
        star (modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ₂ α) s₀) *
          modeProj L.mode p (fun γ => ∑ α : ι, R.rep A⁻¹ α γ * ξ₂ α) s₀) = 0 := by
    have h_p' : (∑ s₀ : Fin L.mode.ν,
        star (modeProj L.mode p' ξ₂ s₀) * modeProj L.mode p' ξ₂ s₀) = 0 := by
      simp [h2_zero]
    rw [sum_star_mul_modeProj_rep L A p ξ₂ ξ₂, h_p', mul_zero]
  have h2_pt := eq_zero_of_sum_star_mul_self_eq_zero h2_sum s''
  have h2_eq :
      (∑ s' : Fin L.mode.ν, wignerModeMatrix L A p s'' s' * pctModeMatrix L p' s' s) =
      modeProj L.mode p
        (fun μ => ∑ α : ι, R.rep A⁻¹ α μ *
          ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β)) s'' := by
    apply sub_eq_zero.mp
    rw [← h2_pt]
    dsimp [modeProj, ξ₂]
    simp_rw [← Complex.star_def]
    have h_term_diff : ∀ μ : ι,
        L.mode.w s'' p μ * ∑ α : ι, R.rep A⁻¹ α μ *
            ((∑ s' : Fin L.mode.ν, L.dual_w s' p' α * pctModeMatrix L p' s' s) -
              ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β)) =
          (∑ s' : Fin L.mode.ν, ∑ α : ι,
            L.mode.w s'' p μ * R.rep A⁻¹ α μ * L.dual_w s' p' α * pctModeMatrix L p' s' s) -
          ∑ α : ι, L.mode.w s'' p μ * (R.rep A⁻¹ α μ *
            ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β)) := by
      intro μ
      rw [Finset.mul_sum]
      have h_alpha : ∀ α : ι,
          L.mode.w s'' p μ * (R.rep A⁻¹ α μ *
              ((∑ s' : Fin L.mode.ν, L.dual_w s' p' α * pctModeMatrix L p' s' s) -
                ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β))) =
            (∑ s' : Fin L.mode.ν,
              L.mode.w s'' p μ * R.rep A⁻¹ α μ * L.dual_w s' p' α * pctModeMatrix L p' s' s) -
            L.mode.w s'' p μ *
              (R.rep A⁻¹ α μ * ∑ β : ι, pctMatrix S β α * star (L.dual_w s p' β)) := by
        intro α
        rw [mul_sub, mul_sub, Finset.mul_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun _ _ => by ring
      rw [Finset.sum_congr rfl fun α _ => h_alpha α, Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_comm
    rw [Finset.sum_congr rfl fun μ _ => h_term_diff μ, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      dsimp [wignerModeMatrix]
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.sum_mul]
    · refine Finset.sum_congr rfl fun μ _ => ?_
      exact Finset.mul_sum _ _ _
  rw [h1_eq, h_comm, ← h2_eq]

end ModeMatrixAlgebra

section FockWavepacketTransforms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma spatialPart_massShellVec (m : ℝ) (p : Fin 3 → ℝ) :
    spatialPart (massShellVec m p) = p := by
  ext j
  fin_cases j <;> rfl

def lorentzModeWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) : SmoothWavepacket where
  amp p := wignerModeMatrix L A p s' s * f.amp (massShellBoost m A⁻¹ p)
  smooth := (contDiff_wignerModeMatrix L A s' s).mul
    (f.smooth.comp (contDiff_massShellBoost L.hm A⁻¹))
  compactSupport := by
    refine HasCompactSupport.of_support_subset_isCompact
      (f.compactSupport.isCompact.image (contDiff_massShellBoost L.hm A).continuous) ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hf_ne : f.amp (massShellBoost m A⁻¹ p) ≠ 0 := by
      intro h0
      exact hp (by simp [h0])
    refine ⟨massShellBoost m A⁻¹ p, subset_tsupport _ (Function.mem_support.mpr hf_ne), ?_⟩
    exact massShellBoost_comp_inv L.hm A p

@[simp]
lemma lorentzModeWavepacket_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (lorentzModeWavepacket L A s' s f).amp p =
      wignerModeMatrix L A p s' s * f.amp (massShellBoost m A⁻¹ p) := rfl

lemma tsupport_lorentzModeWavepacket_subset
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    tsupport (lorentzModeWavepacket L A s' s f).amp ⊆ massShellBoost m A '' tsupport f.amp := by
  have hK : IsCompact (massShellBoost m A '' tsupport f.amp) :=
    f.compactSupport.isCompact.image (contDiff_massShellBoost L.hm A).continuous
  refine closure_minimal ?_ hK.isClosed
  intro p hp
  rw [Function.mem_support, lorentzModeWavepacket_apply] at hp
  have hf_ne : f.amp (massShellBoost m A⁻¹ p) ≠ 0 := fun h0 => hp (by simp [h0])
  exact ⟨massShellBoost m A⁻¹ p, subset_tsupport _ (Function.mem_support.mpr hf_ne),
    massShellBoost_comp_inv L.hm A p⟩

lemma velocityDisjoint_lorentzModeWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s'₁ s₁ s'₂ s₂ : Fin L.mode.ν) {f₁ f₂ : SmoothWavepacket}
    (hf : VelocityDisjoint m f₁ f₂) :
    VelocityDisjoint m (lorentzModeWavepacket L A s'₁ s₁ f₁)
      (lorentzModeWavepacket L A s'₂ s₂ f₂) := by
  rw [velocityDisjoint_iff_tsupport_disjoint L.hm] at hf ⊢
  refine (Set.disjoint_image_of_injective ?_ hf).mono
    (tsupport_lorentzModeWavepacket_subset L A s'₁ s₁ f₁)
    (tsupport_lorentzModeWavepacket_subset L A s'₂ s₂ f₂)
  intro p q hpq
  exact (massShellBoost_injOn L.hm A) trivial trivial hpq

lemma lorentzModeWavepacket_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    lorentzModeWavepacket L 1 s' s f = if s' = s then f else zeroWavepacket := by
  apply SmoothWavepacket.ext
  funext p
  rw [lorentzModeWavepacket_apply, wignerModeMatrix_one, inv_one, massShellBoost_one]
  split_ifs <;> simp

lemma lorentzModeWavepacket_neg_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    lorentzModeWavepacket L (-1) s' s f =
      if s' = s then smulWavepacket η f else zeroWavepacket := by
  have hinv : (-1 : SL2C)⁻¹ = -1 := by
    refine inv_eq_of_mul_eq_one_right ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  apply SmoothWavepacket.ext
  funext p
  rw [lorentzModeWavepacket_apply, wignerModeMatrix_neg_one L hε, hinv, massShellBoost_neg_one]
  split_ifs <;> simp

lemma finsetSum_lorentzModeWavepacket_comp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A B : SL2C)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    finsetSumWavepacket Finset.univ
        (fun b => lorentzModeWavepacket L A s' b (lorentzModeWavepacket L B b s f)) =
      lorentzModeWavepacket L (A * B) s' s f := by
  apply SmoothWavepacket.ext
  funext p
  simp only [finsetSumWavepacket_apply, lorentzModeWavepacket_apply]
  have h_eq :
      (∑ b : Fin L.mode.ν,
        wignerModeMatrix L A p s' b *
          (wignerModeMatrix L B (massShellBoost m A⁻¹ p) b s *
            f.amp (massShellBoost m B⁻¹ (massShellBoost m A⁻¹ p)))) =
      (∑ b : Fin L.mode.ν,
        wignerModeMatrix L A p s' b * wignerModeMatrix L B (massShellBoost m A⁻¹ p) b s) *
        f.amp (massShellBoost m (A * B)⁻¹ p) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [_root_.mul_inv_rev, massShellBoost_mul L.hm]
    ring
  rw [h_eq, wignerModeMatrix_mul L A B p s' s]

lemma lorentzModeWavepacket_translateWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (a : Fin 4 → ℝ)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    lorentzModeWavepacket L A s' s (translateWavepacket m L.hm a f) =
      translateWavepacket m L.hm ((lorentzOfSL2C A).mulVec a)
        (lorentzModeWavepacket L A s' s f) := by
  apply SmoothWavepacket.ext
  funext p
  simp only [lorentzModeWavepacket_apply, translateWavepacket_apply]
  have h_mink :
      minkowskiInner (massShellVec m (massShellBoost m A⁻¹ p)) a =
        minkowskiInner (massShellVec m p) ((lorentzOfSL2C A).mulVec a) := by
    rw [← lorentzOfSL2C_mulVec_massShellVec L.hm A⁻¹ p, ← minkowskiInner_lorentz_pair A]
  have hph :
      fockMinkowskiPhase a (massShellVec m (massShellBoost m A⁻¹ p)) =
        fockMinkowskiPhase ((lorentzOfSL2C A).mulVec a) (massShellVec m p) := by
    dsimp [fockMinkowskiPhase]
    rw [h_mink]
  rw [hph]
  ring

def pctModeWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) : SmoothWavepacket where
  amp p := pctModeMatrix L p s' s * star (f.amp p)
  smooth := (contDiff_pctModeMatrix L s' s).mul (Complex.conjCLE.contDiff.comp f.smooth)
  compactSupport :=
    (HasCompactSupport.comp_left f.compactSupport (star_zero ℂ)).mul_left

@[simp]
lemma pctModeWavepacket_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (pctModeWavepacket L s' s f).amp p = pctModeMatrix L p s' s * star (f.amp p) := rfl

lemma tsupport_pctModeWavepacket_subset
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    tsupport (pctModeWavepacket L s' s f).amp ⊆ tsupport f.amp := by
  refine closure_mono fun p hp => ?_
  rw [Function.mem_support, pctModeWavepacket_apply] at hp
  rw [Function.mem_support]
  intro h0
  exact hp (by simp [h0])

lemma velocityDisjoint_pctModeWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (s'₁ s₁ s'₂ s₂ : Fin L.mode.ν) {f₁ f₂ : SmoothWavepacket}
    (hf : VelocityDisjoint m f₁ f₂) :
    VelocityDisjoint m (pctModeWavepacket L s'₁ s₁ f₁)
      (pctModeWavepacket L s'₂ s₂ f₂) := by
  rw [velocityDisjoint_iff_tsupport_disjoint L.hm] at hf ⊢
  exact hf.mono (tsupport_pctModeWavepacket_subset L s'₁ s₁ f₁)
    (tsupport_pctModeWavepacket_subset L s'₂ s₂ f₂)

lemma finsetSum_pctModeWavepacket_comp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell)
    (s'' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    finsetSumWavepacket Finset.univ
        (fun b => pctModeWavepacket L s'' b (pctModeWavepacket L b s f)) =
      if s'' = s then smulWavepacket η f else zeroWavepacket := by
  apply SmoothWavepacket.ext
  funext p
  simp only [finsetSumWavepacket_apply, pctModeWavepacket_apply]
  trans (∑ b : Fin L.mode.ν, pctModeMatrix L p s'' b * star (pctModeMatrix L p b s)) * f.amp p
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [star_mul', star_star]
    ring
  · rw [pctModeMatrix_mul_conj L hε hC_pct p s'' s]
    split_ifs <;> simp

lemma pctModeWavepacket_translateWavepacket
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (a : Fin 4 → ℝ)
    (s' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    pctModeWavepacket L s' s (translateWavepacket m L.hm a f) =
      translateWavepacket m L.hm (-a) (pctModeWavepacket L s' s f) := by
  apply SmoothWavepacket.ext
  funext p
  simp only [pctModeWavepacket_apply, translateWavepacket_apply, star_mul']
  have hph : star (fockMinkowskiPhase a (massShellVec m p)) =
      fockMinkowskiPhase (-a) (massShellVec m p) := by
    unfold fockMinkowskiPhase
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    have h_mink :
        minkowskiInner (massShellVec m p) (-a) = -minkowskiInner (massShellVec m p) a := by
      simp only [minkowskiInner_explicit, Pi.neg_apply]
      ring
    rw [h_mink, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  rw [hph]
  ring

lemma finsetSum_pctModeWavepacket_lorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (A : SL2C)
    (s'' s : Fin L.mode.ν) (f : SmoothWavepacket) :
    finsetSumWavepacket Finset.univ
        (fun b => pctModeWavepacket L s'' b (lorentzModeWavepacket L A b s f)) =
      finsetSumWavepacket Finset.univ
        (fun b => lorentzModeWavepacket L A s'' b (pctModeWavepacket L b s f)) := by
  apply SmoothWavepacket.ext
  funext p
  simp only [finsetSumWavepacket_apply, pctModeWavepacket_apply, lorentzModeWavepacket_apply]
  calc
    ∑ b : Fin L.mode.ν,
        pctModeMatrix L p s'' b *
          star (wignerModeMatrix L A p b s * f.amp (massShellBoost m A⁻¹ p))
      = (∑ b : Fin L.mode.ν, pctModeMatrix L p s'' b * star (wignerModeMatrix L A p b s)) *
          star (f.amp (massShellBoost m A⁻¹ p)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [star_mul']
          ring
    _ = (∑ b : Fin L.mode.ν,
          wignerModeMatrix L A p s'' b * pctModeMatrix L (massShellBoost m A⁻¹ p) b s) *
          star (f.amp (massShellBoost m A⁻¹ p)) := by
          rw [pctModeMatrix_mul_conj_wigner L hε hC_pct A p s'' s]
    _ = ∑ b : Fin L.mode.ν,
          wignerModeMatrix L A p s'' b *
            (pctModeMatrix L (massShellBoost m A⁻¹ p) b s *
              star (f.amp (massShellBoost m A⁻¹ p))) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => by ring

lemma inner_sum_fockOneParticleVec_lorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s₁ s₂ : Fin L.mode.ν) (f₁ f₂ : SmoothWavepacket) :
    ⟪∑ s' : Fin L.mode.ν, fockOneParticleVec L.mode.ν s' (lorentzModeWavepacket L A s' s₁ f₁),
      ∑ s' : Fin L.mode.ν, fockOneParticleVec L.mode.ν s' (lorentzModeWavepacket L A s' s₂ f₂)⟫_ℂ =
      ⟪fockOneParticleVec L.mode.ν s₁ f₁, fockOneParticleVec L.mode.ν s₂ f₂⟫_ℂ := by
  rw [sum_inner]
  simp_rw [inner_sum, inner_fockOneParticleVec_eq]
  have h_coll :
      (∑ s' : Fin L.mode.ν, ∑ s'' : Fin L.mode.ν,
        if s' = s'' then
          ∫ p : Fin 3 → ℝ,
            star ((lorentzModeWavepacket L A s' s₁ f₁).amp p) *
              (lorentzModeWavepacket L A s'' s₂ f₂).amp p
        else 0) =
      ∑ s' : Fin L.mode.ν,
        ∫ p : Fin 3 → ℝ,
          star ((lorentzModeWavepacket L A s' s₁ f₁).amp p) *
            (lorentzModeWavepacket L A s' s₂ f₂).amp p := by
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [Finset.sum_eq_single s']
    · simp
    · intro s'' _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s'))
  have hint : ∀ s' : Fin L.mode.ν,
      Integrable (fun p : Fin 3 → ℝ =>
        star ((lorentzModeWavepacket L A s' s₁ f₁).amp p) *
          (lorentzModeWavepacket L A s' s₂ f₂).amp p) volume := fun s' =>
    ((lorentzModeWavepacket L A s' s₁ f₁).smooth.continuous.star.mul
      (lorentzModeWavepacket L A s' s₂ f₂).smooth.continuous).integrable_of_hasCompactSupport
      (lorentzModeWavepacket L A s' s₂ f₂).compactSupport.mul_left
  rw [h_coll, ← integral_finsetSum Finset.univ fun s' _ => hint s']
  have h_pt :
      (fun p : Fin 3 → ℝ =>
        ∑ s' : Fin L.mode.ν,
          star ((lorentzModeWavepacket L A s' s₁ f₁).amp p) *
            (lorentzModeWavepacket L A s' s₂ f₂).amp p) =
      fun p : Fin 3 → ℝ =>
        (if s₁ = s₂ then
          ((massShellEnergy m (massShellBoost m A⁻¹ p) / massShellEnergy m p : ℝ) : ℂ) *
            (star (f₁.amp (massShellBoost m A⁻¹ p)) * f₂.amp (massShellBoost m A⁻¹ p))
        else 0) := by
    ext p
    have h_fact :
        (∑ s' : Fin L.mode.ν,
          star (wignerModeMatrix L A p s' s₁ * f₁.amp (massShellBoost m A⁻¹ p)) *
            (wignerModeMatrix L A p s' s₂ * f₂.amp (massShellBoost m A⁻¹ p))) =
        (∑ s' : Fin L.mode.ν,
          star (wignerModeMatrix L A p s' s₁) * wignerModeMatrix L A p s' s₂) *
          (star (f₁.amp (massShellBoost m A⁻¹ p)) * f₂.amp (massShellBoost m A⁻¹ p)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [star_mul']
      ring
    dsimp only [lorentzModeWavepacket_apply]
    rw [h_fact, sum_star_mul_wignerModeMatrix L A p s₁ s₂]
    split_ifs <;> ring
  rw [h_pt]
  by_cases hs : s₁ = s₂
  · subst hs
    simp only [↓reduceIte]
    let F : (Fin 4 → ℝ) → ℂ := fun q =>
      ((2 * q 0 : ℝ) : ℂ) * (star (f₁.amp (spatialPart q)) * f₂.amp (spatialPart q))
    have h_jac := integral_massShell_lorentzOfSL2C_eq L.hm A⁻¹ F
    have hL_eq :
        (fun p : Fin 3 → ℝ =>
          ((massShellEnergy m (massShellBoost m A⁻¹ p) / massShellEnergy m p : ℝ) : ℂ) *
            (star (f₁.amp (massShellBoost m A⁻¹ p)) * f₂.amp (massShellBoost m A⁻¹ p))) =
        fun p : Fin 3 → ℝ =>
          ((2 * massShellEnergy m p)⁻¹ : ℂ) *
            F ((lorentzOfSL2C A⁻¹).mulVec (massShellVec m p)) := by
      ext p
      dsimp [F]
      rw [lorentzOfSL2C_mulVec_massShellVec L.hm A⁻¹ p, spatialPart_massShellVec]
      have h0 : massShellVec m (massShellBoost m A⁻¹ p) 0 =
          massShellEnergy m (massShellBoost m A⁻¹ p) := rfl
      have hω1 : (massShellEnergy m p : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (massShellEnergy_pos L.hm p).ne'
      rw [h0]
      push_cast
      field_simp [hω1]
    have hR_eq :
        (fun p : Fin 3 → ℝ => ((2 * massShellEnergy m p)⁻¹ : ℂ) * F (massShellVec m p)) =
        fun p : Fin 3 → ℝ => star (f₁.amp p) * f₂.amp p := by
      ext p
      dsimp [F]
      rw [spatialPart_massShellVec]
      have h0 : massShellVec m p 0 = massShellEnergy m p := rfl
      have hω1 : (massShellEnergy m p : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (massShellEnergy_pos L.hm p).ne'
      rw [h0]
      push_cast
      field_simp [hω1]
    rw [hL_eq, h_jac, hR_eq]
  · simp_rw [if_neg hs]
    simp only [integral_zero]

lemma inner_sum_fockOneParticleVec_pct
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell)
    (s₁ s₂ : Fin L.mode.ν) (f₁ f₂ : SmoothWavepacket) :
    ⟪∑ s' : Fin L.mode.ν, fockOneParticleVec L.mode.ν s' (pctModeWavepacket L s' s₁ f₁),
      ∑ s' : Fin L.mode.ν, fockOneParticleVec L.mode.ν s' (pctModeWavepacket L s' s₂ f₂)⟫_ℂ =
      star ⟪fockOneParticleVec L.mode.ν s₁ f₁, fockOneParticleVec L.mode.ν s₂ f₂⟫_ℂ := by
  rw [sum_inner]
  simp_rw [inner_sum, inner_fockOneParticleVec_eq]
  have h_coll :
      (∑ s' : Fin L.mode.ν, ∑ s'' : Fin L.mode.ν,
        if s' = s'' then
          ∫ p : Fin 3 → ℝ,
            star ((pctModeWavepacket L s' s₁ f₁).amp p) *
              (pctModeWavepacket L s'' s₂ f₂).amp p
        else 0) =
      ∑ s' : Fin L.mode.ν,
        ∫ p : Fin 3 → ℝ,
          star ((pctModeWavepacket L s' s₁ f₁).amp p) *
            (pctModeWavepacket L s' s₂ f₂).amp p := by
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [Finset.sum_eq_single s']
    · simp
    · intro s'' _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s'))
  have hint : ∀ s' : Fin L.mode.ν,
      Integrable (fun p : Fin 3 → ℝ =>
        star ((pctModeWavepacket L s' s₁ f₁).amp p) *
          (pctModeWavepacket L s' s₂ f₂).amp p) volume := fun s' =>
    ((pctModeWavepacket L s' s₁ f₁).smooth.continuous.star.mul
      (pctModeWavepacket L s' s₂ f₂).smooth.continuous).integrable_of_hasCompactSupport
      (pctModeWavepacket L s' s₂ f₂).compactSupport.mul_left
  rw [h_coll, ← integral_finsetSum Finset.univ fun s' _ => hint s']
  have h_pt :
      (fun p : Fin 3 → ℝ =>
        ∑ s' : Fin L.mode.ν,
          star ((pctModeWavepacket L s' s₁ f₁).amp p) *
            (pctModeWavepacket L s' s₂ f₂).amp p) =
      fun p : Fin 3 → ℝ =>
        (if s₁ = s₂ then star (star (f₁.amp p) * f₂.amp p) else 0) := by
    ext p
    have h_fact :
        (∑ s' : Fin L.mode.ν,
          star (pctModeMatrix L p s' s₁ * star (f₁.amp p)) *
            (pctModeMatrix L p s' s₂ * star (f₂.amp p))) =
        (∑ s' : Fin L.mode.ν, star (pctModeMatrix L p s' s₁) * pctModeMatrix L p s' s₂) *
          star (star (f₁.amp p) * f₂.amp p) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [star_mul', star_mul', star_star]
      ring
    dsimp only [pctModeWavepacket_apply]
    rw [h_fact, sum_star_mul_pctModeMatrix L hε hC_pct p s₁ s₂]
    split_ifs <;> ring
  rw [h_pt]
  by_cases hs : s₁ = s₂
  · subst hs
    simp only [↓reduceIte]
    rw [Complex.star_def, ← integral_conj]
  · simp_rw [if_neg hs]
    simp only [integral_zero, star_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma symmFockMultiParticleVec_eq_zero_of_zero_slot
    (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1) (r : ℕ)
    (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) {i₀ : Fin r}
    (hf0 : f i₀ = zeroWavepacket) :
    symmFockMultiParticleVec ν η hη r s f = 0 := by
  apply Subtype.ext
  rw [coe_symmFockMultiParticleVec, Submodule.coe_zero]
  have h_zero : symmSector ν r η (fockProdAmp ν r s f) = 0 := by
    ext ⟨k, s'⟩
    unfold symmSector
    have hsum :
        (∑ π : Equiv.Perm (Fin r),
          η ^ permInversions π * fockProdAmp ν r s f (fockSectorPermEquiv ν r π (k, s'))) = 0 := by
      refine Finset.sum_eq_zero fun π _ => ?_
      have hamp : fockProdAmp ν r s f (fockSectorPermEquiv ν r π (k, s')) = 0 := by
        dsimp [fockProdAmp, fockSectorPermEquiv]
        split_ifs
        · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
          rw [hf0]
          rfl
        · rfl
      rw [hamp, mul_zero]
    rw [hsum, mul_zero]
    rfl
  exact (liftSectorToFock_congr _ _ measurable_const MemLp.zero
    (fun x => congrFun h_zero x)).trans (liftSectorToFock_zero ν r)

omit [Fintype ι] [DecidableEq ι] in
lemma symmFockMultiParticleVec_smul_all
    (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1) (r : ℕ)
    (s : Fin r → Fin ν) (c : ℂ) (f : Fin r → SmoothWavepacket) :
    symmFockMultiParticleVec ν η hη r s (fun i => smulWavepacket c (f i)) =
      (c ^ r) • symmFockMultiParticleVec ν η hη r s f := by
  apply Subtype.ext
  rw [coe_symmFockMultiParticleVec, Submodule.coe_smul_of_tower, coe_symmFockMultiParticleVec]
  have h_fn :
      symmSector ν r η (fockProdAmp ν r s (fun i => smulWavepacket c (f i))) =
        c ^ r • symmSector ν r η (fockProdAmp ν r s f) := by
    ext x
    unfold symmSector
    simp only [Pi.smul_apply, smul_eq_mul]
    have h_term : ∀ π : Equiv.Perm (Fin r),
        fockProdAmp ν r s (fun i => smulWavepacket c (f i)) (fockSectorPermEquiv ν r π x) =
          c ^ r * fockProdAmp ν r s f (fockSectorPermEquiv ν r π x) := by
      intro π
      dsimp [fockProdAmp, fockSectorPermEquiv]
      split_ifs
      · simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
      · simp
    simp_rw [h_term]
    have h_eq :
        (∑ π : Equiv.Perm (Fin r),
          c ^ r * (η ^ permInversions π * fockProdAmp ν r s f (fockSectorPermEquiv ν r π x))) =
        c ^ r * ∑ π : Equiv.Perm (Fin r),
          η ^ permInversions π * fockProdAmp ν r s f (fockSectorPermEquiv ν r π x) :=
      (Finset.mul_sum _ _ _).symm
    have h_in :
        (∑ π : Equiv.Perm (Fin r),
          η ^ permInversions π *
            (c ^ r * fockProdAmp ν r s f (fockSectorPermEquiv ν r π x))) =
        ∑ π : Equiv.Perm (Fin r),
          c ^ r *
            (η ^ permInversions π * fockProdAmp ν r s f (fockSectorPermEquiv ν r π x)) :=
      Finset.sum_congr rfl fun π _ => by ring
    rw [h_in, h_eq]
    ring
  rw [← liftSectorToFock_smul (c ^ r)
    (measurable_symmSector η (measurable_fockProdAmp ν r s f))
    (memLp_symmSector η (memLp_fockProdAmp ν r s f))]
  exact liftSectorToFock_congr _ _ _ _ fun x => congrFun h_fn x

omit [Fintype ι] [DecidableEq ι] in
lemma symmFockMultiParticleVec_finsetSum_pi {κ : Type*} [Fintype κ]
    (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1) (r : ℕ)
    (s : Fin r → Fin ν) (g : Fin r → κ → SmoothWavepacket) :
    (∑ c : Fin r → κ, symmFockMultiParticleVec ν η hη r s (fun i => g i (c i))) =
      symmFockMultiParticleVec ν η hη r s (fun i => finsetSumWavepacket Finset.univ (g i)) := by
  apply Subtype.ext
  rw [Submodule.coe_sum, coe_symmFockMultiParticleVec]
  simp_rw [coe_symmFockMultiParticleVec]
  let G : (Fin r → κ) → FockSectorDom ν r → ℂ := fun c =>
    symmSector ν r η (fockProdAmp ν r s (fun i => g i (c i)))
  let hmG : ∀ c, Measurable (G c) := fun c =>
    measurable_symmSector η (measurable_fockProdAmp ν r s _)
  let hpG : ∀ c, MemLp (G c) 2 (fockSectorMeasure ν r) := fun c =>
    memLp_symmSector η (memLp_fockProdAmp ν r s _)
  have hsum_meas : Measurable (∑ c : Fin r → κ, G c) := by
    have h_eq : (∑ c : Fin r → κ, G c) = fun x => ∑ c : Fin r → κ, G c x := by
      ext x
      simp
    rw [h_eq]
    exact Finset.measurable_fun_sum Finset.univ fun c _ => hmG c
  have hsum_mem : MemLp (∑ c : Fin r → κ, G c) 2 (fockSectorMeasure ν r) :=
    MeasureTheory.memLp_finsetSum' Finset.univ fun c _ => hpG c
  refine Eq.trans
    ((Finset.sum_congr rfl fun c _ => liftSectorToFock_congr _ _ _ _ fun _ => rfl).trans
      (liftSectorToFock_finsetSum ν r Finset.univ G hmG hpG hsum_meas hsum_mem).symm) ?_
  refine liftSectorToFock_congr _ _ _ _ fun x => ?_
  simp only [Finset.sum_apply]
  dsimp only [G]
  unfold symmSector
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  by_cases h : x.2 ∘ π = s
  · have hL :
        (∑ c : Fin r → κ,
          fockProdAmp ν r s (fun i => g i (c i)) (fockSectorPermEquiv ν r π x)) =
        ∑ c : Fin r → κ, ∏ i : Fin r, (g i (c i)).amp (x.1 (π i)) := by
      refine Finset.sum_congr rfl fun c _ => ?_
      simp [fockProdAmp, fockSectorPermEquiv, h]
    have hR :
        fockProdAmp ν r s (fun i => finsetSumWavepacket Finset.univ (g i))
          (fockSectorPermEquiv ν r π x) =
        ∏ i : Fin r, ∑ a : κ, (g i a).amp (x.1 (π i)) := by
      simp [fockProdAmp, fockSectorPermEquiv, h, finsetSumWavepacket_apply]
    rw [hL, hR]
    exact (Fintype.prod_sum fun i c => (g i c).amp (x.1 (π i))).symm
  · simp [fockProdAmp, fockSectorPermEquiv, h]

end FockWavepacketTransforms

section IntrinsicFockPoincareAndPCT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def symmFockTranslateEquiv (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ) :
    SymmFockHilbert ν η ≃ₗᵢ[ℂ] SymmFockHilbert ν η where
  toLinearEquiv := LinearEquiv.ofLinear
    (symmFockMinkowskiTranslate m ν η a).toLinearMap
    (symmFockMinkowskiTranslate m ν η (-a)).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change (symmFockMinkowskiTranslate m ν η a).comp
        (symmFockMinkowskiTranslate m ν η (-a)) x = x
      rw [← symmFockMinkowskiTranslate_add, add_neg_cancel, symmFockMinkowskiTranslate_zero,
        ContinuousLinearMap.id_apply])
    (by
      apply LinearMap.ext
      intro x
      change (symmFockMinkowskiTranslate m ν η (-a)).comp
        (symmFockMinkowskiTranslate m ν η a) x = x
      rw [← symmFockMinkowskiTranslate_add, neg_add_cancel, symmFockMinkowskiTranslate_zero,
        ContinuousLinearMap.id_apply])
  norm_map' x := norm_symmFockMinkowskiTranslate m ν η a x

@[simp]
lemma symmFockTranslateEquiv_apply (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ)
    (x : SymmFockHilbert ν η) :
    symmFockTranslateEquiv m ν η a x = symmFockMinkowskiTranslate m ν η a x := rfl

@[simp]
theorem symmFockTranslateEquiv_zero (m : ℝ) (ν : ℕ) (η : ℂ) :
    symmFockTranslateEquiv m ν η 0 = LinearIsometryEquiv.refl ℂ (SymmFockHilbert ν η) := by
  apply LinearIsometryEquiv.ext
  intro x
  change symmFockMinkowskiTranslate m ν η 0 x = x
  rw [symmFockMinkowskiTranslate_zero]
  rfl

theorem symmFockTranslateEquiv_add (m : ℝ) (ν : ℕ) (η : ℂ) (a b : Fin 4 → ℝ)
    (x : SymmFockHilbert ν η) :
    symmFockTranslateEquiv m ν η (a + b) x =
      symmFockTranslateEquiv m ν η a (symmFockTranslateEquiv m ν η b x) := by
  change symmFockMinkowskiTranslate m ν η (a + b) x =
    symmFockMinkowskiTranslate m ν η a (symmFockMinkowskiTranslate m ν η b x)
  rw [symmFockMinkowskiTranslate_add]
  rfl

@[simp]
lemma symmFockTranslateEquiv_symm (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ) :
    (symmFockTranslateEquiv m ν η a).symm = symmFockTranslateEquiv m ν η (-a) := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

@[simp]
theorem symmFockTranslateEquiv_vacuum (m : ℝ) (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ) :
    symmFockTranslateEquiv m ν η a (symmFockVacuum ν η) = symmFockVacuum ν η := by
  apply Subtype.ext
  rw [symmFockTranslateEquiv_apply, coe_symmFockMinkowskiTranslate, Lp.ext_iff]
  have h1 := fockMinkowskiTranslate_coeFn m ν a (fockVacuum ν)
  have hvac_coe : (fockVacuum ν : FockOmega ν → ℂ) =ᶠ[ae (fockMeasure ν)]
      sectorToOmega ν 0 (fun _ => 1) :=
    liftSectorToFock_coeFn (ν := ν) (r := 0) measurable_const (memLp_const (1 : ℂ))
  filter_upwards [h1, hvac_coe] with z hz hzv
  change (fockMinkowskiTranslate m a (fockVacuum ν) : FockOmega ν → ℂ) z =
    (fockVacuum ν : FockOmega ν → ℂ) z
  rw [hz]
  rcases z with ⟨r, x⟩
  by_cases hr : r = 0
  · subst hr
    have hph : fockMinkowskiPhase a (fockTotalMomentum m ⟨0, x⟩) = 1 := by
      rw [fockTotalMomentum_zero]
      simp [fockMinkowskiPhase, minkowskiInner_explicit]
    rw [hph, one_mul]
  · have hvac0 : (fockVacuum ν : FockOmega ν → ℂ) ⟨r, x⟩ = 0 := by
      rw [hzv, sectorToOmega_sigmaMk_ne ν hr]
    rw [hvac0, mul_zero]

@[simp]
theorem symmFockTranslateEquiv_oneParticleVec {m : ℝ} (hm : 0 < m)
    (ν : ℕ) (η : ℂ) (a : Fin 4 → ℝ) (s : Fin ν) (f : SmoothWavepacket) :
    symmFockTranslateEquiv m ν η a (symmFockOneParticleVec ν η s f) =
      symmFockOneParticleVec ν η s (translateWavepacket m hm a f) := by
  apply Subtype.ext
  rw [symmFockTranslateEquiv_apply, coe_symmFockMinkowskiTranslate, Lp.ext_iff]
  have h1 := fockMinkowskiTranslate_coeFn m ν a (fockOneParticleVec ν s f)
  have h2 := liftSectorToFock_coeFn (measurable_fockOneParticleFun ν s f)
    (memLp_fockOneParticleFun ν s f)
  have h3 := liftSectorToFock_coeFn
    (measurable_fockOneParticleFun ν s (translateWavepacket m hm a f))
    (memLp_fockOneParticleFun ν s (translateWavepacket m hm a f))
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  change (fockMinkowskiTranslate m a (fockOneParticleVec ν s f) : FockOmega ν → ℂ) z =
    (fockOneParticleVec ν s (translateWavepacket m hm a f) : FockOmega ν → ℂ) z
  rw [hz1]
  unfold fockOneParticleVec
  rw [hz2, hz3]
  rcases z with ⟨r, x⟩
  by_cases hr : r = 1
  · subst hr
    simp only [sectorToOmega_sigmaMk_eq, fockOneParticleFun]
    have hmom : fockTotalMomentum m ⟨1, x⟩ = massShellVec m (x.1 0) := by
      simp [fockTotalMomentum]
    rw [hmom]
    split_ifs <;> simp [translateWavepacket_apply]
  · simp [sectorToOmega_sigmaMk_ne ν hr]

theorem symmFockTranslateEquiv_multiParticleVec {m : ℝ} (hm : 0 < m)
    (ν : ℕ) {η : ℂ} (hη : η = 1 ∨ η = -1) (a : Fin 4 → ℝ)
    (r : ℕ) (s : Fin r → Fin ν) (f : Fin r → SmoothWavepacket) :
    symmFockTranslateEquiv m ν η a (symmFockMultiParticleVec ν η hη r s f) =
      symmFockMultiParticleVec ν η hη r s (fun i => translateWavepacket m hm a (f i)) :=
  symmFockMinkowskiTranslate_multiParticleVec hm ν hη a r s f

abbrev MultiParticleConfig (ν : ℕ) : Type :=
  Σ (r : ℕ), (Fin r → Fin ν) × (Fin r → SmoothWavepacket)

lemma dense_range_all_symmFockMultiParticleVec
    (ν : ℕ) {m : ℝ} (hm : 0 < m) {η : ℂ} (hη : η = 1 ∨ η = -1) :
    Dense (Submodule.span ℂ (Set.range (fun cfg : MultiParticleConfig ν =>
      symmFockMultiParticleVec ν η hη cfg.1 cfg.2.1 cfg.2.2)) :
      Set (SymmFockHilbert ν η)) := by
  have h_sub :
      (Set.range (fun cfg : DisjointWavepacketConfig ν m =>
        symmFockMultiParticleVec ν η hη cfg.1 cfg.2.1 cfg.2.2.1)) ⊆
      Set.range (fun cfg : MultiParticleConfig ν =>
        symmFockMultiParticleVec ν η hη cfg.1 cfg.2.1 cfg.2.2) := by
    rintro _ ⟨⟨r, s, f, _⟩, rfl⟩
    exact ⟨⟨r, s, f⟩, rfl⟩
  exact (dense_range_symmFockMultiParticleVec ν hm hη).mono (Submodule.span_mono h_sub)

def finsuppConjGen (α : Type*) : (α →₀ ℂ) →ₗ⋆[ℂ] (α →₀ ℂ) where
  toFun c := c.mapRange (starRingEnd ℂ) (map_zero _)
  map_add' c₁ c₂ := Finsupp.mapRange_add (map_add _) c₁ c₂
  map_smul' r c := by
    ext a
    simp

theorem exists_unique_antilinearCLM_of_inner_eq_of_dense
    {E F α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (x : α → E) (y : α → F)
    (hinner : ∀ a b : α, ⟪y a, y b⟫_ℂ = star ⟪x a, x b⟫_ℂ)
    (hdense : Dense (Submodule.span ℂ (Set.range x) : Set E)) :
    ∃! W : E →SL[starRingEnd ℂ] F, ∀ a : α, W (x a) = y a := by
  let e : (α →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ x
  let f : (α →₀ ℂ) →ₗ⋆[ℂ] F := (Finsupp.linearCombination ℂ y).comp (finsuppConjGen α)
  have hnorm_eq : ∀ c : α →₀ ℂ, ‖f c‖ = ‖e c‖ := by
    intro c
    have h_in : ⟪f c, f c⟫_ℂ = star ⟪e c, e c⟫_ℂ := by
      change ⟪Finsupp.linearCombination ℂ y (c.mapRange (starRingEnd ℂ) (map_zero _)),
          Finsupp.linearCombination ℂ y (c.mapRange (starRingEnd ℂ) (map_zero _))⟫_ℂ =
        star ⟪Finsupp.linearCombination ℂ x c, Finsupp.linearCombination ℂ x c⟫_ℂ
      have hsum_conj :
          (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) c).sum (fun a r => r • y a) =
            c.sum (fun a r => (starRingEnd ℂ r) • y a) := by
        refine Finsupp.sum_mapRange_index ?_
        intro a
        exact zero_smul ℂ (y a)
      rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, hsum_conj]
      simp only [Finsupp.sum, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
        ← Complex.star_def, star_sum, star_mul', star_star]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hinner b a]
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h_in,
      Complex.star_def, RCLike.conj_re]
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
  let W : E →SL[starRingEnd ℂ] F := f.extendOfNorm e
  have hW_eq : ∀ a : α, W (x a) = y a := fun a => by
    have he_a : e (Finsupp.single a (1 : ℂ)) = x a := by
      simp [e, Finsupp.linearCombination_single]
    have hf_a : f (Finsupp.single a (1 : ℂ)) = y a := by
      dsimp [f, finsuppConjGen]
      simp [Finsupp.linearCombination_single]
    rw [← he_a, LinearMap.extendOfNorm_eq h_denseRange ⟨1, h_norm_le⟩, hf_a]
  refine ⟨W, hW_eq, fun W' hW' => ?_⟩
  have hcomp : W'.toLinearMap.comp e = f := by
    apply Finsupp.lhom_ext
    intro a c
    have he_s : e (Finsupp.single a c) = c • x a := by
      simp [e, Finsupp.linearCombination_single]
    have hf_s : f (Finsupp.single a c) = (starRingEnd ℂ c) • y a := by
      simp [f, finsuppConjGen, Finsupp.mapRange_single, Finsupp.linearCombination_single]
    change W' (e (Finsupp.single a c)) = f (Finsupp.single a c)
    rw [he_s, hf_s, map_smulₛₗ, hW' a]
  exact (LinearMap.extendOfNorm_unique h_denseRange 1 h_norm_le W' hcomp).symm

lemma inner_antilinearCLM_of_dense
    {E F α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (W : E →SL[starRingEnd ℂ] F) (x : α → E)
    (hinner : ∀ a b : α, ⟪W (x a), W (x b)⟫_ℂ = star ⟪x a, x b⟫_ℂ)
    (hdense : Dense (Submodule.span ℂ (Set.range x) : Set E)) (u v : E) :
    ⟪W u, W v⟫_ℂ = star ⟪u, v⟫_ℂ := by
  let S : Submodule ℂ E := Submodule.span ℂ (Set.range x)
  have h_span_left : ∀ a : α, ∀ u₀ ∈ S, ⟪W u₀, W (x a)⟫_ℂ = star ⟪u₀, x a⟫_ℂ := by
    intro a u₀ hu₀
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu₀
    · rintro _ ⟨b, rfl⟩
      exact hinner b a
    · simp
    · intro u₁ u₂ _ _ hu₁ hu₂
      rw [map_add, inner_add_left, inner_add_left, star_add, hu₁, hu₂]
    · intro c u₁ _ hu₁
      rw [map_smulₛₗ, inner_smul_left, inner_smul_left, RingHomCompTriple.comp_apply,
        RingHom.id_apply, star_mul', ← Complex.star_def, star_star, hu₁]
  have h_all_left : ∀ a : α, ∀ u₀ : E, ⟪W u₀, W (x a)⟫_ℂ = star ⟪u₀, x a⟫_ℂ := by
    intro a u₀
    have hc1 : Continuous (fun z : E => ⟪W z, W (x a)⟫_ℂ) :=
      Continuous.inner W.continuous continuous_const
    have hc2 : Continuous (fun z : E => star ⟪z, x a⟫_ℂ) :=
      continuous_star.comp (Continuous.inner continuous_id continuous_const)
    exact hdense.induction (h_span_left a) (isClosed_eq hc1 hc2) u₀
  have h_span_right : ∀ v₀ ∈ S, ⟪W u, W v₀⟫_ℂ = star ⟪u, v₀⟫_ℂ := by
    intro v₀ hv₀
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv₀
    · rintro _ ⟨a, rfl⟩
      exact h_all_left a u
    · simp
    · intro v₁ v₂ _ _ hv₁ hv₂
      rw [map_add, inner_add_right, inner_add_right, star_add, hv₁, hv₂]
    · intro c v₁ _ hv₁
      rw [map_smulₛₗ, inner_smul_right, inner_smul_right, star_mul', ← Complex.star_def, hv₁]
  have hc1 : Continuous (fun z : E => ⟪W u, W z⟫_ℂ) :=
    Continuous.inner continuous_const W.continuous
  have hc2 : Continuous (fun z : E => star ⟪u, z⟫_ℂ) :=
    continuous_star.comp (Continuous.inner continuous_const continuous_id)
  exact hdense.induction h_span_right (isClosed_eq hc1 hc2) v

def symmFockLorentzTarget
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    SymmFockHilbert L.mode.ν η :=
  ∑ s' : Fin r → Fin L.mode.ν,
    symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'
      (fun i => lorentzModeWavepacket L A (s' i) (s i) (f i))

lemma inner_symmFockLorentzTarget_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (r₁ r₂ : ℕ) (s₁ : Fin r₁ → Fin L.mode.ν) (f₁ : Fin r₁ → SmoothWavepacket)
    (s₂ : Fin r₂ → Fin L.mode.ν) (f₂ : Fin r₂ → SmoothWavepacket) :
    ⟪symmFockLorentzTarget L A r₁ s₁ f₁, symmFockLorentzTarget L A r₂ s₂ f₂⟫_ℂ =
      ⟪symmFockMultiParticleVec L.mode.ν η L.mode.hη r₁ s₁ f₁,
        symmFockMultiParticleVec L.mode.ν η L.mode.hη r₂ s₂ f₂⟫_ℂ := by
  by_cases hr : r₁ = r₂
  · subst hr
    unfold symmFockLorentzTarget
    rw [sum_inner, Finset.sum_congr rfl fun s'₁ _ => inner_sum _ _ _]
    simp_rw [inner_symmFockMultiParticleVec_eq]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun s'₁ _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_congr rfl fun s'₁ _ => (Finset.mul_sum _ _ _).symm, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    have h_perm :
        (∑ s'₁ : Fin r₁ → Fin L.mode.ν, ∑ s'₂ : Fin r₁ → Fin L.mode.ν,
          ∏ i : Fin r₁,
            ⟪fockOneParticleVec L.mode.ν (s'₁ i) (lorentzModeWavepacket L A (s'₁ i) (s₁ i) (f₁ i)),
              fockOneParticleVec L.mode.ν (s'₂ (σ.symm i))
                (lorentzModeWavepacket L A (s'₂ (σ.symm i)) (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ) =
        ∑ s'₁ : Fin r₁ → Fin L.mode.ν, ∑ s'₂ : Fin r₁ → Fin L.mode.ν,
          ∏ i : Fin r₁,
            ⟪fockOneParticleVec L.mode.ν (s'₁ i) (lorentzModeWavepacket L A (s'₁ i) (s₁ i) (f₁ i)),
              fockOneParticleVec L.mode.ν (s'₂ i)
                (lorentzModeWavepacket L A (s'₂ i) (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ := by
      refine Finset.sum_congr rfl fun s'₁ _ => ?_
      let τ : (Fin r₁ → Fin L.mode.ν) ≃ (Fin r₁ → Fin L.mode.ν) :=
        { toFun := fun s' => s' ∘ σ
          invFun := fun s' => s' ∘ σ.symm
          left_inv := fun s' => by ext i; simp
          right_inv := fun s' => by ext i; simp }
      rw [← τ.sum_comp]
      refine Finset.sum_congr rfl fun s'₂ _ => ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp [τ]
      simp
    rw [h_perm]
    rw [Finset.sum_congr rfl fun s'₁ _ => (Fintype.prod_sum fun (i : Fin r₁) (b₂ : Fin L.mode.ν) =>
      ⟪fockOneParticleVec L.mode.ν (s'₁ i) (lorentzModeWavepacket L A (s'₁ i) (s₁ i) (f₁ i)),
        fockOneParticleVec L.mode.ν b₂
          (lorentzModeWavepacket L A b₂ (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ).symm]
    rw [(Fintype.prod_sum fun (i : Fin r₁) (b₁ : Fin L.mode.ν) =>
      ∑ b₂ : Fin L.mode.ν,
        ⟪fockOneParticleVec L.mode.ν b₁ (lorentzModeWavepacket L A b₁ (s₁ i) (f₁ i)),
          fockOneParticleVec L.mode.ν b₂
            (lorentzModeWavepacket L A b₂ (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ).symm]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp_rw [← inner_sum]
    rw [← sum_inner]
    exact inner_sum_fockOneParticleVec_lorentz L A (s₁ i) (s₂ (σ.symm i)) (f₁ i) (f₂ (σ.symm i))
  · unfold symmFockLorentzTarget
    rw [sum_inner]
    refine Eq.trans (Finset.sum_eq_zero fun s'₁ _ => ?_)
      (inner_symmFockMultiParticleVec_ne L.mode.ν L.mode.hη hr s₁ f₁ s₂ f₂).symm
    rw [inner_sum]
    refine Finset.sum_eq_zero fun s'₂ _ => ?_
    exact inner_symmFockMultiParticleVec_ne L.mode.ν L.mode.hη hr _ _ _ _

def symmFockLorentzIsometry
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) :
    SymmFockHilbert L.mode.ν η →ₗᵢ[ℂ] SymmFockHilbert L.mode.ν η :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockMultiParticleVec L.mode.ν η L.mode.hη cfg.1 cfg.2.1 cfg.2.2)
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockLorentzTarget L A cfg.1 cfg.2.1 cfg.2.2)
    (fun ⟨r₁, s₁, f₁⟩ ⟨r₂, s₂, f₂⟩ => inner_symmFockLorentzTarget_eq L A r₁ r₂ s₁ f₁ s₂ f₂)
    (dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη)).choose

theorem symmFockLorentzIsometry_multiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    symmFockLorentzIsometry L A (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
      ∑ s' : Fin r → Fin L.mode.ν,
        symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'
          (fun i => lorentzModeWavepacket L A (s' i) (s i) (f i)) :=
  (exists_unique_linearIsometry_of_inner_eq_of_dense
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockMultiParticleVec L.mode.ν η L.mode.hη cfg.1 cfg.2.1 cfg.2.2)
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockLorentzTarget L A cfg.1 cfg.2.1 cfg.2.2)
    (fun ⟨r₁, s₁, f₁⟩ ⟨r₂, s₂, f₂⟩ => inner_symmFockLorentzTarget_eq L A r₁ r₂ s₁ f₁ s₂ f₂)
    (dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη)).choose_spec.1 ⟨r, s, f⟩

theorem symmFockLorentzIsometry_ext
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (U₁ U₂ : SymmFockHilbert L.mode.ν η →L[ℂ] SymmFockHilbert L.mode.ν η)
    (h_eq : ∀ (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket),
      U₁ (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
        U₂ (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)) :
    U₁ = U₂ := by
  apply ContinuousLinearMap.ext
  intro x
  have hdense := dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη
  refine hdense.induction ?_ (isClosed_eq U₁.continuous U₂.continuous) x
  intro y hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨⟨r, s, f⟩, rfl⟩
    exact h_eq r s f
  · simp
  · intro u v _ _ hu hv
    rw [map_add, map_add, hu, hv]
  · intro c u _ hu
    rw [map_smul, map_smul, hu]

@[simp]
theorem symmFockLorentzIsometry_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) :
    symmFockLorentzIsometry L A (symmFockVacuum L.mode.ν η) = symmFockVacuum L.mode.ν η := by
  rw [← symmFockMultiParticleVec_zero L.mode.ν L.mode.hη Fin.elim0 Fin.elim0,
    symmFockLorentzIsometry_multiParticleVec]
  rw [Fintype.sum_eq_single Fin.elim0 fun s' hne => False.elim (hne (Subsingleton.elim _ _))]
  exact congrArg (symmFockMultiParticleVec L.mode.ν η L.mode.hη 0 Fin.elim0)
    (Subsingleton.elim _ Fin.elim0)

theorem symmFockLorentzIsometry_oneParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s : Fin L.mode.ν) (f : SmoothWavepacket) :
    symmFockLorentzIsometry L A (symmFockOneParticleVec L.mode.ν η s f) =
      ∑ s' : Fin L.mode.ν,
        symmFockOneParticleVec L.mode.ν η s' (lorentzModeWavepacket L A s' s f) := by
  rw [← symmFockMultiParticleVec_one L.mode.ν L.mode.hη (fun _ => s) (fun _ => f),
    symmFockLorentzIsometry_multiParticleVec]
  rw [← (Equiv.funUnique (Fin 1) (Fin L.mode.ν)).symm.sum_comp]
  refine Finset.sum_congr rfl fun s' _ => ?_
  exact symmFockMultiParticleVec_one L.mode.ν L.mode.hη _ _

theorem symmFockLorentzIsometry_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) :
    symmFockLorentzIsometry L 1 = LinearIsometry.id := by
  have hclm : (symmFockLorentzIsometry L 1).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (SymmFockHilbert L.mode.ν η) := by
    refine symmFockLorentzIsometry_ext L _ _ fun r s f => ?_
    rw [ContinuousLinearMap.id_apply]
    change symmFockLorentzIsometry L 1 (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) = _
    rw [symmFockLorentzIsometry_multiParticleVec]
    rw [Finset.sum_eq_single s]
    · congr 1
      ext i
      rw [lorentzModeWavepacket_one, if_pos rfl]
    · intro s' _ hne
      have hex : ∃ i₀ : Fin r, s' i₀ ≠ s i₀ := by
        by_contra h_all
        push Not at h_all
        exact hne (funext h_all)
      rcases hex with ⟨i₀, hi₀⟩
      refine symmFockMultiParticleVec_eq_zero_of_zero_slot L.mode.ν L.mode.hη r s' _ (i₀ := i₀) ?_
      rw [lorentzModeWavepacket_one, if_neg hi₀]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s))
  refine DFunLike.ext _ _ fun x => ?_
  exact congrFun (congrArg DFunLike.coe hclm) x

theorem symmFockLorentzIsometry_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A B : SL2C) :
    symmFockLorentzIsometry L (A * B) =
      (symmFockLorentzIsometry L A).comp (symmFockLorentzIsometry L B) := by
  have hclm : (symmFockLorentzIsometry L (A * B)).toContinuousLinearMap =
      ((symmFockLorentzIsometry L A).comp (symmFockLorentzIsometry L B)).toContinuousLinearMap := by
    refine symmFockLorentzIsometry_ext L _ _ fun r s f => ?_
    change symmFockLorentzIsometry L (A * B)
        (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
      symmFockLorentzIsometry L A
        (symmFockLorentzIsometry L B (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f))
    rw [symmFockLorentzIsometry_multiParticleVec, symmFockLorentzIsometry_multiParticleVec, map_sum]
    simp_rw [symmFockLorentzIsometry_multiParticleVec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s'' _ => ?_
    refine (congrArg (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'')
      (funext fun i =>
        (finsetSum_lorentzModeWavepacket_comp L A B (s'' i) (s i) (f i)).symm)).trans ?_
    exact (symmFockMultiParticleVec_finsetSum_pi L.mode.ν L.mode.hη r s'' (fun i b =>
      lorentzModeWavepacket L A (s'' i) b (lorentzModeWavepacket L B b (s i) (f i)))).symm
  refine DFunLike.ext _ _ fun x => ?_
  exact congrFun (congrArg DFunLike.coe hclm) x

theorem symmFockLorentzIsometry_neg_one_multiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    symmFockLorentzIsometry L (-1) (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
      (η ^ r) • symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f := by
  rw [symmFockLorentzIsometry_multiParticleVec, Finset.sum_eq_single s]
  · have h_eq' : symmFockMultiParticleVec L.mode.ν η L.mode.hη r s
        (fun i => lorentzModeWavepacket L (-1) (s i) (s i) (f i)) =
      symmFockMultiParticleVec L.mode.ν η L.mode.hη r s (fun i => smulWavepacket η (f i)) := by
      congr 1
      ext i
      rw [lorentzModeWavepacket_neg_one L hε, if_pos rfl]
    rw [h_eq', symmFockMultiParticleVec_smul_all]
  · intro s' _ hne
    have hex : ∃ i₀ : Fin r, s' i₀ ≠ s i₀ := by
      by_contra h_all
      push Not at h_all
      exact hne (funext h_all)
    rcases hex with ⟨i₀, hi₀⟩
    refine symmFockMultiParticleVec_eq_zero_of_zero_slot L.mode.ν L.mode.hη r s' _ (i₀ := i₀) ?_
    rw [lorentzModeWavepacket_neg_one L hε, if_neg hi₀]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ s))

theorem symmFockLorentzIsometry_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (a : Fin 4 → ℝ)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockLorentzIsometry L A (symmFockTranslateEquiv m L.mode.ν η a x) =
      symmFockTranslateEquiv m L.mode.ν η ((lorentzOfSL2C A).mulVec a)
        (symmFockLorentzIsometry L A x) := by
  have hclm :
      (symmFockLorentzIsometry L A).toContinuousLinearMap.comp
          (symmFockTranslateEquiv m L.mode.ν η a).toLinearIsometry.toContinuousLinearMap =
        (symmFockTranslateEquiv m L.mode.ν η
            ((lorentzOfSL2C A).mulVec a)).toLinearIsometry.toContinuousLinearMap.comp
          (symmFockLorentzIsometry L A).toContinuousLinearMap := by
    refine symmFockLorentzIsometry_ext L _ _ fun r s f => ?_
    change symmFockLorentzIsometry L A
        (symmFockTranslateEquiv m L.mode.ν η a
          (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)) =
      symmFockTranslateEquiv m L.mode.ν η ((lorentzOfSL2C A).mulVec a)
        (symmFockLorentzIsometry L A (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f))
    rw [symmFockTranslateEquiv_multiParticleVec L.hm, symmFockLorentzIsometry_multiParticleVec,
      symmFockLorentzIsometry_multiParticleVec, map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [symmFockTranslateEquiv_multiParticleVec L.hm]
    congr 1
    ext i
    exact (lorentzModeWavepacket_translateWavepacket L A a (s' i) (s i) (f i)) ▸ rfl
  exact congrFun (congrArg DFunLike.coe hclm) x

def symmFockLorentzEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) :
    SymmFockHilbert L.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert L.mode.ν η where
  toLinearEquiv := LinearEquiv.ofLinear
    (symmFockLorentzIsometry L A).toLinearMap
    (symmFockLorentzIsometry L A⁻¹).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change ((symmFockLorentzIsometry L A).comp (symmFockLorentzIsometry L A⁻¹)) x = x
      rw [← symmFockLorentzIsometry_mul, mul_inv_cancel, symmFockLorentzIsometry_one]
      rfl)
    (by
      apply LinearMap.ext
      intro x
      change ((symmFockLorentzIsometry L A⁻¹).comp (symmFockLorentzIsometry L A)) x = x
      rw [← symmFockLorentzIsometry_mul, inv_mul_cancel, symmFockLorentzIsometry_one]
      rfl)
  norm_map' x := (symmFockLorentzIsometry L A).norm_map x

@[simp]
lemma symmFockLorentzEquiv_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockLorentzEquiv L A x = symmFockLorentzIsometry L A x := rfl

@[simp]
lemma symmFockLorentzEquiv_symm
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) :
    (symmFockLorentzEquiv L A).symm = symmFockLorentzEquiv L A⁻¹ := by
  apply LinearIsometryEquiv.ext
  intro x
  rfl

@[simp]
theorem symmFockLorentzEquiv_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) :
    symmFockLorentzEquiv L 1 = LinearIsometryEquiv.refl ℂ (SymmFockHilbert L.mode.ν η) := by
  apply LinearIsometryEquiv.ext
  intro x
  change symmFockLorentzIsometry L 1 x = x
  rw [symmFockLorentzIsometry_one]
  rfl

theorem symmFockLorentzEquiv_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A B : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockLorentzEquiv L (A * B) x =
      symmFockLorentzEquiv L A (symmFockLorentzEquiv L B x) := by
  change symmFockLorentzIsometry L (A * B) x =
    symmFockLorentzIsometry L A (symmFockLorentzIsometry L B x)
  rw [symmFockLorentzIsometry_mul]
  rfl

@[simp]
theorem symmFockLorentzEquiv_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) :
    symmFockLorentzEquiv L A (symmFockVacuum L.mode.ν η) = symmFockVacuum L.mode.ν η :=
  symmFockLorentzIsometry_vacuum L A

theorem symmFockLorentzEquiv_oneParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (s : Fin L.mode.ν) (f : SmoothWavepacket) :
    symmFockLorentzEquiv L A (symmFockOneParticleVec L.mode.ν η s f) =
      ∑ s' : Fin L.mode.ν,
        symmFockOneParticleVec L.mode.ν η s' (lorentzModeWavepacket L A s' s f) :=
  symmFockLorentzIsometry_oneParticleVec L A s f

theorem symmFockLorentzEquiv_multiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    symmFockLorentzEquiv L A (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
      ∑ s' : Fin r → Fin L.mode.ν,
        symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'
          (fun i => lorentzModeWavepacket L A (s' i) (s i) (f i)) :=
  symmFockLorentzIsometry_multiParticleVec L A r s f

theorem symmFockLorentzEquiv_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (A : SL2C) (a : Fin 4 → ℝ)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockLorentzEquiv L A (symmFockTranslateEquiv m L.mode.ν η a x) =
      symmFockTranslateEquiv m L.mode.ν η ((lorentzOfSL2C A).mulVec a)
        (symmFockLorentzEquiv L A x) :=
  symmFockLorentzIsometry_translate L A a x

def symmFockPoincareEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (a : Fin 4 → ℝ) (A : SL2C) :
    SymmFockHilbert L.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert L.mode.ν η :=
  (symmFockLorentzEquiv L A).trans (symmFockTranslateEquiv m L.mode.ν η a)

@[simp]
lemma symmFockPoincareEquiv_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (a : Fin 4 → ℝ) (A : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPoincareEquiv L a A x =
      symmFockTranslateEquiv m L.mode.ν η a (symmFockLorentzEquiv L A x) := rfl

@[simp]
theorem symmFockPoincareEquiv_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) :
    symmFockPoincareEquiv L 0 1 = LinearIsometryEquiv.refl ℂ (SymmFockHilbert L.mode.ν η) := by
  apply LinearIsometryEquiv.ext
  intro x
  simp only [symmFockPoincareEquiv_apply, symmFockLorentzEquiv_one,
    symmFockTranslateEquiv_zero]
  rfl

@[simp]
theorem symmFockPoincareEquiv_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (a : Fin 4 → ℝ) (A : SL2C) :
    symmFockPoincareEquiv L a A (symmFockVacuum L.mode.ν η) = symmFockVacuum L.mode.ν η := by
  simp only [symmFockPoincareEquiv_apply, symmFockLorentzEquiv_vacuum,
    symmFockTranslateEquiv_vacuum]

theorem symmFockPoincareEquiv_mul
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (a₁ a₂ : Fin 4 → ℝ) (A₁ A₂ : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPoincareEquiv L a₁ A₁ (symmFockPoincareEquiv L a₂ A₂ x) =
      symmFockPoincareEquiv L (a₁ + (lorentzOfSL2C A₁).mulVec a₂) (A₁ * A₂) x := by
  simp only [symmFockPoincareEquiv_apply]
  rw [symmFockLorentzEquiv_translate, symmFockLorentzEquiv_mul, ← symmFockTranslateEquiv_add]

def symmFockPCTTarget
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    SymmFockHilbert L.mode.ν η :=
  (η ^ (r * (r - 1) / 2)) •
    ∑ s' : Fin r → Fin L.mode.ν,
      symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'
        (fun i => pctModeWavepacket L (s' i) (s i) (f i))

lemma inner_symmFockPCTTarget_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell)
    (r₁ r₂ : ℕ) (s₁ : Fin r₁ → Fin L.mode.ν) (f₁ : Fin r₁ → SmoothWavepacket)
    (s₂ : Fin r₂ → Fin L.mode.ν) (f₂ : Fin r₂ → SmoothWavepacket) :
    ⟪symmFockPCTTarget L r₁ s₁ f₁, symmFockPCTTarget L r₂ s₂ f₂⟫_ℂ =
      star ⟪symmFockMultiParticleVec L.mode.ν η L.mode.hη r₁ s₁ f₁,
        symmFockMultiParticleVec L.mode.ν η L.mode.hη r₂ s₂ f₂⟫_ℂ := by
  by_cases hr : r₁ = r₂
  · subst hr
    unfold symmFockPCTTarget
    rw [inner_smul_left, inner_smul_right, ← Complex.star_def]
    have hη_sq : star (η ^ (r₁ * (r₁ - 1) / 2)) * (η ^ (r₁ * (r₁ - 1) / 2)) = 1 := by
      rcases L.mode.hη with h1 | h1 <;> rw [h1]
      · simp
      · simp only [star_pow, star_neg, star_one]
        rw [← pow_add, ← two_mul]
        exact Even.neg_one_pow (even_two_mul _)
    rw [← mul_assoc, hη_sq, one_mul, sum_inner,
      Finset.sum_congr rfl fun s'₁ _ => inner_sum _ _ _]
    simp_rw [inner_symmFockMultiParticleVec_eq]
    rw [star_sum, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun s'₁ _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hη_perm : star (η ^ permInversions σ) = η ^ permInversions σ := by
      rcases L.mode.hη with h1 | h1 <;> rw [h1] <;> simp
    rw [star_mul', hη_perm]
    rw [Finset.sum_congr rfl fun s'₁ _ => (Finset.mul_sum _ _ _).symm, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    have h_perm :
        (∑ s'₁ : Fin r₁ → Fin L.mode.ν, ∑ s'₂ : Fin r₁ → Fin L.mode.ν,
          ∏ i : Fin r₁,
            ⟪fockOneParticleVec L.mode.ν (s'₁ i) (pctModeWavepacket L (s'₁ i) (s₁ i) (f₁ i)),
              fockOneParticleVec L.mode.ν (s'₂ (σ.symm i))
                (pctModeWavepacket L (s'₂ (σ.symm i)) (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ) =
        ∑ s'₁ : Fin r₁ → Fin L.mode.ν, ∑ s'₂ : Fin r₁ → Fin L.mode.ν,
          ∏ i : Fin r₁,
            ⟪fockOneParticleVec L.mode.ν (s'₁ i) (pctModeWavepacket L (s'₁ i) (s₁ i) (f₁ i)),
              fockOneParticleVec L.mode.ν (s'₂ i)
                (pctModeWavepacket L (s'₂ i) (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ := by
      refine Finset.sum_congr rfl fun s'₁ _ => ?_
      let τ : (Fin r₁ → Fin L.mode.ν) ≃ (Fin r₁ → Fin L.mode.ν) :=
        { toFun := fun s' => s' ∘ σ
          invFun := fun s' => s' ∘ σ.symm
          left_inv := fun s' => by ext i; simp
          right_inv := fun s' => by ext i; simp }
      rw [← τ.sum_comp]
      refine Finset.sum_congr rfl fun s'₂ _ => ?_
      refine Finset.prod_congr rfl fun i _ => ?_
      dsimp [τ]
      simp
    rw [h_perm]
    rw [Finset.sum_congr rfl fun s'₁ _ => (Fintype.prod_sum fun (i : Fin r₁) (b₂ : Fin L.mode.ν) =>
      ⟪fockOneParticleVec L.mode.ν (s'₁ i) (pctModeWavepacket L (s'₁ i) (s₁ i) (f₁ i)),
        fockOneParticleVec L.mode.ν b₂
          (pctModeWavepacket L b₂ (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ).symm]
    rw [(Fintype.prod_sum fun (i : Fin r₁) (b₁ : Fin L.mode.ν) =>
      ∑ b₂ : Fin L.mode.ν,
        ⟪fockOneParticleVec L.mode.ν b₁ (pctModeWavepacket L b₁ (s₁ i) (f₁ i)),
          fockOneParticleVec L.mode.ν b₂
            (pctModeWavepacket L b₂ (s₂ (σ.symm i)) (f₂ (σ.symm i)))⟫_ℂ).symm]
    rw [star_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp_rw [← inner_sum]
    rw [← sum_inner]
    exact inner_sum_fockOneParticleVec_pct L hε hC_pct (s₁ i) (s₂ (σ.symm i))
      (f₁ i) (f₂ (σ.symm i))
  · unfold symmFockPCTTarget
    rw [inner_smul_left, inner_smul_right, sum_inner]
    have h0 :
        (∑ x : Fin r₁ → Fin L.mode.ν,
          ⟪symmFockMultiParticleVec L.mode.ν η L.mode.hη r₁ x
              (fun i => pctModeWavepacket L (x i) (s₁ i) (f₁ i)),
            ∑ x_1 : Fin r₂ → Fin L.mode.ν,
              symmFockMultiParticleVec L.mode.ν η L.mode.hη r₂ x_1
                (fun i => pctModeWavepacket L (x_1 i) (s₂ i) (f₂ i))⟫_ℂ) = 0 := by
      refine Finset.sum_eq_zero fun s'₁ _ => ?_
      rw [inner_sum]
      refine Finset.sum_eq_zero fun s'₂ _ => ?_
      exact inner_symmFockMultiParticleVec_ne L.mode.ν L.mode.hη hr _ _ _ _
    rw [h0, mul_zero, mul_zero,
      inner_symmFockMultiParticleVec_ne L.mode.ν L.mode.hη hr s₁ f₁ s₂ f₂, star_zero]

def symmFockPCTCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) :
    SymmFockHilbert L.mode.ν η →SL[starRingEnd ℂ] SymmFockHilbert L.mode.ν η :=
  (exists_unique_antilinearCLM_of_inner_eq_of_dense
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockMultiParticleVec L.mode.ν η L.mode.hη cfg.1 cfg.2.1 cfg.2.2)
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockPCTTarget L cfg.1 cfg.2.1 cfg.2.2)
    (fun ⟨r₁, s₁, f₁⟩ ⟨r₂, s₂, f₂⟩ =>
      inner_symmFockPCTTarget_eq L hε hC_pct r₁ r₂ s₁ f₁ s₂ f₂)
    (dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη)).choose

theorem symmFockPCTCLM_multiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    symmFockPCTCLM L hε hC_pct (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
      (η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin L.mode.ν,
          symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'
            (fun i => pctModeWavepacket L (s' i) (s i) (f i)) :=
  (exists_unique_antilinearCLM_of_inner_eq_of_dense
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockMultiParticleVec L.mode.ν η L.mode.hη cfg.1 cfg.2.1 cfg.2.2)
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockPCTTarget L cfg.1 cfg.2.1 cfg.2.2)
    (fun ⟨r₁, s₁, f₁⟩ ⟨r₂, s₂, f₂⟩ =>
      inner_symmFockPCTTarget_eq L hε hC_pct r₁ r₂ s₁ f₁ s₂ f₂)
    (dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη)).choose_spec.1 ⟨r, s, f⟩

theorem symmFockPCTCLM_ext
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell)
    (T₁ T₂ : SymmFockHilbert L.mode.ν η →SL[starRingEnd ℂ] SymmFockHilbert L.mode.ν η)
    (h_eq : ∀ (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket),
      T₁ (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
        T₂ (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)) :
    T₁ = T₂ := by
  apply ContinuousLinearMap.ext
  intro x
  have hdense := dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη
  refine hdense.induction ?_ (isClosed_eq T₁.continuous T₂.continuous) x
  intro y hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨⟨r, s, f⟩, rfl⟩
    exact h_eq r s f
  · simp
  · intro u v _ _ hu hv
    rw [map_add, map_add, hu, hv]
  · intro c u _ hu
    rw [map_smulₛₗ, map_smulₛₗ, hu]

theorem inner_symmFockPCTCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (x y : SymmFockHilbert L.mode.ν η) :
    ⟪symmFockPCTCLM L hε hC_pct x, symmFockPCTCLM L hε hC_pct y⟫_ℂ = star ⟪x, y⟫_ℂ := by
  refine inner_antilinearCLM_of_dense (symmFockPCTCLM L hε hC_pct)
    (fun cfg : MultiParticleConfig L.mode.ν =>
      symmFockMultiParticleVec L.mode.ν η L.mode.hη cfg.1 cfg.2.1 cfg.2.2)
    (fun ⟨r₁, s₁, f₁⟩ ⟨r₂, s₂, f₂⟩ => by
      rw [symmFockPCTCLM_multiParticleVec, symmFockPCTCLM_multiParticleVec]
      exact inner_symmFockPCTTarget_eq L hε hC_pct r₁ r₂ s₁ f₁ s₂ f₂)
    (dense_range_all_symmFockMultiParticleVec L.mode.ν L.hm L.mode.hη) x y

@[simp]
theorem norm_symmFockPCTCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (x : SymmFockHilbert L.mode.ν η) :
    ‖symmFockPCTCLM L hε hC_pct x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    inner_symmFockPCTCLM L hε hC_pct x x, Complex.star_def, RCLike.conj_re]

@[simp]
theorem symmFockPCTCLM_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) :
    symmFockPCTCLM L hε hC_pct (symmFockVacuum L.mode.ν η) = symmFockVacuum L.mode.ν η := by
  rw [← symmFockMultiParticleVec_zero L.mode.ν L.mode.hη Fin.elim0 Fin.elim0,
    symmFockPCTCLM_multiParticleVec]
  rw [Fintype.sum_eq_single Fin.elim0 fun s' hne => False.elim (hne (Subsingleton.elim _ _))]
  simp only [Nat.zero_mul, Nat.zero_div, pow_zero, one_smul]
  exact congrArg (symmFockMultiParticleVec L.mode.ν η L.mode.hη 0 Fin.elim0)
    (Subsingleton.elim _ Fin.elim0)

theorem symmFockPCTCLM_oneParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell)
    (s : Fin L.mode.ν) (f : SmoothWavepacket) :
    symmFockPCTCLM L hε hC_pct (symmFockOneParticleVec L.mode.ν η s f) =
      ∑ s' : Fin L.mode.ν,
        symmFockOneParticleVec L.mode.ν η s' (pctModeWavepacket L s' s f) := by
  rw [← symmFockMultiParticleVec_one L.mode.ν L.mode.hη (fun _ => s) (fun _ => f),
    symmFockPCTCLM_multiParticleVec]
  simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, one_smul]
  rw [← (Equiv.funUnique (Fin 1) (Fin L.mode.ν)).symm.sum_comp]
  refine Finset.sum_congr rfl fun s' _ => ?_
  exact symmFockMultiParticleVec_one L.mode.ν L.mode.hη _ _

theorem symmFockPCTCLM_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTCLM L hε hC_pct (symmFockPCTCLM L hε hC_pct x) =
      symmFockLorentzEquiv L (-1) x := by
  have hclm :
      ((symmFockPCTCLM L hε hC_pct).comp (symmFockPCTCLM L hε hC_pct)).comp
          (ContinuousLinearMap.id ℂ _) =
        (symmFockLorentzIsometry L (-1)).toContinuousLinearMap := by
    refine symmFockLorentzIsometry_ext L _ _ fun r s f => ?_
    change symmFockPCTCLM L hε hC_pct
        (symmFockPCTCLM L hε hC_pct (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)) =
      symmFockLorentzIsometry L (-1) (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)
    rw [symmFockPCTCLM_multiParticleVec, map_smulₛₗ, ← Complex.star_def, map_sum]
    simp_rw [symmFockPCTCLM_multiParticleVec]
    rw [← Finset.smul_sum, smul_smul]
    have hη_sq : star (η ^ (r * (r - 1) / 2)) * (η ^ (r * (r - 1) / 2)) = 1 := by
      rcases L.mode.hη with h1 | h1 <;> rw [h1]
      · simp
      · simp only [star_pow, star_neg, star_one]
        rw [← pow_add, ← two_mul]
        exact Even.neg_one_pow (even_two_mul _)
    rw [hη_sq, one_smul, Finset.sum_comm]
    have h_eq' :
        (∑ s'' : Fin r → Fin L.mode.ν, ∑ x : Fin r → Fin L.mode.ν,
          symmFockMultiParticleVec L.mode.ν η L.mode.hη r s''
            (fun i =>
              pctModeWavepacket L (s'' i) (x i) (pctModeWavepacket L (x i) (s i) (f i)))) =
        ∑ s'' : Fin r → Fin L.mode.ν,
          symmFockMultiParticleVec L.mode.ν η L.mode.hη r s''
            (fun i => if s'' i = s i then smulWavepacket η (f i) else zeroWavepacket) := by
      refine Finset.sum_congr rfl fun s'' _ => ?_
      rw [symmFockMultiParticleVec_finsetSum_pi (g := fun i b =>
        pctModeWavepacket L (s'' i) b (pctModeWavepacket L b (s i) (f i)))]
      congr 1
      ext i
      exact finsetSum_pctModeWavepacket_comp L hε hC_pct (s'' i) (s i) (f i)
    rw [h_eq', Finset.sum_eq_single s]
    · have h_pos :
          (fun i => if s i = s i then smulWavepacket η (f i) else zeroWavepacket) =
          fun i => smulWavepacket η (f i) := by
        ext i
        rw [if_pos rfl]
      rw [h_pos, symmFockMultiParticleVec_smul_all,
        symmFockLorentzIsometry_neg_one_multiParticleVec L hε]
    · intro s'' _ hne
      have hex : ∃ i₀ : Fin r, s'' i₀ ≠ s i₀ := by
        by_contra h_all
        push Not at h_all
        exact hne (funext h_all)
      rcases hex with ⟨i₀, hi₀⟩
      refine symmFockMultiParticleVec_eq_zero_of_zero_slot L.mode.ν L.mode.hη r s'' _
        (i₀ := i₀) ?_
      rw [if_neg hi₀]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s))
  exact congrFun (congrArg DFunLike.coe hclm) x

theorem symmFockPCTCLM_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (a : Fin 4 → ℝ)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTCLM L hε hC_pct (symmFockTranslateEquiv m L.mode.ν η a x) =
      symmFockTranslateEquiv m L.mode.ν η (-a) (symmFockPCTCLM L hε hC_pct x) := by
  have hclm :
      (symmFockPCTCLM L hε hC_pct).comp
          (symmFockTranslateEquiv m L.mode.ν η a).toLinearIsometry.toContinuousLinearMap =
        (symmFockTranslateEquiv m L.mode.ν η (-a)).toLinearIsometry.toContinuousLinearMap.comp
          (symmFockPCTCLM L hε hC_pct) := by
    refine symmFockPCTCLM_ext L _ _ fun r s f => ?_
    change symmFockPCTCLM L hε hC_pct
        (symmFockTranslateEquiv m L.mode.ν η a
          (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)) =
      symmFockTranslateEquiv m L.mode.ν η (-a)
        (symmFockPCTCLM L hε hC_pct (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f))
    rw [symmFockTranslateEquiv_multiParticleVec L.hm, symmFockPCTCLM_multiParticleVec,
      symmFockPCTCLM_multiParticleVec, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [symmFockTranslateEquiv_multiParticleVec L.hm]
    congr 1
    ext i
    exact (pctModeWavepacket_translateWavepacket L a (s' i) (s i) (f i)) ▸ rfl
  exact congrFun (congrArg DFunLike.coe hclm) x

theorem symmFockPCTCLM_lorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (A : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTCLM L hε hC_pct (symmFockLorentzEquiv L A x) =
      symmFockLorentzEquiv L A (symmFockPCTCLM L hε hC_pct x) := by
  have hclm :
      (symmFockPCTCLM L hε hC_pct).comp
          (symmFockLorentzEquiv L A).toLinearIsometry.toContinuousLinearMap =
        (symmFockLorentzEquiv L A).toLinearIsometry.toContinuousLinearMap.comp
          (symmFockPCTCLM L hε hC_pct) := by
    refine symmFockPCTCLM_ext L _ _ fun r s f => ?_
    change symmFockPCTCLM L hε hC_pct
        (symmFockLorentzEquiv L A (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f)) =
      symmFockLorentzEquiv L A
        (symmFockPCTCLM L hε hC_pct (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f))
    rw [symmFockLorentzEquiv_multiParticleVec, symmFockPCTCLM_multiParticleVec, map_sum,
      map_smul, map_sum]
    rw [Finset.sum_congr rfl fun s' _ => symmFockPCTCLM_multiParticleVec L hε hC_pct r s' _]
    conv_rhs =>
      arg 2
      rw [Finset.sum_congr rfl fun s' _ => symmFockLorentzEquiv_multiParticleVec L A r s' _]
    rw [← Finset.smul_sum]
    refine congrArg ((η ^ (r * (r - 1) / 2)) • ·) ?_
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s'' _ => ?_
    rw [symmFockMultiParticleVec_finsetSum_pi (g := fun i b =>
      pctModeWavepacket L (s'' i) b (lorentzModeWavepacket L A b (s i) (f i)))]
    rw [symmFockMultiParticleVec_finsetSum_pi (g := fun i b =>
      lorentzModeWavepacket L A (s'' i) b (pctModeWavepacket L b (s i) (f i)))]
    exact congrArg (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'') (funext fun i =>
      finsetSum_pctModeWavepacket_lorentz L hε hC_pct A (s'' i) (s i) (f i))
  exact congrFun (congrArg DFunLike.coe hclm) x

def symmFockPCTEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) :
    SymmFockHilbert L.mode.ν η ≃ₗᵢ⋆[ℂ] SymmFockHilbert L.mode.ν η where
  toFun := symmFockPCTCLM L hε hC_pct
  invFun x := symmFockLorentzEquiv L (-1) (symmFockPCTCLM L hε hC_pct x)
  left_inv x := by
    dsimp only
    rw [symmFockPCTCLM_sq, ← symmFockLorentzEquiv_mul]
    have hsq : (-1 : SL2C) * (-1 : SL2C) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hsq, symmFockLorentzEquiv_one]
    rfl
  right_inv x := by
    dsimp only
    rw [symmFockPCTCLM_lorentz, symmFockPCTCLM_sq, ← symmFockLorentzEquiv_mul]
    have hsq : (-1 : SL2C) * (-1 : SL2C) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hsq, symmFockLorentzEquiv_one]
    rfl
  map_add' := map_add (symmFockPCTCLM L hε hC_pct)
  map_smul' := map_smulₛₗ (symmFockPCTCLM L hε hC_pct)
  norm_map' := norm_symmFockPCTCLM L hε hC_pct

@[simp]
lemma symmFockPCTEquiv_apply
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTEquiv L hε hC_pct x = symmFockPCTCLM L hε hC_pct x := rfl

theorem inner_symmFockPCTEquiv
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (x y : SymmFockHilbert L.mode.ν η) :
    ⟪symmFockPCTEquiv L hε hC_pct x, symmFockPCTEquiv L hε hC_pct y⟫_ℂ = star ⟪x, y⟫_ℂ :=
  inner_symmFockPCTCLM L hε hC_pct x y

@[simp]
theorem symmFockPCTEquiv_vacuum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) :
    symmFockPCTEquiv L hε hC_pct (symmFockVacuum L.mode.ν η) = symmFockVacuum L.mode.ν η :=
  symmFockPCTCLM_vacuum L hε hC_pct

theorem symmFockPCTEquiv_oneParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (s : Fin L.mode.ν) (f : SmoothWavepacket) :
    symmFockPCTEquiv L hε hC_pct (symmFockOneParticleVec L.mode.ν η s f) =
      ∑ s' : Fin L.mode.ν,
        symmFockOneParticleVec L.mode.ν η s' (pctModeWavepacket L s' s f) :=
  symmFockPCTCLM_oneParticleVec L hε hC_pct s f

theorem symmFockPCTEquiv_multiParticleVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell)
    (r : ℕ) (s : Fin r → Fin L.mode.ν) (f : Fin r → SmoothWavepacket) :
    symmFockPCTEquiv L hε hC_pct (symmFockMultiParticleVec L.mode.ν η L.mode.hη r s f) =
      (η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin L.mode.ν,
          symmFockMultiParticleVec L.mode.ν η L.mode.hη r s'
            (fun i => pctModeWavepacket L (s' i) (s i) (f i)) :=
  symmFockPCTCLM_multiParticleVec L hε hC_pct r s f

theorem symmFockPCTEquiv_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTEquiv L hε hC_pct (symmFockPCTEquiv L hε hC_pct x) =
      symmFockLorentzEquiv L (-1) x :=
  symmFockPCTCLM_sq L hε hC_pct x

theorem symmFockPCTEquiv_sq_oneParticle_fermion
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m (-1) C_shell) (hε : R.HasSpinParity (-1))
    (hC_pct : OnShellPCT R m (-1) C_shell) (s : Fin L.mode.ν) (f : SmoothWavepacket) :
    symmFockPCTEquiv L hε hC_pct
        (symmFockPCTEquiv L hε hC_pct (symmFockOneParticleVec L.mode.ν (-1) s f)) =
      -(symmFockOneParticleVec L.mode.ν (-1) s f) := by
  rw [symmFockPCTEquiv_sq, symmFockLorentzEquiv_apply,
    ← symmFockMultiParticleVec_one L.mode.ν L.mode.hη (fun _ => s) (fun _ => f),
    symmFockLorentzIsometry_neg_one_multiParticleVec L hε, pow_one, neg_one_smul]

theorem symmFockPCTEquiv_translate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (a : Fin 4 → ℝ)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTEquiv L hε hC_pct (symmFockTranslateEquiv m L.mode.ν η a x) =
      symmFockTranslateEquiv m L.mode.ν η (-a) (symmFockPCTEquiv L hε hC_pct x) :=
  symmFockPCTCLM_translate L hε hC_pct a x

theorem symmFockPCTEquiv_lorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (A : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTEquiv L hε hC_pct (symmFockLorentzEquiv L A x) =
      symmFockLorentzEquiv L A (symmFockPCTEquiv L hε hC_pct x) :=
  symmFockPCTCLM_lorentz L hε hC_pct A x

theorem symmFockPCTEquiv_poincare
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m : ℝ} {η : ℂ} {C_shell : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (L : LorentzModeData R S m η C_shell) (hε : R.HasSpinParity η)
    (hC_pct : OnShellPCT R m η C_shell) (a : Fin 4 → ℝ) (A : SL2C)
    (x : SymmFockHilbert L.mode.ν η) :
    symmFockPCTEquiv L hε hC_pct (symmFockPoincareEquiv L a A x) =
      symmFockPoincareEquiv L (-a) A (symmFockPCTEquiv L hε hC_pct x) := by
  simp only [symmFockPoincareEquiv_apply]
  rw [symmFockPCTEquiv_translate, symmFockPCTEquiv_lorentz]

end IntrinsicFockPoincareAndPCT

section PoincareMassShellAndOneParticle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

structure PoincareIsolatedMassShellData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (m M : ℝ) (η : ℂ) extends IsolatedMassShellData R S m M η where
  contDiff_w : ∀ (s : Fin mode.ν) (α : ι),
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => mode.w s p α)
  hC_cov : ∀ (A : SL2C) (p : Fin 3 → ℝ) (α : Fin 2 → ι),
    C_shell α ((lorentzOfSL2C A).mulVec (massShellVec m p)) =
      ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C_shell β (massShellVec m p)

namespace PoincareIsolatedMassShellData

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R} {m M : ℝ} {η : ℂ}

abbrev modeData (P : PoincareIsolatedMassShellData R S m M η) :
    LorentzModeData R S m η P.C_shell where
  hm := P.hm
  mode := P.mode
  contDiff_w := P.contDiff_w
  dual_w := P.dual_w
  contDiff_dual_w := P.contDiff_dual_w
  dual_orthonormal := P.dual_orthonormal
  hC_cov := P.hC_cov

def lorentzEquiv (P : PoincareIsolatedMassShellData R S m M η) (A : SL2C) :
    P.Hilbert ≃ₗᵢ[ℂ] P.Hilbert :=
  P.wightman.toWightmanAxioms.lorentzEquiv A

def poincareEquiv (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) :
    P.Hilbert ≃ₗᵢ[ℂ] P.Hilbert :=
  P.wightman.toWightmanAxioms.poincareEquiv a A

def pctEquiv (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) :
    P.Hilbert ≃ₗᵢ⋆[ℂ] P.Hilbert :=
  P.wightman.toWightmanAxioms.pctEquiv hε

def fockTranslateEquiv (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) :
    SymmFockHilbert P.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert P.mode.ν η :=
  symmFockTranslateEquiv m P.mode.ν η a

def fockLorentzEquiv (P : PoincareIsolatedMassShellData R S m M η) (A : SL2C) :
    SymmFockHilbert P.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert P.mode.ν η :=
  symmFockLorentzEquiv P.modeData A

def fockPoincareEquiv (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) :
    SymmFockHilbert P.mode.ν η ≃ₗᵢ[ℂ] SymmFockHilbert P.mode.ν η :=
  symmFockPoincareEquiv P.modeData a A

def fockPCTEquiv (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell) :
    SymmFockHilbert P.mode.ν η ≃ₗᵢ⋆[ℂ] SymmFockHilbert P.mode.ν η :=
  symmFockPCTEquiv P.modeData hε hC_pct

lemma poincareEquiv_eq_translate_lorentz (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) (x : P.Hilbert) :
    P.poincareEquiv a A x = P.translate a (P.lorentzEquiv A x) := by
  dsimp [poincareEquiv, lorentzEquiv, IsolatedMassShellData.translate,
    WightmanAxioms.poincareEquiv, WightmanAxioms.lorentzEquiv]

end PoincareIsolatedMassShellData

def lorentzIndexedTest (R : HolomorphicLorentzRep ι) (A : SL2C)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun γ => ∑ α : ι, R.rep A⁻¹ α γ • schwartzLorentzCLM 1 A⁻¹ (Ψ α)

def pctIndexedTest {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  fun μ => ∑ α : ι, pctMatrix S α μ • schwartzPTConj 1 (Ψ α)

lemma lorentzIndexedTest_sub (R : HolomorphicLorentzRep ι) (A : SL2C)
    (Ψ₁ Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (γ : ι) :
    lorentzIndexedTest R A Ψ₁ γ - lorentzIndexedTest R A Ψ₂ γ =
      lorentzIndexedTest R A (fun α => Ψ₁ α - Ψ₂ α) γ := by
  dsimp [lorentzIndexedTest]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sub, smul_sub]

lemma pctIndexedTest_sub {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ₁ Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (μ : ι) :
    pctIndexedTest S Ψ₁ μ - pctIndexedTest S Ψ₂ μ =
      pctIndexedTest S (fun α => Ψ₁ α - Ψ₂ α) μ := by
  dsimp [pctIndexedTest]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_sub, smul_sub]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzPrepend_sum_left {κ : Type*} [Fintype κ] (k : ℕ)
    (ψ : κ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k (∑ a : κ, ψ a) F = ∑ a : κ, schwartzPrepend k (ψ a) F := by
  ext x
  simp only [schwartzPrepend_apply, schwartzMap_sum_apply, Finset.sum_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzPrepend_sum_right {κ : Type*} [Fintype κ] (k : ℕ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : κ → SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPrepend k ψ (∑ a : κ, F a) = ∑ a : κ, schwartzPrepend k ψ (F a) := by
  ext x
  simp only [schwartzPrepend_apply, schwartzMap_sum_apply, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzChain_sum {κ : Type*} [Fintype κ] (r : ℕ)
    (f : Fin r → κ → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (fun i => ∑ a : κ, f i a) =
      ∑ c : Fin r → κ, schwartzChain r (fun i => f i (c i)) := by
  induction r with
  | zero =>
    dsimp [schwartzChain]
    rw [Fintype.sum_eq_single Fin.elim0 fun c hne => False.elim (hne (Subsingleton.elim _ _))]
  | succ k ih =>
    dsimp [schwartzChain]
    change schwartzPrepend k (∑ a : κ, f 0 a)
        (schwartzChain k (fun i => ∑ a : κ, (f ∘ Fin.succ) i a)) = _
    rw [ih (f ∘ Fin.succ), schwartzPrepend_sum_left]
    rw [Finset.sum_congr rfl fun a _ => schwartzPrepend_sum_right k (f 0 a) _]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => κ)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzChain_smul (r : ℕ) (c : Fin r → ℂ)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzChain r (fun i => c i • ψ i) = (∏ i : Fin r, c i) • schwartzChain r ψ := by
  induction r with
  | zero => simp [schwartzChain]
  | succ k ih =>
    dsimp [schwartzChain]
    have h_tail : ((fun i : Fin (k + 1) => c i • ψ i) ∘ Fin.succ) =
        fun i : Fin k => (c ∘ Fin.succ) i • (ψ ∘ Fin.succ) i := rfl
    rw [Fin.prod_univ_succ, mul_smul, h_tail, ih (c ∘ Fin.succ) (ψ ∘ Fin.succ),
      schwartzPrepend_smul_left, schwartzPrepend_smul_right]
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzLorentzCLM_fin0_vac (A : SL2C) :
    schwartzLorentzCLM 0 A (momentumWavepacketSchwartz 0 0) =
      momentumWavepacketSchwartz 0 0 := by
  ext x
  rw [schwartzLorentzCLM_apply]
  have hx1 : (fun i : Fin 0 => (lorentzOfSL2C A).mulVec (x i)) = 0 := Subsingleton.elim _ _
  have hx2 : x = 0 := Subsingleton.elim _ _
  rw [hx1, hx2]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzLorentzCLM_schwartzPrepend (k : ℕ) (A : SL2C)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzLorentzCLM (k + 1) A (schwartzPrepend k ψ F) =
      schwartzPrepend k (schwartzLorentzCLM 1 A ψ) (schwartzLorentzCLM k A F) := by
  ext x
  rw [schwartzLorentzCLM_apply, schwartzPrepend_apply, schwartzPrepend_apply,
    schwartzLorentzCLM_apply, schwartzLorentzCLM_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzLorentzCLM_schwartzChain (r : ℕ) (A : SL2C)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzLorentzCLM r A (schwartzChain r ψ) =
      schwartzChain r (fun i => schwartzLorentzCLM 1 A (ψ i)) := by
  induction r with
  | zero =>
    dsimp [schwartzChain]
    exact schwartzLorentzCLM_fin0_vac A
  | succ k ih =>
    dsimp [schwartzChain]
    rw [schwartzLorentzCLM_schwartzPrepend, ih]
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzPTConj_fin0_vac :
    schwartzPTConj 0 (momentumWavepacketSchwartz 0 0) =
      momentumWavepacketSchwartz 0 0 := by
  ext x
  rw [schwartzPTConj_apply]
  have hx1 : -x = 0 := Subsingleton.elim _ _
  have hx2 : x = 0 := Subsingleton.elim _ _
  rw [hx1, hx2, momentumWavepacketSchwartz_zero_eval_zero, star_one]

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzPTConj_schwartzPrepend (k : ℕ)
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (F : SchwartzMap (Fin k → Fin 4 → ℝ) ℂ) :
    schwartzPTConj (k + 1) (schwartzPrepend k ψ F) =
      schwartzPrepend k (schwartzPTConj 1 ψ) (schwartzPTConj k F) := by
  ext x
  rw [schwartzPTConj_apply, schwartzPrepend_apply, schwartzPrepend_apply,
    schwartzPTConj_apply, schwartzPTConj_apply]
  have hL : (fun _ : Fin 1 => (-x) 0) = -fun _ : Fin 1 => x 0 := rfl
  have hR : (fun u : Fin k => (-x) (Fin.succ u)) = -fun u : Fin k => x (Fin.succ u) := rfl
  rw [hL, hR, star_mul']

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzPTConj_schwartzChain (r : ℕ)
    (ψ : Fin r → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzPTConj r (schwartzChain r ψ) =
      schwartzChain r (fun i => schwartzPTConj 1 (ψ i)) := by
  induction r with
  | zero =>
    dsimp [schwartzChain]
    exact schwartzPTConj_fin0_vac
  | succ k ih =>
    dsimp [schwartzChain]
    rw [schwartzPTConj_schwartzPrepend, ih]
    rfl

lemma wightmanIndexedVec_indexedChain_finsetSum_pi {κ : Type*} [Fintype κ]
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (r : ℕ)
    (g : Fin r → κ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData r (indexedChain ι r (fun i => ∑ a : κ, g i a)) =
      ∑ c : Fin r → κ, wightmanIndexedVec WData r (indexedChain ι r (fun i => g i (c i))) := by
  unfold wightmanIndexedVec
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [indexedChain_apply]
  have h_pt : (fun i : Fin r => (∑ a : κ, g i a) (γ i)) =
      fun i : Fin r => ∑ a : κ, g i a (γ i) := by
    funext i
    rw [Finset.sum_apply]
  rw [h_pt, schwartzChain_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [indexedChain_apply]

lemma lorentzIndexedSchwartz_indexedChain (R : HolomorphicLorentzRep ι) (r : ℕ) (A : SL2C)
    (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    lorentzIndexedSchwartz R r A (indexedChain ι r Ψ) =
      indexedChain ι r (fun i => lorentzIndexedTest R A (Ψ i)) := by
  funext γ
  dsimp [lorentzIndexedSchwartz]
  rw [indexedChain_apply]
  dsimp only [lorentzIndexedTest]
  rw [schwartzChain_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [indexedChain_apply, schwartzLorentzCLM_schwartzChain, schwartzChain_smul]

theorem wightmanSpinorLorentz_indexedChain
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    (A : SL2C) (r : ℕ) (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanSpinorLorentz WData hP A (wightmanIndexedVec WData r (indexedChain ι r Ψ)) =
      wightmanIndexedVec WData r (indexedChain ι r (fun i => lorentzIndexedTest R A (Ψ i))) := by
  rw [wightmanSpinorLorentz_wightmanIndexedVec, lorentzIndexedSchwartz_indexedChain]

lemma pctIndexedSchwartz_indexedChain {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (η : ℂ) (r : ℕ) (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (μ : Fin r → ι) :
    pctIndexedSchwartz S η r (indexedChain ι r Ψ) μ =
      (η ^ (r * (r - 1) / 2)) •
        indexedChain ι r (fun i => pctIndexedTest S (Ψ i)) μ := by
  dsimp [pctIndexedSchwartz]
  congr 1
  rw [indexedChain_apply]
  dsimp only [pctIndexedTest]
  rw [schwartzChain_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [indexedChain_apply, schwartzPTConj_schwartzChain, schwartzChain_smul]

theorem wightmanPCTEquiv_indexedChain
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (WData : WightmanPositiveData R S) (hP : PoincareCovariant R WData.W)
    {η : ℂ} (hpct : WightmanPCT η R WData.W) (hε : R.HasSpinParity η)
    (r : ℕ) (Ψ : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanPCTEquiv WData hP hpct hε (wightmanIndexedVec WData r (indexedChain ι r Ψ)) =
      (η ^ (r * (r - 1) / 2)) •
        wightmanIndexedVec WData r (indexedChain ι r (fun i => pctIndexedTest S (Ψ i))) := by
  rw [wightmanPCTEquiv_wightmanIndexedVec]
  unfold wightmanIndexedVec
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [pctIndexedSchwartz_indexedChain, map_smul]

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_schwartzPTConj_one
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (q : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (schwartzPTConj 1 ψ) q = star (minkowskiFourier ψ q) := by
  change minkowskiFourier (schwartzConj (schwartzNeg 1 ψ)) q = _
  rw [minkowskiFourier_schwartzConj_one]
  congr 1
  dsimp [minkowskiFourier]
  refine Eq.trans (integral_neg_eq_self (μ := volume) _).symm ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [neg_neg, Fin.sum_univ_one, Fin.sum_univ_one]
  congr 2
  have hm : minkowskiInner (-q 0) ((-x) 0) = minkowskiInner (q 0) (x 0) := by
    simp [minkowskiInner_explicit]
  rw [hm]

omit [Fintype ι] [DecidableEq ι] in
def IsIsolatedShellSupported (m M : ℝ)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) : Prop :=
  (∃ K : Set (Fin 4 → ℝ), IsClosed K ∧
    (∀ q ∈ K, 0 < q 0 ∧ minkowskiInner q q < M ^ 2) ∧
    ∀ (γ : ι) (q : Fin 4 → ℝ), q ∉ K → minkowskiFourier (Ψ γ) (fun _ => -q) = 0) ∧
  ∀ γ : ι, HasCompactSupport (fun p : Fin 3 → ℝ =>
    minkowskiFourier (Ψ γ) (fun _ => -massShellVec m p))

omit [Fintype ι] [DecidableEq ι] in
lemma isIsolatedShellSupported_sub {m M : ℝ}
    {Ψ₁ Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h₁ : IsIsolatedShellSupported m M Ψ₁) (h₂ : IsIsolatedShellSupported m M Ψ₂) :
    IsIsolatedShellSupported m M (fun γ => Ψ₁ γ - Ψ₂ γ) := by
  rcases h₁ with ⟨⟨K₁, hK₁_cl, hK₁_bd, hK₁_z⟩, h₁_cs⟩
  rcases h₂ with ⟨⟨K₂, hK₂_cl, hK₂_bd, hK₂_z⟩, h₂_cs⟩
  refine ⟨⟨K₁ ∪ K₂, hK₁_cl.union hK₂_cl, fun q hq => ?_, fun γ q hq => ?_⟩, fun γ => ?_⟩
  · rcases hq with hq1 | hq2
    · exact hK₁_bd q hq1
    · exact hK₂_bd q hq2
  · rw [Set.mem_union, not_or] at hq
    rw [← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply, minkowskiFourierCLM_apply,
      minkowskiFourierCLM_apply, hK₁_z γ q hq.1, hK₂_z γ q hq.2, sub_zero]
  · have h_eq : (fun p : Fin 3 → ℝ =>
        minkowskiFourier (Ψ₁ γ - Ψ₂ γ) (fun _ => -massShellVec m p)) =
        (fun p => minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p)) -
          fun p => minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p) := by
      ext p
      rw [← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply,
        minkowskiFourierCLM_apply, minkowskiFourierCLM_apply]
      rfl
    rw [h_eq]
    exact (h₁_cs γ).sub (h₂_cs γ)

omit [Fintype ι] [DecidableEq ι] in
lemma isIsolatedShellSupported_finsetSum {κ : Type*} [Fintype κ] {m M : ℝ}
    (Ψ : κ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hΨ : ∀ b : κ, IsIsolatedShellSupported m M (Ψ b)) :
    IsIsolatedShellSupported m M (fun γ => ∑ b : κ, Ψ b γ) := by
  choose K hK_cl hK_bd hK_z using fun b => (hΨ b).1
  have hK_cs : ∀ (b : κ) (γ : ι), HasCompactSupport (fun p : Fin 3 → ℝ =>
      minkowskiFourier (Ψ b γ) (fun _ => -massShellVec m p)) := fun b => (hΨ b).2
  refine ⟨⟨⋃ b : κ, K b, isClosed_iUnion_of_finite hK_cl, fun q hq => ?_, fun γ q hq => ?_⟩,
    fun γ => ?_⟩
  · rw [Set.mem_iUnion] at hq
    rcases hq with ⟨b, hb⟩
    exact hK_bd b q hb
  · rw [Set.mem_iUnion, not_exists] at hq
    rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [minkowskiFourierCLM_apply]
    exact hK_z b γ q (hq b)
  · have h_eq : (fun p : Fin 3 → ℝ =>
        minkowskiFourier (∑ b : κ, Ψ b γ) (fun _ => -massShellVec m p)) =
        fun p => ∑ b : κ, minkowskiFourier (Ψ b γ) (fun _ => -massShellVec m p) := by
      ext p
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply]
      exact Finset.sum_congr rfl fun b _ => minkowskiFourierCLM_apply 1 (Ψ b γ) _
    rw [h_eq]
    refine HasCompactSupport.of_support_subset_isCompact
      (Finset.isCompact_biUnion Finset.univ fun b _ => (hK_cs b γ).isCompact) ?_
    intro p hp
    rw [Function.mem_support] at hp
    by_contra hnot
    apply hp
    refine Finset.sum_eq_zero fun b _ => ?_
    refine image_eq_zero_of_notMem_tsupport
      (f := fun p : Fin 3 → ℝ => minkowskiFourier (Ψ b γ) (fun _ => -massShellVec m p))
      fun hpb => hnot ?_
    exact Set.mem_biUnion (Finset.mem_univ b) hpb

lemma isIsolatedShellSupported_haagRuelleIndexedTest
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    IsIsolatedShellSupported m M (haagRuelleIndexedTest D s f t) := by
  refine ⟨⟨tsupport (massShellCutoff m M D.hm D.hM), isClosed_tsupport _, fun q hq => ?_,
      fun γ q hq => ?_⟩, fun γ => ?_⟩
  · have hb := tsupport_massShellCutoff_bounds D.hm D.hM hq
    exact ⟨lt_of_lt_of_le (div_pos D.hm (by norm_num)) hb.1, hb.2.2⟩
  · exact minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
      (dualModeWavepacket D s γ f) t hq
  · have h_eq : (fun p : Fin 3 → ℝ =>
        minkowskiFourier (haagRuelleIndexedTest D s f t γ) (fun _ => -massShellVec m p)) =
        fun p => D.dual_w s p γ * f.amp p := by
      ext p
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply]
    rw [h_eq]
    exact f.compactSupport.mul_left

lemma isIsolatedShellSupported_lorentzIndexedTest
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (A : SL2C) (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    IsIsolatedShellSupported m M (lorentzIndexedTest R A (haagRuelleIndexedTest D s f t)) := by
  let L_inv : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' (lorentzOfSL2C A⁻¹))
  let K : Set (Fin 4 → ℝ) := L_inv ⁻¹' tsupport (massShellCutoff m M D.hm D.hM)
  refine ⟨⟨K, (isClosed_tsupport _).preimage L_inv.continuous, fun q hq => ?_,
      fun γ q hq => ?_⟩, fun γ => ?_⟩
  · let q' : Fin 4 → ℝ := (lorentzOfSL2C A⁻¹).mulVec q
    have hq' : q' ∈ tsupport (massShellCutoff m M D.hm D.hM) := hq
    have hb := tsupport_massShellCutoff_bounds D.hm D.hM hq'
    have h_abs := abs_le.mp hb.2.1
    have h_sq4 := massShellGapDelta_four_le_sq (m := m) (M := M)
    have hq'_pos_sq : 0 < minkowskiInner q' q' := by linarith [sq_pos_of_pos D.hm]
    have hq'_cone : q' ∈ forward_light_cone :=
      ⟨lt_of_lt_of_le (div_pos D.hm (by norm_num)) hb.1, hq'_pos_sq⟩
    have hq_cone := lorentzOfSL2C_preserves_forward_light_cone A hq'_cone
    have hq_eq : (lorentzOfSL2C A).mulVec q' = q := by
      dsimp [q']
      rw [Matrix.mulVec_mulVec, ← lorentzOfSL2C_mul, mul_inv_cancel, lorentzOfSL2C_one,
        Matrix.one_mulVec]
    rw [hq_eq] at hq_cone
    have hmink : minkowskiInner q q = minkowskiInner q' q' := by
      conv_lhs => rw [← hq_eq]
      exact minkowskiInner_lorentz A q' q'
    exact ⟨hq_cone.1, hmink ▸ hb.2.2⟩
  · dsimp [lorentzIndexedTest]
    rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [map_smul, _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
      minkowskiFourier_schwartzLorentzCLM_one]
    have h_arg : lorentzEquiv 1 A⁻¹ (fun _ : Fin 1 => -q) =
        fun _ : Fin 1 => -((lorentzOfSL2C A⁻¹).mulVec q) := by
      ext i μ
      change (lorentzOfSL2C A⁻¹).mulVec (-q) μ = -((lorentzOfSL2C A⁻¹).mulVec q) μ
      rw [Matrix.mulVec_neg]
      rfl
    have hq' : (lorentzOfSL2C A⁻¹).mulVec q ∉ tsupport (massShellCutoff m M D.hm D.hM) := hq
    dsimp [haagRuelleIndexedTest]
    rw [h_arg, minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
      (dualModeWavepacket D s α f) t hq', mul_zero]
  · have h_eq : (fun p : Fin 3 → ℝ =>
        minkowskiFourier (lorentzIndexedTest R A (haagRuelleIndexedTest D s f t) γ)
          (fun _ => -massShellVec m p)) =
        fun p => (∑ α : ι, R.rep A⁻¹ α γ * D.dual_w s (massShellBoost m A⁻¹ p) α) *
          f.amp (massShellBoost m A⁻¹ p) := by
      ext p
      dsimp [lorentzIndexedTest]
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_smul, _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
        minkowskiFourier_schwartzLorentzCLM_one]
      have h_arg : lorentzEquiv 1 A⁻¹ (fun _ : Fin 1 => -massShellVec m p) =
          fun _ : Fin 1 => -massShellVec m (massShellBoost m A⁻¹ p) := by
        ext i μ
        change (lorentzOfSL2C A⁻¹).mulVec (-massShellVec m p) μ = _
        rw [Matrix.mulVec_neg, lorentzOfSL2C_mulVec_massShellVec D.hm]
      rw [h_arg]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply]
      ring
    rw [h_eq]
    have h_cs : HasCompactSupport (fun p : Fin 3 → ℝ => f.amp (massShellBoost m A⁻¹ p)) := by
      refine HasCompactSupport.of_support_subset_isCompact
        (f.compactSupport.isCompact.image (contDiff_massShellBoost D.hm A).continuous) ?_
      intro p hp
      rw [Function.mem_support] at hp
      exact ⟨massShellBoost m A⁻¹ p, subset_tsupport _ (Function.mem_support.mpr hp),
        massShellBoost_comp_inv D.hm A p⟩
    exact h_cs.mul_left

lemma isIsolatedShellSupported_pctIndexedTest
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (s : Fin D.mode.ν) (f : SmoothWavepacket) (t : ℝ) :
    IsIsolatedShellSupported m M (pctIndexedTest S (haagRuelleIndexedTest D s f t)) := by
  refine ⟨⟨tsupport (massShellCutoff m M D.hm D.hM), isClosed_tsupport _, fun q hq => ?_,
      fun μ q hq => ?_⟩, fun μ => ?_⟩
  · have hb := tsupport_massShellCutoff_bounds D.hm D.hM hq
    exact ⟨lt_of_lt_of_le (div_pos D.hm (by norm_num)) hb.1, hb.2.2⟩
  · dsimp [pctIndexedTest]
    rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [map_smul, _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
      minkowskiFourier_schwartzPTConj_one]
    dsimp [haagRuelleIndexedTest]
    rw [minkowskiFourier_haagRuelleTestFn_eq_zero_of_notMem D.hm D.hM
      (dualModeWavepacket D s α f) t hq, map_zero, mul_zero]
  · have h_eq : (fun p : Fin 3 → ℝ =>
        minkowskiFourier (pctIndexedTest S (haagRuelleIndexedTest D s f t) μ)
          (fun _ => -massShellVec m p)) =
        fun p => (∑ α : ι, pctMatrix S α μ * star (D.dual_w s p α)) * star (f.amp p) := by
      ext p
      dsimp [pctIndexedTest]
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_smul, _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
        minkowskiFourier_schwartzPTConj_one]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply, map_mul]
      ring
    rw [h_eq]
    exact (HasCompactSupport.comp_left f.compactSupport (star_zero ℂ)).mul_left

lemma twoPoint_borchersConcat_eq_massShell_of_right_closed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (β : Fin 2 → ι) (ψ₁ ψ₂ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (K : Set (Fin 4 → ℝ)) (hK_closed : IsClosed K)
    (hK_bounds : ∀ q ∈ K, 0 < q 0 ∧ minkowskiInner q q < M ^ 2)
    (hψ₂ : ∀ q : Fin 4 → ℝ, q ∉ K → minkowskiFourier ψ₂ (fun _ => -q) = 0) :
    D.wightman.WData.W 2 β (borchersConcatSchwartz 1 1 ψ₁ ψ₂) =
      massShellTwoPointW m D.C_shell D.hC 2 β (borchersConcatSchwartz 1 1 ψ₁ ψ₂) := by
  refine D.twoPoint_shell β (borchersConcatSchwartz 1 1 ψ₁ ψ₂) ?_
  let U : Set (Fin 2 → Fin 4 → ℝ) := { p | -p 1 ∉ K }
  have hU_open : IsOpen U :=
    hK_closed.isOpen_compl.preimage (by fun_prop : Continuous fun p : Fin 2 → Fin 4 → ℝ => -p 1)
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
    intro hp_k
    have hb := hK_bounds (p 0) hp_k
    rcases h_cases with hp0 | hpM
    · rw [hp0] at hb
      exact (lt_irrefl (0 : ℝ)) hb.1
    · linarith [hpM.2, hb.2]
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

lemma continuous_minkowskiFourier_on_massShell {m : ℝ}
    (ψ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    Continuous (fun p : Fin 3 → ℝ => minkowskiFourier ψ (fun _ => -massShellVec m p)) := by
  have h_eq : (fun p : Fin 3 → ℝ => minkowskiFourier ψ (fun _ => -massShellVec m p)) =
      fun p : Fin 3 → ℝ => (minkowskiFourierCLM 1 ψ) (fun _ => -massShellVec m p) := by
    ext p
    rw [minkowskiFourierCLM_apply]
  rw [h_eq]
  exact (minkowskiFourierCLM 1 ψ).continuous.comp
    (continuous_pi fun _ => (continuous_massShellVec m).neg)

lemma wightmanIndexedVec_one_eq_sum (WData : WightmanPositiveData R S)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    wightmanIndexedVec WData 1 (indexedChain ι 1 (fun _ => Ψ)) =
      ∑ α : ι, wightmanSchwartzVec WData 1 (fun _ => α) (Ψ α) := by
  unfold wightmanIndexedVec
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h_eq : (fun _ : Fin 1 => α) = (Equiv.funUnique (Fin 1) ι).symm α := by
    ext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h_eq, indexedChain_apply]
  have h_arg : (fun i : Fin 1 => Ψ (((Equiv.funUnique (Fin 1) ι).symm α) i)) =
      fun _ : Fin 1 => Ψ α := by
    funext i
    rw [Subsingleton.elim i 0]
    rfl
  rw [h_arg]
  dsimp [schwartzChain]
  rw [schwartzPrepend_zero_vac]

lemma inner_wightmanIndexedVec_one_of_isolatedShellSupported
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (Ψ₁ Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h₁ : IsIsolatedShellSupported m M Ψ₁) (h₂ : IsIsolatedShellSupported m M Ψ₂) :
    ⟪wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₁)),
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₂))⟫_ℂ =
      ∫ p : Fin 3 → ℝ,
        ∑ s' : Fin D.mode.ν,
          star (modeProj D.mode p
            (fun γ => minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p)) s') *
            modeProj D.mode p
              (fun γ => minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p)) s' := by
  rcases h₁ with ⟨_, hcs₁⟩
  rcases h₂ with ⟨⟨K₂, hK₂_cl, hK₂_bd, hK₂_z⟩, hcs₂⟩
  rw [wightmanIndexedVec_one_eq_sum, wightmanIndexedVec_one_eq_sum, sum_inner]
  simp_rw [inner_sum]
  let g₁ : ι → (Fin 3 → ℝ) → ℂ := fun α₁ p => minkowskiFourier (Ψ₁ α₁) (fun _ => -massShellVec m p)
  let g₂ : ι → (Fin 3 → ℝ) → ℂ := fun α₂ p => minkowskiFourier (Ψ₂ α₂) (fun _ => -massShellVec m p)
  have hg₁_cont : ∀ α₁ : ι, Continuous (g₁ α₁) := fun α₁ =>
    continuous_minkowskiFourier_on_massShell (Ψ₁ α₁)
  have hg₂_cont : ∀ α₂ : ι, Continuous (g₂ α₂) := fun α₂ =>
    continuous_minkowskiFourier_on_massShell (Ψ₂ α₂)
  have h_term : ∀ α₁ α₂ : ι,
      ⟪wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₁) (Ψ₁ α₁),
        wightmanSchwartzVec D.wightman.WData 1 (fun _ => α₂) (Ψ₂ α₂)⟫_ℂ =
      ∫ p : Fin 3 → ℝ, (star (g₁ α₁ p) * g₂ α₂ p) *
        (∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p) := by
    intro α₁ α₂
    rw [inner_wightmanSchwartzVec, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    have h_shell : ∀ γ : ι,
        D.wightman.WData.W (1 + 1)
          (Fin.append ((fun _ : Fin 1 => γ) ∘ Fin.rev) (fun _ : Fin 1 => α₂))
          (borchersConcatSchwartz 1 1 (Ψ₁ α₁) (Ψ₂ α₂)) =
        ∫ p : Fin 3 → ℝ,
          massShellWeight m D.C_shell ![γ, α₂] p * (star (g₁ α₁ p) * g₂ α₂ p) := by
      intro γ
      have h_app : (Fin.append ((fun _ : Fin 1 => γ) ∘ Fin.rev) (fun _ : Fin 1 => α₂)) =
          ![γ, α₂] := by
        ext i; fin_cases i <;> rfl
      rw [h_app]
      have h_two := twoPoint_borchersConcat_eq_massShell_of_right_closed D ![γ, α₂]
        (Ψ₁ α₁) (Ψ₂ α₂) K₂ hK₂_cl hK₂_bd (hK₂_z α₂)
      rw [h_two, massShellTwoPointW_two_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      dsimp only
      rw [minkowskiFourier_split_one_one_twoPointMomentum (massShellVec m p)
        (Ψ₁ α₁) (Ψ₂ α₂) _ (borchersConcatSchwartz_apply 1 1 _ _)]
      rfl
    have h_sum_step :
        (∑ γ : ι,
          (∏ i : Fin 1, S.C α₁ ((Equiv.funUnique (Fin 1) ι).symm γ i)) *
            D.wightman.WData.W (1 + 1)
              (Fin.append ((Equiv.funUnique (Fin 1) ι).symm γ ∘ Fin.rev) (fun _ => α₂))
              (borchersConcatSchwartz 1 1 (Ψ₁ α₁) (Ψ₂ α₂))) =
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
      rcases D.hC.2 ![γ, α₂] with ⟨B_w, _, hBw⟩
      let K_int : (Fin 3 → ℝ) → ℝ := fun p =>
        ‖S.C α₁ γ‖ * B_w * ‖star (g₁ α₁ p) * g₂ α₂ p‖
      have h_prod_cont : Continuous (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
        (hg₁_cont α₁).star.mul (hg₂_cont α₂)
      have h_prod_supp : HasCompactSupport (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
        (hcs₂ α₂).mul_left
      have hK_int : Integrable K_int volume :=
        ((h_prod_cont.norm).integrable_of_hasCompactSupport h_prod_supp.norm).const_mul
          (‖S.C α₁ γ‖ * B_w)
      have h_meas : Measurable (fun p : Fin 3 → ℝ =>
          S.C α₁ γ * (massShellWeight m D.C_shell ![γ, α₂] p * (star (g₁ α₁ p) * g₂ α₂ p))) :=
        measurable_const.mul ((measurable_massShellWeight D.hC ![γ, α₂]).mul h_prod_cont.measurable)
      refine hK_int.mono' h_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
      rw [norm_mul, norm_mul]
      calc ‖S.C α₁ γ‖ * (‖massShellWeight m D.C_shell ![γ, α₂] p‖ *
            ‖star (g₁ α₁ p) * g₂ α₂ p‖)
          ≤ ‖S.C α₁ γ‖ * (B_w * ‖star (g₁ α₁ p) * g₂ α₂ p‖) := by gcongr; exact hBw p
        _ = K_int p := by dsimp [K_int]; ring
    rw [← integral_finsetSum Finset.univ fun γ _ => h_int_each γ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    dsimp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => by ring
  simp_rw [h_term]
  have h_prod_int : ∀ α₁ α₂ : ι, Integrable
      (fun p : Fin 3 → ℝ => (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p) volume := by
    intro α₁ α₂
    have h_prod_cont : Continuous (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
      (hg₁_cont α₁).star.mul (hg₂_cont α₂)
    have h_prod_supp : HasCompactSupport (fun p : Fin 3 → ℝ => star (g₁ α₁ p) * g₂ α₂ p) :=
      (hcs₂ α₂).mul_left
    have h_meas_w : Measurable (fun p : Fin 3 → ℝ =>
        ∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p) :=
      Finset.measurable_sum Finset.univ fun δ _ =>
        measurable_const.mul (measurable_massShellWeight D.hC ![δ, α₂])
    have hB : ∀ δ : ι, ∃ B_w : ℝ, 0 ≤ B_w ∧
        ∀ p : Fin 3 → ℝ, ‖massShellWeight m D.C_shell ![δ, α₂] p‖ ≤ B_w :=
      fun δ => D.hC.2 ![δ, α₂]
    choose B_w hBw_nn hBw using hB
    let C_bd : ℝ := ∑ δ : ι, ‖S.C α₁ δ‖ * B_w δ
    have h_dom_int : Integrable (fun p : Fin 3 → ℝ =>
        C_bd * ‖star (g₁ α₁ p) * g₂ α₂ p‖) volume :=
      ((h_prod_cont.norm).integrable_of_hasCompactSupport h_prod_supp.norm).const_mul C_bd
    refine h_dom_int.mono' (h_prod_cont.measurable.mul h_meas_w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    have h_sum_le :
        ‖∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p‖ ≤ C_bd := by
      calc ‖∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p‖
          ≤ ∑ δ : ι, ‖S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p‖ := norm_sum_le _ _
        _ ≤ ∑ δ : ι, ‖S.C α₁ δ‖ * B_w δ := by
            refine Finset.sum_le_sum fun δ _ => ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hBw δ p) (norm_nonneg _)
        _ = C_bd := rfl
    exact (mul_le_mul_of_nonneg_left h_sum_le (norm_nonneg _)).trans (le_of_eq (mul_comm _ _))
  have h_sum_int :
      (∑ α₁ : ι, ∑ α₂ : ι, ∫ p : Fin 3 → ℝ, (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p) =
      ∫ p : Fin 3 → ℝ, ∑ α₁ : ι, ∑ α₂ : ι, (star (g₁ α₁ p) * g₂ α₂ p) *
        ∑ δ : ι, S.C α₁ δ * massShellWeight m D.C_shell ![δ, α₂] p := by
    symm
    rw [integral_finsetSum Finset.univ fun α₁ _ =>
      integrable_finsetSum Finset.univ fun α₂ _ => h_prod_int α₁ α₂]
    refine Finset.sum_congr rfl fun α₁ _ => ?_
    exact integral_finsetSum Finset.univ fun α₂ _ => h_prod_int α₁ α₂
  rw [h_sum_int]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact (sum_star_mul_modeProj D.mode p (fun α => g₁ α p) (fun α => g₂ α p)).symm

lemma wightmanIndexedVec_one_eq_of_modeProj_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (Ψ₁ Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h₁ : IsIsolatedShellSupported m M Ψ₁) (h₂ : IsIsolatedShellSupported m M Ψ₂)
    (h_proj : ∀ (s' : Fin D.mode.ν) (p : Fin 3 → ℝ),
      modeProj D.mode p (fun γ => minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p)) s' =
      modeProj D.mode p (fun γ => minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p)) s') :
    wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₁)) =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₂)) := by
  have hdiff : wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₁)) -
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₂)) =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => fun γ => Ψ₁ γ - Ψ₂ γ)) := by
    rw [wightmanIndexedVec_one_eq_sum, wightmanIndexedVec_one_eq_sum, wightmanIndexedVec_one_eq_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun γ _ => (map_sub _ _ _).symm
  rw [← sub_eq_zero, hdiff, ← inner_self_eq_zero (𝕜 := ℂ)]
  have h_sub := isIsolatedShellSupported_sub h₁ h₂
  rw [inner_wightmanIndexedVec_one_of_isolatedShellSupported D _ _ h_sub h_sub]
  have h_zero : (fun p : Fin 3 → ℝ =>
      ∑ s' : Fin D.mode.ν,
        star (modeProj D.mode p (fun γ => minkowskiFourier (Ψ₁ γ - Ψ₂ γ)
            (fun _ => -massShellVec m p)) s') *
          modeProj D.mode p (fun γ => minkowskiFourier (Ψ₁ γ - Ψ₂ γ)
            (fun _ => -massShellVec m p)) s') = fun _ => 0 := by
    ext p
    refine Finset.sum_eq_zero fun s' _ => ?_
    have hz : modeProj D.mode p (fun γ => minkowskiFourier (Ψ₁ γ - Ψ₂ γ)
        (fun _ => -massShellVec m p)) s' = 0 := by
      dsimp [modeProj]
      have h_sub_proj :
          (∑ γ : ι, D.mode.w s' p γ *
            minkowskiFourier (Ψ₁ γ - Ψ₂ γ) (fun _ => -massShellVec m p)) =
          modeProj D.mode p (fun γ => minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p)) s' -
          modeProj D.mode p (fun γ => minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p)) s' := by
        dsimp [modeProj]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [← minkowskiFourierCLM_apply, map_sub, _root_.sub_apply, minkowskiFourierCLM_apply,
          minkowskiFourierCLM_apply, mul_sub]
      rw [h_sub_proj, h_proj s' p, sub_self]
    rw [hz, mul_zero]
  rw [h_zero, integral_zero]

theorem lorentz_haagRuelleVacCreate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (s : Fin P.mode.ν) (f : SmoothWavepacket) (t t' : ℝ) :
    P.lorentzEquiv A (haagRuelleVacCreate P.toIsolatedMassShellData s f t) =
      ∑ s' : Fin P.mode.ν,
        haagRuelleVacCreate P.toIsolatedMassShellData s'
          (lorentzModeWavepacket P.modeData A s' s f) t' := by
  let D := P.toIsolatedMassShellData
  let Ψ₁ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    lorentzIndexedTest R A (haagRuelleIndexedTest D s f t)
  let Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun γ => ∑ s' : Fin P.mode.ν,
      haagRuelleIndexedTest D s' (lorentzModeWavepacket P.modeData A s' s f) t' γ
  have hL : P.lorentzEquiv A (haagRuelleVacCreate D s f t) =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₁)) := by
    have h_vac_eq : haagRuelleVacCreate D s f t =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ => haagRuelleIndexedTest D s f t)) := by
      unfold haagRuelleVacCreate haagRuelleApply indexedChain
      rfl
    rw [h_vac_eq]
    exact wightmanSpinorLorentz_indexedChain D.wightman.WData D.wightman.poincare A 1
      (fun _ => haagRuelleIndexedTest D s f t)
  have hR : (∑ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (lorentzModeWavepacket P.modeData A s' s f) t') =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₂)) := by
    have h_each : ∀ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (lorentzModeWavepacket P.modeData A s' s f) t' =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ =>
            haagRuelleIndexedTest D s' (lorentzModeWavepacket P.modeData A s' s f) t')) := by
      intro s'
      unfold haagRuelleVacCreate haagRuelleApply indexedChain
      rfl
    simp_rw [h_each, wightmanIndexedVec_one_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← map_sum]
  rw [hL, hR]
  refine wightmanIndexedVec_one_eq_of_modeProj_eq D Ψ₁ Ψ₂
    (isIsolatedShellSupported_lorentzIndexedTest D A s f t)
    (isIsolatedShellSupported_finsetSum _ fun s' =>
      isIsolatedShellSupported_haagRuelleIndexedTest D s'
        (lorentzModeWavepacket P.modeData A s' s f) t')
    fun s' p => ?_
  dsimp [modeProj]
  have h_lhs :
      (∑ γ : ι, P.mode.w s' p γ * minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p)) =
      wignerModeMatrix P.modeData A p s' s * f.amp (massShellBoost m A⁻¹ p) := by
    have h_term : ∀ γ : ι,
        P.mode.w s' p γ * minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p) =
          ∑ α : ι,
            P.mode.w s' p γ * R.rep A⁻¹ α γ *
              (P.dual_w s (massShellBoost m A⁻¹ p) α * f.amp (massShellBoost m A⁻¹ p)) := by
      intro γ
      dsimp [Ψ₁, lorentzIndexedTest]
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_smul, _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
        minkowskiFourier_schwartzLorentzCLM_one]
      have h_arg : lorentzEquiv 1 A⁻¹ (fun _ : Fin 1 => -massShellVec m p) =
          fun _ : Fin 1 => -massShellVec m (massShellBoost m A⁻¹ p) := by
        ext i μ
        change (lorentzOfSL2C A⁻¹).mulVec (-massShellVec m p) μ = _
        rw [Matrix.mulVec_neg, lorentzOfSL2C_mulVec_massShellVec D.hm]
      rw [h_arg]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply]
      ring
    rw [Finset.sum_congr rfl fun γ _ => h_term γ, Finset.sum_comm]
    dsimp [wignerModeMatrix, PoincareIsolatedMassShellData.modeData]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    calc (∑ γ : ι, P.mode.w s' p γ * R.rep A⁻¹ α γ *
            (P.dual_w s (massShellBoost m A⁻¹ p) α *
              f.amp (massShellBoost m A⁻¹ p)))
        = ∑ γ : ι, (P.mode.w s' p γ * R.rep A⁻¹ α γ *
            P.dual_w s (massShellBoost m A⁻¹ p) α) *
              f.amp (massShellBoost m A⁻¹ p) :=
          Finset.sum_congr rfl fun γ _ => by ring
      _ = (∑ γ : ι, P.mode.w s' p γ * R.rep A⁻¹ α γ *
            P.dual_w s (massShellBoost m A⁻¹ p) α) *
              f.amp (massShellBoost m A⁻¹ p) :=
          (Finset.sum_mul _ _ _).symm
  have h_rhs :
      (∑ γ : ι, P.mode.w s' p γ * minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p)) =
      wignerModeMatrix P.modeData A p s' s * f.amp (massShellBoost m A⁻¹ p) := by
    have h_term : ∀ γ : ι,
        P.mode.w s' p γ * minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p) =
          ∑ b : Fin P.mode.ν,
            (P.mode.w s' p γ * P.dual_w b p γ) *
              (wignerModeMatrix P.modeData A p b s * f.amp (massShellBoost m A⁻¹ p)) := by
      intro γ
      dsimp [Ψ₂]
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [minkowskiFourierCLM_apply]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply,
        lorentzModeWavepacket_apply]
      ring
    rw [Finset.sum_congr rfl fun γ _ => h_term γ, Finset.sum_comm]
    have h_b : ∀ b : Fin P.mode.ν,
        (∑ γ : ι, P.mode.w s' p γ * P.dual_w b p γ *
            (wignerModeMatrix P.modeData A p b s * f.amp (massShellBoost m A⁻¹ p))) =
          (if s' = b then 1 else 0) *
            (wignerModeMatrix P.modeData A p b s * f.amp (massShellBoost m A⁻¹ p)) := by
      intro b
      rw [← Finset.sum_mul, P.dual_orthonormal s' b p]
    rw [Finset.sum_congr rfl fun b _ => h_b b, Finset.sum_eq_single s']
    · simp
    · intro b _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s'))
  rw [h_lhs, h_rhs]

theorem pct_haagRuelleVacCreate
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (s : Fin P.mode.ν) (f : SmoothWavepacket) (t t' : ℝ) :
    P.pctEquiv hε (haagRuelleVacCreate P.toIsolatedMassShellData s f t) =
      ∑ s' : Fin P.mode.ν,
        haagRuelleVacCreate P.toIsolatedMassShellData s'
          (pctModeWavepacket P.modeData s' s f) t' := by
  let D := P.toIsolatedMassShellData
  let Ψ₁ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    pctIndexedTest S (haagRuelleIndexedTest D s f t)
  let Ψ₂ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun γ => ∑ s' : Fin P.mode.ν,
      haagRuelleIndexedTest D s' (pctModeWavepacket P.modeData s' s f) t' γ
  have hL : P.pctEquiv hε (haagRuelleVacCreate D s f t) =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₁)) := by
    have h_vac_eq : haagRuelleVacCreate D s f t =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ => haagRuelleIndexedTest D s f t)) := by
      unfold haagRuelleVacCreate haagRuelleApply indexedChain
      rfl
    rw [h_vac_eq]
    have h_pct := wightmanPCTEquiv_indexedChain D.wightman.WData D.wightman.poincare
      D.wightman.toWightmanAxioms.wightmanPCT hε 1 (fun _ => haagRuelleIndexedTest D s f t)
    simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, one_smul] at h_pct
    exact h_pct
  have hR : (∑ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (pctModeWavepacket P.modeData s' s f) t') =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ₂)) := by
    have h_each : ∀ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (pctModeWavepacket P.modeData s' s f) t' =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ =>
            haagRuelleIndexedTest D s' (pctModeWavepacket P.modeData s' s f) t')) := by
      intro s'
      unfold haagRuelleVacCreate haagRuelleApply indexedChain
      rfl
    simp_rw [h_each, wightmanIndexedVec_one_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← map_sum]
  rw [hL, hR]
  refine wightmanIndexedVec_one_eq_of_modeProj_eq D Ψ₁ Ψ₂
    (isIsolatedShellSupported_pctIndexedTest D s f t)
    (isIsolatedShellSupported_finsetSum _ fun s' =>
      isIsolatedShellSupported_haagRuelleIndexedTest D s'
        (pctModeWavepacket P.modeData s' s f) t')
    fun s' p => ?_
  dsimp [modeProj]
  have h_lhs :
      (∑ γ : ι, P.mode.w s' p γ * minkowskiFourier (Ψ₁ γ) (fun _ => -massShellVec m p)) =
      pctModeMatrix P.modeData p s' s * star (f.amp p) := by
    have h_term : ∀ μ : ι,
        P.mode.w s' p μ * minkowskiFourier (Ψ₁ μ) (fun _ => -massShellVec m p) =
          ∑ α : ι,
            P.mode.w s' p μ * pctMatrix S α μ * star (P.dual_w s p α) * star (f.amp p) := by
      intro μ
      dsimp [Ψ₁, pctIndexedTest]
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [map_smul, _root_.smul_apply, smul_eq_mul, minkowskiFourierCLM_apply,
        minkowskiFourier_schwartzPTConj_one]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply, map_mul]
      dsimp [D]
      ring
    rw [Finset.sum_congr rfl fun μ _ => h_term μ, Finset.sum_comm]
    dsimp [pctModeMatrix, PoincareIsolatedMassShellData.modeData]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_mul]
  have h_rhs :
      (∑ γ : ι, P.mode.w s' p γ * minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p)) =
      pctModeMatrix P.modeData p s' s * star (f.amp p) := by
    have h_term : ∀ γ : ι,
        P.mode.w s' p γ * minkowskiFourier (Ψ₂ γ) (fun _ => -massShellVec m p) =
          ∑ b : Fin P.mode.ν,
            (P.mode.w s' p γ * P.dual_w b p γ) *
              (pctModeMatrix P.modeData p b s * star (f.amp p)) := by
      intro γ
      dsimp [Ψ₂]
      rw [← minkowskiFourierCLM_apply, map_sum, schwartzMap_sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [minkowskiFourierCLM_apply]
      dsimp [haagRuelleIndexedTest]
      rw [minkowskiFourier_haagRuelleTestFn_massShell, dualModeWavepacket_apply,
        pctModeWavepacket_apply]
      dsimp [D]
      ring
    rw [Finset.sum_congr rfl fun γ _ => h_term γ, Finset.sum_comm]
    have h_b : ∀ b : Fin P.mode.ν,
        (∑ γ : ι, P.mode.w s' p γ * P.dual_w b p γ *
            (pctModeMatrix P.modeData p b s * star (f.amp p))) =
          (if s' = b then 1 else 0) * (pctModeMatrix P.modeData p b s * star (f.amp p)) := by
      intro b
      rw [← Finset.sum_mul, P.dual_orthonormal s' b p]
    rw [Finset.sum_congr rfl fun b _ => h_b b, Finset.sum_eq_single s']
    · simp
    · intro b _ hne
      simp [Ne.symm hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s'))
  rw [h_lhs, h_rhs]

end PoincareMassShellAndOneParticle

section QuasiLocalChainEquivalence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma seminorm_comp_realCLM_le
    (T : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℝ] SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (l d : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ,
        SchwartzMap.seminorm ℝ l d (T φ) ≤
          C * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 φ := by
  have h_with := schwartz_withSeminorms ℝ (Fin 1 → Fin 4 → ℝ) ℂ
  let q_sem : Seminorm ℝ (SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :=
    (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ (l, d)).comp T.toLinearMap
  have hq_cont : Continuous q_sem := (h_with.continuous_seminorm (l, d)).comp T.continuous
  obtain ⟨s, C₀, _, h_bd⟩ := Seminorm.bound_of_continuous h_with q_sem hq_cont
  refine ⟨s, (C₀ : ℝ), NNReal.coe_nonneg C₀, fun φ => ?_⟩
  have h1 : SchwartzMap.seminorm ℝ l d (T φ) ≤
      (C₀ : ℝ) * (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ)) φ := by
    have h_le := h_bd φ
    exact le_trans h_le (le_of_eq (NNReal.smul_def _ _))
  have h2 : (s.sup (schwartzSeminormFamily ℝ (Fin 1 → Fin 4 → ℝ) ℂ)) φ ≤
      ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 φ := by
    refine Seminorm.finset_sup_apply_le (Finset.sum_nonneg fun p _ => apply_nonneg _ _)
      fun p hp => ?_
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    exact Finset.single_le_sum (fun p' _ => apply_nonneg (SchwartzMap.seminorm ℝ p'.1 p'.2) φ) hp
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg C₀))

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_realCLM
    (T : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℝ] SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t α => T (Ψ t α)) := by
  intro α l d
  obtain ⟨s, C₀, hC₀_nn, h_bd⟩ := seminorm_comp_realCLM_le T l d
  have h_each : ∀ p : s, ∃ (deg_p : ℕ) (C_p : ℝ), 0 ≤ C_p ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ p.1.1 p.1.2 (Ψ t α) ≤ C_p * (1 + |t|) ^ deg_p :=
    fun p => h α p.1.1 p.1.2
  choose deg_p C_p hCp_nn hCp_bd using h_each
  let deg : ℕ := Finset.univ.sup deg_p
  let C : ℝ := C₀ * ∑ p : s, C_p p
  refine ⟨deg, C, mul_nonneg hC₀_nn (Finset.sum_nonneg fun p _ => hCp_nn p), fun t => ?_⟩
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  refine (h_bd (Ψ t α)).trans ?_
  have h_sum : (∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (Ψ t α)) ≤
      (∑ p : s, C_p p) * (1 + |t|) ^ deg := by
    rw [← Finset.sum_attach s fun p => SchwartzMap.seminorm ℝ p.1 p.2 (Ψ t α), Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => (hCp_bd p t).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ht1 (Finset.le_sup (Finset.mem_univ p))) (hCp_nn p)
  calc C₀ * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (Ψ t α)
      ≤ C₀ * ((∑ p : s, C_p p) * (1 + |t|) ^ deg) := mul_le_mul_of_nonneg_left h_sum hC₀_nn
    _ = C * (1 + |t|) ^ deg := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestRapidDecay_realCLM
    (T : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℝ] SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t α => T (Ψ t α)) := by
  intro α l d N
  obtain ⟨s, C₀, hC₀_nn, h_bd⟩ := seminorm_comp_realCLM_le T l d
  have h_each : ∀ p : s, ∃ C_p : ℝ, 0 ≤ C_p ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ p.1.1 p.1.2 (Ψ t α) * (1 + |t|) ^ N ≤ C_p :=
    fun p => h α p.1.1 p.1.2 N
  choose C_p hCp_nn hCp_bd using h_each
  let C : ℝ := C₀ * ∑ p : s, C_p p
  refine ⟨C, mul_nonneg hC₀_nn (Finset.sum_nonneg fun p _ => hCp_nn p), fun t => ?_⟩
  have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
  calc SchwartzMap.seminorm ℝ l d (T (Ψ t α)) * (1 + |t|) ^ N
      ≤ (C₀ * ∑ p ∈ s, SchwartzMap.seminorm ℝ p.1 p.2 (Ψ t α)) * (1 + |t|) ^ N :=
        mul_le_mul_of_nonneg_right (h_bd (Ψ t α)) ht_nn
    _ = C₀ * ∑ p : s, SchwartzMap.seminorm ℝ p.1.1 p.1.2 (Ψ t α) * (1 + |t|) ^ N := by
        rw [mul_assoc, Finset.sum_mul, Finset.univ_eq_attach]
        congr 1
        exact (Finset.sum_attach s fun p =>
          SchwartzMap.seminorm ℝ p.1 p.2 (Ψ t α) * (1 + |t|) ^ N).symm
    _ ≤ C := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hCp_bd p t) hC₀_nn

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_finsetSum {κ : Type*} [Fintype κ]
    (Ψ : κ → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h : ∀ b : κ, IndexedTestPolyGrowth (Ψ b)) :
    IndexedTestPolyGrowth (fun t α => ∑ b : κ, Ψ b t α) := by
  intro α l d
  have h_each : ∀ b : κ, ∃ (deg_b : ℕ) (C_b : ℝ), 0 ≤ C_b ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ l d (Ψ b t α) ≤ C_b * (1 + |t|) ^ deg_b :=
    fun b => h b α l d
  choose deg_b C_b hCb_nn hCb_bd using h_each
  let deg : ℕ := Finset.univ.sup deg_b
  let C : ℝ := ∑ b : κ, C_b b
  refine ⟨deg, C, Finset.sum_nonneg fun b _ => hCb_nn b, fun t => ?_⟩
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc SchwartzMap.seminorm ℝ l d (∑ b : κ, Ψ b t α)
      ≤ ∑ b : κ, SchwartzMap.seminorm ℝ l d (Ψ b t α) := seminorm_finset_sum_le l d Finset.univ _
    _ ≤ ∑ b : κ, C_b b * (1 + |t|) ^ deg := by
        refine Finset.sum_le_sum fun b _ => (hCb_bd b t).trans ?_
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ ht1 (Finset.le_sup (Finset.mem_univ b))) (hCb_nn b)
    _ = C * (1 + |t|) ^ deg := (Finset.sum_mul _ _ _).symm

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestRapidDecay_finsetSum {κ : Type*} [Fintype κ]
    (Ψ : κ → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h : ∀ b : κ, IndexedTestRapidDecay (Ψ b)) :
    IndexedTestRapidDecay (fun t α => ∑ b : κ, Ψ b t α) := by
  intro α l d N
  have h_each : ∀ b : κ, ∃ C_b : ℝ, 0 ≤ C_b ∧
      ∀ t : ℝ, SchwartzMap.seminorm ℝ l d (Ψ b t α) * (1 + |t|) ^ N ≤ C_b :=
    fun b => h b α l d N
  choose C_b hCb_nn hCb_bd using h_each
  refine ⟨∑ b : κ, C_b b, Finset.sum_nonneg fun b _ => hCb_nn b, fun t => ?_⟩
  have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
  calc SchwartzMap.seminorm ℝ l d (∑ b : κ, Ψ b t α) * (1 + |t|) ^ N
      ≤ (∑ b : κ, SchwartzMap.seminorm ℝ l d (Ψ b t α)) * (1 + |t|) ^ N :=
        mul_le_mul_of_nonneg_right (seminorm_finset_sum_le l d Finset.univ _) ht_nn
    _ = ∑ b : κ, SchwartzMap.seminorm ℝ l d (Ψ b t α) * (1 + |t|) ^ N := Finset.sum_mul _ _ _
    _ ≤ ∑ b : κ, C_b b := Finset.sum_le_sum fun b _ => hCb_bd b t

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_smul_const (c : ι → ℂ)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t α => c α • Ψ t α) := by
  intro α l d
  obtain ⟨deg, C, hC_nn, hC⟩ := h α l d
  refine ⟨deg, ‖c α‖ * C, mul_nonneg (norm_nonneg _) hC_nn, fun t => ?_⟩
  rw [seminorm_complex_smul_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestRapidDecay_smul_const (c : ι → ℂ)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t α => c α • Ψ t α) := by
  intro α l d N
  obtain ⟨C, hC_nn, hC⟩ := h α l d N
  refine ⟨‖c α‖ * C, mul_nonneg (norm_nonneg _) hC_nn, fun t => ?_⟩
  rw [seminorm_complex_smul_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)

omit [DecidableEq ι] in
lemma indexedTestPolyGrowth_matrixTransform (M : Matrix ι ι ℂ)
    (T : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℝ] SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t γ => ∑ α : ι, M α γ • T (Ψ t α)) := by
  have h_term : ∀ α : ι, IndexedTestPolyGrowth (fun t γ => M α γ • T (Ψ t α)) := fun α => by
    intro γ l d
    obtain ⟨deg, C, hC_nn, hC⟩ :=
      indexedTestPolyGrowth_realCLM T h α l d
    refine ⟨deg, ‖M α γ‖ * C, mul_nonneg (norm_nonneg _) hC_nn, fun t => ?_⟩
    rw [seminorm_complex_smul_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)
  have h_sum := indexedTestPolyGrowth_finsetSum (fun α t γ => M α γ • T (Ψ t α)) h_term
  simpa only [Finset.sum_apply] using h_sum

omit [DecidableEq ι] in
lemma indexedTestRapidDecay_matrixTransform (M : Matrix ι ι ℂ)
    (T : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℝ] SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t γ => ∑ α : ι, M α γ • T (Ψ t α)) := by
  have h_term : ∀ α : ι, IndexedTestRapidDecay (fun t γ => M α γ • T (Ψ t α)) := fun α => by
    intro γ l d N
    obtain ⟨C, hC_nn, hC⟩ := indexedTestRapidDecay_realCLM T h α l d N
    refine ⟨‖M α γ‖ * C, mul_nonneg (norm_nonneg _) hC_nn, fun t => ?_⟩
    rw [seminorm_complex_smul_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)
  exact indexedTestRapidDecay_finsetSum (fun α t γ => M α γ • T (Ψ t α)) h_term

lemma indexedTestPolyGrowth_lorentzIndexedTest (R : HolomorphicLorentzRep ι) (A : SL2C)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t => lorentzIndexedTest R A (Ψ t)) :=
  indexedTestPolyGrowth_matrixTransform (R.rep A⁻¹)
    ((schwartzLorentzCLM 1 A⁻¹).restrictScalars ℝ) h

lemma indexedTestRapidDecay_lorentzIndexedTest (R : HolomorphicLorentzRep ι) (A : SL2C)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t => lorentzIndexedTest R A (Ψ t)) :=
  indexedTestRapidDecay_matrixTransform (R.rep A⁻¹)
    ((schwartzLorentzCLM 1 A⁻¹).restrictScalars ℝ) h

omit [Fintype ι] [DecidableEq ι] in
def schwartzPTConjRealCLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℝ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ where
  toLinearMap :=
    { toFun := schwartzPTConj n
      map_add' := map_add (schwartzPTConj n)
      map_smul' := fun r f => by
        change schwartzPTConj n ((r : ℂ) • f) = (r : ℂ) • schwartzPTConj n f
        rw [map_smulₛₗ, Complex.conj_ofReal] }
  cont := (schwartzPTConj n).continuous

lemma indexedTestPolyGrowth_pctIndexedTest {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t => pctIndexedTest S (Ψ t)) :=
  indexedTestPolyGrowth_matrixTransform (pctMatrix S) (schwartzPTConjRealCLM 1) h

lemma indexedTestRapidDecay_pctIndexedTest {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t => pctIndexedTest S (Ψ t)) :=
  indexedTestRapidDecay_matrixTransform (pctMatrix S) (schwartzPTConjRealCLM 1) h

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestPolyGrowth_comp_neg
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestPolyGrowth Ψ) :
    IndexedTestPolyGrowth (fun t => Ψ (-t)) := by
  intro α l d
  obtain ⟨deg, C, hC_nn, hC⟩ := h α l d
  refine ⟨deg, C, hC_nn, fun t => ?_⟩
  simpa [abs_neg] using hC (-t)

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestRapidDecay_comp_neg
    {Ψ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h : IndexedTestRapidDecay Ψ) :
    IndexedTestRapidDecay (fun t => Ψ (-t)) := by
  intro α l d N
  obtain ⟨C, hC_nn, hC⟩ := h α l d N
  refine ⟨C, hC_nn, fun t => ?_⟩
  simpa [abs_neg] using hC (-t)

omit [Fintype ι] [DecidableEq ι] in
lemma indexedTestRapidDecay_sub
    {Ψ₁ Ψ₂ : ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ}
    (h₁ : IndexedTestRapidDecay Ψ₁) (h₂ : IndexedTestRapidDecay Ψ₂) :
    IndexedTestRapidDecay (fun t α => Ψ₁ t α - Ψ₂ t α) := by
  intro α l d N
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := h₁ α l d N
  obtain ⟨C₂, hC₂_nn, hC₂⟩ := h₂ α l d N
  refine ⟨C₁ + C₂, add_nonneg hC₁_nn hC₂_nn, fun t => ?_⟩
  have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
  have h_tri := map_sub_le_add (SchwartzMap.seminorm ℝ l d) (Ψ₁ t α) (Ψ₂ t α)
  calc SchwartzMap.seminorm ℝ l d (Ψ₁ t α - Ψ₂ t α) * (1 + |t|) ^ N
      ≤ (SchwartzMap.seminorm ℝ l d (Ψ₁ t α) + SchwartzMap.seminorm ℝ l d (Ψ₂ t α)) *
          (1 + |t|) ^ N := mul_le_mul_of_nonneg_right h_tri ht_nn
    _ = SchwartzMap.seminorm ℝ l d (Ψ₁ t α) * (1 + |t|) ^ N +
          SchwartzMap.seminorm ℝ l d (Ψ₂ t α) * (1 + |t|) ^ N := add_mul _ _ _
    _ ≤ C₁ + C₂ := add_le_add (hC₁ t) (hC₂ t)

omit [Fintype ι] [DecidableEq ι] in
def cycleToLastFun {p : ℕ} (j : Fin (p + 1)) (a : Fin (p + 1)) : Fin (p + 1) :=
  if a.val < j.val then a
  else if h : a.val < p then ⟨a.val + 1, by omega⟩
  else j

omit [Fintype ι] [DecidableEq ι] in
lemma eq_cycleToLastFun_of_move_right {p : ℕ} (j : Fin (p + 1))
    (σ : Equiv.Perm (Fin (p + 1)))
    (h_last : σ ⟨j.val + (p - j.val), by omega⟩ = j)
    (h_lt : ∀ a : Fin (p + 1), a.val < j.val → σ a = a)
    (h_mid : ∀ u : Fin (p - j.val),
      σ ⟨j.val + u.val, by omega⟩ = ⟨j.val + 1 + u.val, by omega⟩)
    (a : Fin (p + 1)) :
    σ a = cycleToLastFun j a := by
  dsimp [cycleToLastFun]
  by_cases ha : a.val < j.val
  · rw [if_pos ha]
    exact h_lt a ha
  · rw [if_neg ha]
    by_cases hap : a.val < p
    · rw [dif_pos hap]
      let u : Fin (p - j.val) := ⟨a.val - j.val, by omega⟩
      have ha_eq : a = ⟨j.val + u.val, by omega⟩ := by
        ext
        dsimp [u]
        omega
      have hσa : σ a = ⟨j.val + 1 + u.val, by omega⟩ :=
        (congrArg σ ha_eq).trans (h_mid u)
      rw [hσa]
      ext
      dsimp [u]
      omega
    · rw [dif_neg hap]
      have ha_lt := a.isLt
      have hj_lt := j.isLt
      have ha_eq : a = ⟨j.val + (p - j.val), by omega⟩ := by
        ext
        dsimp only
        omega
      rw [ha_eq, h_last]

omit [Fintype ι] [DecidableEq ι] in
lemma tsupport_sub_subset_union {E : Type*} [TopologicalSpace E] (f g : E → ℂ) :
    tsupport (fun x => f x - g x) ⊆ tsupport f ∪ tsupport g := by
  refine closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport g))
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  have hf : f x = 0 := image_eq_zero_of_notMem_tsupport hnot.1
  have hg : g x = 0 := image_eq_zero_of_notMem_tsupport hnot.2
  exact hx (by rw [hf, hg, sub_zero])

theorem norm_indexedChain_sub_rapid_decay_of_oneParticle_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (Ψ Φ Ψ_core Φ_core : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i))
    (hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ i))
    (hΨc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ_core i))
    (hΦc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ_core i))
    (hΨ_tail : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Ψ i t α - Ψ_core i t α))
    (hΦ_tail : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Φ i t α - Φ_core i t α))
    (hsp : ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∀ (j k : Fin r), j.val < k.val → ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        (x₁ ∈ tsupport (Ψ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
          x₁ ∈ tsupport (Φ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ)) →
        x₂ ∈ tsupport (Ψ_core k t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0))
    (hone : ∀ (j : Fin r) (t : ℝ),
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ j t)) =
        wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Φ j t)))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))‖ *
        (1 + |t|) ^ N ≤ C := by
  rcases r with _ | p
  · refine ⟨0, le_rfl, fun t => ?_⟩
    have h0 : indexedChain ι 0 (fun i => Ψ i t) = indexedChain ι 0 (fun i => Φ i t) := by
      funext γ
      rfl
    rw [h0, sub_self, norm_zero, zero_mul]
  · let r := p + 1
    obtain ⟨C_diff1, hCd1_nn, hCd1⟩ := norm_indexedChain_sub_rapid_decay D.wightman.WData r
      Ψ Ψ_core hΨ_poly hΨc_poly hΨ_tail N
    obtain ⟨C_diff2, hCd2_nn, hCd2⟩ := norm_indexedChain_sub_rapid_decay D.wightman.WData r
      Φ Φ_core hΦ_poly hΦc_poly hΦ_tail N
    obtain ⟨T₀, hT0_pos, hT0_sp⟩ := hsp
    let hyb : ℕ → Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
      fun m i => if i.val < m then Φ_core i else Ψ_core i
    have h_hyb_poly : ∀ (m : ℕ) (i : Fin r), IndexedTestPolyGrowth (hyb m i) := fun m i => by
      dsimp [hyb]
      split_ifs
      · exact hΦc_poly i
      · exact hΨc_poly i
    have h_slot : ∀ j : Fin r, ∃ C_j : ℝ, 0 ≤ C_j ∧ ∀ t : ℝ,
        ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => hyb j.val i t)) -
          wightmanIndexedVec D.wightman.WData r
            (indexedChain ι r (fun i => hyb (j.val + 1) i t))‖ * (1 + |t|) ^ N ≤ C_j := by
      intro j
      obtain ⟨deg1, C1, hC1_nn, hC1⟩ := norm_indexedChain_poly_growth D.wightman.WData r
        (hyb j.val) (h_hyb_poly j.val)
      obtain ⟨deg2, C2, hC2_nn, hC2⟩ := norm_indexedChain_poly_growth D.wightman.WData r
        (hyb (j.val + 1)) (h_hyb_poly (j.val + 1))
      let M_small : ℝ := 1 + max T₀ 1
      have hMs_pos : 0 < M_small := by positivity
      let C_small : ℝ :=
        C1 * M_small ^ (deg1 + N) + C2 * M_small ^ (deg2 + N)
      let tail_diff : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
        Function.update (fun i => hyb j.val (cycleToLastFun j i)) (Fin.last p)
          (fun t α => (Ψ j t α - Ψ_core j t α) - (Φ j t α - Φ_core j t α))
      have h_td_poly : ∀ i : Fin r, IndexedTestPolyGrowth (tail_diff i) := fun i => by
        by_cases hi : i = Fin.last p
        · subst hi
          simpa [tail_diff, Function.update_self] using indexedTestPolyGrowth_sub
            (indexedTestPolyGrowth_of_rapidDecay (hΨ_tail j))
            (indexedTestPolyGrowth_of_rapidDecay (hΦ_tail j))
        · simpa [tail_diff, Function.update_of_ne hi] using
            h_hyb_poly j.val (cycleToLastFun j i)
      have h_td_dec : IndexedTestRapidDecay (tail_diff (Fin.last p)) := by
        simpa [tail_diff, Function.update_self] using
          indexedTestRapidDecay_sub (hΨ_tail j) (hΦ_tail j)
      obtain ⟨C_large, hCl_nn, hCl⟩ := norm_indexedChain_rapid_decay_of_slot D.wightman.WData r
        (Fin.last p) tail_diff h_td_poly h_td_dec N
      refine ⟨max C_small C_large, le_trans (by positivity) (le_max_left _ _), fun t => ?_⟩
      have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
      by_cases ht_lt : |t| < max T₀ 1
      · have h_1t : 1 + |t| ≤ M_small := by dsimp [M_small]; linarith
        have h_1t_nn : 0 ≤ 1 + |t| := by positivity
        calc ‖wightmanIndexedVec D.wightman.WData r
                (indexedChain ι r (fun i => hyb j.val i t)) -
              wightmanIndexedVec D.wightman.WData r
                (indexedChain ι r (fun i => hyb (j.val + 1) i t))‖ * (1 + |t|) ^ N
            ≤ (‖wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb j.val i t))‖ +
                ‖wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb (j.val + 1) i t))‖) * (1 + |t|) ^ N :=
              mul_le_mul_of_nonneg_right (norm_sub_le _ _) ht_nn
          _ = ‖wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb j.val i t))‖ * (1 + |t|) ^ N +
                ‖wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb (j.val + 1) i t))‖ * (1 + |t|) ^ N :=
              add_mul _ _ _
          _ ≤ C1 * (1 + |t|) ^ deg1 * (1 + |t|) ^ N +
                C2 * (1 + |t|) ^ deg2 * (1 + |t|) ^ N :=
              add_le_add (mul_le_mul_of_nonneg_right (hC1 t) ht_nn)
                (mul_le_mul_of_nonneg_right (hC2 t) ht_nn)
          _ ≤ C_small := by
              refine add_le_add ?_ ?_
              · calc C1 * (1 + |t|) ^ deg1 * (1 + |t|) ^ N
                    ≤ C1 * M_small ^ deg1 * M_small ^ N := mul_le_mul
                        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h_1t_nn h_1t _) hC1_nn)
                        (pow_le_pow_left₀ h_1t_nn h_1t _) ht_nn (by positivity)
                  _ = C1 * M_small ^ (deg1 + N) := by rw [pow_add]; ring
              · calc C2 * (1 + |t|) ^ deg2 * (1 + |t|) ^ N
                    ≤ C2 * M_small ^ deg2 * M_small ^ N := mul_le_mul
                        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h_1t_nn h_1t _) hC2_nn)
                        (pow_le_pow_left₀ h_1t_nn h_1t _) ht_nn (by positivity)
                  _ = C2 * M_small ^ (deg2 + N) := by rw [pow_add]; ring
          _ ≤ max C_small C_large := le_max_left _ _
      · have ht_ge : max T₀ 1 ≤ |t| := not_lt.mp ht_lt
        have ht_T0 : T₀ ≤ |t| := (le_max_left T₀ 1).trans ht_ge
        let diff_j : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
          Function.update (fun i => hyb j.val i t) j (Ψ_core j t - Φ_core j t)
        have h_diff_eq :
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => hyb j.val i t)) -
              wightmanIndexedVec D.wightman.WData r
                (indexedChain ι r (fun i => hyb (j.val + 1) i t)) =
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r diff_j) := by
          have h_lhs_upd : (fun i => hyb j.val i t) =
              Function.update (fun i => hyb j.val i t) j (Ψ_core j t) := by
            ext i α x
            by_cases hi : i = j
            · subst hi; simp [hyb]
            · simp [Function.update_of_ne hi]
          have h_rhs_upd : (fun i => hyb (j.val + 1) i t) =
              Function.update (fun i => hyb j.val i t) j (Φ_core j t) := by
            ext i α x
            by_cases hi : i = j
            · subst hi; simp [hyb]
            · have hne : i.val ≠ j.val := fun h => hi (Fin.ext h)
              have hiff : i.val < j.val + 1 ↔ i.val < j.val := by omega
              simp [hyb, hiff, Function.update_of_ne hi]
          rw [h_lhs_upd, h_rhs_upd, ← wightmanIndexedVec_indexedChain_update_sub]
        have h_sp_j : ∀ u : Fin (p - j.val), ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
            x₁ ∈ tsupport (diff_j j α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
            x₂ ∈ tsupport (diff_j ⟨j.val + 1 + u.val, by omega⟩ α₂ :
              (Fin 1 → Fin 4 → ℝ) → ℂ) →
            is_spacelike (x₁ 0 - x₂ 0) := by
          intro u α₁ α₂ x₁ x₂ hx₁ hx₂
          have hne : (⟨j.val + 1 + u.val, by omega⟩ : Fin r) ≠ j := by
            intro h
            have hv := congrArg Fin.val h
            dsimp at hv
            omega
          have hnot_lt : ¬(j.val + 1 + u.val < j.val) := by omega
          have hx₁' : x₁ ∈ tsupport (Ψ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
              x₁ ∈ tsupport (Φ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
            dsimp [diff_j] at hx₁
            rw [Function.update_self] at hx₁
            exact tsupport_sub_subset_union _ _ hx₁
          have hx₂' : x₂ ∈ tsupport (Ψ_core ⟨j.val + 1 + u.val, by omega⟩ t α₂ :
              (Fin 1 → Fin 4 → ℝ) → ℂ) := by
            dsimp [diff_j] at hx₂
            rw [Function.update_of_ne hne] at hx₂
            simpa [hyb, hnot_lt] using hx₂
          exact hT0_sp t ht_T0 j ⟨j.val + 1 + u.val, by omega⟩
            (by dsimp; omega) α₁ α₂ x₁ x₂ hx₁' hx₂'
        obtain ⟨σ, ⟨hσ_last, hσ_lt, hσ_mid, _⟩, h_mv⟩ :=
          wightmanIndexedVec_indexedChain_move_right D.wightman.WData D.locality r diff_j j
            (p - j.val) (by omega) h_sp_j
        have h_η_norm : ‖η ^ (p - j.val)‖ = 1 := by
          rw [norm_pow]
          rcases D.mode.hη with h1 | h1 <;> simp [h1]
        let base_j : Fin r → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
          Function.update (fun i => hyb j.val (cycleToLastFun j i) t) (Fin.last p) (Ψ j t - Φ j t)
        have h_perm_eq : (diff_j ∘ σ) =
            Function.update base_j (Fin.last p) (Ψ_core j t - Φ_core j t) := by
          ext i α x
          have hσ_eq := eq_cycleToLastFun_of_move_right j σ hσ_last hσ_lt hσ_mid i
          by_cases hi : i = Fin.last p
          · subst hi
            have hc_last : cycleToLastFun j (Fin.last p) = j := by
              dsimp [cycleToLastFun]
              have h1 : ¬(p < j.val) := by omega
              have h2 : ¬(p < p) := lt_irrefl p
              rw [if_neg h1, dif_neg h2]
            rw [Function.comp_apply, hσ_eq, hc_last]
            simp [diff_j, Function.update_self]
          · have hc_ne : cycleToLastFun j i ≠ j := by
              dsimp [cycleToLastFun]
              split_ifs with h1 h2
              · intro h
                have hv := congrArg Fin.val h
                omega
              · intro h
                have hv := congrArg Fin.val h
                simp at hv
                omega
              · exfalso
                apply hi
                ext
                simp only [Fin.val_last]
                omega
            rw [Function.comp_apply, hσ_eq, Function.update_of_ne hi]
            simp [diff_j, base_j, Function.update_of_ne hi, Function.update_of_ne hc_ne]
        have h_last_sub : Ψ_core j t - Φ_core j t =
            (Ψ j t - Φ j t) - (fun α => (Ψ j t α - Ψ_core j t α) - (Φ j t α - Φ_core j t α)) := by
          ext α x
          simp only [Pi.sub_apply, _root_.sub_apply]
          ring
        have h_zero_main :
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r base_j) = 0 := by
          have h_tail_zero : wightmanIndexedVec D.wightman.WData 1
              (indexedChain ι 1 (fun u => base_j (Fin.natAdd p u))) = (0 : ℂ) • D.vacuum := by
            rw [zero_smul]
            have h_base_last : (fun u : Fin 1 => base_j (Fin.natAdd p u)) =
                fun _ => Ψ j t - Φ j t := by
              ext u α x
              have hu : (Fin.natAdd p u : Fin (p + 1)) = Fin.last p := by
                ext
                rw [Subsingleton.elim u 0]
                simp
              rw [hu]
              simp [base_j, Function.update_self]
            rw [h_base_last]
            have h_sub_w :
                wightmanIndexedVec D.wightman.WData 1
                  (indexedChain ι 1 (fun _ => Ψ j t - Φ j t)) =
                wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ j t)) -
                wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Φ j t)) := by
              rw [wightmanIndexedVec_one_eq_sum, wightmanIndexedVec_one_eq_sum,
                wightmanIndexedVec_one_eq_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun γ _ => map_sub _ _ _
            rw [h_sub_w, hone j t, sub_self]
          have h_con := wightmanIndexedVec_indexedChain_contract_right D.wightman.WData p 1
            base_j h_tail_zero
          rw [zero_smul] at h_con
          exact h_con
        have h_eq_tail :
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r (diff_j ∘ σ)) =
            -(wightmanIndexedVec D.wightman.WData r
              (indexedChain ι r (fun i => tail_diff i t))) := by
          have h_upd_tail : Function.update base_j (Fin.last p)
              (fun α => (Ψ j t α - Ψ_core j t α) - (Φ j t α - Φ_core j t α)) =
              fun i => tail_diff i t := by
            ext i α x
            by_cases hi : i = Fin.last p
            · subst hi
              simp [tail_diff, Function.update_self]
            · simp [tail_diff, base_j, Function.update_of_ne hi]
          have h_base_id : Function.update base_j (Fin.last p) (Ψ j t - Φ j t) = base_j := by
            ext i α x
            by_cases hi : i = Fin.last p
            · subst hi; simp [base_j, Function.update_self]
            · simp [Function.update_of_ne hi]
          rw [h_perm_eq, h_last_sub, wightmanIndexedVec_indexedChain_update_sub, h_base_id,
            h_zero_main, zero_sub, h_upd_tail]
        calc ‖wightmanIndexedVec D.wightman.WData r
                (indexedChain ι r (fun i => hyb j.val i t)) -
              wightmanIndexedVec D.wightman.WData r
                (indexedChain ι r (fun i => hyb (j.val + 1) i t))‖ * (1 + |t|) ^ N
            = ‖η ^ (p - j.val) •
                  wightmanIndexedVec D.wightman.WData r (indexedChain ι r (diff_j ∘ σ))‖ *
                (1 + |t|) ^ N := by
              rw [h_diff_eq, h_mv]
          _ = ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => tail_diff i t))‖ *
                (1 + |t|) ^ N := by
              rw [norm_smul, h_η_norm, one_mul, h_eq_tail, norm_neg]
          _ ≤ C_large := hCl t
          _ ≤ max C_small C_large := le_max_right _ _
    choose C_j hCj_nn hCj_bd using h_slot
    let C_core : ℝ := ∑ j : Fin r, C_j j
    refine ⟨C_diff1 + C_core + C_diff2,
      add_nonneg (add_nonneg hCd1_nn (Finset.sum_nonneg fun j _ => hCj_nn j)) hCd2_nn,
      fun t => ?_⟩
    have ht_nn : 0 ≤ (1 + |t|) ^ N := pow_nonneg (by positivity) N
    have h0 : (fun i => hyb 0 i t) = fun i => Ψ_core i t := by
      ext i α x; simp [hyb]
    have hr_end : (fun i => hyb r i t) = fun i => Φ_core i t := by
      ext i α x; simp [hyb, i.isLt]
    have h_tel :
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t)) =
        ∑ m ∈ Finset.range r,
          (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => hyb m i t)) -
            wightmanIndexedVec D.wightman.WData r
              (indexedChain ι r (fun i => hyb (m + 1) i t))) := by
      rw [Finset.sum_range_sub', h0, hr_end]
    have h_core_bd :
        ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖ *
          (1 + |t|) ^ N ≤ C_core := by
      rw [h_tel]
      calc ‖∑ m ∈ Finset.range r,
              (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => hyb m i t)) -
                wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb (m + 1) i t)))‖ * (1 + |t|) ^ N
          ≤ (∑ m ∈ Finset.range r,
              ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => hyb m i t)) -
                wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb (m + 1) i t))‖) * (1 + |t|) ^ N :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) ht_nn
        _ = ∑ j : Fin r,
              ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => hyb j.val i t)) -
                wightmanIndexedVec D.wightman.WData r
                  (indexedChain ι r (fun i => hyb (j.val + 1) i t))‖ * (1 + |t|) ^ N := by
            rw [← Fin.sum_univ_eq_sum_range, Finset.sum_mul]
        _ ≤ C_core := Finset.sum_le_sum fun j _ => hCj_bd j t
    have h_split :
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) =
        (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t))) +
        (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))) -
        (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))) := by
      abel
    have h_tri :
        ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))‖ ≤
        ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t))‖ +
        ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖ +
        ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖ := by
      rw [h_split]
      exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    calc ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
            wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))‖ *
            (1 + |t|) ^ N
        ≤ (‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t))‖ +
            ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖ +
            ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖) *
            (1 + |t|) ^ N := mul_le_mul_of_nonneg_right h_tri ht_nn
      _ = ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t))‖ *
              (1 + |t|) ^ N +
            ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ_core i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖ *
              (1 + |t|) ^ N +
            ‖wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) -
              wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ_core i t))‖ *
              (1 + |t|) ^ N := by ring
      _ ≤ C_diff1 + C_core + C_diff2 := add_le_add (add_le_add (hCd1 t) h_core_bd) (hCd2 t)

lemma tendsto_indexedChain_sub_zero_of_oneParticle_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (D : IsolatedMassShellData R S m M η)
    (r : ℕ) (Ψ Φ Ψ_core Φ_core : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i))
    (hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ i))
    (hΨc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ_core i))
    (hΦc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ_core i))
    (hΨ_tail : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Ψ i t α - Ψ_core i t α))
    (hΦ_tail : ∀ i : Fin r, IndexedTestRapidDecay (fun t α => Φ i t α - Φ_core i t α))
    (hsp : ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∀ (j k : Fin r), j.val < k.val → ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        (x₁ ∈ tsupport (Ψ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
          x₁ ∈ tsupport (Φ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ)) →
        x₂ ∈ tsupport (Ψ_core k t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0))
    (hone : ∀ (j : Fin r) (t : ℝ),
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ j t)) =
        wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Φ j t)))
    {F : Filter ℝ} (hF : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0)) :
    Tendsto (fun t : ℝ =>
      wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))) F (𝓝 0) := by
  obtain ⟨C, _, hC_bd⟩ := norm_indexedChain_sub_rapid_decay_of_oneParticle_eq D r Ψ Φ
    Ψ_core Φ_core hΨ_poly hΦ_poly hΨc_poly hΦc_poly hΨ_tail hΦ_tail hsp hone 1
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds (by simpa using hF.const_mul C)
    (fun t => norm_nonneg _) (fun t => ?_))
  have ht_pos : 0 < 1 + |t| := by positivity
  exact (le_mul_inv_iff₀ ht_pos).mpr (by simpa [pow_one] using hC_bd t)

omit [Fintype ι] [DecidableEq ι] in
lemma is_spacelike_of_cone_bounds
    {V₁ V₂ : Set (Fin 3 → ℝ)} {d_sep R₁ R₂ t : ℝ}
    (ht : 1 ≤ |t|) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hgap : R₁ + R₂ < d_sep - (R₁ + R₂))
    (h_sep : ∀ v₁ ∈ V₁, ∀ v₂ ∈ V₂, d_sep ≤ ‖v₁ - v₂‖)
    {x₁ x₂ : Fin 4 → ℝ}
    (hx₁t : |x₁ 0 - t| ≤ R₁ * |t|)
    (hx₁s : ∃ v₁ ∈ V₁, ‖spatialPart x₁ - t • v₁‖ ≤ R₁ * |t|)
    (hx₂t : |x₂ 0 - t| ≤ R₂ * |t|)
    (hx₂s : ∃ v₂ ∈ V₂, ‖spatialPart x₂ - t • v₂‖ ≤ R₂ * |t|) :
    is_spacelike (x₁ - x₂) := by
  rcases hx₁s with ⟨v₁, hv₁, hx₁sp⟩
  rcases hx₂s with ⟨v₂, hv₂, hx₂sp⟩
  have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
  have h_time_le : |x₁ 0 - x₂ 0| ≤ (R₁ + R₂) * |t| := by
    have htri : |x₁ 0 - x₂ 0| ≤ |x₁ 0 - t| + |x₂ 0 - t| := by
      have heq : x₁ 0 - x₂ 0 = (x₁ 0 - t) - (x₂ 0 - t) := by ring
      rw [heq]
      exact abs_sub _ _
    linarith
  have h_sp_ge : (d_sep - (R₁ + R₂)) * |t| ≤ ‖spatialPart x₁ - spatialPart x₂‖ := by
    have hv := h_sep v₁ hv₁ v₂ hv₂
    have htv : d_sep * |t| ≤ ‖t • v₁ - t • v₂‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      calc d_sep * |t| = |t| * d_sep := mul_comm _ _
        _ ≤ |t| * ‖v₁ - v₂‖ := mul_le_mul_of_nonneg_left hv ht_pos.le
    have htri : ‖t • v₁ - t • v₂‖ ≤
        ‖spatialPart x₁ - t • v₁‖ + ‖spatialPart x₁ - spatialPart x₂‖ +
          ‖spatialPart x₂ - t • v₂‖ := by
      have heq : t • v₁ - t • v₂ =
          -(spatialPart x₁ - t • v₁) + (spatialPart x₁ - spatialPart x₂) +
            (spatialPart x₂ - t • v₂) := by abel
      rw [heq]
      calc ‖-(spatialPart x₁ - t • v₁) + (spatialPart x₁ - spatialPart x₂) +
              (spatialPart x₂ - t • v₂)‖
          ≤ ‖-(spatialPart x₁ - t • v₁) + (spatialPart x₁ - spatialPart x₂)‖ +
              ‖spatialPart x₂ - t • v₂‖ := norm_add_le _ _
        _ ≤ (‖-(spatialPart x₁ - t • v₁)‖ + ‖spatialPart x₁ - spatialPart x₂‖) +
              ‖spatialPart x₂ - t • v₂‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ = _ := by rw [norm_neg]
    linarith
  have h_gap_t : (R₁ + R₂) * |t| < (d_sep - (R₁ + R₂)) * |t| :=
    mul_lt_mul_of_pos_right hgap ht_pos
  have h_time_sq : (x₁ 0 - x₂ 0) ^ 2 ≤ ((R₁ + R₂) * |t|) ^ 2 := by
    rw [← sq_abs (x₁ 0 - x₂ 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) h_time_le 2
  have h_strict_sq : ((R₁ + R₂) * |t|) ^ 2 < ((d_sep - (R₁ + R₂)) * |t|) ^ 2 := by
    have h_nn : 0 ≤ (R₁ + R₂) * |t| := mul_nonneg (add_nonneg hR₁ hR₂) ht_pos.le
    nlinarith
  have h_sp_sq : ((d_sep - (R₁ + R₂)) * |t|) ^ 2 ≤ ‖spatialPart (x₁ - x₂)‖ ^ 2 := by
    have h_eq : spatialPart (x₁ - x₂) = spatialPart x₁ - spatialPart x₂ := by
      ext j; simp [spatialPart]
    rw [h_eq]
    exact pow_le_pow_left₀ (mul_nonneg (by linarith) ht_pos.le) h_sp_ge 2
  have h_eucl := sum_sq_fin3_ge_pi_norm_sq (spatialPart (x₁ - x₂))
  have hm_eq : minkowskiInner (x₁ - x₂) (x₁ - x₂) =
      (x₁ 0 - x₂ 0) ^ 2 -
        (spatialPart (x₁ - x₂) 0 ^ 2 + spatialPart (x₁ - x₂) 1 ^ 2 +
          spatialPart (x₁ - x₂) 2 ^ 2) := by
    rw [minkowskiInner_explicit]
    simp [spatialPart]
    ring
  unfold is_spacelike
  rw [hm_eq]
  linarith

end QuasiLocalChainEquivalence

section WaveOperatorIntertwining

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma exists_mem_tsupport_of_mem_tsupport_finsetSum
    {κ E : Type*} [Fintype κ] [TopologicalSpace E]
    (f : κ → E → ℂ) {x : E}
    (hx : x ∈ tsupport (fun y : E => ∑ a : κ, f a y)) :
    ∃ a : κ, x ∈ tsupport (f a) := by
  by_contra h_none
  push Not at h_none
  let K : Set E := ⋃ a : κ, tsupport (f a)
  have hK_closed : IsClosed K := isClosed_iUnion_of_finite fun a => isClosed_tsupport (f a)
  have h_sub : Function.support (fun y : E => ∑ a : κ, f a y) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    refine Finset.sum_eq_zero fun a _ => ?_
    refine image_eq_zero_of_notMem_tsupport fun hmem => hyK ?_
    exact Set.mem_iUnion.mpr ⟨a, hmem⟩
  have hxK : x ∈ K := closure_minimal h_sub hK_closed hx
  rw [Set.mem_iUnion] at hxK
  obtain ⟨a, ha⟩ := hxK
  exact h_none a ha

lemma tsupport_lorentzIndexedTest_subset
    (R : HolomorphicLorentzRep ι) (A : SL2C)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (γ : ι) {x : Fin 1 → Fin 4 → ℝ}
    (hx : x ∈ tsupport (lorentzIndexedTest R A Ψ γ : (Fin 1 → Fin 4 → ℝ) → ℂ)) :
    ∃ α : ι, lorentzEquiv 1 A⁻¹ x ∈ tsupport (Ψ α : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
  by_contra h_none
  push Not at h_none
  let K : Set (Fin 1 → Fin 4 → ℝ) :=
    ⋃ α : ι, (lorentzEquiv 1 A⁻¹) ⁻¹' tsupport (Ψ α : (Fin 1 → Fin 4 → ℝ) → ℂ)
  have hK_closed : IsClosed K :=
    isClosed_iUnion_of_finite fun α =>
      (isClosed_tsupport _).preimage (lorentzEquiv 1 A⁻¹).continuous
  have h_sub : Function.support
      (lorentzIndexedTest R A Ψ γ : (Fin 1 → Fin 4 → ℝ) → ℂ) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    dsimp [lorentzIndexedTest]
    rw [schwartzMap_sum_apply]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [_root_.smul_apply, smul_eq_mul, schwartzLorentzCLM_apply]
    have hmem : lorentzEquiv 1 A⁻¹ y ∉ tsupport (Ψ α : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
      intro hmem
      exact hyK (Set.mem_iUnion.mpr ⟨α, hmem⟩)
    have h_arg : (fun i : Fin 1 => (lorentzOfSL2C A⁻¹).mulVec (y i)) = lorentzEquiv 1 A⁻¹ y := rfl
    rw [h_arg, image_eq_zero_of_notMem_tsupport hmem, mul_zero]
  have hxK : x ∈ K := closure_minimal h_sub hK_closed hx
  rw [Set.mem_iUnion] at hxK
  obtain ⟨α, hα⟩ := hxK
  exact h_none α hα

lemma tsupport_pctIndexedTest_subset
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ : ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (μ : ι) {x : Fin 1 → Fin 4 → ℝ}
    (hx : x ∈ tsupport (pctIndexedTest S Ψ μ : (Fin 1 → Fin 4 → ℝ) → ℂ)) :
    ∃ α : ι, -x ∈ tsupport (Ψ α : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
  by_contra h_none
  push Not at h_none
  let K : Set (Fin 1 → Fin 4 → ℝ) :=
    ⋃ α : ι, Neg.neg ⁻¹' tsupport (Ψ α : (Fin 1 → Fin 4 → ℝ) → ℂ)
  have hK_closed : IsClosed K :=
    isClosed_iUnion_of_finite fun α => (isClosed_tsupport _).preimage continuous_neg
  have h_sub : Function.support (pctIndexedTest S Ψ μ : (Fin 1 → Fin 4 → ℝ) → ℂ) ⊆ K := by
    intro y hy
    by_contra hyK
    apply hy
    dsimp [pctIndexedTest]
    rw [schwartzMap_sum_apply]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [_root_.smul_apply, smul_eq_mul, schwartzPTConj_apply]
    have hmem : -y ∉ tsupport (Ψ α : (Fin 1 → Fin 4 → ℝ) → ℂ) := by
      intro hmem
      exact hyK (Set.mem_iUnion.mpr ⟨α, hmem⟩)
    rw [image_eq_zero_of_notMem_tsupport hmem, star_zero, mul_zero]
  have hxK : x ∈ K := closure_minimal h_sub hK_closed hx
  rw [Set.mem_iUnion] at hxK
  obtain ⟨α, hα⟩ := hxK
  exact h_none α hα

omit [Fintype ι] [DecidableEq ι] in
lemma exists_pairwise_velocitySep {m : ℝ} (hm : 0 < m)
    {r : ℕ} (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    ∃ d_sep : ℝ, 0 < d_sep ∧
      ∀ (i j : Fin r), i ≠ j →
        ∀ v₁ ∈ velocitySupport m (f i), ∀ v₂ ∈ velocitySupport m (f j), d_sep ≤ ‖v₁ - v₂‖ := by
  rcases r with _ | k
  · exact ⟨1, zero_lt_one, fun i => Fin.elim0 i⟩
  · let d_of : Fin (k + 1) × Fin (k + 1) → ℝ := fun ij =>
      if hij : ij.1 ≠ ij.2 then (exists_pos_sep_of_velocityDisjoint hm (hf hij)).choose else 1
    have hd_pos : ∀ ij : Fin (k + 1) × Fin (k + 1), 0 < d_of ij := fun ij => by
      dsimp [d_of]
      by_cases hij : ij.1 ≠ ij.2
      · rw [dif_pos hij]
        exact (exists_pos_sep_of_velocityDisjoint hm (hf hij)).choose_spec.1
      · rw [dif_neg hij]
        exact zero_lt_one
    let d_sep : ℝ := Finset.univ.inf' Finset.univ_nonempty d_of
    refine ⟨d_sep, (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun ij _ => hd_pos ij, ?_⟩
    intro i j hij v₁ hv₁ v₂ hv₂
    have h1 : d_sep ≤ d_of (i, j) := Finset.inf'_le d_of (Finset.mem_univ _)
    have h_eq : d_of (i, j) = (exists_pos_sep_of_velocityDisjoint hm (hf hij)).choose := by
      dsimp [d_of]
      exact dif_pos hij
    rw [h_eq] at h1
    exact h1.trans
      ((exists_pos_sep_of_velocityDisjoint hm (hf hij)).choose_spec.2 v₁ hv₁ v₂ hv₂)

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_velocityVec {m : ℝ} (hm : 0 < m) : Continuous (velocityVec m) := by
  have h_inv : Continuous (fun p : Fin 3 → ℝ => (massShellEnergy m p)⁻¹) :=
    (continuous_massShellEnergy m).inv₀ fun p => (massShellEnergy_pos hm p).ne'
  exact h_inv.smul continuous_id

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_massShellBoost_prod (m : ℝ) :
    Continuous (fun q : SL2C × (Fin 3 → ℝ) => massShellBoost m q.1 q.2) := by
  refine continuous_pi fun j => ?_
  dsimp [massShellBoost, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum Finset.univ fun ν _ => ?_
  exact ((continuous_lorentzOfSL2C_entry j.succ ν).comp continuous_fst).mul
    ((continuous_apply ν).comp ((continuous_massShellVec m).comp continuous_snd))

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_massShellBoost_comp {α : Type*} [TopologicalSpace α]
    {m : ℝ} {g : α → SL2C} {p : α → Fin 3 → ℝ}
    (hg : Continuous g) (hp : Continuous p) :
    Continuous (fun a : α => massShellBoost m (g a) (p a)) := by
  refine continuous_pi fun j => ?_
  dsimp [massShellBoost, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum Finset.univ fun ν _ => ?_
  exact ((continuous_lorentzOfSL2C_entry j.succ ν).comp hg).mul
    ((continuous_apply ν).comp ((continuous_massShellVec m).comp hp))

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_sl2cUpper : Continuous (fun z : ℂ => (⟨!![1, z; (0 : ℂ), 1],
    sl2c_upper_det_u z⟩ : SL2C)) := by
  refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const
  · exact continuous_const

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_sl2cLower : Continuous (fun z : ℂ => (⟨!![1, (0 : ℂ); z, 1],
    sl2c_lower_det_l z⟩ : SL2C)) := by
  refine Continuous.subtype_mk (continuous_pi fun i => continuous_pi fun j => ?_) _
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_id
  · exact continuous_const

lemma wightmanIndexedVec_one_pct_eq_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (s : Fin P.mode.ν) (f : SmoothWavepacket) (t t' : ℝ) :
    wightmanIndexedVec P.wightman.WData 1
        (indexedChain ι 1 (fun _ =>
          pctIndexedTest S (haagRuelleIndexedTest P.toIsolatedMassShellData s f t))) =
      wightmanIndexedVec P.wightman.WData 1
        (indexedChain ι 1 (fun _ γ => ∑ s' : Fin P.mode.ν,
          haagRuelleIndexedTest P.toIsolatedMassShellData s'
            (pctModeWavepacket P.modeData s' s f) t' γ)) := by
  let D := P.toIsolatedMassShellData
  have hL : P.pctEquiv hε (haagRuelleVacCreate D s f t) =
      wightmanIndexedVec D.wightman.WData 1
        (indexedChain ι 1 (fun _ => pctIndexedTest S (haagRuelleIndexedTest D s f t))) := by
    have h_vac_eq : haagRuelleVacCreate D s f t =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ => haagRuelleIndexedTest D s f t)) := rfl
    rw [h_vac_eq]
    have h_pct := wightmanPCTEquiv_indexedChain D.wightman.WData D.wightman.poincare
      D.wightman.toWightmanAxioms.wightmanPCT hε 1 (fun _ => haagRuelleIndexedTest D s f t)
    simp only [Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, one_smul] at h_pct
    exact h_pct
  have hR : (∑ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (pctModeWavepacket P.modeData s' s f) t') =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ γ =>
        ∑ s' : Fin P.mode.ν, haagRuelleIndexedTest D s'
          (pctModeWavepacket P.modeData s' s f) t' γ)) := by
    have h_each : ∀ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (pctModeWavepacket P.modeData s' s f) t' =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ =>
            haagRuelleIndexedTest D s' (pctModeWavepacket P.modeData s' s f) t')) := fun _ => rfl
    simp_rw [h_each, wightmanIndexedVec_one_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← map_sum]
  rw [← hL, ← hR]
  exact pct_haagRuelleVacCreate P hε s f t t'

lemma wightmanIndexedVec_one_lorentz_eq_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (s : Fin P.mode.ν) (f : SmoothWavepacket) (t t' : ℝ) :
    wightmanIndexedVec P.wightman.WData 1
        (indexedChain ι 1 (fun _ =>
          lorentzIndexedTest R A (haagRuelleIndexedTest P.toIsolatedMassShellData s f t))) =
      wightmanIndexedVec P.wightman.WData 1
        (indexedChain ι 1 (fun _ γ => ∑ s' : Fin P.mode.ν,
          haagRuelleIndexedTest P.toIsolatedMassShellData s'
            (lorentzModeWavepacket P.modeData A s' s f) t' γ)) := by
  let D := P.toIsolatedMassShellData
  have hL : P.lorentzEquiv A (haagRuelleVacCreate D s f t) =
      wightmanIndexedVec D.wightman.WData 1
        (indexedChain ι 1 (fun _ =>
          lorentzIndexedTest R A (haagRuelleIndexedTest D s f t))) := by
    have h_vac_eq : haagRuelleVacCreate D s f t =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ => haagRuelleIndexedTest D s f t)) := rfl
    rw [h_vac_eq]
    exact wightmanSpinorLorentz_indexedChain D.wightman.WData D.wightman.poincare A 1
      (fun _ => haagRuelleIndexedTest D s f t)
  have hR : (∑ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (lorentzModeWavepacket P.modeData A s' s f) t') =
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ γ =>
        ∑ s' : Fin P.mode.ν, haagRuelleIndexedTest D s'
          (lorentzModeWavepacket P.modeData A s' s f) t' γ)) := by
    have h_each : ∀ s' : Fin P.mode.ν,
        haagRuelleVacCreate D s' (lorentzModeWavepacket P.modeData A s' s f) t' =
        wightmanIndexedVec D.wightman.WData 1
          (indexedChain ι 1 (fun _ =>
            haagRuelleIndexedTest D s' (lorentzModeWavepacket P.modeData A s' s f) t')) :=
      fun _ => rfl
    simp_rw [h_each, wightmanIndexedVec_one_eq_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [← map_sum]
  rw [← hL, ← hR]
  exact lorentz_haagRuelleVacCreate P A s f t t'

lemma pct_haagRuelleLimit
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η)
    {F_src F_dst : Filter ℝ} [F_src.NeBot]
    (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F_src (𝓝 0))
    (h_neg : Tendsto Neg.neg F_src F_dst)
    (L_src L_dst : ∀ (r : ℕ), (Fin r → Fin P.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → P.Hilbert)
    (hL_src : ∀ r s f hf, Tendsto (haagRuelleChainVec P.toIsolatedMassShellData r s f)
      F_src (𝓝 (L_src r s f hf)))
    (hL_dst : ∀ r s f hf, Tendsto (haagRuelleChainVec P.toIsolatedMassShellData r s f)
      F_dst (𝓝 (L_dst r s f hf)))
    (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    P.pctEquiv hε (L_src r s f hf) =
      (η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin P.mode.ν,
          L_dst r s' (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i))
            (fun _ _ hij => velocityDisjoint_pctModeWavepacket P.modeData _ _ _ _ (hf hij)) := by
  let D := P.toIsolatedMassShellData
  obtain ⟨d_sep, hd_pos, h_sep⟩ := exists_pairwise_velocitySep D.hm f hf
  let r_cone : ℝ := d_sep / 6
  have hr_cone : 0 < r_cone := by positivity
  let Ψ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun i t => pctIndexedTest S (haagRuelleIndexedTest D (s i) (f i) t)
  let Ψ_core : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun i t => pctIndexedTest S (haagRuelleCoreIndexedTest D (s i) (f i) r_cone hr_cone t)
  let Φ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t γ =>
    ∑ b : Fin P.mode.ν, haagRuelleIndexedTest D b
      (pctModeWavepacket P.modeData b (s i) (f i)) (-t) γ
  let Φ_core : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t γ =>
    ∑ b : Fin P.mode.ν, haagRuelleCoreIndexedTest D b
      (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t) γ
  have hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i) := fun i =>
    indexedTestPolyGrowth_pctIndexedTest S (indexedTestPolyGrowth_haagRuelle D (s i) (f i))
  have hΨc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ_core i) := fun i =>
    indexedTestPolyGrowth_pctIndexedTest S
      (indexedTestPolyGrowth_haagRuelleCore D (s i) (f i) r_cone hr_cone)
  have hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ i) := fun i =>
    indexedTestPolyGrowth_finsetSum (fun b t => haagRuelleIndexedTest D b
      (pctModeWavepacket P.modeData b (s i) (f i)) (-t))
      fun b => indexedTestPolyGrowth_comp_neg
        (indexedTestPolyGrowth_haagRuelle D b (pctModeWavepacket P.modeData b (s i) (f i)))
  have hΦc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ_core i) := fun i =>
    indexedTestPolyGrowth_finsetSum (fun b t => haagRuelleCoreIndexedTest D b
      (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t))
      fun b => indexedTestPolyGrowth_comp_neg
        (indexedTestPolyGrowth_haagRuelleCore D b
          (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone)
  have hΨ_tail : ∀ i : Fin r,
      IndexedTestRapidDecay (fun t α => Ψ i t α - Ψ_core i t α) := fun i => by
    have h_eq : (fun t α => Ψ i t α - Ψ_core i t α) = fun t =>
        pctIndexedTest S (haagRuelleTailIndexedTest D (s i) (f i) r_cone hr_cone t) := by
      ext t α x
      dsimp [Ψ, Ψ_core]
      rw [pctIndexedTest_sub]
      congr 1
    rw [h_eq]
    exact indexedTestRapidDecay_pctIndexedTest S
      (indexedTestRapidDecay_haagRuelleTail D (s i) (f i) r_cone hr_cone)
  have hΦ_tail : ∀ i : Fin r,
      IndexedTestRapidDecay (fun t α => Φ i t α - Φ_core i t α) := fun i => by
    have h_eq : (fun t α => Φ i t α - Φ_core i t α) = fun t γ =>
        ∑ b : Fin P.mode.ν, haagRuelleTailIndexedTest D b
          (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t) γ := by
      ext t γ x
      dsimp [Φ, Φ_core]
      rw [schwartzMap_sum_apply, _root_.sub_apply, schwartzMap_sum_apply, schwartzMap_sum_apply,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← _root_.sub_apply, haagRuelleIndexedTest_sub_core]
    rw [h_eq]
    exact indexedTestRapidDecay_finsetSum (fun b t => haagRuelleTailIndexedTest D b
      (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t))
      fun b => indexedTestRapidDecay_comp_neg (indexedTestRapidDecay_haagRuelleTail D b
        (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone)
  have h_cone_pct : ∀ (i : Fin r) (t : ℝ), 1 ≤ |t| → ∀ (α : ι) (x : Fin 1 → Fin 4 → ℝ),
      (x ∈ tsupport (Ψ_core i t α : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
        x ∈ tsupport (Φ_core i t α : (Fin 1 → Fin 4 → ℝ) → ℂ)) →
      |x 0 0 - (-t)| ≤ r_cone * |-t| ∧
        ∃ v ∈ velocitySupport m (f i), ‖spatialPart (x 0) - (-t) • v‖ ≤ r_cone * |-t| := by
    intro i t ht α x hx
    rcases hx with hxΨ | hxΦ
    · obtain ⟨β, hβ⟩ := tsupport_pctIndexedTest_subset S _ α hxΨ
      have hcore := tsupport_timeModCoreTestFn_subset D.hm
        (dualModeWavepacket D (s i) β (f i)) _ _ _ r_cone hr_cone t hβ
      obtain ⟨ht_bd, v, hv, hsp_bd⟩ := tsupport_velocityConeCutoff_large_time D.hm
        (dualModeWavepacket D (s i) β (f i)) r_cone hr_cone ht hcore
      have h_t_neg : |x 0 0 - (-t)| ≤ r_cone * |-t| := by
        rw [abs_neg t]
        have h_eq : x 0 0 - (-t) = -((-x) 0 0 - t) := by
          simp only [Pi.neg_apply]
          ring
        rw [h_eq, abs_neg]
        exact ht_bd
      have h_sp_neg : ‖spatialPart (x 0) - (-t) • v‖ ≤ r_cone * |-t| := by
        rw [abs_neg t]
        have h_eq : spatialPart (x 0) - (-t) • v = -(spatialPart ((-x) 0) - t • v) := by
          ext j
          simp [spatialPart]
          ring
        rw [h_eq, norm_neg]
        exact hsp_bd
      exact ⟨h_t_neg, v, velocitySupport_dualModeWavepacket_subset D (s i) β (f i) hv, h_sp_neg⟩
    · have h_sum_fn :
          (⇑(∑ b : Fin P.mode.ν, haagRuelleCoreIndexedTest D b
              (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t) α) :
            (Fin 1 → Fin 4 → ℝ) → ℂ) =
          fun y : Fin 1 → Fin 4 → ℝ => ∑ b : Fin P.mode.ν,
            (haagRuelleCoreIndexedTest D b
              (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t) α :
              (Fin 1 → Fin 4 → ℝ) → ℂ) y := by
        ext y
        rw [schwartzMap_sum_apply]
      have h_sum : x ∈ tsupport (fun y : Fin 1 → Fin 4 → ℝ => ∑ b : Fin P.mode.ν,
          (haagRuelleCoreIndexedTest D b
            (pctModeWavepacket P.modeData b (s i) (f i)) r_cone hr_cone (-t) α :
            (Fin 1 → Fin 4 → ℝ) → ℂ) y) := by
        dsimp [Φ_core] at hxΦ
        rwa [h_sum_fn] at hxΦ
      obtain ⟨b, hb⟩ := exists_mem_tsupport_of_mem_tsupport_finsetSum _ h_sum
      have hcore := tsupport_timeModCoreTestFn_subset D.hm
        (dualModeWavepacket D b α (pctModeWavepacket P.modeData b (s i) (f i)))
        _ _ _ r_cone hr_cone (-t) hb
      have ht_neg : 1 ≤ |-t| := by rwa [abs_neg]
      obtain ⟨ht_bd, v, hv, hsp_bd⟩ := tsupport_velocityConeCutoff_large_time D.hm
        (dualModeWavepacket D b α (pctModeWavepacket P.modeData b (s i) (f i)))
        r_cone hr_cone ht_neg hcore
      have hv_pct := velocitySupport_dualModeWavepacket_subset D b α
        (pctModeWavepacket P.modeData b (s i) (f i)) hv
      obtain ⟨p, hp, rfl⟩ := hv_pct
      exact ⟨ht_bd, velocityVec m p,
        ⟨p, tsupport_pctModeWavepacket_subset P.modeData b (s i) (f i) hp, rfl⟩, hsp_bd⟩
  have hsp : ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∀ (j k : Fin r), j.val < k.val → ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        (x₁ ∈ tsupport (Ψ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
          x₁ ∈ tsupport (Φ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ)) →
        x₂ ∈ tsupport (Ψ_core k t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0) := by
    refine ⟨1, zero_lt_one, fun t ht j k hjk α₁ α₂ x₁ x₂ hx₁ hx₂ => ?_⟩
    obtain ⟨hx₁t, hx₁s⟩ := h_cone_pct j t ht α₁ x₁ hx₁
    obtain ⟨hx₂t, hx₂s⟩ := h_cone_pct k t ht α₂ x₂ (Or.inl hx₂)
    have hgap : r_cone + r_cone < d_sep - (r_cone + r_cone) := by
      dsimp [r_cone]
      linarith
    have hjk_ne : j ≠ k := Fin.ne_of_lt hjk
    have ht_neg : 1 ≤ |-t| := by rwa [abs_neg]
    exact is_spacelike_of_cone_bounds ht_neg hr_cone.le hr_cone.le hgap
      (fun v₁ hv₁ v₂ hv₂ => h_sep j k hjk_ne v₁ hv₁ v₂ hv₂) hx₁t hx₁s hx₂t hx₂s
  have hone : ∀ (j : Fin r) (t : ℝ),
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ j t)) =
        wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Φ j t)) :=
    fun j t => wightmanIndexedVec_one_pct_eq_sum P hε (s j) (f j) t (-t)
  have h_zero_diff := tendsto_indexedChain_sub_zero_of_oneParticle_eq D r Ψ Φ Ψ_core Φ_core
    hΨ_poly hΦ_poly hΨc_poly hΦc_poly hΨ_tail hΦ_tail hsp hone hF_inv
  have h_zero_smul := h_zero_diff.const_smul (η ^ (r * (r - 1) / 2))
  have h_lhs_tend : Tendsto
      (fun t : ℝ => (η ^ (r * (r - 1) / 2)) •
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)))
      F_src (𝓝 (P.pctEquiv hε (L_src r s f hf))) := by
    have h_pct_eq :
        (fun t : ℝ => (η ^ (r * (r - 1) / 2)) •
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t))) =
        fun t => P.pctEquiv hε (haagRuelleChainVec D r s f t) := by
      funext t
      exact (wightmanPCTEquiv_indexedChain D.wightman.WData D.wightman.poincare
        D.wightman.toWightmanAxioms.wightmanPCT hε r _).symm
    rw [h_pct_eq]
    exact (P.pctEquiv hε).isometry.continuous.tendsto _ |>.comp (hL_src r s f hf)
  have h_rhs_tend : Tendsto
      (fun t : ℝ => (η ^ (r * (r - 1) / 2)) •
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)))
      F_src (𝓝 ((η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin P.mode.ν,
          L_dst r s' (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i))
            (fun _ _ hij => velocityDisjoint_pctModeWavepacket P.modeData _ _ _ _ (hf hij)))) := by
    have h_sum_eq : ∀ t : ℝ,
        wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)) =
        ∑ s' : Fin r → Fin P.mode.ν, haagRuelleChainVec D r s'
          (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i)) (-t) := by
      intro t
      have hΦ_pi : (fun i : Fin r => Φ i t) =
          fun i => ∑ b : Fin P.mode.ν,
            haagRuelleIndexedTest D b (pctModeWavepacket P.modeData b (s i) (f i)) (-t) := by
        ext i γ x
        dsimp [Φ]
        rw [Finset.sum_apply, schwartzMap_sum_apply]
      rw [hΦ_pi]
      exact wightmanIndexedVec_indexedChain_finsetSum_pi D.wightman.WData r _
    simp_rw [h_sum_eq]
    refine (tendsto_finsetSum Finset.univ fun s' _ =>
      (hL_dst r s' (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i))
        (fun _ _ hij =>
          velocityDisjoint_pctModeWavepacket P.modeData _ _ _ _ (hf hij))).comp h_neg).const_smul
      (η ^ (r * (r - 1) / 2))
  have h_sub_tend : Tendsto
      (fun t : ℝ => (η ^ (r * (r - 1) / 2)) •
        (wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)) -
          wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t))))
      F_src (𝓝 (P.pctEquiv hε (L_src r s f hf) - (η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin P.mode.ν,
          L_dst r s' (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i))
            (fun _ _ hij =>
              velocityDisjoint_pctModeWavepacket P.modeData _ _ _ _ (hf hij)))) := by
    simpa [smul_sub] using h_lhs_tend.sub h_rhs_tend
  rw [smul_zero] at h_zero_smul
  exact sub_eq_zero.mp (tendsto_nhds_unique h_sub_tend h_zero_smul)

theorem pct_haagRuelleOutVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η)
    (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    P.pctEquiv hε (haagRuelleOutVec P.toIsolatedMassShellData r s f hf) =
      (η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin P.mode.ν,
          haagRuelleInVec P.toIsolatedMassShellData r s'
            (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i))
            (fun _ _ hij => velocityDisjoint_pctModeWavepacket P.modeData _ _ _ _ (hf hij)) :=
  pct_haagRuelleLimit P hε tendsto_inv_one_add_abs_atTop Filter.tendsto_neg_atTop_atBot
    (haagRuelleOutVec P.toIsolatedMassShellData) (haagRuelleInVec P.toIsolatedMassShellData)
    (tendsto_haagRuelleChainVec_atTop P.toIsolatedMassShellData)
    (tendsto_haagRuelleChainVec_atBot P.toIsolatedMassShellData) r s f hf

theorem pct_haagRuelleInVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η)
    (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    P.pctEquiv hε (haagRuelleInVec P.toIsolatedMassShellData r s f hf) =
      (η ^ (r * (r - 1) / 2)) •
        ∑ s' : Fin r → Fin P.mode.ν,
          haagRuelleOutVec P.toIsolatedMassShellData r s'
            (fun i => pctModeWavepacket P.modeData (s' i) (s i) (f i))
            (fun _ _ hij => velocityDisjoint_pctModeWavepacket P.modeData _ _ _ _ (hf hij)) :=
  pct_haagRuelleLimit P hε tendsto_inv_one_add_abs_atBot Filter.tendsto_neg_atBot_atTop
    (haagRuelleInVec P.toIsolatedMassShellData) (haagRuelleOutVec P.toIsolatedMassShellData)
    (tendsto_haagRuelleChainVec_atBot P.toIsolatedMassShellData)
    (tendsto_haagRuelleChainVec_atTop P.toIsolatedMassShellData) r s f hf

theorem pct_mollerWaveOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell)
    (Ψ : SymmFockHilbert P.mode.ν η) :
    P.pctEquiv hε (mollerWaveOut P.toIsolatedMassShellData Ψ) =
      mollerWaveIn P.toIsolatedMassShellData (P.fockPCTEquiv hε hC_pct Ψ) := by
  let D := P.toIsolatedMassShellData
  let S_gen : Submodule ℂ (SymmFockHilbert D.mode.ν η) :=
    Submodule.span ℂ (Set.range (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1))
  have h_dense : Dense (S_gen : Set (SymmFockHilbert D.mode.ν η)) :=
    dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη
  have h_on_span : ∀ v ∈ S_gen, P.pctEquiv hε (mollerWaveOut D v) =
      mollerWaveIn D (P.fockPCTEquiv hε hC_pct v) := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨r, s, f, hf⟩, rfl⟩
      dsimp only
      rw [mollerWaveOut_symmFockMultiParticleVec D r s f hf, pct_haagRuelleOutVec P hε r s f hf,
        PoincareIsolatedMassShellData.fockPCTEquiv,
        symmFockPCTEquiv_multiParticleVec P.modeData hε hC_pct r s f, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun s' _ => ?_
      exact (mollerWaveIn_symmFockMultiParticleVec D r s' _ _).symm
    · simp
    · intro u w _ _ hu hw
      rw [map_add, map_add, map_add, map_add, hu, hw]
    · intro c u _ hu
      rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, hu]
  have hL_cont : Continuous (fun v => P.pctEquiv hε (mollerWaveOut D v)) :=
    (P.pctEquiv hε).isometry.continuous.comp (mollerWaveOut D).continuous
  have hR_cont : Continuous (fun v => mollerWaveIn D (P.fockPCTEquiv hε hC_pct v)) :=
    (mollerWaveIn D).continuous.comp (P.fockPCTEquiv hε hC_pct).isometry.continuous
  exact h_dense.induction h_on_span (isClosed_eq hL_cont hR_cont) Ψ

theorem pct_mollerWaveIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell)
    (Ψ : SymmFockHilbert P.mode.ν η) :
    P.pctEquiv hε (mollerWaveIn P.toIsolatedMassShellData Ψ) =
      mollerWaveOut P.toIsolatedMassShellData (P.fockPCTEquiv hε hC_pct Ψ) := by
  let D := P.toIsolatedMassShellData
  let S_gen : Submodule ℂ (SymmFockHilbert D.mode.ν η) :=
    Submodule.span ℂ (Set.range (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1))
  have h_dense : Dense (S_gen : Set (SymmFockHilbert D.mode.ν η)) :=
    dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη
  have h_on_span : ∀ v ∈ S_gen, P.pctEquiv hε (mollerWaveIn D v) =
      mollerWaveOut D (P.fockPCTEquiv hε hC_pct v) := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨r, s, f, hf⟩, rfl⟩
      dsimp only
      rw [mollerWaveIn_symmFockMultiParticleVec D r s f hf, pct_haagRuelleInVec P hε r s f hf,
        PoincareIsolatedMassShellData.fockPCTEquiv,
        symmFockPCTEquiv_multiParticleVec P.modeData hε hC_pct r s f, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun s' _ => ?_
      exact (mollerWaveOut_symmFockMultiParticleVec D r s' _ _).symm
    · simp
    · intro u w _ _ hu hw
      rw [map_add, map_add, map_add, map_add, hu, hw]
    · intro c u _ hu
      rw [map_smul, map_smulₛₗ, map_smulₛₗ, map_smul, hu]
  have hL_cont : Continuous (fun v => P.pctEquiv hε (mollerWaveIn D v)) :=
    (P.pctEquiv hε).isometry.continuous.comp (mollerWaveIn D).continuous
  have hR_cont : Continuous (fun v => mollerWaveOut D (P.fockPCTEquiv hε hC_pct v)) :=
    (mollerWaveOut D).continuous.comp (P.fockPCTEquiv hε hC_pct).isometry.continuous
  exact h_dense.induction h_on_span (isClosed_eq hL_cont hR_cont) Ψ

lemma lorentz_haagRuelleLimit_of_small
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot] (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0))
    (L : ∀ (r : ℕ), (Fin r → Fin P.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → P.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec P.toIsolatedMassShellData r s f)
      F (𝓝 (L r s f hf)))
    (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j))
    (d_sep : ℝ) (hd_pos : 0 < d_sep)
    (h_sep : ∀ (i j : Fin r), i ≠ j →
      ∀ v₁ ∈ velocitySupport m (f i), ∀ v₂ ∈ velocitySupport m (f j), d_sep ≤ ‖v₁ - v₂‖)
    (A : SL2C)
    (hA_mat : ∀ μ ν : Fin 4,
      |lorentzOfSL2C A μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν| ≤
        (d_sep / 12) / (4 * (1 + d_sep / 12)))
    (hA_vel : ∀ (i : Fin r) (p : Fin 3 → ℝ), p ∈ tsupport (f i).amp →
      ‖velocityVec m (massShellBoost m A p) - velocityVec m p‖ ≤ d_sep / 12) :
    P.lorentzEquiv A (L r s f hf) =
      ∑ s' : Fin r → Fin P.mode.ν,
        L r s' (fun i => lorentzModeWavepacket P.modeData A (s' i) (s i) (f i))
          (fun _ _ hij =>
            velocityDisjoint_lorentzModeWavepacket P.modeData A _ _ _ _ (hf hij)) := by
  let D := P.toIsolatedMassShellData
  let r₁ : ℝ := d_sep / 12
  have hr₁ : 0 < r₁ := by positivity
  let Ψ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun i t => lorentzIndexedTest R A (haagRuelleIndexedTest D (s i) (f i) t)
  let Ψ_core : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
    fun i t => lorentzIndexedTest R A (haagRuelleCoreIndexedTest D (s i) (f i) r₁ hr₁ t)
  let Φ : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t γ =>
    ∑ b : Fin P.mode.ν, haagRuelleIndexedTest D b
      (lorentzModeWavepacket P.modeData A b (s i) (f i)) t γ
  let Φ_core : Fin r → ℝ → ι → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun i t γ =>
    ∑ b : Fin P.mode.ν, haagRuelleCoreIndexedTest D b
      (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t γ
  have hΨ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ i) := fun i =>
    indexedTestPolyGrowth_lorentzIndexedTest R A (indexedTestPolyGrowth_haagRuelle D (s i) (f i))
  have hΨc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Ψ_core i) := fun i =>
    indexedTestPolyGrowth_lorentzIndexedTest R A
      (indexedTestPolyGrowth_haagRuelleCore D (s i) (f i) r₁ hr₁)
  have hΦ_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ i) := fun i =>
    indexedTestPolyGrowth_finsetSum (fun b t => haagRuelleIndexedTest D b
      (lorentzModeWavepacket P.modeData A b (s i) (f i)) t)
      fun b => indexedTestPolyGrowth_haagRuelle D b
        (lorentzModeWavepacket P.modeData A b (s i) (f i))
  have hΦc_poly : ∀ i : Fin r, IndexedTestPolyGrowth (Φ_core i) := fun i =>
    indexedTestPolyGrowth_finsetSum (fun b t => haagRuelleCoreIndexedTest D b
      (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t)
      fun b => indexedTestPolyGrowth_haagRuelleCore D b
        (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁
  have hΨ_tail : ∀ i : Fin r,
      IndexedTestRapidDecay (fun t α => Ψ i t α - Ψ_core i t α) := fun i => by
    have h_eq : (fun t α => Ψ i t α - Ψ_core i t α) = fun t =>
        lorentzIndexedTest R A (haagRuelleTailIndexedTest D (s i) (f i) r₁ hr₁ t) := by
      ext t α x
      dsimp [Ψ, Ψ_core]
      rw [lorentzIndexedTest_sub]
      congr 1
    rw [h_eq]
    exact indexedTestRapidDecay_lorentzIndexedTest R A
      (indexedTestRapidDecay_haagRuelleTail D (s i) (f i) r₁ hr₁)
  have hΦ_tail : ∀ i : Fin r,
      IndexedTestRapidDecay (fun t α => Φ i t α - Φ_core i t α) := fun i => by
    have h_eq : (fun t α => Φ i t α - Φ_core i t α) = fun t γ =>
        ∑ b : Fin P.mode.ν, haagRuelleTailIndexedTest D b
          (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t γ := by
      ext t γ x
      dsimp [Φ, Φ_core]
      rw [schwartzMap_sum_apply, _root_.sub_apply, schwartzMap_sum_apply, schwartzMap_sum_apply,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← _root_.sub_apply, haagRuelleIndexedTest_sub_core]
    rw [h_eq]
    exact indexedTestRapidDecay_finsetSum (fun b t => haagRuelleTailIndexedTest D b
      (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t)
      fun b => indexedTestRapidDecay_haagRuelleTail D b
        (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁
  have h_cone_lor : ∀ (i : Fin r) (t : ℝ), 1 ≤ |t| → ∀ (α : ι) (x : Fin 1 → Fin 4 → ℝ),
      (x ∈ tsupport (Ψ_core i t α : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
        x ∈ tsupport (Φ_core i t α : (Fin 1 → Fin 4 → ℝ) → ℂ)) →
      |x 0 0 - t| ≤ (2 * r₁) * |t| ∧
        ∃ v ∈ velocitySupport m (f i),
          ‖spatialPart (x 0) - t • v‖ ≤ (2 * r₁) * |t| := by
    intro i t ht α x hx
    have ht_pos : 0 < |t| := lt_of_lt_of_le zero_lt_one ht
    rcases hx with hxΨ | hxΦ
    · obtain ⟨β, hβ⟩ := tsupport_lorentzIndexedTest_subset R A _ α hxΨ
      have hcore := tsupport_timeModCoreTestFn_subset D.hm
        (dualModeWavepacket D (s i) β (f i)) _ _ _ r₁ hr₁ t hβ
      obtain ⟨ht_bd, v, hv, hsp_bd⟩ := tsupport_velocityConeCutoff_large_time D.hm
        (dualModeWavepacket D (s i) β (f i)) r₁ hr₁ ht hcore
      have hv_orig := velocitySupport_dualModeWavepacket_subset D (s i) β (f i) hv
      obtain ⟨p, hp, rfl⟩ := hv_orig
      let y : Fin 1 → Fin 4 → ℝ := lorentzEquiv 1 A⁻¹ x
      have hx_eq : x 0 = (lorentzOfSL2C A).mulVec (y 0) := by
        have hxy := (lorentzEquiv 1 A).apply_symm_apply x
        have hsymm : (lorentzEquiv 1 A).symm = lorentzEquiv 1 A⁻¹ := by
          ext i μ
          rfl
        rw [hsymm] at hxy
        exact congrFun hxy.symm 0
      have hv_lt : ‖velocityVec m p‖ ≤ 1 := (norm_velocityVec_lt_one D.hm p).le
      have hy0 : |y 0 0| ≤ (1 + r₁) * |t| := by
        have htri : |y 0 0| ≤ |y 0 0 - t| + |t| := by
          calc |y 0 0| = |(y 0 0 - t) + t| := by ring_nf
            _ ≤ |y 0 0 - t| + |t| := abs_add_le _ _
        linarith
      have hysp : ‖spatialPart (y 0)‖ ≤ (1 + r₁) * |t| := by
        have htri : ‖spatialPart (y 0)‖ ≤
            ‖spatialPart (y 0) - t • velocityVec m p‖ + ‖t • velocityVec m p‖ := by
          calc ‖spatialPart (y 0)‖
              = ‖(spatialPart (y 0) - t • velocityVec m p) + t • velocityVec m p‖ := by
                congr 1; abel
            _ ≤ ‖spatialPart (y 0) - t • velocityVec m p‖ + ‖t • velocityVec m p‖ :=
                norm_add_le _ _
        have htv : ‖t • velocityVec m p‖ ≤ 1 * |t| := by
          rw [norm_smul, Real.norm_eq_abs]
          calc |t| * ‖velocityVec m p‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hv_lt ht_pos.le
            _ = 1 * |t| := by ring
        linarith
      have hy_all : ∀ ν : Fin 4, |y 0 ν| ≤ (1 + r₁) * |t| := fun ν => by
        fin_cases ν
        · exact hy0
        · exact (Real.norm_eq_abs _ ▸
            norm_le_pi_norm (spatialPart (y 0)) 0).trans hysp
        · exact (Real.norm_eq_abs _ ▸
            norm_le_pi_norm (spatialPart (y 0)) 1).trans hysp
        · exact (Real.norm_eq_abs _ ▸
            norm_le_pi_norm (spatialPart (y 0)) 2).trans hysp
      have h_diff_coord : ∀ μ : Fin 4, |x 0 μ - y 0 μ| ≤ r₁ * |t| := fun μ => by
        have hy_sum : y 0 μ = ∑ ν : Fin 4, (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν * y 0 ν := by
          rw [Finset.sum_eq_single μ]
          · simp
          · intro ν _ hne; simp [Matrix.one_apply_ne hne.symm]
          · intro hnot; exact False.elim (hnot (Finset.mem_univ μ))
        have h_eq : x 0 μ - y 0 μ =
            ∑ ν : Fin 4, (lorentzOfSL2C A μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) * y 0 ν := by
          rw [hx_eq, Matrix.mulVec, dotProduct]
          conv_lhs =>
            arg 2
            rw [hy_sum]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [sub_mul]
        rw [h_eq]
        calc |∑ ν : Fin 4,
              (lorentzOfSL2C A μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) * y 0 ν|
            ≤ ∑ ν : Fin 4,
                |(lorentzOfSL2C A μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) * y 0 ν| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ ν : Fin 4,
                |lorentzOfSL2C A μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν| * |y 0 ν| := by
              refine Finset.sum_congr rfl fun ν _ => abs_mul _ _
          _ ≤ ∑ _ν : Fin 4, (r₁ / (4 * (1 + r₁))) * ((1 + r₁) * |t|) :=
              Finset.sum_le_sum fun ν _ => mul_le_mul (hA_mat μ ν) (hy_all ν)
                (abs_nonneg _) (by positivity)
          _ = 4 * ((r₁ / (4 * (1 + r₁))) * ((1 + r₁) * |t|)) := by simp
          _ = r₁ * |t| := by
              have h_nz : 1 + r₁ ≠ 0 := by positivity
              field_simp [h_nz]
      have hx_t : |x 0 0 - t| ≤ (2 * r₁) * |t| := by
        have htri : |x 0 0 - t| ≤ |x 0 0 - y 0 0| + |y 0 0 - t| := by
          have h : x 0 0 - t = (x 0 0 - y 0 0) + (y 0 0 - t) := by ring
          rw [h]
          exact abs_add_le _ _
        linarith [h_diff_coord 0]
      have hx_sp : ‖spatialPart (x 0) - t • velocityVec m p‖ ≤ (2 * r₁) * |t| := by
        have h_diff_sp : ‖spatialPart (x 0) - spatialPart (y 0)‖ ≤ r₁ * |t| := by
          rw [pi_norm_le_iff_of_nonneg (mul_nonneg hr₁.le ht_pos.le)]
          intro j
          rw [Pi.sub_apply, Real.norm_eq_abs]
          exact h_diff_coord j.succ
        have htri : ‖spatialPart (x 0) - t • velocityVec m p‖ ≤
            ‖spatialPart (x 0) - spatialPart (y 0)‖ +
              ‖spatialPart (y 0) - t • velocityVec m p‖ := by
          have h : spatialPart (x 0) - t • velocityVec m p =
              (spatialPart (x 0) - spatialPart (y 0)) +
                (spatialPart (y 0) - t • velocityVec m p) := by abel
          rw [h]
          exact norm_add_le _ _
        linarith
      exact ⟨hx_t, velocityVec m p, ⟨p, hp, rfl⟩, hx_sp⟩
    · have h_sum_fn :
          (⇑(∑ b : Fin P.mode.ν, haagRuelleCoreIndexedTest D b
              (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t α) :
            (Fin 1 → Fin 4 → ℝ) → ℂ) =
          fun z : Fin 1 → Fin 4 → ℝ => ∑ b : Fin P.mode.ν,
            (haagRuelleCoreIndexedTest D b
              (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t α :
              (Fin 1 → Fin 4 → ℝ) → ℂ) z := by
        ext z
        rw [schwartzMap_sum_apply]
      have h_sum : x ∈ tsupport (fun z : Fin 1 → Fin 4 → ℝ => ∑ b : Fin P.mode.ν,
          (haagRuelleCoreIndexedTest D b
            (lorentzModeWavepacket P.modeData A b (s i) (f i)) r₁ hr₁ t α :
            (Fin 1 → Fin 4 → ℝ) → ℂ) z) := by
        dsimp [Φ_core] at hxΦ
        rwa [h_sum_fn] at hxΦ
      obtain ⟨b, hb⟩ := exists_mem_tsupport_of_mem_tsupport_finsetSum _ h_sum
      have hcore := tsupport_timeModCoreTestFn_subset D.hm
        (dualModeWavepacket D b α (lorentzModeWavepacket P.modeData A b (s i) (f i)))
        _ _ _ r₁ hr₁ t hb
      obtain ⟨ht_bd, v', hv', hsp_bd⟩ := tsupport_velocityConeCutoff_large_time D.hm
        (dualModeWavepacket D b α (lorentzModeWavepacket P.modeData A b (s i) (f i)))
        r₁ hr₁ ht hcore
      have hv_lor := velocitySupport_dualModeWavepacket_subset D b α
        (lorentzModeWavepacket P.modeData A b (s i) (f i)) hv'
      obtain ⟨q, hq, rfl⟩ := hv_lor
      obtain ⟨p, hp, hq_eq⟩ := tsupport_lorentzModeWavepacket_subset P.modeData A b (s i) (f i) hq
      subst hq_eq
      have h_t : |x 0 0 - t| ≤ (2 * r₁) * |t| := by linarith [mul_nonneg hr₁.le ht_pos.le]
      have h_sp : ‖spatialPart (x 0) - t • velocityVec m p‖ ≤ (2 * r₁) * |t| := by
        have htri : ‖spatialPart (x 0) - t • velocityVec m p‖ ≤
            ‖spatialPart (x 0) - t • velocityVec m (massShellBoost m A p)‖ +
              ‖t • (velocityVec m (massShellBoost m A p) - velocityVec m p)‖ := by
          have h : spatialPart (x 0) - t • velocityVec m p =
              (spatialPart (x 0) - t • velocityVec m (massShellBoost m A p)) +
                t • (velocityVec m (massShellBoost m A p) - velocityVec m p) := by
            rw [smul_sub]
            abel
          rw [h]
          exact norm_add_le _ _
        have hshift : ‖t • (velocityVec m (massShellBoost m A p) - velocityVec m p)‖ ≤
            r₁ * |t| := by
          rw [norm_smul, Real.norm_eq_abs, mul_comm]
          exact mul_le_mul_of_nonneg_right (hA_vel i p hp) ht_pos.le
        linarith
      exact ⟨h_t, velocityVec m p, ⟨p, hp, rfl⟩, h_sp⟩
  have hsp : ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| →
      ∀ (j k : Fin r), j.val < k.val → ∀ (α₁ α₂ : ι) (x₁ x₂ : Fin 1 → Fin 4 → ℝ),
        (x₁ ∈ tsupport (Ψ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ) ∨
          x₁ ∈ tsupport (Φ_core j t α₁ : (Fin 1 → Fin 4 → ℝ) → ℂ)) →
        x₂ ∈ tsupport (Ψ_core k t α₂ : (Fin 1 → Fin 4 → ℝ) → ℂ) →
        is_spacelike (x₁ 0 - x₂ 0) := by
    refine ⟨1, zero_lt_one, fun t ht j k hjk α₁ α₂ x₁ x₂ hx₁ hx₂ => ?_⟩
    obtain ⟨hx₁t, hx₁s⟩ := h_cone_lor j t ht α₁ x₁ hx₁
    obtain ⟨hx₂t, hx₂s⟩ := h_cone_lor k t ht α₂ x₂ (Or.inl hx₂)
    have hR : 0 ≤ 2 * r₁ := by positivity
    have hgap : (2 * r₁) + (2 * r₁) < d_sep - ((2 * r₁) + (2 * r₁)) := by
      dsimp [r₁]
      linarith
    have hjk_ne : j ≠ k := Fin.ne_of_lt hjk
    exact is_spacelike_of_cone_bounds ht hR hR hgap
      (fun v₁ hv₁ v₂ hv₂ => h_sep j k hjk_ne v₁ hv₁ v₂ hv₂) hx₁t hx₁s hx₂t hx₂s
  have hone : ∀ (j : Fin r) (t : ℝ),
      wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Ψ j t)) =
        wightmanIndexedVec D.wightman.WData 1 (indexedChain ι 1 (fun _ => Φ j t)) :=
    fun j t => wightmanIndexedVec_one_lorentz_eq_sum P A (s j) (f j) t t
  have h_zero_diff := tendsto_indexedChain_sub_zero_of_oneParticle_eq D r Ψ Φ Ψ_core Φ_core
    hΨ_poly hΦ_poly hΨc_poly hΦc_poly hΨ_tail hΦ_tail hsp hone hF_inv
  have h_lhs_tend : Tendsto
      (fun t : ℝ => wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t)))
      F (𝓝 (P.lorentzEquiv A (L r s f hf))) := by
    have h_eq :
        (fun t : ℝ => wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Ψ i t))) =
        fun t => P.lorentzEquiv A (haagRuelleChainVec D r s f t) := by
      funext t
      exact (wightmanSpinorLorentz_indexedChain D.wightman.WData D.wightman.poincare A r _).symm
    rw [h_eq]
    exact (P.lorentzEquiv A).isometry.continuous.tendsto _ |>.comp (hL r s f hf)
  have h_rhs_tend : Tendsto
      (fun t : ℝ => wightmanIndexedVec D.wightman.WData r (indexedChain ι r (fun i => Φ i t)))
      F (𝓝 (∑ s' : Fin r → Fin P.mode.ν,
        L r s' (fun i => lorentzModeWavepacket P.modeData A (s' i) (s i) (f i))
          (fun _ _ hij =>
            velocityDisjoint_lorentzModeWavepacket P.modeData A _ _ _ _ (hf hij)))) := by
    have h_sum_eq :
        (fun t : ℝ => wightmanIndexedVec D.wightman.WData r
          (indexedChain ι r (fun i => Φ i t))) =
        fun t => ∑ s' : Fin r → Fin P.mode.ν, haagRuelleChainVec D r s'
          (fun i => lorentzModeWavepacket P.modeData A (s' i) (s i) (f i)) t := by
      funext t
      have hΦ_pi : (fun i : Fin r => Φ i t) =
          fun i => ∑ b : Fin P.mode.ν,
            haagRuelleIndexedTest D b (lorentzModeWavepacket P.modeData A b (s i) (f i)) t := by
        ext i γ x
        dsimp [Φ]
        rw [Finset.sum_apply, schwartzMap_sum_apply]
      rw [hΦ_pi]
      exact wightmanIndexedVec_indexedChain_finsetSum_pi D.wightman.WData r _
    rw [h_sum_eq]
    exact tendsto_finsetSum Finset.univ fun s' _ =>
      hL r s' (fun i => lorentzModeWavepacket P.modeData A (s' i) (s i) (f i))
        (fun _ _ hij => velocityDisjoint_lorentzModeWavepacket P.modeData A _ _ _ _ (hf hij))
  exact sub_eq_zero.mp (tendsto_nhds_unique (h_lhs_tend.sub h_rhs_tend) h_zero_diff)

omit [Fintype ι] [DecidableEq ι] in
lemma exists_oneParam_uniform_velocitySep
    {m : ℝ} (hm : 0 < m) (G : ℂ → SL2C) (hG_cont : Continuous G)
    (r' : ℕ) (f : Fin (r' + 1) → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin (r' + 1) => VelocityDisjoint m (f i) (f j)) (z : ℂ) :
    ∃ d_tube : ℝ, 0 < d_tube ∧
      ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i j : Fin (r' + 1)), i ≠ j →
          ∀ p ∈ tsupport (f i).amp, ∀ q ∈ tsupport (f j).amp,
            d_tube ≤ ‖velocityVec m (massShellBoost m (G ((u : ℂ) * z)) p) -
              velocityVec m (massShellBoost m (G ((u : ℂ) * z)) q)‖ := by
  classical
  have h_pair : ∀ ij : Fin (r' + 1) × Fin (r' + 1), ∃ d : ℝ, 0 < d ∧
      (ij.1 ≠ ij.2 → ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
        ∀ p ∈ tsupport (f ij.1).amp, ∀ q ∈ tsupport (f ij.2).amp,
          d ≤ ‖velocityVec m (massShellBoost m (G ((u : ℂ) * z)) p) -
            velocityVec m (massShellBoost m (G ((u : ℂ) * z)) q)‖) := by
    intro ij
    by_cases hij : ij.1 ≠ ij.2
    · let K_ij : Set (ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
        Set.Icc (0 : ℝ) 1 ×ˢ (tsupport (f ij.1).amp ×ˢ tsupport (f ij.2).amp)
      by_cases hne : K_ij.Nonempty
      · let φ : ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ := fun upq =>
          ‖velocityVec m (massShellBoost m (G ((upq.1 : ℂ) * z)) upq.2.1) -
            velocityVec m (massShellBoost m (G ((upq.1 : ℂ) * z)) upq.2.2)‖
        have hK_cpct : IsCompact K_ij :=
          isCompact_Icc.prod
            ((f ij.1).compactSupport.isCompact.prod (f ij.2).compactSupport.isCompact)
        have hφ_cont : Continuous φ := by
          have hG_sub : Continuous (fun upq : ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              G ((upq.1 : ℂ) * z)) :=
            hG_cont.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
          have h_mb1 : Continuous (fun upq : ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              massShellBoost m (G ((upq.1 : ℂ) * z)) upq.2.1) :=
            continuous_massShellBoost_comp hG_sub (continuous_fst.comp continuous_snd)
          have h_mb2 : Continuous (fun upq : ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
              massShellBoost m (G ((upq.1 : ℂ) * z)) upq.2.2) :=
            continuous_massShellBoost_comp hG_sub (continuous_snd.comp continuous_snd)
          exact (((continuous_velocityVec hm).comp h_mb1).sub
            ((continuous_velocityVec hm).comp h_mb2)).norm
        obtain ⟨upq₀, hmem, hmin⟩ := hK_cpct.exists_isMinOn hne hφ_cont.continuousOn
        have hne_0 : φ upq₀ ≠ 0 := by
          intro h0
          dsimp only [φ] at h0
          rw [norm_eq_zero, sub_eq_zero] at h0
          have hmb := velocityVec_injective hm h0
          have hpq := massShellBoost_injOn hm (G ((upq₀.1 : ℂ) * z)) trivial trivial hmb
          have hdisj := (velocityDisjoint_iff_tsupport_disjoint hm (f ij.1) (f ij.2)).mp (hf hij)
          exact Set.disjoint_left.mp hdisj hmem.2.1 (hpq ▸ hmem.2.2)
        have hpos : 0 < φ upq₀ := lt_of_le_of_ne (norm_nonneg _) hne_0.symm
        refine ⟨φ upq₀, hpos, fun _ u hu p hp q hq => ?_⟩
        have hmem_upq : (u, (p, q)) ∈ K_ij := ⟨hu, hp, hq⟩
        have h_le : φ upq₀ ≤ φ (u, (p, q)) := hmin hmem_upq
        exact h_le
      · exact ⟨1, zero_lt_one, fun _ u hu p hp q hq =>
          False.elim (hne ⟨(u, (p, q)), hu, hp, hq⟩)⟩
    · exact ⟨1, zero_lt_one, fun h => False.elim (hij h)⟩
  choose d_ij hd_pos hd_sep using h_pair
  refine ⟨Finset.univ.inf' Finset.univ_nonempty d_ij,
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun ij _ => hd_pos ij,
    fun u hu i j hij p hp q hq => ?_⟩
  exact (Finset.inf'_le d_ij (Finset.mem_univ (i, j))).trans (hd_sep (i, j) hij u hu p hp q hq)

omit [Fintype ι] [DecidableEq ι] in
lemma exists_oneParam_step_count
    {m : ℝ} (hm : 0 < m) (G : ℂ → SL2C) (hG_cont : Continuous G) (hG_zero : G 0 = 1)
    (K_all : Set (Fin 3 → ℝ)) (hK_cpct : IsCompact K_all)
    {r₁ eps_mat : ℝ} (hr₁ : 0 < r₁) (heps : 0 < eps_mat) (z : ℂ) :
    ∃ N : ℕ, 0 < N ∧
      (∀ μ ν : Fin 4,
        |lorentzOfSL2C (G (z / (N : ℂ))) μ ν -
          (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν| ≤ eps_mat) ∧
      (∀ q ∈ K_all,
        ‖velocityVec m (massShellBoost m (G (z / (N : ℂ))) q) - velocityVec m q‖ ≤ r₁) := by
  classical
  have h_mat_ev : ∀ μ ν : Fin 4, ∀ᶠ w : ℂ in 𝓝 0,
      |lorentzOfSL2C (G w) μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν| ≤ eps_mat := by
    intro μ ν
    have hcont_at : ContinuousAt
        (fun w : ℂ => lorentzOfSL2C (G w) μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) 0 :=
      (((continuous_lorentzOfSL2C_entry μ ν).comp hG_cont).sub continuous_const).continuousAt
    have h0 : lorentzOfSL2C (G 0) μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν = 0 := by
      rw [hG_zero, lorentzOfSL2C_one, sub_self]
    have h_tend := hcont_at.tendsto
    rw [h0] at h_tend
    have h_ball : ∀ᶠ w : ℂ in 𝓝 0,
        dist (lorentzOfSL2C (G w) μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν) 0 < eps_mat :=
      h_tend (Metric.ball_mem_nhds 0 heps)
    exact h_ball.mono fun w hw => by
      rw [Real.dist_eq, sub_zero] at hw
      exact hw.le
  have h_mat_all : ∀ᶠ w : ℂ in 𝓝 0, ∀ μ ν : Fin 4,
      |lorentzOfSL2C (G w) μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν| ≤ eps_mat := by
    have h1 : ∀ μ : Fin 4, ∀ᶠ w : ℂ in 𝓝 0, ∀ ν : Fin 4,
        |lorentzOfSL2C (G w) μ ν - (1 : Matrix (Fin 4) (Fin 4) ℝ) μ ν| ≤ eps_mat :=
      fun μ => Filter.eventually_all.mpr (h_mat_ev μ)
    exact Filter.eventually_all.mpr h1
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.mem_nhds_iff.mp h_mat_all
  let ψ : ℂ × (Fin 3 → ℝ) → ℝ := fun wp =>
    ‖velocityVec m (massShellBoost m (G wp.1) wp.2) - velocityVec m wp.2‖
  have hψ_cont : Continuous ψ := by
    have h_mb : Continuous (fun wp : ℂ × (Fin 3 → ℝ) => massShellBoost m (G wp.1) wp.2) :=
      continuous_massShellBoost_comp (hG_cont.comp continuous_fst) continuous_snd
    exact (((continuous_velocityVec hm).comp h_mb).sub
      ((continuous_velocityVec hm).comp continuous_snd)).norm
  have hψ_local : ∀ p : Fin 3 → ℝ,
      ∃ δ_p > 0, ∃ ε_p > 0, ∀ w ∈ Metric.ball (0 : ℂ) δ_p,
        ∀ q ∈ Metric.ball p ε_p, ψ (w, q) ≤ r₁ := fun p => by
    have h0 : ψ (0, p) = 0 := by
      dsimp [ψ]
      rw [hG_zero, massShellBoost_one, sub_self, norm_zero]
    have h_nhds := (hψ_cont.continuousAt (x := (0, p))).tendsto
      (Metric.ball_mem_nhds (ψ (0, p)) hr₁)
    rw [nhds_prod_eq] at h_nhds
    obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h_nhds
    obtain ⟨δ_p, hδ_p_pos, hδ_p⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨ε_p, hε_p_pos, hε_p⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨δ_p, hδ_p_pos, ε_p, hε_p_pos, fun w hw q hq => ?_⟩
    have hmem := hUV (Set.mk_mem_prod (hδ_p hw) (hε_p hq))
    change ψ (w, q) ∈ Metric.ball (ψ (0, p)) r₁ at hmem
    rw [h0, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hmem
    exact hmem.le
  choose δ_p hδp_pos ε_p hεp_pos h_loc using hψ_local
  obtain ⟨t_cov, ht_cov⟩ := hK_cpct.elim_finite_subcover
    (fun p => Metric.ball p (ε_p p)) (fun p => Metric.isOpen_ball)
    fun p _ => Set.mem_iUnion.mpr ⟨p, Metric.mem_ball_self (hεp_pos p)⟩
  let δ₂ : ℝ := if hne : t_cov.Nonempty then t_cov.inf' hne δ_p else 1
  have hδ₂_pos : 0 < δ₂ := by
    dsimp [δ₂]
    split_ifs with hne
    · exact (Finset.lt_inf'_iff hne).mpr fun p _ => hδp_pos p
    · exact zero_lt_one
  have hδ₂ : ∀ w ∈ Metric.ball (0 : ℂ) δ₂, ∀ q ∈ K_all, ψ (w, q) ≤ r₁ := by
    intro w hw q hq
    have hmem := ht_cov hq
    rw [Set.mem_iUnion₂] at hmem
    obtain ⟨p, hp_cov, hq_ball⟩ := hmem
    have hne : t_cov.Nonempty := ⟨p, hp_cov⟩
    have hle : δ₂ ≤ δ_p p := by
      dsimp [δ₂]
      rw [dif_pos hne]
      exact Finset.inf'_le δ_p hp_cov
    have hw_p : w ∈ Metric.ball (0 : ℂ) (δ_p p) :=
      Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hw) hle)
    exact h_loc p w hw_p q hq_ball
  let δ : ℝ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  obtain ⟨M_n, hMn⟩ := exists_nat_gt (‖z‖ / δ)
  let N : ℕ := max 1 M_n
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left 1 M_n)
  have hN_gt : ‖z‖ / δ < (N : ℝ) := lt_of_lt_of_le hMn (by exact_mod_cast le_max_right 1 M_n)
  have h_step_norm : ‖z / (N : ℂ)‖ < δ := by
    have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
    rw [Complex.norm_div, Complex.norm_natCast, div_lt_iff₀ hN_real_pos]
    exact (div_lt_iff₀ hδ_pos).mp hN_gt |>.trans_eq (mul_comm _ _)
  have h_ball1 : z / (N : ℂ) ∈ Metric.ball (0 : ℂ) δ₁ :=
    Metric.mem_ball.mpr (by
      rw [dist_zero_right]
      exact lt_of_lt_of_le h_step_norm (min_le_left _ _))
  have h_ball2 : z / (N : ℂ) ∈ Metric.ball (0 : ℂ) δ₂ :=
    Metric.mem_ball.mpr (by
      rw [dist_zero_right]
      exact lt_of_lt_of_le h_step_norm (min_le_right _ _))
  exact ⟨N, hN_pos, hδ₁ h_ball1, fun q hq => hδ₂ (z / (N : ℂ)) h_ball2 q hq⟩

lemma lorentz_waveOp_of_oneParam
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot] (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0))
    (L : ∀ (r : ℕ), (Fin r → Fin P.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → P.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec P.toIsolatedMassShellData r s f)
      F (𝓝 (L r s f hf)))
    (W : SymmFockHilbert P.mode.ν η →ₗᵢ[ℂ] P.Hilbert)
    (hW : ∀ (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      W (symmFockMultiParticleVec P.mode.ν η P.mode.hη r s f) = L r s f hf)
    (G : ℂ → SL2C) (hG_cont : Continuous G) (hG_zero : G 0 = 1)
    (hG_add : ∀ w₁ w₂ : ℂ, G (w₁ + w₂) = G w₁ * G w₂)
    (z : ℂ) (Ψ : SymmFockHilbert P.mode.ν η) :
    P.lorentzEquiv (G z) (W Ψ) = W (P.fockLorentzEquiv (G z) Ψ) := by
  let D := P.toIsolatedMassShellData
  have h_on_mp : ∀ (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      P.lorentzEquiv (G z) (W (symmFockMultiParticleVec D.mode.ν η D.mode.hη r s f)) =
        W (P.fockLorentzEquiv (G z) (symmFockMultiParticleVec D.mode.ν η D.mode.hη r s f)) := by
    intro r s f hf
    rcases r with _ | r'
    · have h_mp0 : symmFockMultiParticleVec D.mode.ν η D.mode.hη 0 s f =
          symmFockVacuum D.mode.ν η :=
        symmFockMultiParticleVec_zero D.mode.ν D.mode.hη s f
      have h_vac0 : L 0 s f hf = D.vacuum := by
        have h_eq : haagRuelleChainVec D 0 s f = fun _ => D.vacuum :=
          funext fun t => haagRuelleChainVec_zero D s f t
        have h_tend := hL 0 s f hf
        rw [h_eq] at h_tend
        exact tendsto_nhds_unique h_tend tendsto_const_nhds
      have h_wvac : W (symmFockVacuum D.mode.ν η) = D.vacuum := by
        rw [← h_mp0, hW 0 s f hf, h_vac0]
      have h_lv : P.lorentzEquiv (G z) D.vacuum = D.vacuum :=
        wightmanSpinorLorentzEquiv_vacuum D.wightman.WData D.wightman.poincare (G z)
      have h_fv : P.fockLorentzEquiv (G z) (symmFockVacuum D.mode.ν η) =
          symmFockVacuum D.mode.ν η :=
        symmFockLorentzEquiv_vacuum P.modeData (G z)
      rw [h_mp0, h_fv, h_wvac, h_lv]
    · obtain ⟨d_tube, hdt_pos, h_tube_sep⟩ :=
        exists_oneParam_uniform_velocitySep D.hm G hG_cont r' f hf z
      let r₁ : ℝ := d_tube / 12
      have hr₁ : 0 < r₁ := by positivity
      let eps_mat : ℝ := r₁ / (4 * (1 + r₁))
      have heps_mat : 0 < eps_mat := by positivity
      let K_all : Set (Fin 3 → ℝ) := ⋃ i : Fin (r' + 1),
        (fun uq : ℝ × (Fin 3 → ℝ) => massShellBoost m (G ((uq.1 : ℂ) * z)) uq.2) ''
          (Set.Icc (0 : ℝ) 1 ×ˢ tsupport (f i).amp)
      have hK_all_cpct : IsCompact K_all := by
        refine isCompact_iUnion fun i => ?_
        have hG_sub : Continuous (fun uq : ℝ × (Fin 3 → ℝ) => G ((uq.1 : ℂ) * z)) :=
          hG_cont.comp ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)
        have h_im : Continuous (fun uq : ℝ × (Fin 3 → ℝ) =>
            massShellBoost m (G ((uq.1 : ℂ) * z)) uq.2) :=
          continuous_massShellBoost_comp hG_sub continuous_snd
        exact (isCompact_Icc.prod (f i).compactSupport.isCompact).image h_im
      obtain ⟨N, hN_pos, hA_mat, hA_vel⟩ := exists_oneParam_step_count D.hm G hG_cont hG_zero
        K_all hK_all_cpct hr₁ heps_mat z
      let step_z : ℂ := z / (N : ℂ)
      have h_ind : ∀ k : ℕ, k ≤ N →
          P.lorentzEquiv (G ((k : ℂ) * step_z))
              (W (symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s f)) =
            W (P.fockLorentzEquiv (G ((k : ℂ) * step_z))
              (symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s f)) := by
        intro k hk
        induction k with
        | zero =>
          rw [Nat.cast_zero, zero_mul, hG_zero]
          have hl1 : P.lorentzEquiv 1
              (W (symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s f)) =
              W (symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s f) := by
            change wightmanSpinorLorentzEquiv D.wightman.WData D.wightman.poincare 1 _ = _
            rw [wightmanSpinorLorentzEquiv_one]
            rfl
          have hf1 : P.fockLorentzEquiv 1
              (symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s f) =
              symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s f := by
            dsimp [PoincareIsolatedMassShellData.fockLorentzEquiv]
            rw [symmFockLorentzEquiv_one]
            rfl
          rw [hl1, hf1]
        | succ k ih =>
          have hk_le : k ≤ N := Nat.le_of_succ_le hk
          have ih_k := ih hk_le
          have h_add_eq : ((k + 1 : ℕ) : ℂ) * step_z = step_z + (k : ℂ) * step_z := by
            push_cast
            ring
          rw [h_add_eq, hG_add]
          let A_k := G ((k : ℂ) * step_z)
          have h_mul_l : ∀ x : P.Hilbert,
              P.lorentzEquiv (G step_z * A_k) x =
                P.lorentzEquiv (G step_z) (P.lorentzEquiv A_k x) :=
            fun x => wightmanSpinorLorentzEquiv_mul D.wightman.WData D.wightman.poincare _ _ x
          have h_mul_f : ∀ x : SymmFockHilbert D.mode.ν η,
              P.fockLorentzEquiv (G step_z * A_k) x =
                P.fockLorentzEquiv (G step_z) (P.fockLorentzEquiv A_k x) :=
            fun x => symmFockLorentzEquiv_mul P.modeData _ _ x
          rw [h_mul_l, ih_k, h_mul_f]
          dsimp [PoincareIsolatedMassShellData.fockLorentzEquiv]
          rw [symmFockLorentzEquiv_multiParticleVec, map_sum, map_sum, map_sum, map_sum]
          refine Finset.sum_congr rfl fun s_k _ => ?_
          let g_k : Fin (r' + 1) → SmoothWavepacket := fun i =>
            lorentzModeWavepacket P.modeData A_k (s_k i) (s i) (f i)
          have hg_disj : Pairwise fun i j : Fin (r' + 1) => VelocityDisjoint m (g_k i) (g_k j) :=
            fun _ _ hij => velocityDisjoint_lorentzModeWavepacket P.modeData A_k _ _ _ _ (hf hij)
          have hu_mem : ((k : ℝ) / (N : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
            refine ⟨by positivity, ?_⟩
            rw [div_le_one (by exact_mod_cast hN_pos)]
            exact_mod_cast hk_le
          have hAk_eq : A_k = G (((((k : ℝ) / (N : ℝ)) : ℝ) : ℂ) * z) := by
            dsimp [A_k, step_z]
            congr 1
            push_cast
            ring
          have hgk_sep : ∀ (i j : Fin (r' + 1)), i ≠ j →
              ∀ v₁ ∈ velocitySupport m (g_k i), ∀ v₂ ∈ velocitySupport m (g_k j),
                d_tube ≤ ‖v₁ - v₂‖ := by
            intro i j hij v₁ hv₁ v₂ hv₂
            obtain ⟨q₁, hq₁, rfl⟩ := hv₁
            obtain ⟨q₂, hq₂, rfl⟩ := hv₂
            obtain ⟨p₁, hp₁, rfl⟩ := tsupport_lorentzModeWavepacket_subset P.modeData A_k (s_k i)
              (s i) (f i) hq₁
            obtain ⟨p₂, hp₂, rfl⟩ := tsupport_lorentzModeWavepacket_subset P.modeData A_k (s_k j)
              (s j) (f j) hq₂
            rw [hAk_eq]
            exact h_tube_sep ((k : ℝ) / (N : ℝ)) hu_mem i j hij p₁ hp₁ p₂ hp₂
          have hgk_vel : ∀ (i : Fin (r' + 1)) (q : Fin 3 → ℝ), q ∈ tsupport (g_k i).amp →
              ‖velocityVec m (massShellBoost m (G step_z) q) - velocityVec m q‖ ≤ r₁ := by
            intro i q hq
            obtain ⟨p, hp, rfl⟩ := tsupport_lorentzModeWavepacket_subset P.modeData A_k (s_k i)
              (s i) (f i) hq
            have hmemK : massShellBoost m A_k p ∈ K_all := by
              rw [hAk_eq, Set.mem_iUnion]
              exact ⟨i, ((k : ℝ) / (N : ℝ), p), ⟨hu_mem, hp⟩, rfl⟩
            exact hA_vel _ hmemK
          rw [hW (r' + 1) s_k g_k hg_disj]
          have h_small := lorentz_haagRuelleLimit_of_small P hF_inv L hL (r' + 1) s_k g_k hg_disj
            d_tube hdt_pos hgk_sep (G step_z) hA_mat hgk_vel
          rw [h_small]
          change (∑ s' : Fin (r' + 1) → Fin P.mode.ν, L (r' + 1) s' _ _) =
            W (symmFockLorentzEquiv P.modeData (G step_z)
              (symmFockMultiParticleVec D.mode.ν η D.mode.hη (r' + 1) s_k g_k))
          rw [symmFockLorentzEquiv_multiParticleVec, map_sum]
          refine Finset.sum_congr rfl fun s' _ => ?_
          exact (hW (r' + 1) s' _ _).symm
      have h_final := h_ind N le_rfl
      have hNz : ((N : ℂ) * step_z) = z := by
        dsimp [step_z]
        have hN_ne : (N : ℂ) ≠ 0 := by exact_mod_cast hN_pos.ne'
        exact mul_div_cancel₀ z hN_ne
      rwa [hNz] at h_final
  let S_gen : Submodule ℂ (SymmFockHilbert D.mode.ν η) :=
    Submodule.span ℂ (Set.range (fun cfg : DisjointWavepacketConfig D.mode.ν m =>
      symmFockMultiParticleVec D.mode.ν η D.mode.hη cfg.1 cfg.2.1 cfg.2.2.1))
  have h_dense : Dense (S_gen : Set (SymmFockHilbert D.mode.ν η)) :=
    dense_range_symmFockMultiParticleVec D.mode.ν D.hm D.mode.hη
  have h_on_span : ∀ v ∈ S_gen, P.lorentzEquiv (G z) (W v) =
      W (P.fockLorentzEquiv (G z) v) := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨⟨r, s, f, hf⟩, rfl⟩
      exact h_on_mp r s f hf
    · simp
    · intro u w _ _ hu hw
      rw [map_add, map_add, map_add, map_add, hu, hw]
    · intro c u _ hu
      rw [map_smul, map_smul, map_smul, map_smul, hu]
  have hL_cont : Continuous (fun v => P.lorentzEquiv (G z) (W v)) :=
    (P.lorentzEquiv (G z)).isometry.continuous.comp W.continuous
  have hR_cont : Continuous (fun v => W (P.fockLorentzEquiv (G z) v)) :=
    W.continuous.comp (P.fockLorentzEquiv (G z)).isometry.continuous
  exact h_dense.induction h_on_span (isClosed_eq hL_cont hR_cont) Ψ

lemma lorentz_waveOp
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    {F : Filter ℝ} [F.NeBot] (hF_inv : Tendsto (fun t : ℝ => (1 + |t|)⁻¹) F (𝓝 0))
    (L : ∀ (r : ℕ), (Fin r → Fin P.mode.ν) → (f : Fin r → SmoothWavepacket) →
      Pairwise (fun i j : Fin r => VelocityDisjoint m (f i) (f j)) → P.Hilbert)
    (hL : ∀ r s f hf, Tendsto (haagRuelleChainVec P.toIsolatedMassShellData r s f)
      F (𝓝 (L r s f hf)))
    (W : SymmFockHilbert P.mode.ν η →ₗᵢ[ℂ] P.Hilbert)
    (hW : ∀ (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      W (symmFockMultiParticleVec P.mode.ν η P.mode.hη r s f) = L r s f hf)
    (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    P.lorentzEquiv A (W Ψ) = W (P.fockLorentzEquiv A Ψ) := by
  have h_gen := sl2c_generated_by_upper_lower A
  induction h_gen generalizing Ψ with
  | upper z =>
    let G : ℂ → SL2C := fun w => ⟨!![1, w; (0 : ℂ), 1], sl2c_upper_det_u w⟩
    refine lorentz_waveOp_of_oneParam P hF_inv L hL W hW G continuous_sl2cUpper ?_ ?_ z Ψ
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [G]
    · intro w₁ w₂
      ext i j
      fin_cases i <;> fin_cases j <;> simp [G, Matrix.mul_apply, add_comm]
  | lower z =>
    let G : ℂ → SL2C := fun w => ⟨!![1, (0 : ℂ); w, 1], sl2c_lower_det_l w⟩
    refine lorentz_waveOp_of_oneParam P hF_inv L hL W hW G continuous_sl2cLower ?_ ?_ z Ψ
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [G]
    · intro w₁ w₂
      ext i j
      fin_cases i <;> fin_cases j <;> simp [G, Matrix.mul_apply, add_comm]
  | one =>
    have hl1 : P.lorentzEquiv 1 (W Ψ) = W Ψ := by
      change wightmanSpinorLorentzEquiv P.wightman.WData P.wightman.poincare 1 (W Ψ) = W Ψ
      rw [wightmanSpinorLorentzEquiv_one]
      rfl
    have hf1 : P.fockLorentzEquiv 1 Ψ = Ψ := by
      dsimp [PoincareIsolatedMassShellData.fockLorentzEquiv]
      rw [symmFockLorentzEquiv_one]
      rfl
    rw [hl1, hf1]
  | @mul A₁ B₁ _ _ ihA ihB =>
    have h_mul_l : ∀ x : P.Hilbert,
        P.lorentzEquiv (A₁ * B₁) x = P.lorentzEquiv A₁ (P.lorentzEquiv B₁ x) :=
      fun x => wightmanSpinorLorentzEquiv_mul P.wightman.WData P.wightman.poincare A₁ B₁ x
    have h_mul_f : ∀ x : SymmFockHilbert P.mode.ν η,
        P.fockLorentzEquiv (A₁ * B₁) x = P.fockLorentzEquiv A₁ (P.fockLorentzEquiv B₁ x) :=
      fun x => symmFockLorentzEquiv_mul P.modeData A₁ B₁ x
    rw [h_mul_l, ihB Ψ, ihA _, h_mul_f]
  | @inv B _ ihB =>
    have h_mul_l : ∀ x : P.Hilbert,
        P.lorentzEquiv (B⁻¹ * B) x = P.lorentzEquiv B⁻¹ (P.lorentzEquiv B x) :=
      fun x => wightmanSpinorLorentzEquiv_mul P.wightman.WData P.wightman.poincare B⁻¹ B x
    have hl1 : P.lorentzEquiv 1 (W (P.fockLorentzEquiv B⁻¹ Ψ)) =
        W (P.fockLorentzEquiv B⁻¹ Ψ) := by
      change wightmanSpinorLorentzEquiv P.wightman.WData P.wightman.poincare 1 _ = _
      rw [wightmanSpinorLorentzEquiv_one]
      rfl
    have h_mul_f : P.fockLorentzEquiv B (P.fockLorentzEquiv B⁻¹ Ψ) = Ψ := by
      dsimp [PoincareIsolatedMassShellData.fockLorentzEquiv]
      rw [← symmFockLorentzEquiv_mul, mul_inv_cancel, symmFockLorentzEquiv_one]
      rfl
    have h_eq := ihB (P.fockLorentzEquiv B⁻¹ Ψ)
    rw [h_mul_f] at h_eq
    have h_app := congrArg (P.lorentzEquiv B⁻¹) h_eq
    rw [← h_mul_l, inv_mul_cancel, hl1] at h_app
    exact h_app.symm

theorem lorentz_mollerWaveOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    P.lorentzEquiv A (mollerWaveOut P.toIsolatedMassShellData Ψ) =
      mollerWaveOut P.toIsolatedMassShellData (P.fockLorentzEquiv A Ψ) :=
  lorentz_waveOp P tendsto_inv_one_add_abs_atTop
    (haagRuelleOutVec P.toIsolatedMassShellData)
    (tendsto_haagRuelleChainVec_atTop P.toIsolatedMassShellData)
    (mollerWaveOut P.toIsolatedMassShellData)
    (mollerWaveOut_symmFockMultiParticleVec P.toIsolatedMassShellData) A Ψ

theorem lorentz_mollerWaveIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    P.lorentzEquiv A (mollerWaveIn P.toIsolatedMassShellData Ψ) =
      mollerWaveIn P.toIsolatedMassShellData (P.fockLorentzEquiv A Ψ) :=
  lorentz_waveOp P tendsto_inv_one_add_abs_atBot
    (haagRuelleInVec P.toIsolatedMassShellData)
    (tendsto_haagRuelleChainVec_atBot P.toIsolatedMassShellData)
    (mollerWaveIn P.toIsolatedMassShellData)
    (mollerWaveIn_symmFockMultiParticleVec P.toIsolatedMassShellData) A Ψ

theorem poincare_mollerWaveOut
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    P.poincareEquiv a A (mollerWaveOut P.toIsolatedMassShellData Ψ) =
      mollerWaveOut P.toIsolatedMassShellData (P.fockPoincareEquiv a A Ψ) := by
  rw [P.poincareEquiv_eq_translate_lorentz, lorentz_mollerWaveOut P A Ψ,
    translate_mollerWaveOut P.toIsolatedMassShellData a _]
  rfl

theorem poincare_mollerWaveIn
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    P.poincareEquiv a A (mollerWaveIn P.toIsolatedMassShellData Ψ) =
      mollerWaveIn P.toIsolatedMassShellData (P.fockPoincareEquiv a A Ψ) := by
  rw [P.poincareEquiv_eq_translate_lorentz, lorentz_mollerWaveIn P A Ψ,
    translate_mollerWaveIn P.toIsolatedMassShellData a _]
  rfl

theorem lorentz_haagRuelleOutVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    P.lorentzEquiv A (haagRuelleOutVec P.toIsolatedMassShellData r s f hf) =
      ∑ s' : Fin r → Fin P.mode.ν,
        haagRuelleOutVec P.toIsolatedMassShellData r s'
          (fun i => lorentzModeWavepacket P.modeData A (s' i) (s i) (f i))
          (fun _ _ hij =>
            velocityDisjoint_lorentzModeWavepacket P.modeData A _ _ _ _ (hf hij)) := by
  have h_eq := lorentz_mollerWaveOut P A
    (symmFockMultiParticleVec P.mode.ν η P.mode.hη r s f)
  rw [mollerWaveOut_symmFockMultiParticleVec P.toIsolatedMassShellData r s f hf,
    PoincareIsolatedMassShellData.fockLorentzEquiv, symmFockLorentzEquiv_multiParticleVec,
    map_sum] at h_eq
  rw [h_eq]
  refine Finset.sum_congr rfl fun s' _ => ?_
  exact mollerWaveOut_symmFockMultiParticleVec P.toIsolatedMassShellData r s' _ _

theorem lorentz_haagRuelleInVec
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (r : ℕ) (s : Fin r → Fin P.mode.ν) (f : Fin r → SmoothWavepacket)
    (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)) :
    P.lorentzEquiv A (haagRuelleInVec P.toIsolatedMassShellData r s f hf) =
      ∑ s' : Fin r → Fin P.mode.ν,
        haagRuelleInVec P.toIsolatedMassShellData r s'
          (fun i => lorentzModeWavepacket P.modeData A (s' i) (s i) (f i))
          (fun _ _ hij =>
            velocityDisjoint_lorentzModeWavepacket P.modeData A _ _ _ _ (hf hij)) := by
  have h_eq := lorentz_mollerWaveIn P A
    (symmFockMultiParticleVec P.mode.ν η P.mode.hη r s f)
  rw [mollerWaveIn_symmFockMultiParticleVec P.toIsolatedMassShellData r s f hf,
    PoincareIsolatedMassShellData.fockLorentzEquiv, symmFockLorentzEquiv_multiParticleVec,
    map_sum] at h_eq
  rw [h_eq]
  refine Finset.sum_congr rfl fun s' _ => ?_
  exact mollerWaveIn_symmFockMultiParticleVec P.toIsolatedMassShellData r s' _ _

end WaveOperatorIntertwining

section SMatrixPoincareAndCPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem poincare_mem_asymptoticSubspaceOut_iff
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) (x : P.Hilbert) :
    P.poincareEquiv a A x ∈ AsymptoticSubspaceOut P.toIsolatedMassShellData ↔
      x ∈ AsymptoticSubspaceOut P.toIsolatedMassShellData := by
  constructor
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveOut P.toIsolatedMassShellData Ψ = P.poincareEquiv a A x at hΨ
    refine LinearMap.mem_range.mpr ⟨(P.fockPoincareEquiv a A).symm Ψ, ?_⟩
    change mollerWaveOut P.toIsolatedMassShellData ((P.fockPoincareEquiv a A).symm Ψ) = x
    apply (P.poincareEquiv a A).injective
    rw [poincare_mollerWaveOut, LinearIsometryEquiv.apply_symm_apply]
    exact hΨ
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveOut P.toIsolatedMassShellData Ψ = x at hΨ
    refine LinearMap.mem_range.mpr ⟨P.fockPoincareEquiv a A Ψ, ?_⟩
    change mollerWaveOut P.toIsolatedMassShellData (P.fockPoincareEquiv a A Ψ) =
      P.poincareEquiv a A x
    rw [← hΨ, poincare_mollerWaveOut]

theorem poincare_mem_asymptoticSubspaceIn_iff
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) (x : P.Hilbert) :
    P.poincareEquiv a A x ∈ AsymptoticSubspaceIn P.toIsolatedMassShellData ↔
      x ∈ AsymptoticSubspaceIn P.toIsolatedMassShellData := by
  constructor
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveIn P.toIsolatedMassShellData Ψ = P.poincareEquiv a A x at hΨ
    refine LinearMap.mem_range.mpr ⟨(P.fockPoincareEquiv a A).symm Ψ, ?_⟩
    change mollerWaveIn P.toIsolatedMassShellData ((P.fockPoincareEquiv a A).symm Ψ) = x
    apply (P.poincareEquiv a A).injective
    rw [poincare_mollerWaveIn, LinearIsometryEquiv.apply_symm_apply]
    exact hΨ
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveIn P.toIsolatedMassShellData Ψ = x at hΨ
    refine LinearMap.mem_range.mpr ⟨P.fockPoincareEquiv a A Ψ, ?_⟩
    change mollerWaveIn P.toIsolatedMassShellData (P.fockPoincareEquiv a A Ψ) =
      P.poincareEquiv a A x
    rw [← hΨ, poincare_mollerWaveIn]

theorem pct_mem_asymptoticSubspaceOut_iff_in
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell) (x : P.Hilbert) :
    P.pctEquiv hε x ∈ AsymptoticSubspaceOut P.toIsolatedMassShellData ↔
      x ∈ AsymptoticSubspaceIn P.toIsolatedMassShellData := by
  constructor
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveOut P.toIsolatedMassShellData Ψ = P.pctEquiv hε x at hΨ
    refine LinearMap.mem_range.mpr ⟨(P.fockPCTEquiv hε hC_pct).symm Ψ, ?_⟩
    change mollerWaveIn P.toIsolatedMassShellData ((P.fockPCTEquiv hε hC_pct).symm Ψ) = x
    apply (P.pctEquiv hε).injective
    rw [pct_mollerWaveIn P hε hC_pct, LinearIsometryEquiv.apply_symm_apply]
    exact hΨ
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveIn P.toIsolatedMassShellData Ψ = x at hΨ
    refine LinearMap.mem_range.mpr ⟨P.fockPCTEquiv hε hC_pct Ψ, ?_⟩
    change mollerWaveOut P.toIsolatedMassShellData (P.fockPCTEquiv hε hC_pct Ψ) = P.pctEquiv hε x
    rw [← hΨ, pct_mollerWaveIn P hε hC_pct]

theorem pct_mem_asymptoticSubspaceIn_iff_out
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell) (x : P.Hilbert) :
    P.pctEquiv hε x ∈ AsymptoticSubspaceIn P.toIsolatedMassShellData ↔
      x ∈ AsymptoticSubspaceOut P.toIsolatedMassShellData := by
  constructor
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveIn P.toIsolatedMassShellData Ψ = P.pctEquiv hε x at hΨ
    refine LinearMap.mem_range.mpr ⟨(P.fockPCTEquiv hε hC_pct).symm Ψ, ?_⟩
    change mollerWaveOut P.toIsolatedMassShellData ((P.fockPCTEquiv hε hC_pct).symm Ψ) = x
    apply (P.pctEquiv hε).injective
    rw [pct_mollerWaveOut P hε hC_pct, LinearIsometryEquiv.apply_symm_apply]
    exact hΨ
  · intro hx
    obtain ⟨Ψ, hΨ⟩ := LinearMap.mem_range.mp hx
    change mollerWaveOut P.toIsolatedMassShellData Ψ = x at hΨ
    refine LinearMap.mem_range.mpr ⟨P.fockPCTEquiv hε hC_pct Ψ, ?_⟩
    change mollerWaveIn P.toIsolatedMassShellData (P.fockPCTEquiv hε hC_pct Ψ) = P.pctEquiv hε x
    rw [← hΨ, pct_mollerWaveOut P hε hC_pct]

theorem pct_image_asymptoticSubspaceOut_eq_in
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell) :
    P.pctEquiv hε '' (AsymptoticSubspaceOut P.toIsolatedMassShellData : Set P.Hilbert) =
      (AsymptoticSubspaceIn P.toIsolatedMassShellData : Set P.Hilbert) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (pct_mem_asymptoticSubspaceIn_iff_out P hε hC_pct x).mpr hx
  · intro hy
    refine ⟨(P.pctEquiv hε).symm y, ?_, LinearIsometryEquiv.apply_symm_apply _ y⟩
    rw [SetLike.mem_coe, ← pct_mem_asymptoticSubspaceIn_iff_out P hε hC_pct,
      LinearIsometryEquiv.apply_symm_apply]
    exact hy

theorem weakAsymptoticCompleteness_iff_pct_mem_out
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell) :
    WeakAsymptoticCompleteness P.toIsolatedMassShellData ↔
      ∀ x : P.Hilbert, P.pctEquiv hε x ∈ AsymptoticSubspaceOut P.toIsolatedMassShellData ↔
        x ∈ AsymptoticSubspaceOut P.toIsolatedMassShellData := by
  constructor
  · intro hweak x
    rw [pct_mem_asymptoticSubspaceOut_iff_in P hε hC_pct x, hweak]
  · intro h_pct
    ext x
    rw [← pct_mem_asymptoticSubspaceOut_iff_in P hε hC_pct x, h_pct x]

theorem scatteringOperatorCLM_comm_lorentz
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    scatteringOperatorCLM P.toIsolatedMassShellData (P.fockLorentzEquiv A Ψ) =
      P.fockLorentzEquiv A (scatteringOperatorCLM P.toIsolatedMassShellData Ψ) := by
  let D := P.toIsolatedMassShellData
  refine ext_inner_left ℂ fun Φ => ?_
  have hR : ⟪Φ, P.fockLorentzEquiv A (scatteringOperatorCLM D Ψ)⟫_ℂ =
      ⟪(P.fockLorentzEquiv A).symm Φ, scatteringOperatorCLM D Ψ⟫_ℂ := by
    conv_lhs => rw [← (P.fockLorentzEquiv A).apply_symm_apply Φ]
    exact (P.fockLorentzEquiv A).inner_map_map _ _
  have h_out : mollerWaveOut D Φ =
      P.lorentzEquiv A (mollerWaveOut D ((P.fockLorentzEquiv A).symm Φ)) := by
    rw [lorentz_mollerWaveOut, LinearIsometryEquiv.apply_symm_apply]
  have hL : ⟪Φ, scatteringOperatorCLM D (P.fockLorentzEquiv A Ψ)⟫_ℂ =
      ⟪(P.fockLorentzEquiv A).symm Φ, scatteringOperatorCLM D Ψ⟫_ℂ := by
    rw [inner_scatteringOperatorCLM, ← lorentz_mollerWaveIn P A Ψ, h_out,
      (P.lorentzEquiv A).inner_map_map, ← inner_scatteringOperatorCLM]
  exact hL.trans hR.symm

theorem scatteringOperatorCLM_comm_poincare
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    scatteringOperatorCLM P.toIsolatedMassShellData (P.fockPoincareEquiv a A Ψ) =
      P.fockPoincareEquiv a A (scatteringOperatorCLM P.toIsolatedMassShellData Ψ) := by
  change scatteringOperatorCLM P.toIsolatedMassShellData
      (symmFockMinkowskiTranslate m P.mode.ν η a (P.fockLorentzEquiv A Ψ)) =
    symmFockMinkowskiTranslate m P.mode.ν η a
      (P.fockLorentzEquiv A (scatteringOperatorCLM P.toIsolatedMassShellData Ψ))
  rw [scatteringOperatorCLM_comm_translate P.toIsolatedMassShellData a,
    scatteringOperatorCLM_comm_lorentz P A Ψ]

theorem scatteringOperatorCLM_comp_poincare
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (a : Fin 4 → ℝ) (A : SL2C) :
    (scatteringOperatorCLM P.toIsolatedMassShellData).comp
        (P.fockPoincareEquiv a A).toLinearIsometry.toContinuousLinearMap =
      (P.fockPoincareEquiv a A).toLinearIsometry.toContinuousLinearMap.comp
        (scatteringOperatorCLM P.toIsolatedMassShellData) := by
  apply ContinuousLinearMap.ext
  intro Ψ
  exact scatteringOperatorCLM_comm_poincare P a A Ψ

theorem inner_symmFockPCTEquiv_scatteringOperatorCLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell)
    (Φ Ψ : SymmFockHilbert P.mode.ν η) :
    ⟪P.fockPCTEquiv hε hC_pct Φ,
        scatteringOperatorCLM P.toIsolatedMassShellData (P.fockPCTEquiv hε hC_pct Ψ)⟫_ℂ =
      ⟪Ψ, scatteringOperatorCLM P.toIsolatedMassShellData Φ⟫_ℂ := by
  let D := P.toIsolatedMassShellData
  rw [inner_scatteringOperatorCLM, ← pct_mollerWaveOut P hε hC_pct Ψ,
    ← pct_mollerWaveIn P hε hC_pct Φ]
  have h_pct := inner_wightmanPCTEquiv D.wightman.WData D.wightman.poincare
    D.wightman.toWightmanAxioms.wightmanPCT hε (mollerWaveIn D Φ) (mollerWaveOut D Ψ)
  change ⟪P.pctEquiv hε (mollerWaveIn D Φ), P.pctEquiv hε (mollerWaveOut D Ψ)⟫_ℂ =
      star ⟪mollerWaveIn D Φ, mollerWaveOut D Ψ⟫_ℂ at h_pct
  have h_swap : star ⟪mollerWaveIn D Φ, mollerWaveOut D Ψ⟫_ℂ =
      ⟪mollerWaveOut D Ψ, mollerWaveIn D Φ⟫_ℂ := inner_conj_symm _ _
  rw [h_pct, h_swap, ← inner_scatteringOperatorCLM]

theorem symmFockPCTEquiv_symm_scatteringOperatorCLM_pct
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell)
    (Ψ : SymmFockHilbert P.mode.ν η) :
    (P.fockPCTEquiv hε hC_pct).symm
        (scatteringOperatorCLM P.toIsolatedMassShellData (P.fockPCTEquiv hε hC_pct Ψ)) =
      (scatteringOperatorCLM P.toIsolatedMassShellData).adjoint Ψ := by
  let D := P.toIsolatedMassShellData
  refine ext_inner_left ℂ fun Φ => ?_
  have h_inn := inner_symmFockPCTEquiv P.modeData hε hC_pct Φ
    ((P.fockPCTEquiv hε hC_pct).symm (scatteringOperatorCLM D (P.fockPCTEquiv hε hC_pct Ψ)))
  change ⟪P.fockPCTEquiv hε hC_pct Φ,
      P.fockPCTEquiv hε hC_pct ((P.fockPCTEquiv hε hC_pct).symm
        (scatteringOperatorCLM D (P.fockPCTEquiv hε hC_pct Ψ)))⟫_ℂ =
    star ⟪Φ, (P.fockPCTEquiv hε hC_pct).symm
      (scatteringOperatorCLM D (P.fockPCTEquiv hε hC_pct Ψ))⟫_ℂ at h_inn
  rw [LinearIsometryEquiv.apply_symm_apply] at h_inn
  have h_star := congrArg star h_inn.symm
  have h_swap : star ⟪Ψ, scatteringOperatorCLM D Φ⟫_ℂ =
      ⟪scatteringOperatorCLM D Φ, Ψ⟫_ℂ := inner_conj_symm _ _
  have h_adj : ⟪scatteringOperatorCLM D Φ, Ψ⟫_ℂ =
      ⟪Φ, (scatteringOperatorCLM D).adjoint Ψ⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_right (scatteringOperatorCLM D) Φ Ψ).symm
  rw [star_star, inner_symmFockPCTEquiv_scatteringOperatorCLM P hε hC_pct Φ Ψ,
    h_swap, h_adj] at h_star
  exact h_star

theorem scatteringWeakUnitary_comm_poincare
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hweak : WeakAsymptoticCompleteness P.toIsolatedMassShellData)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    scatteringWeakUnitary P.toIsolatedMassShellData hweak (P.fockPoincareEquiv a A Ψ) =
      P.fockPoincareEquiv a A (scatteringWeakUnitary P.toIsolatedMassShellData hweak Ψ) := by
  simp only [scatteringWeakUnitary_apply]
  exact scatteringOperatorCLM_comm_poincare P a A Ψ

theorem scatteringUnitary_comm_poincare
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hcomp : AsymptoticCompleteness P.toIsolatedMassShellData)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert P.mode.ν η) :
    scatteringUnitary P.toIsolatedMassShellData hcomp (P.fockPoincareEquiv a A Ψ) =
      P.fockPoincareEquiv a A (scatteringUnitary P.toIsolatedMassShellData hcomp Ψ) := by
  rw [scatteringUnitary_eq_weak]
  exact scatteringWeakUnitary_comm_poincare P hcomp.toWeak a A Ψ

theorem symmFockPCTEquiv_symm_scatteringWeakUnitary_pct
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell)
    (hweak : WeakAsymptoticCompleteness P.toIsolatedMassShellData)
    (Ψ : SymmFockHilbert P.mode.ν η) :
    (P.fockPCTEquiv hε hC_pct).symm
        (scatteringWeakUnitary P.toIsolatedMassShellData hweak (P.fockPCTEquiv hε hC_pct Ψ)) =
      (scatteringWeakUnitary P.toIsolatedMassShellData hweak).symm Ψ := by
  let D := P.toIsolatedMassShellData
  rw [scatteringWeakUnitary_apply, symmFockPCTEquiv_symm_scatteringOperatorCLM_pct P hε hC_pct Ψ]
  refine ext_inner_left ℂ fun Φ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← scatteringWeakUnitary_apply D hweak Φ,
    LinearIsometryEquiv.inner_map_eq_flip]

theorem symmFockPCTEquiv_symm_scatteringUnitary_pct
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} (P : PoincareIsolatedMassShellData R S m M η)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η P.C_shell)
    (hcomp : AsymptoticCompleteness P.toIsolatedMassShellData)
    (Ψ : SymmFockHilbert P.mode.ν η) :
    (P.fockPCTEquiv hε hC_pct).symm
        (scatteringUnitary P.toIsolatedMassShellData hcomp (P.fockPCTEquiv hε hC_pct Ψ)) =
      (scatteringUnitary P.toIsolatedMassShellData hcomp).symm Ψ := by
  rw [scatteringUnitary_eq_weak]
  exact symmFockPCTEquiv_symm_scatteringWeakUnitary_pct P hε hC_pct hcomp.toWeak Ψ

end SMatrixPoincareAndCPT

section EuclidPoincareScatteringBridge

structure EuclidPoincareIsolatedMassShellData {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (m M : ℝ) (η : ℂ) (𝒮 : SchwingerFamily ι) extends
    EuclidIsolatedMassShellData R S m M η 𝒮 where
  contDiff_w : ∀ (s : Fin mode.ν) (α : ι),
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => mode.w s p α)
  hC_cov : ∀ (A : SL2C) (p : Fin 3 → ℝ) (α : Fin 2 → ι),
    C_shell α ((lorentzOfSL2C A).mulVec (massShellVec m p)) =
      ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C_shell β (massShellVec m p)

namespace EuclidPoincareIsolatedMassShellData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {m M : ℝ} {η : ℂ} {𝒮 : SchwingerFamily ι}

abbrev toPoincareData (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮) :
    PoincareIsolatedMassShellData R S m M η :=
  { E.toIsolatedMassShellData with
    contDiff_w := E.contDiff_w
    hC_cov := E.hC_cov }

def osLorentzEquiv (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮) (A : SL2C) :
    E.OSHilbert ≃ₗᵢ[ℂ] E.OSHilbert :=
  (E.osToWightmanEquiv.trans (E.toPoincareData.lorentzEquiv A)).trans E.osToWightmanEquiv.symm

def osPoincareEquiv (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (a : Fin 4 → ℝ) (A : SL2C) :
    E.OSHilbert ≃ₗᵢ[ℂ] E.OSHilbert :=
  (E.osToWightmanEquiv.trans (E.toPoincareData.poincareEquiv a A)).trans E.osToWightmanEquiv.symm

def osPCTEquiv (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) :
    E.OSHilbert ≃ₗᵢ⋆[ℂ] E.OSHilbert where
  toFun x := E.osToWightmanEquiv.symm (E.toPoincareData.pctEquiv hε (E.osToWightmanEquiv x))
  invFun x :=
    E.osToWightmanEquiv.symm ((E.toPoincareData.pctEquiv hε).symm (E.osToWightmanEquiv x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' c x := by rw [map_smul, map_smulₛₗ, map_smul]
  norm_map' x := by simp

@[simp]
lemma osToWightmanEquiv_osLorentzEquiv
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮) (A : SL2C) (x : E.OSHilbert) :
    E.osToWightmanEquiv (E.osLorentzEquiv A x) =
      E.toPoincareData.lorentzEquiv A (E.osToWightmanEquiv x) := by
  simp [osLorentzEquiv]

@[simp]
lemma osToWightmanEquiv_osPoincareEquiv
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (a : Fin 4 → ℝ) (A : SL2C) (x : E.OSHilbert) :
    E.osToWightmanEquiv (E.osPoincareEquiv a A x) =
      E.toPoincareData.poincareEquiv a A (E.osToWightmanEquiv x) := by
  simp [osPoincareEquiv]

@[simp]
lemma osToWightmanEquiv_osPCTEquiv
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (x : E.OSHilbert) :
    E.osToWightmanEquiv (E.osPCTEquiv hε x) =
      E.toPoincareData.pctEquiv hε (E.osToWightmanEquiv x) := by
  change E.osToWightmanEquiv
      (E.osToWightmanEquiv.symm (E.toPoincareData.pctEquiv hε (E.osToWightmanEquiv x))) = _
  exact E.osToWightmanEquiv.apply_symm_apply _

theorem osPoincareEquiv_one_eq_osSpacetimeTranslate
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮) (a : Fin 4 → ℝ) (Ψ : E.OSHilbert) :
    E.osPoincareEquiv a 1 Ψ = E.osSpacetimeTranslate a Ψ := by
  have htr : E.osToWightmanEquiv (E.osSpacetimeTranslate a Ψ) =
      E.toIsolatedMassShellData.translate a (E.osToWightmanEquiv Ψ) :=
    (fullEuclid_os_generalWightman_reconstruction_of_linearGrowth
      E.fullOS E.timeCluster E.linearGrowth E.vacuumNormalized).2.2.2.2.2.1 a Ψ
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPoincareEquiv,
    E.toPoincareData.poincareEquiv_eq_translate_lorentz, htr]
  congr 1
  change wightmanSpinorLorentzEquiv E.toIsolatedMassShellData.wightman.WData
      E.toIsolatedMassShellData.wightman.poincare 1 (E.osToWightmanEquiv Ψ) = _
  rw [wightmanSpinorLorentzEquiv_one]
  rfl

theorem osPoincareEquiv_mul
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (a₁ a₂ : Fin 4 → ℝ) (A₁ A₂ : SL2C) (Ψ : E.OSHilbert) :
    E.osPoincareEquiv a₁ A₁ (E.osPoincareEquiv a₂ A₂ Ψ) =
      E.osPoincareEquiv (a₁ + (lorentzOfSL2C A₁).mulVec a₂) (A₁ * A₂) Ψ := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPoincareEquiv, osToWightmanEquiv_osPoincareEquiv,
    osToWightmanEquiv_osPoincareEquiv]
  exact wightmanPoincareEquiv_mul E.toIsolatedMassShellData.wightman.WData
    E.toIsolatedMassShellData.wightman.poincare a₁ a₂ A₁ A₂ (E.osToWightmanEquiv Ψ)

@[simp]
theorem osPoincareEquiv_vacuum
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮) (a : Fin 4 → ℝ) (A : SL2C) :
    E.osPoincareEquiv a A E.osVacuumVec = E.osVacuumVec := by
  have hvac := (fullEuclid_os_generalWightman_reconstruction_of_linearGrowth
    E.fullOS E.timeCluster E.linearGrowth E.vacuumNormalized).2.2.2.2.1
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPoincareEquiv]
  have hvac' : E.osToWightmanEquiv E.osVacuumVec =
      wightmanVacuum E.toIsolatedMassShellData.wightman.WData := hvac
  rw [hvac']
  exact wightmanPoincareEquiv_vacuum E.toIsolatedMassShellData.wightman.WData
    E.toIsolatedMassShellData.wightman.poincare a A

@[simp]
theorem osPCTEquiv_vacuum
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮) (hε : R.HasSpinParity η) :
    E.osPCTEquiv hε E.osVacuumVec = E.osVacuumVec := by
  have hvac := (fullEuclid_os_generalWightman_reconstruction_of_linearGrowth
    E.fullOS E.timeCluster E.linearGrowth E.vacuumNormalized).2.2.2.2.1
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPCTEquiv]
  have hvac' : E.osToWightmanEquiv E.osVacuumVec =
      wightmanVacuum E.toIsolatedMassShellData.wightman.WData := hvac
  rw [hvac']
  exact wightmanPCTEquiv_vacuum E.toIsolatedMassShellData.wightman.WData
    E.toIsolatedMassShellData.wightman.poincare
    E.toIsolatedMassShellData.wightman.toWightmanAxioms.wightmanPCT hε

theorem inner_osPCTEquiv
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (Φ Ψ : E.OSHilbert) :
    ⟪E.osPCTEquiv hε Φ, E.osPCTEquiv hε Ψ⟫_ℂ = star ⟪Φ, Ψ⟫_ℂ := by
  calc ⟪E.osPCTEquiv hε Φ, E.osPCTEquiv hε Ψ⟫_ℂ
      = ⟪E.osToWightmanEquiv (E.osPCTEquiv hε Φ),
          E.osToWightmanEquiv (E.osPCTEquiv hε Ψ)⟫_ℂ :=
        (E.osToWightmanEquiv.inner_map_map _ _).symm
    _ = ⟪E.toPoincareData.pctEquiv hε (E.osToWightmanEquiv Φ),
          E.toPoincareData.pctEquiv hε (E.osToWightmanEquiv Ψ)⟫_ℂ := by
        rw [osToWightmanEquiv_osPCTEquiv, osToWightmanEquiv_osPCTEquiv]
    _ = star ⟪E.osToWightmanEquiv Φ, E.osToWightmanEquiv Ψ⟫_ℂ :=
        inner_wightmanPCTEquiv E.toIsolatedMassShellData.wightman.WData
          E.toIsolatedMassShellData.wightman.poincare
          E.toIsolatedMassShellData.wightman.toWightmanAxioms.wightmanPCT hε _ _
    _ = star ⟪Φ, Ψ⟫_ℂ := by rw [E.osToWightmanEquiv.inner_map_map]

theorem osPCTEquiv_sq
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (Ψ : E.OSHilbert) :
    E.osPCTEquiv hε (E.osPCTEquiv hε Ψ) = E.osLorentzEquiv (-1) Ψ := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPCTEquiv, osToWightmanEquiv_osPCTEquiv,
    osToWightmanEquiv_osLorentzEquiv]
  exact wightmanPCTEquiv_sq E.toIsolatedMassShellData.wightman.WData
    E.toIsolatedMassShellData.wightman.poincare
    E.toIsolatedMassShellData.wightman.toWightmanAxioms.wightmanPCT hε
    (E.osToWightmanEquiv Ψ)

theorem osPCTEquiv_poincare
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (a : Fin 4 → ℝ) (A : SL2C) (Ψ : E.OSHilbert) :
    E.osPCTEquiv hε (E.osPoincareEquiv a A Ψ) =
      E.osPoincareEquiv (-a) A (E.osPCTEquiv hε Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPCTEquiv, osToWightmanEquiv_osPoincareEquiv,
    osToWightmanEquiv_osPoincareEquiv, osToWightmanEquiv_osPCTEquiv]
  exact wightmanPCTEquiv_poincare E.toIsolatedMassShellData.wightman.WData
    E.toIsolatedMassShellData.wightman.poincare
    E.toIsolatedMassShellData.wightman.toWightmanAxioms.wightmanPCT hε a A
    (E.osToWightmanEquiv Ψ)

theorem osLorentzEquiv_osMollerWaveOut
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (A : SL2C) (Ψ : SymmFockHilbert E.mode.ν η) :
    E.osLorentzEquiv A (E.osMollerWaveOut Ψ) =
      E.osMollerWaveOut (E.toPoincareData.fockLorentzEquiv A Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osLorentzEquiv,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut]
  exact lorentz_mollerWaveOut E.toPoincareData A Ψ

theorem osLorentzEquiv_osMollerWaveIn
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (A : SL2C) (Ψ : SymmFockHilbert E.mode.ν η) :
    E.osLorentzEquiv A (E.osMollerWaveIn Ψ) =
      E.osMollerWaveIn (E.toPoincareData.fockLorentzEquiv A Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osLorentzEquiv,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn]
  exact lorentz_mollerWaveIn E.toPoincareData A Ψ

theorem osPoincareEquiv_osMollerWaveOut
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert E.mode.ν η) :
    E.osPoincareEquiv a A (E.osMollerWaveOut Ψ) =
      E.osMollerWaveOut (E.toPoincareData.fockPoincareEquiv a A Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPoincareEquiv,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut]
  exact poincare_mollerWaveOut E.toPoincareData a A Ψ

theorem osPoincareEquiv_osMollerWaveIn
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert E.mode.ν η) :
    E.osPoincareEquiv a A (E.osMollerWaveIn Ψ) =
      E.osMollerWaveIn (E.toPoincareData.fockPoincareEquiv a A Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPoincareEquiv,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn]
  exact poincare_mollerWaveIn E.toPoincareData a A Ψ

theorem osPCTEquiv_osMollerWaveOut
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η E.C_shell)
    (Ψ : SymmFockHilbert E.mode.ν η) :
    E.osPCTEquiv hε (E.osMollerWaveOut Ψ) =
      E.osMollerWaveIn (E.toPoincareData.fockPCTEquiv hε hC_pct Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPCTEquiv,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn]
  exact pct_mollerWaveOut E.toPoincareData hε hC_pct Ψ

theorem osPCTEquiv_osMollerWaveIn
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η E.C_shell)
    (Ψ : SymmFockHilbert E.mode.ν η) :
    E.osPCTEquiv hε (E.osMollerWaveIn Ψ) =
      E.osMollerWaveOut (E.toPoincareData.fockPCTEquiv hε hC_pct Ψ) := by
  apply E.osToWightmanEquiv.injective
  rw [osToWightmanEquiv_osPCTEquiv,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn,
    E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut]
  exact pct_mollerWaveIn E.toPoincareData hε hC_pct Ψ

theorem osPCTEquiv_sq_osMollerWaveOut_oneParticle
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {𝒮 : SchwingerFamily ι}
    (E : EuclidPoincareIsolatedMassShellData R S m M (-1) 𝒮)
    (hε : R.HasSpinParity (-1)) (s : Fin E.mode.ν) (f : SmoothWavepacket) :
    E.osPCTEquiv hε (E.osPCTEquiv hε (E.osMollerWaveOut
        (symmFockOneParticleVec E.mode.ν (-1) s f))) =
      -(E.osMollerWaveOut (symmFockOneParticleVec E.mode.ν (-1) s f)) := by
  rw [osPCTEquiv_sq, osLorentzEquiv_osMollerWaveOut]
  have h1 : E.toPoincareData.fockLorentzEquiv (-1) (symmFockOneParticleVec E.mode.ν (-1) s f) =
      -(symmFockOneParticleVec E.mode.ν (-1) s f) := by
    let L := E.toPoincareData.modeData
    change symmFockLorentzIsometry L (-1) (symmFockOneParticleVec L.mode.ν (-1) s f) =
      -(symmFockOneParticleVec L.mode.ν (-1) s f)
    rw [← symmFockMultiParticleVec_one L.mode.ν L.mode.hη (fun _ => s) (fun _ => f),
      symmFockLorentzIsometry_neg_one_multiParticleVec L hε, pow_one, neg_one_smul]
  rw [h1, map_neg]

end EuclidPoincareIsolatedMassShellData

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullEuclid_os_poincare_pct_scattering_synthesis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {m M : ℝ} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (E : EuclidPoincareIsolatedMassShellData R S m M η 𝒮)
    (hε : R.HasSpinParity η) (hC_pct : OnShellPCT R m η E.C_shell) :
    let D := E.toIsolatedMassShellData
    D.wightman.WData.W =
      osReconstructedWightmanFamily_of_linearGrowth E.fullOS.toOSAxioms E.linearGrowth ∧
    LocalCommutativity η D.wightman.WData.W ∧
    (∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E.tubeData.E n α x) ∧
    (∀ (r : ℕ) (s : Fin r → Fin D.mode.ν) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      Tendsto (haagRuelleChainVec D r s f) atTop (𝓝 (haagRuelleOutVec D r s f hf)) ∧
      Tendsto (haagRuelleChainVec D r s f) atBot (𝓝 (haagRuelleInVec D r s f hf))) ∧
    (∀ (a : Fin 4 → ℝ) (Ψ : E.OSHilbert), E.osPoincareEquiv a 1 Ψ = E.osSpacetimeTranslate a Ψ) ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C), E.osPoincareEquiv a A E.osVacuumVec = E.osVacuumVec) ∧
    E.osPCTEquiv hε E.osVacuumVec = E.osVacuumVec ∧
    (∀ Ψ : E.OSHilbert, E.osPCTEquiv hε (E.osPCTEquiv hε Ψ) = E.osLorentzEquiv (-1) Ψ) ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert E.mode.ν η),
      E.osPoincareEquiv a A (E.osMollerWaveIn Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPoincareEquiv a A Ψ) ∧
      E.osPoincareEquiv a A (E.osMollerWaveOut Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPoincareEquiv a A Ψ)) ∧
    (∀ Ψ : SymmFockHilbert E.mode.ν η,
      E.osPCTEquiv hε (E.osMollerWaveOut Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPCTEquiv hε hC_pct Ψ) ∧
      E.osPCTEquiv hε (E.osMollerWaveIn Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPCTEquiv hε hC_pct Ψ)) ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert E.mode.ν η),
      scatteringOperatorCLM D (E.toPoincareData.fockPoincareEquiv a A Ψ) =
        E.toPoincareData.fockPoincareEquiv a A (scatteringOperatorCLM D Ψ)) ∧
    (∀ Ψ : SymmFockHilbert E.mode.ν η,
      (E.toPoincareData.fockPCTEquiv hε hC_pct).symm
          (scatteringOperatorCLM D (E.toPoincareData.fockPCTEquiv hε hC_pct Ψ)) =
        (scatteringOperatorCLM D).adjoint Ψ) := by
  have h_base := fullEuclid_os_haagRuelle_scattering_synthesis E.toEuclidIsolatedMassShellData
  exact ⟨h_base.1, h_base.2.1, h_base.2.2.2.1, h_base.2.2.2.2.2.1,
    E.osPoincareEquiv_one_eq_osSpacetimeTranslate, E.osPoincareEquiv_vacuum,
    E.osPCTEquiv_vacuum hε, E.osPCTEquiv_sq hε,
    fun a A Ψ => ⟨E.osPoincareEquiv_osMollerWaveIn a A Ψ, E.osPoincareEquiv_osMollerWaveOut a A Ψ⟩,
    fun Ψ => ⟨E.osPCTEquiv_osMollerWaveOut hε hC_pct Ψ, E.osPCTEquiv_osMollerWaveIn hε hC_pct Ψ⟩,
    scatteringOperatorCLM_comm_poincare E.toPoincareData,
    symmFockPCTEquiv_symm_scatteringOperatorCLM_pct E.toPoincareData hε hC_pct⟩

end

end EuclidPoincareScatteringBridge

section ConcreteModelsAndWitnesses

lemma contDiff_kgModeData {m : ℝ} (hm : 0 < m) (s : Fin 1) (α : Unit) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (kgModeData hm).w s p α) := by
  unfold kgModeData
  exact Complex.ofRealCLM.contDiff.comp
    (((contDiff_const.mul (contDiff_massShellEnergy hm)).sqrt fun p =>
      (mul_pos zero_lt_two (massShellEnergy_pos hm p)).ne').inv fun p =>
      (Real.sqrt_pos.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm p))).ne')

lemma contDiff_diracModeRaw (m : ℝ) (s : Fin 2) (α : Fin 2 ⊕ Fin 2)
    (h_en : ContDiff ℝ (⊤ : ℕ∞) (massShellEnergy m)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => diracModeRaw m s p α) := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (p 0 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (p 1 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (p 2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).contDiff
  have hcE : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (massShellEnergy m p : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h_en
  fin_cases s <;> rcases α with i | i <;> fin_cases i <;> dsimp [diracModeRaw]
  · exact contDiff_const
  · exact contDiff_const
  · exact hcE.add h2
  · exact h0.sub (h1.mul contDiff_const)
  · exact contDiff_const.mul (hcE.add h2)
  · exact contDiff_const.mul (h0.add (h1.mul contDiff_const))
  · exact contDiff_const
  · exact contDiff_const

lemma contDiff_diracModeData {m : ℝ} (hm : 0 < m) (s : Fin 2) (α : Fin 2 ⊕ Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (diracModeData hm).w s p α) := by
  unfold diracModeData
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_diracModeScale hm)).mul
    (contDiff_diracModeRaw m s α (contDiff_massShellEnergy hm))

lemma contDiff_chargedKGModeData {m : ℝ} (hm : 0 < m) (s : Fin 2) (α : Unit ⊕ Unit) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (chargedKGModeData hm).w s p α) := by
  unfold chargedKGModeData directSumModeData
  exact contDiff_directSumModeW (contDiff_kgModeData hm) (contDiff_kgModeData hm) s α

lemma contDiff_chargedDiracModeData {m : ℝ} (hm : 0 < m)
    (s : Fin 4) (α : (Fin 2 ⊕ Fin 2) ⊕ (Fin 2 ⊕ Fin 2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (chargedDiracModeData hm).w s p α) := by
  unfold chargedDiracModeData directSumModeData
  exact contDiff_directSumModeW (contDiff_diracModeData hm) (contDiff_diracModeData hm) s α

lemma chargedKGRep_spinParity : chargedKGRep.HasSpinParity 1 :=
  directSumRep_spinParity trivialRep_spinParity trivialRep_spinParity

lemma chargedDiracRep_spinParity : chargedDiracRep.HasSpinParity (-1) :=
  directSumRep_spinParity diracRep_spinParity diracRep_spinParity

lemma massiveKGCoeff_onShellPCT : OnShellPCT trivialRep m 1 massiveKGCoeff := by
  intro _ _
  simp [massiveKGCoeff, trivialRep]

lemma chargedKGCoeff_onShellPCT : OnShellPCT chargedKGRep m 1 chargedKGCoeff := by
  intro p α
  exact chargedKGCoeff_pct (massShellVec m p) α

lemma diracMassShellCoeff_onShellPCT (m : ℝ) :
    OnShellPCT diracRep m (-1) (diracMassShellCoeff m) := by
  intro p α
  exact diracMassShellCoeff_pct m (massShellVec m p) α

lemma chargedDiracCoeff_onShellPCT (m : ℝ) :
    OnShellPCT chargedDiracRep m (-1) (chargedDiracCoeff m) := by
  intro p α
  exact chargedDiracCoeff_pct m (massShellVec m p) α

abbrev wickMassShellEuclidPoincareData
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    {m : ℝ} (hm : 0 < m) {η : ℂ} {C : (Fin 2 → ι) → (Fin 4 → ℝ) → ℂ}
    (M_mode : MassShellModeData R S m η C) (hC : MassShellCoeffData m C)
    (contDiff_w : ∀ (s : Fin M_mode.ν) (α : ι),
      ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => M_mode.w s p α))
    (hC_cov : ∀ (A : SL2C) (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α ((lorentzOfSL2C A).mulVec q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, R.rep A (α i) (β i)) * C β q)
    (hC_herm : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      star (C α q) =
        ∑ β : Fin 2 → ι, (∏ i : Fin 2, S.C (α i) (β i)) * C (β ∘ Fin.rev) q)
    (hC_pct : ∀ (q : Fin 4 → ℝ) (α : Fin 2 → ι),
      C α q = η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) * C (β ∘ Fin.rev) q)
    (dual_w : Fin M_mode.ν → (Fin 3 → ℝ) → ι → ℂ)
    (contDiff_dual_w : ∀ (s : Fin M_mode.ν) (α : ι),
      ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => dual_w s p α))
    (dual_orthonormal : ∀ (s₁ s₂ : Fin M_mode.ν) (p : Fin 3 → ℝ),
      ∑ α : ι, M_mode.w s₁ p α * dual_w s₂ p α = if s₁ = s₂ then 1 else 0) :
    EuclidPoincareIsolatedMassShellData R S m (2 * m) η
      (wickMassShellFullS R m hm η C hC) where
  toEuclidIsolatedMassShellData :=
    wickMassShellEuclidIsolatedData R S hm M_mode hC hC_cov hC_herm hC_pct dual_w
      contDiff_dual_w dual_orthonormal
  contDiff_w := contDiff_w
  hC_cov A p α := hC_cov A (massShellVec m p) α

abbrev freeKGEuclidPoincareData {m : ℝ} (hm : 0 < m) :
    EuclidPoincareIsolatedMassShellData trivialRep trivialStarStructure m (2 * m) 1
      (freeKGFullS m hm) where
  toEuclidIsolatedMassShellData := freeKGEuclidIsolatedMassShellData hm
  contDiff_w := contDiff_kgModeData hm
  hC_cov _ _ _ := by
    dsimp only [freeKGEuclidIsolatedMassShellData]
    simp [massiveKGCoeff, trivialRep, HolomorphicLorentzRep.rep_apply]

abbrev chargedKGEuclidPoincareData {m : ℝ} (hm : 0 < m) :
    EuclidPoincareIsolatedMassShellData chargedKGRep chargedKGStarStructure m (2 * m) 1
      (chargedKGFullS m hm) where
  toEuclidIsolatedMassShellData := chargedKGEuclidIsolatedMassShellData hm
  contDiff_w := contDiff_chargedKGModeData hm
  hC_cov A p α := chargedKGCoeff_cov A (massShellVec m p) α

abbrev freeDiracEuclidPoincareData {m : ℝ} (hm : 0 < m) :
    EuclidPoincareIsolatedMassShellData diracRep diracStarStructure m (2 * m) (-1)
      (freeDiracFullS m hm) where
  toEuclidIsolatedMassShellData := freeDiracEuclidIsolatedMassShellData hm
  contDiff_w := contDiff_diracModeData hm
  hC_cov A p α := diracMassShellCoeff_lorentz m A (massShellVec m p) α

abbrev chargedDiracEuclidPoincareData {m : ℝ} (hm : 0 < m) :
    EuclidPoincareIsolatedMassShellData chargedDiracRep chargedDiracStarStructure m (2 * m) (-1)
      (chargedDiracFullS m hm) where
  toEuclidIsolatedMassShellData := chargedDiracEuclidIsolatedMassShellData hm
  contDiff_w := contDiff_chargedDiracModeData hm
  hC_cov A p α := chargedDiracCoeff_cov m A (massShellVec m p) α

def conjWavepacket (f : SmoothWavepacket) : SmoothWavepacket where
  amp p := star (f.amp p)
  smooth := Complex.conjCLE.contDiff.comp f.smooth
  compactSupport := HasCompactSupport.comp_left f.compactSupport (star_zero ℂ)

@[simp]
lemma conjWavepacket_apply (f : SmoothWavepacket) (p : Fin 3 → ℝ) :
    (conjWavepacket f).amp p = star (f.amp p) := rfl

def chargedKGEigenScale (m : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * massShellEnergy m p))⁻¹

def chargedKGEigenW (m : ℝ) : Fin 2 → (Fin 3 → ℝ) → (Unit ⊕ Unit) → ℂ
  | 0, p, Sum.inl () => (chargedKGEigenScale m p : ℂ)
  | 0, p, Sum.inr () => Complex.I * (chargedKGEigenScale m p : ℂ)
  | 1, p, Sum.inl () => (chargedKGEigenScale m p : ℂ)
  | 1, p, Sum.inr () => -Complex.I * (chargedKGEigenScale m p : ℂ)

lemma contDiff_chargedKGEigenScale {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ (⊤ : ℕ∞) (chargedKGEigenScale m) := by
  unfold chargedKGEigenScale
  exact contDiff_const.mul
    (((contDiff_const.mul (contDiff_massShellEnergy hm)).sqrt fun p =>
      (mul_pos zero_lt_two (massShellEnergy_pos hm p)).ne').inv fun p =>
      (Real.sqrt_pos.mpr (mul_pos zero_lt_two (massShellEnergy_pos hm p))).ne')

lemma contDiff_chargedKGEigenW {m : ℝ} (hm : 0 < m) (s : Fin 2) (α : Unit ⊕ Unit) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => chargedKGEigenW m s p α) := by
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (chargedKGEigenScale m p : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_chargedKGEigenScale hm)
  fin_cases s <;> rcases α with ⟨⟩ | ⟨⟩ <;> dsimp [chargedKGEigenW]
  · exact hsc
  · exact contDiff_const.mul hsc
  · exact hsc
  · exact contDiff_const.mul hsc

abbrev chargedKGEigenModeData {m : ℝ} (hm : 0 < m) :
    MassShellModeData chargedKGRep chargedKGStarStructure m 1 chargedKGCoeff where
  ν := 2
  hη := Or.inl rfl
  w := chargedKGEigenW m
  measurable_w s α := (contDiff_chargedKGEigenW hm s α).continuous.measurable
  M := (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * m))⁻¹
  hM := mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
  norm_w_le s p α := by
    have hle : chargedKGEigenScale m p ≤ (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * m))⁻¹ := by
      unfold chargedKGEigenScale
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      exact inv_anti₀ (Real.sqrt_pos.mpr (by linarith))
        (Real.sqrt_le_sqrt (by linarith [massShellEnergy_ge_mass hm p]))
    have hnn : 0 ≤ chargedKGEigenScale m p :=
      mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))
    fin_cases s <;> rcases α with ⟨⟩ | ⟨⟩ <;>
      dsimp [chargedKGEigenW]
    · rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      exact hle
    · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      exact hle
    · rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      exact hle
    · rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
      exact hle
  factor_weight p α β := by
    have hpos : 0 ≤ 2 * massShellEnergy m p := by linarith [massShellEnergy_pos hm p]
    have hsq : (chargedKGEigenScale m p : ℂ) * (chargedKGEigenScale m p : ℂ) =
        (((2 : ℝ)⁻¹ * (2 * massShellEnergy m p)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      dsimp [chargedKGEigenScale]
      calc ((Real.sqrt 2)⁻¹ * (Real.sqrt (2 * massShellEnergy m p))⁻¹) *
            ((Real.sqrt 2)⁻¹ * (Real.sqrt (2 * massShellEnergy m p))⁻¹)
          = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
              ((Real.sqrt (2 * massShellEnergy m p))⁻¹ *
                (Real.sqrt (2 * massShellEnergy m p))⁻¹) := by ring
        _ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ *
              (Real.sqrt (2 * massShellEnergy m p) * Real.sqrt (2 * massShellEnergy m p))⁻¹ := by
            rw [← mul_inv, ← mul_inv]
        _ = (2 : ℝ)⁻¹ * (2 * massShellEnergy m p)⁻¹ := by
            rw [Real.mul_self_sqrt (by positivity), Real.mul_self_sqrt hpos]
    have hC_sum : ∀ x : Unit ⊕ Unit,
        (∑ γ : Unit ⊕ Unit, chargedKGStarStructure.C x γ *
          massShellWeight m chargedKGCoeff ![γ, β] p) =
        massShellWeight m chargedKGCoeff ![x, β] p := fun x => by
      rw [Fintype.sum_eq_single x]
      · simp [chargedKGStarStructure, directSumStarStructure, trivialStarStructure]
      · intro γ hne
        have hzero : chargedKGStarStructure.C x γ = 0 := by
          rcases x with ⟨⟩ | ⟨⟩ <;> rcases γ with ⟨⟩ | ⟨⟩ <;>
            simp [chargedKGStarStructure, directSumStarStructure, trivialStarStructure] at hne ⊢
        rw [hzero, zero_mul]
    rw [hC_sum α, Fin.sum_univ_two]
    have h_inl : starRingEnd ℂ (chargedKGEigenScale m p : ℂ) =
        (chargedKGEigenScale m p : ℂ) := Complex.conj_ofReal _
    have h_inr0 : starRingEnd ℂ (Complex.I * (chargedKGEigenScale m p : ℂ)) =
        -Complex.I * (chargedKGEigenScale m p : ℂ) := by simp
    have h_inr1 : starRingEnd ℂ (-Complex.I * (chargedKGEigenScale m p : ℂ)) =
        Complex.I * (chargedKGEigenScale m p : ℂ) := by simp
    rcases α with ⟨⟩ | ⟨⟩ <;> rcases β with ⟨⟩ | ⟨⟩ <;>
      dsimp [chargedKGEigenW, massShellWeight, chargedKGCoeff, directSumCoeff, massiveKGCoeff]
    · rw [h_inl]
      symm
      calc ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenScale m p : ℂ) +
            (chargedKGEigenScale m p : ℂ) * (chargedKGEigenScale m p : ℂ))
          = (2 : ℂ) * ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenScale m p : ℂ)) := by ring
        _ = (2 : ℂ) * (((2 : ℝ)⁻¹ * (2 * massShellEnergy m p)⁻¹ : ℝ) : ℂ) := by rw [hsq]
        _ = ((2 * massShellEnergy m p : ℂ)⁻¹) * 1 := by
            push_cast
            ring
    · rw [h_inl]
      ring
    · rw [h_inr0, h_inr1]
      ring
    · rw [h_inr0, h_inr1]
      symm
      calc (-Complex.I * (chargedKGEigenScale m p : ℂ) *
              (Complex.I * (chargedKGEigenScale m p : ℂ)) +
            Complex.I * (chargedKGEigenScale m p : ℂ) *
              (-Complex.I * (chargedKGEigenScale m p : ℂ)))
          = (-Complex.I * Complex.I + Complex.I * (-Complex.I)) *
              ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenScale m p : ℂ)) := by ring
        _ = (2 : ℂ) * ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenScale m p : ℂ)) := by
            simp only [neg_mul, mul_neg, Complex.I_mul_I, neg_neg]
            ring
        _ = (2 : ℂ) * (((2 : ℝ)⁻¹ * (2 * massShellEnergy m p)⁻¹ : ℝ) : ℂ) := by rw [hsq]
        _ = ((2 * massShellEnergy m p : ℂ)⁻¹) * 1 := by
            push_cast
            ring

def chargedKGEigenDualScale (m : ℝ) (p : Fin 3 → ℝ) : ℝ :=
  (Real.sqrt 2)⁻¹ * Real.sqrt (2 * massShellEnergy m p)

def chargedKGEigenDualMode (m : ℝ) : Fin 2 → (Fin 3 → ℝ) → (Unit ⊕ Unit) → ℂ
  | 0, p, Sum.inl () => (chargedKGEigenDualScale m p : ℂ)
  | 0, p, Sum.inr () => -Complex.I * (chargedKGEigenDualScale m p : ℂ)
  | 1, p, Sum.inl () => (chargedKGEigenDualScale m p : ℂ)
  | 1, p, Sum.inr () => Complex.I * (chargedKGEigenDualScale m p : ℂ)

lemma contDiff_chargedKGEigenDualMode {m : ℝ} (hm : 0 < m) (s : Fin 2) (α : Unit ⊕ Unit) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => chargedKGEigenDualMode m s p α) := by
  have hsc : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 3 → ℝ => (chargedKGEigenDualScale m p : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
      ((contDiff_const.mul (contDiff_massShellEnergy hm)).sqrt fun p =>
        (mul_pos zero_lt_two (massShellEnergy_pos hm p)).ne'))
  fin_cases s <;> rcases α with ⟨⟩ | ⟨⟩ <;> dsimp [chargedKGEigenDualMode]
  · exact hsc
  · exact contDiff_const.mul hsc
  · exact hsc
  · exact contDiff_const.mul hsc

lemma chargedKGEigenScale_mul_dual {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) :
    (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) = (2 : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul]
  have hr : chargedKGEigenScale m p * chargedKGEigenDualScale m p = (2 : ℝ)⁻¹ := by
    dsimp [chargedKGEigenScale, chargedKGEigenDualScale]
    have hpos : 0 < 2 * massShellEnergy m p := mul_pos zero_lt_two (massShellEnergy_pos hm p)
    have hsqrt : (Real.sqrt (2 * massShellEnergy m p))⁻¹ * Real.sqrt (2 * massShellEnergy m p) =
        1 :=
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hpos)
    calc ((Real.sqrt 2)⁻¹ * (Real.sqrt (2 * massShellEnergy m p))⁻¹) *
          ((Real.sqrt 2)⁻¹ * Real.sqrt (2 * massShellEnergy m p))
        = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) *
            ((Real.sqrt (2 * massShellEnergy m p))⁻¹ * Real.sqrt (2 * massShellEnergy m p)) := by
          ring
      _ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ * 1 := by rw [← mul_inv, hsqrt]
      _ = (2 : ℝ)⁻¹ := by rw [mul_one, Real.mul_self_sqrt (by positivity)]
  rw [hr]
  push_cast
  rfl

lemma chargedKGEigenDualMode_orthonormal {m : ℝ} (hm : 0 < m)
    (s₁ s₂ : Fin 2) (p : Fin 3 → ℝ) :
    ∑ α : Unit ⊕ Unit, (chargedKGEigenModeData hm).w s₁ p α * chargedKGEigenDualMode m s₂ p α =
      if s₁ = s₂ then 1 else 0 := by
  have hcd := chargedKGEigenScale_mul_dual hm p
  rw [Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique]
  fin_cases s₁ <;> fin_cases s₂ <;>
    dsimp [chargedKGEigenModeData, chargedKGEigenW, chargedKGEigenDualMode]
  · calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          Complex.I * (chargedKGEigenScale m p : ℂ) *
            (-Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + Complex.I * (-Complex.I)) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 2 * (2 : ℂ)⁻¹ := by rw [hcd, mul_neg, Complex.I_mul_I, neg_neg]; norm_num
      _ = 1 := by norm_num
  · calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          Complex.I * (chargedKGEigenScale m p : ℂ) *
            (Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + Complex.I * Complex.I) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 0 := by rw [Complex.I_mul_I]; simp
  · calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          -Complex.I * (chargedKGEigenScale m p : ℂ) *
            (-Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + (-Complex.I) * (-Complex.I)) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 0 := by simp [Complex.I_mul_I]
  · calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          -Complex.I * (chargedKGEigenScale m p : ℂ) *
            (Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + (-Complex.I) * Complex.I) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 2 * (2 : ℂ)⁻¹ := by rw [hcd, neg_mul, Complex.I_mul_I, neg_neg]; norm_num
      _ = 1 := by norm_num

abbrev chargedKGEigenEuclidPoincareData {m : ℝ} (hm : 0 < m) :
    EuclidPoincareIsolatedMassShellData chargedKGRep chargedKGStarStructure m (2 * m) 1
      (chargedKGFullS m hm) :=
  wickMassShellEuclidPoincareData chargedKGRep chargedKGStarStructure hm
    (chargedKGEigenModeData hm) (chargedKGCoeff_data hm) (contDiff_chargedKGEigenW hm)
    chargedKGCoeff_cov chargedKGCoeff_herm chargedKGCoeff_pct
    (chargedKGEigenDualMode m) (contDiff_chargedKGEigenDualMode hm)
    (chargedKGEigenDualMode_orthonormal hm)

lemma pctModeMatrix_chargedKGEigen {m : ℝ} (hm : 0 < m) (p : Fin 3 → ℝ) (s' s : Fin 2) :
    pctModeMatrix (chargedKGEigenEuclidPoincareData hm).toPoincareData.modeData p s' s =
      if s' = Equiv.swap (0 : Fin 2) 1 s then 1 else 0 := by
  have hpct : ∀ α μ : Unit ⊕ Unit, pctMatrix chargedKGStarStructure α μ =
      if α = μ then 1 else 0 := by
    intro α μ
    rcases α with ⟨⟩ | ⟨⟩ <;> rcases μ with ⟨⟩ | ⟨⟩ <;>
      simp [pctMatrix, chargedKGStarStructure, directSumStarStructure, trivialStarStructure,
        chargedKGRep, directSumRep, trivialRep, Matrix.mul_apply]
  have hsum : pctModeMatrix (chargedKGEigenEuclidPoincareData hm).toPoincareData.modeData p s' s =
      ∑ μ : Unit ⊕ Unit, (chargedKGEigenModeData hm).w s' p μ *
        star (chargedKGEigenDualMode m s p μ) := by
    unfold pctModeMatrix
    dsimp [EuclidPoincareIsolatedMassShellData.toPoincareData,
      PoincareIsolatedMassShellData.modeData, chargedKGEigenEuclidPoincareData,
      wickMassShellEuclidPoincareData, wickMassShellEuclidIsolatedData,
      EuclidIsolatedMassShellData.toIsolatedMassShellData]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_eq_single μ]
    · simp [hpct μ μ]
    · intro α _ hne
      simp [hpct α μ, hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ μ))
  rw [hsum, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique]
  have hcd := chargedKGEigenScale_mul_dual hm p
  have h_d_inl : starRingEnd ℂ (chargedKGEigenDualScale m p : ℂ) =
      (chargedKGEigenDualScale m p : ℂ) := Complex.conj_ofReal _
  have h_d_inr0 : starRingEnd ℂ (-Complex.I * (chargedKGEigenDualScale m p : ℂ)) =
      Complex.I * (chargedKGEigenDualScale m p : ℂ) := by simp
  have h_d_inr1 : starRingEnd ℂ (Complex.I * (chargedKGEigenDualScale m p : ℂ)) =
      -Complex.I * (chargedKGEigenDualScale m p : ℂ) := by simp
  fin_cases s' <;> fin_cases s <;>
    dsimp [chargedKGEigenModeData, chargedKGEigenW, chargedKGEigenDualMode]
  · rw [h_d_inl, h_d_inr0]
    calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          Complex.I * (chargedKGEigenScale m p : ℂ) *
            (Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + Complex.I * Complex.I) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 0 := by rw [Complex.I_mul_I]; simp
  · rw [h_d_inl, h_d_inr1]
    calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          Complex.I * (chargedKGEigenScale m p : ℂ) *
            (-Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + Complex.I * (-Complex.I)) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 2 * (2 : ℂ)⁻¹ := by rw [hcd, mul_neg, Complex.I_mul_I, neg_neg]; norm_num
      _ = 1 := by norm_num
  · rw [h_d_inl, h_d_inr0]
    calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          -Complex.I * (chargedKGEigenScale m p : ℂ) *
            (Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + (-Complex.I) * Complex.I) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 2 * (2 : ℂ)⁻¹ := by rw [hcd, neg_mul, Complex.I_mul_I, neg_neg]; norm_num
      _ = 1 := by norm_num
  · rw [h_d_inl, h_d_inr1]
    calc (chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ) +
          -Complex.I * (chargedKGEigenScale m p : ℂ) *
            (-Complex.I * (chargedKGEigenDualScale m p : ℂ))
        = (1 + (-Complex.I) * (-Complex.I)) *
            ((chargedKGEigenScale m p : ℂ) * (chargedKGEigenDualScale m p : ℂ)) := by ring
      _ = 0 := by simp [Complex.I_mul_I]

lemma symmFockOneParticleVec_zeroWavepacket (ν : ℕ) (η : ℂ) (s : Fin ν) :
    symmFockOneParticleVec ν η s zeroWavepacket = 0 := by
  apply Subtype.ext
  exact fockOneParticleVec_zero ν s

theorem chargedKGEigen_fockPCT_zero {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) :
    (chargedKGEigenEuclidPoincareData hm).toPoincareData.fockPCTEquiv
        chargedKGRep_spinParity chargedKGCoeff_onShellPCT
        (symmFockOneParticleVec 2 1 0 f) =
      symmFockOneParticleVec 2 1 1 (conjWavepacket f) := by
  let L := (chargedKGEigenEuclidPoincareData hm).toPoincareData.modeData
  have hp0 : pctModeWavepacket L (0 : Fin 2) (0 : Fin 2) f = zeroWavepacket := by
    apply SmoothWavepacket.ext
    funext p
    rw [pctModeWavepacket_apply]
    dsimp only [L]
    rw [pctModeMatrix_chargedKGEigen hm p 0 0]
    simp
  have hp1 : pctModeWavepacket L (1 : Fin 2) (0 : Fin 2) f = conjWavepacket f := by
    apply SmoothWavepacket.ext
    funext p
    rw [pctModeWavepacket_apply]
    dsimp only [L]
    rw [pctModeMatrix_chargedKGEigen hm p 1 0]
    simp
  have h1 := symmFockPCTEquiv_oneParticleVec L chargedKGRep_spinParity chargedKGCoeff_onShellPCT
    (0 : Fin 2) f
  have h2 : (∑ s' : Fin L.mode.ν,
      symmFockOneParticleVec L.mode.ν 1 s' (pctModeWavepacket L s' (0 : Fin 2) f)) =
      symmFockOneParticleVec 2 1 1 (conjWavepacket f) := by
    change (∑ s' : Fin 2, symmFockOneParticleVec 2 1 s'
        (pctModeWavepacket L s' (0 : Fin 2) f)) = _
    rw [Fin.sum_univ_two, hp0, hp1, symmFockOneParticleVec_zeroWavepacket, zero_add]
  exact h1.trans h2

theorem chargedKGEigen_fockPCT_one {m : ℝ} (hm : 0 < m) (f : SmoothWavepacket) :
    (chargedKGEigenEuclidPoincareData hm).toPoincareData.fockPCTEquiv
        chargedKGRep_spinParity chargedKGCoeff_onShellPCT
        (symmFockOneParticleVec 2 1 1 f) =
      symmFockOneParticleVec 2 1 0 (conjWavepacket f) := by
  let L := (chargedKGEigenEuclidPoincareData hm).toPoincareData.modeData
  have hp0 : pctModeWavepacket L (0 : Fin 2) (1 : Fin 2) f = conjWavepacket f := by
    apply SmoothWavepacket.ext
    funext p
    rw [pctModeWavepacket_apply]
    dsimp only [L]
    rw [pctModeMatrix_chargedKGEigen hm p 0 1]
    simp
  have hp1 : pctModeWavepacket L (1 : Fin 2) (1 : Fin 2) f = zeroWavepacket := by
    apply SmoothWavepacket.ext
    funext p
    rw [pctModeWavepacket_apply]
    dsimp only [L]
    rw [pctModeMatrix_chargedKGEigen hm p 1 1]
    simp
  have h1 := symmFockPCTEquiv_oneParticleVec L chargedKGRep_spinParity chargedKGCoeff_onShellPCT
    (1 : Fin 2) f
  have h2 : (∑ s' : Fin L.mode.ν,
      symmFockOneParticleVec L.mode.ν 1 s' (pctModeWavepacket L s' (1 : Fin 2) f)) =
      symmFockOneParticleVec 2 1 0 (conjWavepacket f) := by
    change (∑ s' : Fin 2, symmFockOneParticleVec 2 1 s'
        (pctModeWavepacket L s' (1 : Fin 2) f)) = _
    rw [Fin.sum_univ_two, hp0, hp1, symmFockOneParticleVec_zeroWavepacket, add_zero]
  exact h1.trans h2

theorem chargedKGEigen_exists_os_particle_antiparticle_swap {m : ℝ} (hm : 0 < m) :
    let E := chargedKGEigenEuclidPoincareData hm
    ∃ f₀ : SmoothWavepacket,
      let Ψ_pos := E.osMollerWaveOut (symmFockOneParticleVec 2 1 0 f₀)
      let Ψ_neg := E.osMollerWaveIn (symmFockOneParticleVec 2 1 1 (conjWavepacket f₀))
      Ψ_pos ≠ 0 ∧
      E.osPCTEquiv chargedKGRep_spinParity Ψ_pos = Ψ_neg ∧
      ⟪Ψ_pos, E.osPCTEquiv chargedKGRep_spinParity Ψ_pos⟫_ℂ = 0 ∧
      E.osPCTEquiv chargedKGRep_spinParity Ψ_pos ≠ Ψ_pos := by
  let E := chargedKGEigenEuclidPoincareData hm
  let f₀ : SmoothWavepacket := disjointBumpPacket 1 0
  let v₀ : SymmFockHilbert 2 1 := symmFockOneParticleVec 2 1 0 f₀
  let v₁ : SymmFockHilbert 2 1 := symmFockOneParticleVec 2 1 1 (conjWavepacket f₀)
  have hv0_inner : ⟪v₀, v₀⟫_ℂ ≠ 0 := by
    change ⟪fockOneParticleVec 2 0 (disjointBumpPacket 1 0),
        fockOneParticleVec 2 0 (disjointBumpPacket 1 0)⟫_ℂ ≠ 0
    exact inner_fockOneParticleVec_bump3DWavepacket_ne_zero (0 : Fin 2)
      ![3 * ((0 : Fin 1).val : ℝ), 0, 0] 1 zero_lt_one
  have hv0_ne : v₀ ≠ 0 := fun h0 => hv0_inner (by rw [h0, inner_zero_left])
  have hpos_ne : E.osMollerWaveOut v₀ ≠ 0 := by
    intro h0
    exact hv0_ne (E.osMollerWaveOut.injective (h0.trans (map_zero _).symm))
  have hswap : E.osPCTEquiv chargedKGRep_spinParity (E.osMollerWaveOut v₀) =
      E.osMollerWaveIn v₁ := by
    rw [E.osPCTEquiv_osMollerWaveOut chargedKGRep_spinParity chargedKGCoeff_onShellPCT v₀,
      chargedKGEigen_fockPCT_zero hm f₀]
  have h_in_eq_out : E.osMollerWaveIn v₁ = E.osMollerWaveOut v₁ := by
    apply E.osToWightmanEquiv.injective
    rw [E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveIn,
      E.toEuclidIsolatedMassShellData.osToWightmanEquiv_osMollerWaveOut]
    exact mollerWaveIn_oneParticle_eq_out E.toIsolatedMassShellData
      (show Fin E.mode.ν from (1 : Fin 2)) (conjWavepacket f₀)
  have horth :
      ⟪E.osMollerWaveOut v₀, E.osPCTEquiv chargedKGRep_spinParity (E.osMollerWaveOut v₀)⟫_ℂ =
        0 := by
    rw [hswap, h_in_eq_out, E.osMollerWaveOut.inner_map_map]
    change ⟪fockOneParticleVec 2 (0 : Fin 2) f₀,
        fockOneParticleVec 2 (1 : Fin 2) (conjWavepacket f₀)⟫_ℂ = 0
    rw [inner_fockOneParticleVec_eq]
    simp
  have hne : E.osPCTEquiv chargedKGRep_spinParity (E.osMollerWaveOut v₀) ≠
      E.osMollerWaveOut v₀ := by
    intro heq
    rw [heq, inner_self_eq_zero] at horth
    exact hpos_ne horth
  exact ⟨f₀, hpos_ne, hswap, horth, hne⟩

theorem freeDirac_exists_os_oneParticle_kramers_neg {m : ℝ} (hm : 0 < m) :
    let E := freeDiracEuclidPoincareData hm
    ∃ Ψ₁ : E.OSHilbert,
      Ψ₁ ≠ 0 ∧
      E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ₁) = -Ψ₁ ∧
      E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ₁) ≠ Ψ₁ := by
  let E := freeDiracEuclidPoincareData hm
  let v₁ : SymmFockHilbert 2 (-1) := symmFockOneParticleVec 2 (-1) 0 (disjointBumpPacket 1 0)
  have hv1_inner : ⟪v₁, v₁⟫_ℂ ≠ 0 := by
    change ⟪fockOneParticleVec 2 0 (disjointBumpPacket 1 0),
        fockOneParticleVec 2 0 (disjointBumpPacket 1 0)⟫_ℂ ≠ 0
    exact inner_fockOneParticleVec_bump3DWavepacket_ne_zero (0 : Fin 2)
      ![3 * ((0 : Fin 1).val : ℝ), 0, 0] 1 zero_lt_one
  have hv1_ne : v₁ ≠ 0 := fun h0 => hv1_inner (by rw [h0, inner_zero_left])
  let Ψ₁ : E.OSHilbert := E.osMollerWaveOut v₁
  have hpos_ne : Ψ₁ ≠ 0 := by
    intro h0
    exact hv1_ne (E.osMollerWaveOut.injective (h0.trans (map_zero _).symm))
  have hsq : E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ₁) = -Ψ₁ :=
    E.osPCTEquiv_sq_osMollerWaveOut_oneParticle diracRep_spinParity
      (show Fin E.mode.ν from (0 : Fin 2)) (disjointBumpPacket 1 0)
  have hne : E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ₁) ≠ Ψ₁ := by
    intro heq
    rw [hsq] at heq
    have h2 : (2 : ℂ) • Ψ₁ = 0 := by
      have hsub : Ψ₁ - (-Ψ₁) = 0 := by rw [heq, sub_self]
      have hadd : Ψ₁ + Ψ₁ = 0 := by simpa [sub_neg_eq_add] using hsub
      simpa [two_smul] using hadd
    exact hpos_ne ((smul_eq_zero.mp h2).resolve_left (by norm_num))
  exact ⟨Ψ₁, hpos_ne, hsq, hne⟩

theorem chargedDirac_exists_os_oneParticle_kramers_neg {m : ℝ} (hm : 0 < m) :
    let E := chargedDiracEuclidPoincareData hm
    ∃ Ψ₁ : E.OSHilbert,
      Ψ₁ ≠ 0 ∧
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ₁) =
        -Ψ₁ ∧
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ₁) ≠
        Ψ₁ := by
  let E := chargedDiracEuclidPoincareData hm
  let v₁ : SymmFockHilbert 4 (-1) := symmFockOneParticleVec 4 (-1) 0 (disjointBumpPacket 1 0)
  have hv1_inner : ⟪v₁, v₁⟫_ℂ ≠ 0 := by
    change ⟪fockOneParticleVec 4 0 (disjointBumpPacket 1 0),
        fockOneParticleVec 4 0 (disjointBumpPacket 1 0)⟫_ℂ ≠ 0
    exact inner_fockOneParticleVec_bump3DWavepacket_ne_zero (0 : Fin 4)
      ![3 * ((0 : Fin 1).val : ℝ), 0, 0] 1 zero_lt_one
  have hv1_ne : v₁ ≠ 0 := fun h0 => hv1_inner (by rw [h0, inner_zero_left])
  let Ψ₁ : E.OSHilbert := E.osMollerWaveOut v₁
  have hpos_ne : Ψ₁ ≠ 0 := by
    intro h0
    exact hv1_ne (E.osMollerWaveOut.injective (h0.trans (map_zero _).symm))
  have hsq :
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ₁) =
        -Ψ₁ :=
    E.osPCTEquiv_sq_osMollerWaveOut_oneParticle chargedDiracRep_spinParity
      (show Fin E.mode.ν from (0 : Fin 4)) (disjointBumpPacket 1 0)
  have hne :
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ₁) ≠
        Ψ₁ := by
    intro heq
    rw [hsq] at heq
    have h2 : (2 : ℂ) • Ψ₁ = 0 := by
      have hsub : Ψ₁ - (-Ψ₁) = 0 := by rw [heq, sub_self]
      have hadd : Ψ₁ + Ψ₁ = 0 := by simpa [sub_neg_eq_add] using hsub
      simpa [two_smul] using hadd
    exact hpos_ne ((smul_eq_zero.mp h2).resolve_left (by norm_num))
  exact ⟨Ψ₁, hpos_ne, hsq, hne⟩

theorem freeKG_euclid_poincare_pct_master {m : ℝ} (hm : 0 < m) :
    let E := freeKGEuclidPoincareData hm
    let D := E.toIsolatedMassShellData
    AsymptoticCompleteness D ∧
    E.osMollerWaveIn = E.osMollerWaveOut ∧
    Function.Surjective E.osMollerWaveIn ∧
    Function.Surjective E.osMollerWaveOut ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert 1 1),
      E.osPoincareEquiv a A (E.osMollerWaveIn Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPoincareEquiv a A Ψ) ∧
      E.osPoincareEquiv a A (E.osMollerWaveOut Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPoincareEquiv a A Ψ)) ∧
    (∀ Ψ : SymmFockHilbert 1 1,
      E.osPCTEquiv trivialRep_spinParity (E.osMollerWaveOut Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPCTEquiv trivialRep_spinParity
          massiveKGCoeff_onShellPCT Ψ) ∧
      E.osPCTEquiv trivialRep_spinParity (E.osMollerWaveIn Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPCTEquiv trivialRep_spinParity
          massiveKGCoeff_onShellPCT Ψ)) ∧
    (∀ Ψ : E.OSHilbert,
      E.osPCTEquiv trivialRep_spinParity (E.osPCTEquiv trivialRep_spinParity Ψ) =
        E.osLorentzEquiv (-1) Ψ) ∧
    scatteringOperatorCLM D = ContinuousLinearMap.id ℂ (SymmFockHilbert 1 1) ∧
    (∀ (Ψ : SymmFockHilbert 1 1),
      (E.toPoincareData.fockPCTEquiv trivialRep_spinParity massiveKGCoeff_onShellPCT).symm
          (scatteringOperatorCLM D (E.toPoincareData.fockPCTEquiv trivialRep_spinParity
            massiveKGCoeff_onShellPCT Ψ)) =
        (scatteringOperatorCLM D).adjoint Ψ) ∧
    (∀ {η : ℂ}, FullEuclidOSAxioms trivialRep trivialStarStructure η (freeKGFullS m hm) →
      η = 1) ∧
    (∀ r : ℕ, ∃ (s : Fin r → Fin 1) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      E.osMollerWaveIn (symmFockMultiParticleVec 1 1 (Or.inl rfl) r s f) ≠ 0 ∧
      haagRuelleInVec D r s f hf ≠ 0 ∧
      haagRuelleOutVec D r s f hf ≠ 0) := by
  let E := freeKGEuclidPoincareData hm
  have hm_base := freeKG_euclid_scattering_master hm
  have h_syn := fullEuclid_os_poincare_pct_scattering_synthesis E trivialRep_spinParity
    massiveKGCoeff_onShellPCT
  exact ⟨hm_base.1, hm_base.2.1, hm_base.2.2.1, hm_base.2.2.2.1, h_syn.2.2.2.2.2.2.2.2.1,
    h_syn.2.2.2.2.2.2.2.2.2.1, h_syn.2.2.2.2.2.2.2.1, hm_base.2.2.2.2.1,
    h_syn.2.2.2.2.2.2.2.2.2.2.2, hm_base.2.2.2.2.2.1, hm_base.2.2.2.2.2.2⟩

theorem chargedKG_euclid_poincare_pct_master {m : ℝ} (hm : 0 < m) :
    let E := chargedKGEuclidPoincareData hm
    let D := E.toIsolatedMassShellData
    let E_eig := chargedKGEigenEuclidPoincareData hm
    AsymptoticCompleteness D ∧
    E.osMollerWaveIn = E.osMollerWaveOut ∧
    Function.Surjective E.osMollerWaveIn ∧
    Function.Surjective E.osMollerWaveOut ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert 2 1),
      E.osPoincareEquiv a A (E.osMollerWaveIn Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPoincareEquiv a A Ψ) ∧
      E.osPoincareEquiv a A (E.osMollerWaveOut Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPoincareEquiv a A Ψ)) ∧
    (∀ Ψ : SymmFockHilbert 2 1,
      E.osPCTEquiv chargedKGRep_spinParity (E.osMollerWaveOut Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPCTEquiv chargedKGRep_spinParity
          chargedKGCoeff_onShellPCT Ψ) ∧
      E.osPCTEquiv chargedKGRep_spinParity (E.osMollerWaveIn Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPCTEquiv chargedKGRep_spinParity
          chargedKGCoeff_onShellPCT Ψ)) ∧
    scatteringOperatorCLM D = ContinuousLinearMap.id ℂ (SymmFockHilbert 2 1) ∧
    (∀ (f₀ : SmoothWavepacket), (∃ p : Fin 3 → ℝ, f₀.amp p ≠ 0) →
      E.osMollerWaveIn
        (symmFockMultiParticleVec 2 1 (Or.inl rfl) 2 ![0, 1] (fun _ => f₀)) ≠ 0) ∧
    (∀ {η : ℂ}, FullEuclidOSAxioms chargedKGRep chargedKGStarStructure η
      (chargedKGFullS m hm) → η = 1) ∧
    (∀ r : ℕ, ∃ (s : Fin r → Fin 2) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      E.osMollerWaveIn (symmFockMultiParticleVec 2 1 (Or.inl rfl) r s f) ≠ 0 ∧
      haagRuelleInVec D r s f hf ≠ 0 ∧
      haagRuelleOutVec D r s f hf ≠ 0) ∧
    (∃ f₀ : SmoothWavepacket,
      let Ψ_pos := E_eig.osMollerWaveOut (symmFockOneParticleVec 2 1 0 f₀)
      let Ψ_neg := E_eig.osMollerWaveIn (symmFockOneParticleVec 2 1 1 (conjWavepacket f₀))
      Ψ_pos ≠ 0 ∧
      E_eig.osPCTEquiv chargedKGRep_spinParity Ψ_pos = Ψ_neg ∧
      ⟪Ψ_pos, E_eig.osPCTEquiv chargedKGRep_spinParity Ψ_pos⟫_ℂ = 0 ∧
      E_eig.osPCTEquiv chargedKGRep_spinParity Ψ_pos ≠ Ψ_pos) := by
  let E := chargedKGEuclidPoincareData hm
  have hm_base := chargedKG_euclid_scattering_master hm
  have h_syn := fullEuclid_os_poincare_pct_scattering_synthesis E chargedKGRep_spinParity
    chargedKGCoeff_onShellPCT
  exact ⟨hm_base.1, hm_base.2.1, hm_base.2.2.1, hm_base.2.2.2.1, h_syn.2.2.2.2.2.2.2.2.1,
    h_syn.2.2.2.2.2.2.2.2.2.1, hm_base.2.2.2.2.1, hm_base.2.2.2.2.2.1,
    hm_base.2.2.2.2.2.2.1, hm_base.2.2.2.2.2.2.2,
    chargedKGEigen_exists_os_particle_antiparticle_swap hm⟩

theorem freeDirac_euclid_poincare_pct_master {m : ℝ} (hm : 0 < m) :
    let E := freeDiracEuclidPoincareData hm
    let D := E.toIsolatedMassShellData
    AsymptoticCompleteness D ∧
    E.osMollerWaveIn = E.osMollerWaveOut ∧
    Function.Surjective E.osMollerWaveIn ∧
    Function.Surjective E.osMollerWaveOut ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert 2 (-1)),
      E.osPoincareEquiv a A (E.osMollerWaveIn Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPoincareEquiv a A Ψ) ∧
      E.osPoincareEquiv a A (E.osMollerWaveOut Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPoincareEquiv a A Ψ)) ∧
    (∀ Ψ : SymmFockHilbert 2 (-1),
      E.osPCTEquiv diracRep_spinParity (E.osMollerWaveOut Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPCTEquiv diracRep_spinParity
          (diracMassShellCoeff_onShellPCT m) Ψ) ∧
      E.osPCTEquiv diracRep_spinParity (E.osMollerWaveIn Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPCTEquiv diracRep_spinParity
          (diracMassShellCoeff_onShellPCT m) Ψ)) ∧
    (∀ Ψ : E.OSHilbert,
      E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ) =
        E.osLorentzEquiv (-1) Ψ) ∧
    scatteringOperatorCLM D = ContinuousLinearMap.id ℂ (SymmFockHilbert 2 (-1)) ∧
    (∀ (s₀ : Fin 2) (f₀ : SmoothWavepacket),
      E.osMollerWaveIn
        (symmFockMultiParticleVec 2 (-1) (Or.inr rfl) 2 (fun _ => s₀) (fun _ => f₀)) = 0) ∧
    (∀ (f₀ : SmoothWavepacket), (∃ p : Fin 3 → ℝ, f₀.amp p ≠ 0) →
      E.osMollerWaveIn
        (symmFockMultiParticleVec 2 (-1) (Or.inr rfl) 2 ![0, 1] (fun _ => f₀)) ≠ 0) ∧
    (∀ {η : ℂ}, FullEuclidOSAxioms diracRep diracStarStructure η (freeDiracFullS m hm) →
      η = -1) ∧
    (∀ r : ℕ, ∃ (s : Fin r → Fin 2) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      E.osMollerWaveIn (symmFockMultiParticleVec 2 (-1) (Or.inr rfl) r s f) ≠ 0 ∧
      haagRuelleInVec D r s f hf ≠ 0 ∧
      haagRuelleOutVec D r s f hf ≠ 0) ∧
    (∃ Ψ₁ : E.OSHilbert,
      Ψ₁ ≠ 0 ∧
      E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ₁) = -Ψ₁ ∧
      E.osPCTEquiv diracRep_spinParity (E.osPCTEquiv diracRep_spinParity Ψ₁) ≠ Ψ₁) := by
  let E := freeDiracEuclidPoincareData hm
  have hm_base := freeDirac_euclid_scattering_master hm
  have h_syn := fullEuclid_os_poincare_pct_scattering_synthesis E diracRep_spinParity
    (diracMassShellCoeff_onShellPCT m)
  exact ⟨hm_base.1, hm_base.2.1, hm_base.2.2.1, hm_base.2.2.2.1, h_syn.2.2.2.2.2.2.2.2.1,
    h_syn.2.2.2.2.2.2.2.2.2.1, h_syn.2.2.2.2.2.2.2.1, hm_base.2.2.2.2.1,
    hm_base.2.2.2.2.2.1, hm_base.2.2.2.2.2.2.1, hm_base.2.2.2.2.2.2.2.1,
    hm_base.2.2.2.2.2.2.2.2, freeDirac_exists_os_oneParticle_kramers_neg hm⟩

theorem chargedDirac_euclid_poincare_pct_master {m : ℝ} (hm : 0 < m) :
    let E := chargedDiracEuclidPoincareData hm
    let D := E.toIsolatedMassShellData
    AsymptoticCompleteness D ∧
    E.osMollerWaveIn = E.osMollerWaveOut ∧
    Function.Surjective E.osMollerWaveIn ∧
    Function.Surjective E.osMollerWaveOut ∧
    (∀ (a : Fin 4 → ℝ) (A : SL2C) (Ψ : SymmFockHilbert 4 (-1)),
      E.osPoincareEquiv a A (E.osMollerWaveIn Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPoincareEquiv a A Ψ) ∧
      E.osPoincareEquiv a A (E.osMollerWaveOut Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPoincareEquiv a A Ψ)) ∧
    (∀ Ψ : SymmFockHilbert 4 (-1),
      E.osPCTEquiv chargedDiracRep_spinParity (E.osMollerWaveOut Ψ) =
        E.osMollerWaveIn (E.toPoincareData.fockPCTEquiv chargedDiracRep_spinParity
          (chargedDiracCoeff_onShellPCT m) Ψ) ∧
      E.osPCTEquiv chargedDiracRep_spinParity (E.osMollerWaveIn Ψ) =
        E.osMollerWaveOut (E.toPoincareData.fockPCTEquiv chargedDiracRep_spinParity
          (chargedDiracCoeff_onShellPCT m) Ψ)) ∧
    (∀ Ψ : E.OSHilbert,
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ) =
        E.osLorentzEquiv (-1) Ψ) ∧
    scatteringOperatorCLM D = ContinuousLinearMap.id ℂ (SymmFockHilbert 4 (-1)) ∧
    (∀ (s₀ : Fin 4) (f₀ : SmoothWavepacket),
      E.osMollerWaveIn
        (symmFockMultiParticleVec 4 (-1) (Or.inr rfl) 2 (fun _ => s₀) (fun _ => f₀)) = 0) ∧
    (∀ {s₁ s₂ : Fin 4}, s₁ ≠ s₂ → ∀ (f₀ : SmoothWavepacket),
      (∃ p : Fin 3 → ℝ, f₀.amp p ≠ 0) →
      E.osMollerWaveIn
        (symmFockMultiParticleVec 4 (-1) (Or.inr rfl) 2 ![s₁, s₂] (fun _ => f₀)) ≠ 0) ∧
    (∀ {η : ℂ}, FullEuclidOSAxioms chargedDiracRep chargedDiracStarStructure η
      (chargedDiracFullS m hm) → η = -1) ∧
    (∀ r : ℕ, ∃ (s : Fin r → Fin 4) (f : Fin r → SmoothWavepacket)
      (hf : Pairwise fun i j : Fin r => VelocityDisjoint m (f i) (f j)),
      E.osMollerWaveIn (symmFockMultiParticleVec 4 (-1) (Or.inr rfl) r s f) ≠ 0 ∧
      haagRuelleInVec D r s f hf ≠ 0 ∧
      haagRuelleOutVec D r s f hf ≠ 0) ∧
    (∃ Ψ₁ : E.OSHilbert,
      Ψ₁ ≠ 0 ∧
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ₁) =
        -Ψ₁ ∧
      E.osPCTEquiv chargedDiracRep_spinParity (E.osPCTEquiv chargedDiracRep_spinParity Ψ₁) ≠
        Ψ₁) := by
  let E := chargedDiracEuclidPoincareData hm
  have hm_base := chargedDirac_euclid_scattering_master hm
  have h_syn := fullEuclid_os_poincare_pct_scattering_synthesis E chargedDiracRep_spinParity
    (chargedDiracCoeff_onShellPCT m)
  exact ⟨hm_base.1, hm_base.2.1, hm_base.2.2.1, hm_base.2.2.2.1, h_syn.2.2.2.2.2.2.2.2.1,
    h_syn.2.2.2.2.2.2.2.2.2.1, h_syn.2.2.2.2.2.2.2.1, hm_base.2.2.2.2.1,
    hm_base.2.2.2.2.2.1, hm_base.2.2.2.2.2.2.1, hm_base.2.2.2.2.2.2.2.1,
    hm_base.2.2.2.2.2.2.2.2, chargedDirac_exists_os_oneParticle_kramers_neg hm⟩

end ConcreteModelsAndWitnesses

end

end QFT
