import WightmanFramework
import AnalyticContinuation
import DistributionEOW

namespace QFT

open Geometry Geometry.MatrixAnalysis
open Complex Topology Filter Set
open scoped Matrix MatrixNormed

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def vector_bhw_diff (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι)
    (x : Fin 6 → ℂ) : ℂ :=
  let Λ := local_chart x
  let A := sl2c_chart_invFun (local_chart_e x).1
  let B := sl2c_chart_invFun (local_chart_e x).2
  E.H n α (Λ • z) - ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z

lemma finset_sum_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ) (x : E)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∑ i ∈ s, f i e) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const
  | insert a s ha ih =>
    have h_eq : (fun e => ∑ i ∈ insert a s, f i e) = fun e => f a e + ∑ i ∈ s, f i e := by
      ext e
      exact Finset.sum_insert ha
    rw [h_eq]
    apply AnalyticAt.add
    · exact hf a (Finset.mem_insert_self a s)
    · apply ih
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)

lemma fintype_sum_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℂ) (x : E)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∑ i : ι, f i e) x := by
  classical
  exact finset_sum_analyticAt Finset.univ f x (fun i _ => hf i)

lemma fintype_prod_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℂ) (x : E)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∏ i : ι, f i e) x := by
  classical
  let s := (Finset.univ : Finset ι)
  have h_prod : AnalyticAt ℂ (fun e => ∏ i ∈ s, f i e) x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact analyticAt_const
    | insert a s ha ih =>
      have h_eq : (fun e => ∏ i ∈ insert a s, f i e) = fun e => f a e * ∏ i ∈ s, f i e := by
        ext e
        exact Finset.prod_insert ha
      rw [h_eq]
      exact AnalyticAt.mul (hf a) ih
  exact h_prod

lemma mvPolynomial_eval_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {σ : Type*} (P : MvPolynomial σ ℂ)
    (f : σ → E → ℂ) (x : E) (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => MvPolynomial.eval (fun i => f i e) P) x := by
  apply MvPolynomial.induction_on P
  · intro c
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  · intro p q hp hq
    simp only [map_add]
    exact AnalyticAt.add hp hq
  · intro p n hp
    simp only [map_mul, MvPolynomial.eval_X]
    exact AnalyticAt.mul hp (hf n)

lemma rep_sigma_analytic (R : HolomorphicLorentzRep ι) (α β : ι) :
    AnalyticAt ℂ (fun x : Fin 6 → ℂ =>
      let A := sl2c_chart_invFun (local_chart_e x).1
      let B := sl2c_chart_invFun (local_chart_e x).2
      R.σ (A, B) α β) 0 := by
  rcases R.polynomial α β with ⟨P, hP⟩
  have h_eq : (fun x : Fin 6 → ℂ =>
      let A := sl2c_chart_invFun (local_chart_e x).1
      let B := sl2c_chart_invFun (local_chart_e x).2
      R.σ (A, B) α β) = fun x => MvPolynomial.eval (fun i =>
        Sum.elim (fun a => (sl2c_chart_invFun (local_chart_e x).1).1 a.1 a.2)
          (fun a => (sl2c_chart_invFun (local_chart_e x).2).1 a.1 a.2) i) P := by
    ext x
    exact hP (sl2c_chart_invFun (local_chart_e x).1, sl2c_chart_invFun (local_chart_e x).2)
  rw [h_eq]
  apply mvPolynomial_eval_analyticAt
  intro i
  rcases i with a | a
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).1) 0 :=
      ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L
          local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).1 = 0 := by ext i; simp [local_chart_e]
    have hA : AnalyticAt ℂ (fun x => (sl2c_chart_invFun (local_chart_e x).1).1) 0 :=
      AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1)
        (f := fun x => (local_chart_e x).1) (h0 ▸ h2) h1
    exact analyticAt_matrix_elem hA a.1 a.2
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).2) 0 :=
      ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L
          local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).2 = 0 := by ext i; simp [local_chart_e]
    have hB : AnalyticAt ℂ (fun x => (sl2c_chart_invFun (local_chart_e x).2).1) 0 :=
      AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1)
        (f := fun x => (local_chart_e x).2) (h0 ▸ h2) h1
    exact analyticAt_matrix_elem hB a.1 a.2

lemma vector_bhw_diff_analytic (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (α : Fin n → ι) :
    AnalyticAt ℂ (vector_bhw_diff R W E n z α) 0 := by
  have h1 : AnalyticAt ℂ (fun x => E.H n α (local_chart x • z)) 0 := by
    have h_an_on := E.analytic n α
    have hU : forward_tube_n n ∈ 𝓝 z := (forward_tube_n_isOpen n).mem_nhds hz
    have h_an_at := h_an_on.analyticAt hU
    exact local_chart_analytic n (E.H n α) z h_an_at
  have h2 : AnalyticAt ℂ (fun x => ∑ β : Fin n → ι,
      (∏ i, R.σ (sl2c_chart_invFun (local_chart_e x).1,
        sl2c_chart_invFun (local_chart_e x).2) (α i) (β i)) * E.H n β z) 0 := by
    apply fintype_sum_analyticAt
    intro β
    apply AnalyticAt.mul
    · apply fintype_prod_analyticAt
      intro i
      exact rep_sigma_analytic R (α i) (β i)
    · exact analyticAt_const
  exact AnalyticAt.sub h1 h2

lemma vector_bhw_diff_eq_zero_on_real (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) (x : Fin 6 → ℝ)
    (h_tube : local_chart (fun i => (x i : ℂ)) • z ∈ forward_tube_n n) :
    vector_bhw_diff R W E n z α (fun i => (x i : ℂ)) = 0 := by
  dsimp [vector_bhw_diff]
  let x_c := fun i => (x i : ℂ)
  let A := sl2c_chart_invFun (local_chart_e x_c).1
  let B := sl2c_chart_invFun (local_chart_e x_c).2
  have hB : B = sl2c_conj A := by
    have h_B1 : B.1 = Matrix.map A.1 star := local_chart_B_eq_map_conj x
    apply Subtype.ext
    exact h_B1
  have h_cov' := h_cov n A z hz
  have h_Lam : local_chart x_c = spinorPhi (A, B) := by rfl
  have h_Lam' : local_chart x_c = spinorPhi (A, sl2c_conj A) := by rw [h_Lam, hB]
  have h_tube' : spinorPhi (A, sl2c_conj A) • z ∈ forward_tube_n n := by
    rw [← h_Lam']
    exact h_tube
  specialize h_cov' h_tube' α
  rw [h_Lam']
  rw [h_cov']
  have h_eq_sum : ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) * E.H n β z =
      ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (A, B) (α i) (β i)) * E.H n β z := by
    apply Finset.sum_congr rfl
    intro β _
    have h_rep : ∀ i, R.rep A (α i) (β i) = R.σ (A, B) (α i) (β i) := by
      intro i
      have hd : R.rep A (α i) (β i) = R.σ (A, sl2c_conj A) (α i) (β i) := by rfl
      rw [hd, ← hB]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact h_rep i
  rw [h_eq_sum]
  exact sub_self _

lemma local_chart_action_continuous (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    ContinuousAt (fun x : Fin 6 → ℂ => local_chart x • z) 0 := by
  have h_act_an : AnalyticAt ℂ (fun x => (local_chart x) • z) 0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    have H2 : (fun x => ((local_chart x) • z) i j) =
        fun x => ∑ k : Fin 4, (local_chart x).1.1 j k * z i k := by
      ext x
      rfl
    rw [H2]
    apply fintype_sum_analyticAt
    intro k
    apply AnalyticAt.mul
    · exact analyticAt_matrix_elem4 local_chart_matrix_analytic j k
    · exact analyticAt_const
  exact h_act_an.continuousAt

lemma vector_bhw_diff_eq_zero_near_zero (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), vector_bhw_diff R W E n z α x = 0 := by
  have hF_analytic : AnalyticAt ℂ (vector_bhw_diff R W E n z α) 0 :=
    vector_bhw_diff_analytic R W E n z hz α
  have hG_analytic : AnalyticAt ℂ (fun _ : Fin 6 → ℂ => (0 : ℂ)) 0 := analyticAt_const
  let my_ofRealN : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℂ) :=
    ContinuousLinearMap.pi (fun i =>
      ContinuousLinearMap.comp Complex.ofRealCLM (ContinuousLinearMap.proj i))
  have h_ofReal : ∀ x : Fin 6 → ℝ, my_ofRealN x = (fun i => (x i : ℂ)) := fun _ => rfl
  have h_cont_R :
      ContinuousAt (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z) 0 := by
    have h_comp : (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z) =
        (fun x => local_chart x • z) ∘ my_ofRealN := rfl
    rw [h_comp]
    apply ContinuousAt.comp
    · exact local_chart_action_continuous n z
    · exact my_ofRealN.continuous.continuousAt
  have h_tube_nhds :
      ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, local_chart (fun i => (x i : ℂ)) • z ∈ forward_tube_n n := by
    have h_open := forward_tube_n_isOpen n
    have hz0 : (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) = 0 := by ext i; simp
    have h0 : local_chart (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) • z = z := by
      rw [hz0]
      have h1 : local_chart 0 = 1 := local_chart_zero
      rw [h1]
      exact one_smul _ z
    have hz_nhds : forward_tube_n n ∈ 𝓝 z := h_open.mem_nhds hz
    have h0' : (fun (x : Fin 6 → ℝ) => local_chart (fun i => (x i : ℂ)) • z) 0 = z := h0
    have hz_nhds' :
        forward_tube_n n ∈
          𝓝 ((fun (x : Fin 6 → ℝ) => local_chart (fun i => (x i : ℂ)) • z) 0) := by
      rw [h0']
      exact hz_nhds
    exact h_cont_R.preimage_mem_nhds hz_nhds'
  have h_real_eq :
      ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, vector_bhw_diff R W E n z α (fun i => (x i : ℂ)) = 0 := by
    apply Filter.Eventually.mono h_tube_nhds
    intro x hx
    exact vector_bhw_diff_eq_zero_on_real R W E h_cov n z hz α x hx
  have h_real_eq2 : ∀ᶠ x : Fin 6 → ℝ in 𝓝 0,
      vector_bhw_diff R W E n z α (my_ofRealN x) = (fun _ => (0 : ℂ)) (my_ofRealN x) := by
    apply Filter.Eventually.mono h_real_eq
    intro x hx
    rw [h_ofReal]
    exact hx
  exact Analysis.analytic_nhds_eq_of_real_eq_N (vector_bhw_diff R W E n z α) (fun _ => 0) 0
    my_ofRealN h_ofReal hF_analytic hG_analytic h_real_eq2

lemma sum_prod_S_eq_H (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α z = ∑ β : Fin n → ι, (∏ i, R.σ (-1, -1) (α i) (β i)) * E.H n β z := by
  have hz_inv : spinorPhi ((-1 : SL2C), sl2c_conj (-1 : SL2C)) • z ∈ forward_tube_n n := by
    have h_conj : sl2c_conj (-1 : SL2C) = -1 := by
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
    rw [h_conj]
    have h_spinor : spinorPhi ((-1 : SL2C), (-1 : SL2C)) = 1 := by
      have h := Geometry.PolarDecomposition.spinorPhi_neg_neg (1 : SL2C) (1 : SL2C)
      rw [h]; exact map_one spinorPhi
    rw [h_spinor]
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [e]
    exact hz
  have h_cov_apply := h_cov n (-1) z hz hz_inv α
  have h_conj : sl2c_conj (-1 : SL2C) = -1 := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
  rw [h_conj] at h_cov_apply
  have h_spinor : spinorPhi ((-1 : SL2C), (-1 : SL2C)) = 1 := by
    have h := Geometry.PolarDecomposition.spinorPhi_neg_neg (1 : SL2C) (1 : SL2C)
    rw [h]; exact map_one spinorPhi
  rw [h_spinor] at h_cov_apply
  have h_one_smul : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ _
  rw [h_one_smul] at h_cov_apply
  have h_rep : R.rep (-1) = R.σ (-1, -1) := by
    rw [HolomorphicLorentzRep.rep_apply, h_conj]
  simp_rw [h_rep] at h_cov_apply
  exact h_cov_apply

lemma G_eq_G_neg (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) (A B : SL2C) :
    ∑ β : Fin n → ι, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β z =
    ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z := by
  have h_neg : ((-A, -B) : SL2C × SL2C) = (A, B) * (-1, -1) := by
    ext1
    · apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
    · apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
  have h_sigma : R.σ (-A, -B) = R.σ (A, B) * R.σ (-1, -1) := by
    rw [h_neg, map_mul]
  have h_prod : ∀ β : Fin n → ι, ∏ i, R.σ (-A, -B) (α i) (β i) =
      ∏ i, ∑ k_i : ι, R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i) := by
    intro β
    apply Finset.prod_congr rfl
    intro i _
    exact congr_fun (congr_fun h_sigma (α i)) (β i)
  have h_sum_prod : ∀ β : Fin n → ι,
      (∏ i, ∑ k_i : ι, R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i)) =
      ∑ k : Fin n → ι, ∏ i, (R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) := by
    intro β
    exact Finset.prod_univ_sum (fun _ => (Finset.univ : Finset ι))
      (fun i k_i => R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i))
  calc
    ∑ β, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β z
      = ∑ β, (∑ k : Fin n → ι,
          ∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro β _
        rw [h_prod β, h_sum_prod β]
    _ = ∑ β, ∑ k : Fin n → ι,
        (∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro β _
        exact Finset.sum_mul _ _ _
    _ = ∑ k : Fin n → ι, ∑ β,
        (∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        exact Finset.sum_comm
    _ = ∑ k : Fin n → ι, ∑ β,
        (∏ i, R.σ (A, B) (α i) (k i)) * (∏ i, R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro β _
        rw [Finset.prod_mul_distrib]
    _ = ∑ k : Fin n → ι,
        (∏ i, R.σ (A, B) (α i) (k i)) * ∑ β, (∏ i, R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro β _
        ring
    _ = ∑ k : Fin n → ι, (∏ i, R.σ (A, B) (α i) (k i)) * E.H n k z := by
        apply Finset.sum_congr rfl
        intro k _
        have h_S := sum_prod_S_eq_H R W E h_cov n z hz k
        rw [← h_S]

lemma spinor_action_eq_self_imp (A B : SL2C) (h : spinorPhi (A, B) = 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    A.1 * X * B.1ᵀ = X := by
  have h_mat : spinorPhi_matrix A B = 1 := by
    have h1 : spinorPhi_matrix A B = (spinorPhi (A, B)).val.val := rfl
    rw [h1, h]
    rfl
  have h_act : ∀ x, spinor_action A.1 B.1 x = x := by
    intro x
    rw [← spinorPhi_matrix_mulVec, h_mat, Matrix.one_mulVec]
  have h1 := h_act (spinor_to_vec X)
  rw [spinor_action, vec_to_spinor_right_inv] at h1
  have h2 := congrArg vec_to_spinor h1
  rw [vec_to_spinor_right_inv, vec_to_spinor_right_inv] at h2
  exact h2

lemma spinorPhi_eq_one_imp (A B : SL2C) (h : spinorPhi (A, B) = 1) :
    (A, B) = (1, 1) ∨ (A, B) = (-1, -1) := by
  have hX := spinor_action_eq_self_imp A B h
  have hAB : A.1 * B.1ᵀ = 1 := by simpa using hX 1
  have hBA : B.1ᵀ * A.1 = 1 := mul_eq_one_comm.mp hAB
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, A.1 * X = X * A.1 := by
    intro X
    have := hX X
    calc A.1 * X = (A.1 * X * B.1ᵀ) * A.1 := by
          rw [mul_assoc (A.1 * X), hBA, mul_one]
      _ = X * A.1 := by rw [this]
  have e1 := hcomm !![1, 0; 0, 0]
  have e2 := hcomm !![0, 1; 0, 0]
  have hA := Matrix.eta_fin_two A.1
  have hdet : A.1.det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have hb : A.1 0 1 = 0 := by
    have h := (congrFun (congrFun e1 0) 1).symm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hc : A.1 1 0 = 0 := by
    have h := congrFun (congrFun e1 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have had : A.1 0 0 = A.1 1 1 := by
    have h := congrFun (congrFun e2 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  set a := A.1 0 0 with ha
  have haa : a * a = 1 := by
    rw [hb, hc, ← had] at hdet
    simpa using hdet
  have hA' : A.1 = !![a, 0; 0, a] := by
    rw [Matrix.eta_fin_two A.1, hb, hc, ← had]
  have h_aB00 : a * B.1 0 0 = 1 := by
    have h := congrFun (congrFun hAB 0) 0
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB00 : B.1 0 0 = a := by
    calc B.1 0 0 = (a * a) * B.1 0 0 := by rw [haa, one_mul]
      _ = a * (a * B.1 0 0) := by ring
      _ = a := by rw [h_aB00, mul_one]
  have h_aB11 : a * B.1 1 1 = 1 := by
    have h := congrFun (congrFun hAB 1) 1
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB11 : B.1 1 1 = a := by
    calc B.1 1 1 = (a * a) * B.1 1 1 := by rw [haa, one_mul]
      _ = a * (a * B.1 1 1) := by ring
      _ = a := by rw [h_aB11, mul_one]
  have h_aB01 : a = 0 ∨ B.1 0 1 = 0 := by
    have h := congrFun (congrFun hAB 1) 0
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB01 : B.1 0 1 = 0 := by
    rcases h_aB01 with h0 | h0
    · have ha_ne : a ≠ 0 := by intro h0'; rw [h0'] at haa; simp at haa
      exact absurd h0 ha_ne
    · exact h0
  have h_aB10 : a = 0 ∨ B.1 1 0 = 0 := by
    have h := congrFun (congrFun hAB 0) 1
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB10 : B.1 1 0 = 0 := by
    rcases h_aB10 with h0 | h0
    · have ha_ne : a ≠ 0 := by intro h0'; rw [h0'] at haa; simp at haa
      exact absurd h0 ha_ne
    · exact h0
  have hB' : B.1 = !![a, 0; 0, a] := by
    rw [Matrix.eta_fin_two B.1, hB00, hB01, hB10, hB11]
  rcases mul_self_eq_one_iff.mp haa with h1 | h1
  · left
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hA', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [hB', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · right
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hA', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [hB', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp

noncomputable def Tm (R : HolomorphicLorentzRep ι) (n : ℕ) (g : SL2C × SL2C)
    (α β : Fin n → ι) : ℂ :=
  ∏ i, R.σ g (α i) (β i)

lemma Tm_mul (R : HolomorphicLorentzRep ι) (n : ℕ) (g h : SL2C × SL2C) (α β : Fin n → ι) :
    Tm R n (g * h) α β = ∑ γ : Fin n → ι, Tm R n g α γ * Tm R n h γ β := by
  unfold Tm
  have h1 : ∀ i, R.σ (g * h) (α i) (β i) = ∑ k : ι, R.σ g (α i) k * R.σ h k (β i) := by
    intro i; rw [map_mul, Matrix.mul_apply]
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ι))
    (fun i k_i => R.σ g (α i) k_i * R.σ h k_i (β i))
  have h3 : ∏ i, ∑ k_i : ι, R.σ g (α i) k_i * R.σ h k_i (β i)
      = ∑ k : Fin n → ι, ∏ i, (R.σ g (α i) (k i) * R.σ h (k i) (β i)) := h2
  rw [h3]
  apply Finset.sum_congr rfl
  intro γ _
  exact Finset.prod_mul_distrib

lemma Tm_one (R : HolomorphicLorentzRep ι) (n : ℕ) (α β : Fin n → ι) :
    Tm R n 1 α β = if α = β then 1 else 0 := by
  unfold Tm
  rw [map_one]
  by_cases h : α = β
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma Tm_injective (R : HolomorphicLorentzRep ι) (n : ℕ) (g : SL2C × SL2C)
    (v : (Fin n → ι) → ℂ) (h : ∀ α, ∑ β, Tm R n g α β * v β = 0) : ∀ γ, v γ = 0 := by
  intro γ
  have h1 : ∑ α, Tm R n g⁻¹ γ α * (∑ β, Tm R n g α β * v β) = 0 := by
    simp [h]
  have h2 : ∑ α, Tm R n g⁻¹ γ α * (∑ β, Tm R n g α β * v β) = v γ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have key : ∀ β, ∑ α, Tm R n g⁻¹ γ α * (Tm R n g α β * v β) =
        (if γ = β then 1 else 0) * v β := by
      intro β
      rw [← Tm_one R n γ β, ← inv_mul_cancel g, Tm_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun α _ => by ring)
    simp_rw [key]
    simp
  rw [← h2]; exact h1

noncomputable def dd (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (g : SL2C × SL2C) (α : Fin n → ι) : ℂ :=
  E.H n α (spinorPhi g • z) - ∑ β, Tm R n g α β * E.H n β z

lemma dd_mul (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (h g : SL2C × SL2C) (α : Fin n → ι) :
    dd R W E n z (h * g) α =
      (E.H n α (spinorPhi h • (spinorPhi g • z)) -
        ∑ β, Tm R n h α β * E.H n β (spinorPhi g • z)) +
      ∑ β, Tm R n h α β * dd R W E n z g β := by
  unfold dd
  have e1 : spinorPhi (h * g) • z = spinorPhi h • (spinorPhi g • z) := by
    rw [map_mul]; exact mul_smul _ _ _
  rw [e1]
  have e2 : ∑ γ, Tm R n (h * g) α γ * E.H n γ z =
      ∑ β, Tm R n h α β * ∑ γ, Tm R n g β γ * E.H n γ z := by
    simp_rw [Tm_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  rw [e2]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

lemma dd_neg (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (g : SL2C × SL2C) (α : Fin n → ι) :
    dd R W E n z (-g.1, -g.2) α = dd R W E n z g α := by
  obtain ⟨A, B⟩ := g
  unfold dd Tm
  rw [Geometry.PolarDecomposition.spinorPhi_neg_neg A B]
  have := G_eq_G_neg R W E h_cov n z hz α A B
  rw [this]

lemma dd_eq_of_phi_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (g g' : SL2C × SL2C) (h : spinorPhi g = spinorPhi g') (α : Fin n → ι) :
    dd R W E n z g' α = dd R W E n z g α := by
  have hk : spinorPhi (g⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hg' : g' = g * (g⁻¹ * g') := by simp
  rcases spinorPhi_eq_one_imp (g⁻¹ * g').1 (g⁻¹ * g').2 hk with h1 | h1
  · have : g⁻¹ * g' = 1 := h1
    rw [this, mul_one] at hg'
    rw [← hg']
  · have h2 : g⁻¹ * g' = (-1, -1) := h1
    rw [h2] at hg'
    have h3 : g' = (-g.1, -g.2) := by
      rw [hg']
      refine Prod.ext ?_ ?_ <;> simp
    rw [h3]
    exact dd_neg R W E h_cov n z hz g α

noncomputable def gcart (x : Fin 6 → ℂ) : SL2C × SL2C :=
  (sl2c_chart_invFun (local_chart_e x).1, sl2c_chart_invFun (local_chart_e x).2)

lemma local_chart_eq (x : Fin 6 → ℂ) : local_chart x = spinorPhi (gcart x) := rfl

lemma local_nbhd (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (g1 : SL2C × SL2C)
    (hg1 : spinorPhi g1 • z ∈ forward_tube_n n) :
    ∀ᶠ Λ in 𝓝 (spinorPhi g1), ∃ x : Fin 6 → ℂ, Λ = spinorPhi (gcart x * g1) ∧
      ∀ α, vector_bhw_diff R W E n (spinorPhi g1 • z) α x = 0 := by
  have h_ev : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (spinorPhi g1 • z) α x = 0 :=
    Filter.eventually_all.mpr (fun α => vector_bhw_diff_eq_zero_near_zero R W E h_cov n _ hg1 α)
  obtain ⟨U, hU, hUeq⟩ := eventually_iff_exists_mem.mp h_ev
  have h_img := local_chart_isOpenMap_at_zero U hU
  have h_mult : Tendsto (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)
      (𝓝 (spinorPhi g1)) (𝓝 1) := by
    have h0 := (continuous_mul_const (spinorPhi g1)⁻¹ : Continuous
      (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)).tendsto (spinorPhi g1)
    rwa [mul_inv_cancel] at h0
  filter_upwards [h_mult h_img] with Λ hΛ
  obtain ⟨x, hx, hxe⟩ := hΛ
  refine ⟨x, ?_, hUeq x hx⟩
  rw [map_mul, ← local_chart_eq, hxe, inv_mul_cancel_right]

theorem complex_covariance_of_real (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) :
    ComplexCovariant R E := by
  intro n A B z hz_tube hz_trans α
  let D := orbit_domain n z
  have hD_conn : IsConnected D := is_connected_orbit_domain n z hz_tube
  have hD_open : IsOpen D := orbit_domain_isOpen n z
  let u : Set SpecialSpecialComplexLorentzGroup :=
    {Λ | Λ ∈ D ∧ ∃ g, spinorPhi g = Λ ∧ ∀ α, dd R W E n z g α = 0}
  let v : Set SpecialSpecialComplexLorentzGroup := D \ u
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ0 ⟨hΛ0D, g0, hg0, hd0⟩
    subst hg0
    have hz0 : spinorPhi g0 • z ∈ forward_tube_n n := hΛ0D
    have h_loc := local_nbhd R W E h_cov n z g0 hz0
    have h_D : D ∈ 𝓝 (spinorPhi g0) := hD_open.mem_nhds hΛ0D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, gcart x * g0, hΛx.symm, ?_⟩
    intro α'
    rw [dd_mul]
    have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g0 • z)) -
        ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g0 • z) =
        vector_bhw_diff R W E n (spinorPhi g0 • z) α' x := rfl
    rw [h1, hx0 α']
    simp [hd0]
  have hv_open : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ1 ⟨hΛ1D, hΛ1u⟩
    obtain ⟨g1, hg1⟩ := spinorPhi_surjective Λ1
    subst hg1
    have hz1 : spinorPhi g1 • z ∈ forward_tube_n n := hΛ1D
    have h_loc := local_nbhd R W E h_cov n z g1 hz1
    have h_D : D ∈ 𝓝 (spinorPhi g1) := hD_open.mem_nhds hΛ1D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, ?_⟩
    rintro ⟨_, g', hg', hd'⟩
    apply hΛ1u
    refine ⟨hΛ1D, g1, rfl, ?_⟩
    have hphi : spinorPhi (gcart x * g1) = spinorPhi g' := by rw [← hΛx, hg']
    have hzero : ∀ α', dd R W E n z (gcart x * g1) α' = 0 := by
      intro α'
      rw [dd_eq_of_phi_eq R W E h_cov n z hz_tube _ _ hphi.symm α']
      exact hd' α'
    have hzero' : ∀ α', ∑ β, Tm R n (gcart x) α' β * dd R W E n z g1 β = 0 := by
      intro α'
      have := hzero α'
      rw [dd_mul] at this
      have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g1 • z)) -
          ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g1 • z) =
          vector_bhw_diff R W E n (spinorPhi g1 • z) α' x := rfl
      rw [h1, hx0 α', zero_add] at this
      exact this
    exact Tm_injective R n (gcart x) _ hzero'
  have huv : Disjoint u v := by
    rw [Set.disjoint_iff]
    rintro Λ ⟨hu, hv⟩
    exact hv.2 hu
  have h_union : D ⊆ u ∪ v := by
    intro Λ hΛ
    by_cases h : Λ ∈ u
    · exact Or.inl h
    · exact Or.inr ⟨hΛ, h⟩
  have h_nonempty : (D ∩ u).Nonempty := by
    have h1 : (1 : SpecialSpecialComplexLorentzGroup) ∈ D := by
      change (1 : SpecialSpecialComplexLorentzGroup) • z ∈ forward_tube_n n
      have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
      rw [e]; exact hz_tube
    refine ⟨1, h1, h1, 1, map_one _, ?_⟩
    intro α'
    unfold dd
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [map_one, e]
    simp [Tm_one]
  have h_sub : D ⊆ u :=
    hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have hmem : spinorPhi (A, B) ∈ u := h_sub hz_trans
  obtain ⟨_, g, hg, hd⟩ := hmem
  have := dd_eq_of_phi_eq R W E h_cov n z hz_tube g (A, B) hg α
  rw [hd α] at this
  unfold dd Tm at this
  exact sub_eq_zero.mp this

noncomputable def spinorPT : SpecialSpecialComplexLorentzGroup :=
  spinorPhi (-1, 1)

lemma spinorPT_val_unit :
    spinorPT.val = -(1 : Matrix.GeneralLinearGroup (Fin 4) ℂ) := by
  dsimp [spinorPT]
  have h := Geometry.PolarDecomposition.spinorPhi_neg_left (1 : SL2C) (1 : SL2C)
  have h1 : spinorPhi ((1 : SL2C), (1 : SL2C)) = 1 := map_one spinorPhi
  rw [h1] at h
  exact h

lemma spinorPT_val :
    spinorPT.val.val = -(1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := congrArg Units.val spinorPT_val_unit
  exact h

lemma spinorPhi_one_neg_one :
    spinorPhi ((1 : SL2C), (-1 : SL2C)) = spinorPT := by
  dsimp [spinorPT]
  have h := Geometry.PolarDecomposition.spinorPhi_neg_neg (-1 : SL2C) (1 : SL2C)
  rw [neg_neg] at h
  exact h

lemma spinorPT_smul_vec (v : Fin 4 → ℂ) :
    spinorPT • v = -v := by
  change (spinorPT.val.val).mulVec v = -v
  rw [spinorPT_val, Matrix.neg_mulVec, Matrix.one_mulVec]

lemma spinorPT_smul (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spinorPT • z = -z := by
  ext i k
  exact congrFun (spinorPT_smul_vec (z i)) k

lemma spinorPhi_neg_one_one_smul (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spinorPhi ((-1 : SL2C), (1 : SL2C)) • z = -z :=
  spinorPT_smul n z

lemma spinorPhi_one_neg_one_smul (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spinorPhi ((1 : SL2C), (-1 : SL2C)) • z = -z := by
  rw [spinorPhi_one_neg_one]
  exact spinorPT_smul n z

lemma spinorPT_mul_self :
    spinorPT * spinorPT = 1 := by
  dsimp [spinorPT]
  rw [← map_mul]
  have h : ((-1 : SL2C), (1 : SL2C)) * ((-1 : SL2C), (1 : SL2C)) = 1 := by
    ext1 <;> simp
  rw [h, map_one]

lemma spinorPT_inv :
    spinorPT⁻¹ = spinorPT :=
  inv_eq_of_mul_eq_one_right spinorPT_mul_self

lemma neg_mem_forward_light_cone_iff (v : Fin 4 → ℝ) :
    -v ∈ forward_light_cone ↔ v ∈ backward_light_cone := by
  dsimp [forward_light_cone, backward_light_cone]
  rw [minkowskiInner_explicit, minkowskiInner_explicit]
  simp only [Pi.neg_apply, neg_mul_neg]
  constructor <;> rintro ⟨h0, h1⟩ <;> refine ⟨by linarith, h1⟩

lemma neg_mem_backward_light_cone_iff (v : Fin 4 → ℝ) :
    -v ∈ backward_light_cone ↔ v ∈ forward_light_cone := by
  rw [← neg_mem_forward_light_cone_iff, neg_neg]

lemma neg_diff_im_eq (n : ℕ) (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) :
    (fun k => -(((-z) i - (-z) ⟨i.val + 1, hi⟩) k).im) =
      -(fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im) := by
  ext k
  simp only [Pi.neg_apply, Pi.sub_apply, Complex.sub_im, Complex.neg_im]
  ring

lemma neg_mem_forward_tube_n_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    -z ∈ forward_tube_n n ↔ z ∈ backward_tube_n n := by
  constructor
  · intro hz i hi
    have h := hz i hi
    rw [neg_diff_im_eq, neg_mem_forward_light_cone_iff] at h
    exact h
  · intro hz i hi
    have h := hz i hi
    rw [← neg_mem_forward_light_cone_iff, ← neg_diff_im_eq] at h
    exact h

lemma neg_rev_diff_eq (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) :
    ((-(z ∘ Fin.rev)) i - (-(z ∘ Fin.rev)) ⟨i.val + 1, hi⟩) =
      z ⟨n - 1 - (i.val + 1), by omega⟩ -
      z ⟨(n - 1 - (i.val + 1)) + 1, by omega⟩ := by
  ext k
  simp only [Pi.neg_apply, Pi.sub_apply, Function.comp_apply]
  have h1 : (Fin.rev ⟨i.val + 1, hi⟩ : Fin n) = ⟨n - 1 - (i.val + 1), by omega⟩ := by
    ext
    dsimp [Fin.rev]
    omega
  have h2 : (Fin.rev i : Fin n) = ⟨(n - 1 - (i.val + 1)) + 1, by omega⟩ := by
    ext
    dsimp [Fin.rev]
    omega
  rw [h1, h2]
  ring

lemma neg_rev_mem_forward_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    -(z ∘ Fin.rev) ∈ forward_tube_n n := by
  intro i hi
  rw [neg_rev_diff_eq n z i hi]
  exact hz ⟨n - 1 - (i.val + 1), by omega⟩ (by dsimp; omega)

lemma neg_rev_involutive (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    -((-(z ∘ Fin.rev)) ∘ Fin.rev) = z := by
  ext i k
  simp [Fin.rev_rev]

lemma neg_rev_mem_forward_tube_n_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    -(z ∘ Fin.rev) ∈ forward_tube_n n ↔ z ∈ forward_tube_n n := by
  constructor
  · intro h
    have h2 := neg_rev_mem_forward_tube_n n (-(z ∘ Fin.rev)) h
    rwa [neg_rev_involutive] at h2
  · exact neg_rev_mem_forward_tube_n n z

lemma rev_mem_backward_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    (z ∘ Fin.rev) ∈ backward_tube_n n :=
  (neg_mem_forward_tube_n_iff n (z ∘ Fin.rev)).mp (neg_rev_mem_forward_tube_n n z hz)

lemma spinorPT_smul_rev_mem_forward_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    spinorPT • (z ∘ Fin.rev) ∈ forward_tube_n n := by
  rw [spinorPT_smul]
  exact neg_rev_mem_forward_tube_n n z hz

lemma backward_tube_subset_extended_tube_n (n : ℕ) :
    backward_tube_n n ⊆ extended_tube_n n := by
  intro z hz
  have h_neg : -z ∈ forward_tube_n n := (neg_mem_forward_tube_n_iff n z).mpr hz
  dsimp [extended_tube_n]
  rw [Set.mem_iUnion]
  refine ⟨spinorPT, -z, h_neg, ?_⟩
  dsimp
  rw [spinorPT_smul, neg_neg]

lemma rev_mem_extended_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    (z ∘ Fin.rev) ∈ extended_tube_n n :=
  backward_tube_subset_extended_tube_n n (rev_mem_backward_tube_n n z hz)

theorem vladimirov_complexCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W) :
    ComplexCovariant R (vladimirovTubeExtension R W hspec hP) :=
  complex_covariance_of_real R W
    (vladimirovTubeExtension R W hspec hP)
    (vladimirov_tubeCovariant R W hspec hP)

lemma prod_spinParity (R : HolomorphicLorentzRep ι) (ε : ℂ)
    (hε : R.HasSpinParity ε) (n : ℕ) (α β : Fin n → ι) :
    (∏ i : Fin n, R.σ (-1, -1) (α i) (β i)) = if α = β then ε ^ n else 0 := by
  rw [hε.1]
  by_cases h : α = β
  · subst h
    simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [Matrix.one_apply_ne hi])

theorem tube_spin_parity_selection (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (ε : ℂ) (hε : R.HasSpinParity ε)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α z = ε ^ n * E.H n α z := by
  have h_sum := sum_prod_S_eq_H R W E h_cov n z hz α
  simp_rw [prod_spinParity R ε hε n α] at h_sum
  simpa using h_sum

theorem tube_eq_zero_of_odd_fermion (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (hε : R.HasSpinParity (-1))
    (n : ℕ) (hn : Odd n) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α z = 0 := by
  have h_sel := tube_spin_parity_selection R W E h_cov (-1) hε n z hz α
  rw [Odd.neg_one_pow hn] at h_sel
  linear_combination (1 / 2 : ℂ) * h_sel

open MeasureTheory

noncomputable def tubeBasePoint (n : ℕ) : Fin n → Fin 4 → ℂ :=
  fun i k => Complex.I * (((i.val : ℝ) * unit_time_vector k : ℝ) : ℂ)

lemma tubeBasePoint_mem_forward_tube_n (n : ℕ) :
    tubeBasePoint n ∈ forward_tube_n n := by
  intro i hi
  have h_eq : (fun k => -((tubeBasePoint n i - tubeBasePoint n ⟨i.val + 1, hi⟩) k).im) =
      unit_time_vector := by
    ext k
    simp only [tubeBasePoint, Pi.sub_apply, Complex.sub_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [h_eq]
  exact unit_time_vector_mem_forward_light_cone

def spacelikeVec : Fin 4 → ℝ :=
  fun k => if k = 1 then -1 else 0

lemma is_spacelike_of_mem_ball_spacelikeVec (u : Fin 4 → ℝ)
    (hu : u ∈ Metric.ball spacelikeVec (1 / 2)) :
    is_spacelike u := by
  rw [Metric.mem_ball, dist_eq_norm] at hu
  have h0 : ‖(u - spacelikeVec) 0‖ < 1 / 2 :=
    lt_of_le_of_lt (norm_le_pi_norm (u - spacelikeVec) 0) hu
  have h1 : ‖(u - spacelikeVec) 1‖ < 1 / 2 :=
    lt_of_le_of_lt (norm_le_pi_norm (u - spacelikeVec) 1) hu
  have h0_eq : (u - spacelikeVec) 0 = u 0 := by
    dsimp [spacelikeVec]; ring
  have h1_eq : (u - spacelikeVec) 1 = u 1 + 1 := by
    dsimp [spacelikeVec]; ring
  rw [h0_eq, Real.norm_eq_abs, abs_lt] at h0
  rw [h1_eq, Real.norm_eq_abs, abs_lt] at h1
  have h2_sq : 0 ≤ u 2 * u 2 := mul_self_nonneg (u 2)
  have h3_sq : 0 ≤ u 3 * u 3 := mul_self_nonneg (u 3)
  dsimp [is_spacelike]
  rw [minkowskiInner_explicit]
  nlinarith

def jostCenter (n : ℕ) : Fin n → Fin 4 → ℝ :=
  fun i k => if k = 1 then (i.val : ℝ) else 0

lemma jostCenter_diff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    jostCenter n i - jostCenter n ⟨i.val + 1, hi⟩ = spacelikeVec := by
  ext k
  dsimp [jostCenter, spacelikeVec]
  split_ifs <;> push_cast <;> ring

lemma ball_jostCenter_subset_jost_points_n (n : ℕ) :
    Metric.ball (jostCenter n) (1 / 4) ⊆ jost_points_n n := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h_diff : jost_differences_n n x ⊆ Metric.ball spacelikeVec (1 / 2) := by
    rintro v ⟨i, hi, rfl⟩
    let j : Fin n := ⟨i.val + 1, hi⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h_sub : x i - x j - spacelikeVec =
        (x - jostCenter n) i - (x - jostCenter n) j := by
      rw [← jostCenter_diff n i hi]
      ext k
      simp only [Pi.sub_apply]
      ring
    rw [h_sub]
    have hi_norm : ‖(x - jostCenter n) i‖ ≤ ‖x - jostCenter n‖ :=
      norm_le_pi_norm (x - jostCenter n) i
    have hj_norm : ‖(x - jostCenter n) j‖ ≤ ‖x - jostCenter n‖ :=
      norm_le_pi_norm (x - jostCenter n) j
    have h_tri : ‖(x - jostCenter n) i - (x - jostCenter n) j‖ ≤
        ‖(x - jostCenter n) i‖ + ‖(x - jostCenter n) j‖ :=
      norm_sub_le _ _
    linarith
  have h_hull : jost_convex_hull n x ⊆ Metric.ball spacelikeVec (1 / 2) :=
    convexHull_min h_diff (convex_ball spacelikeVec (1 / 2))
  intro v hv
  exact is_spacelike_of_mem_ball_spacelikeVec v (h_hull hv)

noncomputable def jostBump (n : ℕ) : ContDiffBump (jostCenter n) where
  rIn := 1 / 16
  rOut := 1 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma jostBump_complex_hasCompactSupport (n : ℕ) :
    HasCompactSupport (fun x : Fin n → Fin 4 → ℝ => ((jostBump n x : ℝ) : ℂ)) :=
  (jostBump n).hasCompactSupport.comp_left Complex.ofReal_zero

lemma jostBump_complex_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → Fin 4 → ℝ => ((jostBump n x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (jostBump n).contDiff

noncomputable def jostSchwartz (n : ℕ) : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (jostBump_complex_hasCompactSupport n).toSchwartzMap (jostBump_complex_contDiff n)

lemma jostSchwartz_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    jostSchwartz n x = ((jostBump n x : ℝ) : ℂ) := rfl

lemma jostSchwartz_tsupport_subset_jost_points (n : ℕ) :
    tsupport (jostSchwartz n : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n n := by
  have h_supp : Function.support (jostSchwartz n : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
      Metric.ball (jostCenter n) (1 / 8) := by
    intro x hx
    have hx_bump : jostBump n x ≠ 0 := by
      intro h0
      apply hx
      rw [jostSchwartz_apply, h0, Complex.ofReal_zero]
    have hx_s : x ∈ Function.support (jostBump n) := hx_bump
    rw [(jostBump n).support_eq] at hx_s
    exact hx_s
  have h_tsupp : tsupport (jostSchwartz n : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
      Metric.closedBall (jostCenter n) (1 / 8) :=
    (closure_mono h_supp).trans Metric.closure_ball_subset_closedBall
  refine h_tsupp.trans (fun x hx => ball_jostCenter_subset_jost_points_n n ?_)
  exact Metric.closedBall_subset_ball (by norm_num) hx

lemma jostSchwartz_mem_jost_points_of_ne_zero (n : ℕ) (x : Fin n → Fin 4 → ℝ)
    (hx : jostSchwartz n x ≠ 0) :
    x ∈ jost_points_n n :=
  jostSchwartz_tsupport_subset_jost_points n (subset_tsupport _ hx)

lemma integral_jostSchwartz_ne_zero (n : ℕ) :
    (∫ x : Fin n → Fin 4 → ℝ, jostSchwartz n x) ≠ 0 := by
  have h_re : (∫ x : Fin n → Fin 4 → ℝ, ((jostBump n x : ℝ) : ℂ)) =
      Complex.ofReal (∫ x : Fin n → Fin 4 → ℝ, (jostBump n x : ℝ)) :=
    integral_ofReal
  intro h0
  change (∫ x : Fin n → Fin 4 → ℝ, ((jostBump n x : ℝ) : ℂ)) = 0 at h0
  rw [h_re, Complex.ofReal_eq_zero] at h0
  exact ne_of_gt (ContDiffBump.integral_pos (jostBump n)) h0

lemma abs_det_of_involutive_cle (n : ℕ)
    (e : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ))
    (h_inv : ∀ x, e (e x) = x) :
    |LinearMap.det e.toLinearMap| = 1 := by
  have h_comp : e.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact h_inv x
  have h_det := congr_arg LinearMap.det h_comp
  rw [LinearMap.det_comp, LinearMap.det_id] at h_det
  rcases mul_self_eq_one_iff.mp h_det with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

lemma measurePreserving_of_involutive_cle (n : ℕ)
    (e : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ))
    (h_inv : ∀ x, e (e x) = x) :
    MeasurePreserving e volume volume := by
  have h_abs := abs_det_of_involutive_cle n e h_inv
  have h_det_ne : LinearMap.det e.toLinearMap ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at h_abs
    exact zero_ne_one h_abs
  have h_map := Measure.map_linearMap_addHaar_eq_smul_addHaar volume h_det_ne
  rw [abs_inv, h_abs, inv_one, ENNReal.ofReal_one, one_smul] at h_map
  exact ⟨e.continuous.measurable, h_map⟩

lemma integral_comp_of_involutive_cle (n : ℕ)
    (e : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ))
    (h_inv : ∀ x, e (e x) = x)
    (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x, g (e x)) = ∫ x, g x := by
  have h_meas := measurePreserving_of_involutive_cle n e h_inv
  have h_emb : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  exact h_meas.integral_comp h_emb g

def revLinearEquiv (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃ₗ[ℝ] (Fin n → Fin 4 → ℝ) where
  toFun x i := x (Fin.rev i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x i := x (Fin.rev i)
  left_inv x := by ext i k; simp [Fin.rev_rev]
  right_inv x := by ext i k; simp [Fin.rev_rev]

noncomputable def revCLE (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
  (revLinearEquiv n).toContinuousLinearEquiv

lemma revCLE_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    revCLE n x = fun i => x (Fin.rev i) := rfl

lemma revCLE_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    revCLE n (revCLE n x) = x := by
  ext i k
  simp [revCLE_apply, Fin.rev_rev]

lemma integral_comp_rev (n : ℕ) (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (fun i => x (Fin.rev i))) = ∫ x, g x :=
  integral_comp_of_involutive_cle n (revCLE n) (revCLE_involutive n) g

noncomputable def schwartzRevCLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (revCLE n)

@[simp]
lemma schwartzRevCLM_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzRevCLM n f x = f (fun i => x (Fin.rev i)) := rfl

def pctLinearEquiv (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃ₗ[ℝ] (Fin n → Fin 4 → ℝ) where
  toFun x i := -x (Fin.rev i)
  map_add' x y := by ext i k; simp [add_comm]
  map_smul' c x := by ext i k; simp
  invFun x i := -x (Fin.rev i)
  left_inv x := by ext i k; simp [Fin.rev_rev]
  right_inv x := by ext i k; simp [Fin.rev_rev]

noncomputable def pctCLE (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
  (pctLinearEquiv n).toContinuousLinearEquiv

lemma pctCLE_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    pctCLE n x = fun i => -x (Fin.rev i) := rfl

lemma pctCLE_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    pctCLE n (pctCLE n x) = x := by
  ext i k
  simp [pctCLE_apply, Fin.rev_rev]

lemma integral_comp_pct (n : ℕ) (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (fun i => -x (Fin.rev i))) = ∫ x, g x :=
  integral_comp_of_involutive_cle n (pctCLE n) (pctCLE_involutive n) g

noncomputable def schwartzPCTCLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (pctCLE n)

@[simp]
lemma schwartzPCTCLM_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzPCTCLM n f x = f (fun i => -x (Fin.rev i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_eq_zero_eval {W : WightmanFamily ι} (hspec : ZeroMomentumSpectrumCondition W)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) :
    vladimirov_H W n α z = vladimirov_H W n α 0 :=
  vladimirov_H_eq_const_of_zero_fourier W n α (hspec n α) z

omit [Fintype ι] [DecidableEq ι] in
lemma W_n_eq_vladimirov_H_zero_mul_integral {W : WightmanFamily ι}
    (hspec : ZeroMomentumSpectrumCondition W)
    (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = vladimirov_H W n α 0 * ∫ x, f x :=
  W_n_eq_integral_of_zero_fourier W n α (hspec n α) f

def TubeWeakLocality (η : ℂ) {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n →
    E.H n α (-(z ∘ Fin.rev)) = η ^ (n * (n - 1) / 2) * E.H n (α ∘ Fin.rev) z

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_zero_weakLocality {W : WightmanFamily ι} {η : ℂ}
    (hspec : ZeroMomentumSpectrumCondition W) (hloc : WeakLocality η W)
    (n : ℕ) (α : Fin n → ι) :
    vladimirov_H W n α 0 = η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) 0 := by
  let f := jostSchwartz n
  let f' := schwartzRevCLM n f
  have hf_jost : tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n n :=
    jostSchwartz_tsupport_subset_jost_points n
  have hf'_rev : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x := by
    intro x
    dsimp [f']
    congr 1
    ext i k
    simp [Fin.rev_rev]
  have hW := hloc n α f f' hf_jost hf'_rev
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f,
      W_n_eq_vladimirov_H_zero_mul_integral hspec n (α ∘ Fin.rev) f'] at hW
  have h_int_eq : (∫ x, f' x) = ∫ x, f x :=
    integral_comp_rev n f
  rw [h_int_eq, ← mul_assoc] at hW
  exact mul_right_cancel₀ (integral_jostSchwartz_ne_zero n) hW

theorem vladimirov_tubeWeakLocality (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) :
    TubeWeakLocality η (vladimirovTubeExtension R W hspec hP) := by
  intro n α z _hz
  change vladimirov_H W n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z
  rw [vladimirov_H_eq_zero_eval hspec n α (-(z ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) z]
  exact vladimirov_H_zero_weakLocality hspec hloc n α

theorem global_weakLocality_of_tubeWeakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (h_tloc : TubeWeakLocality η (vladimirovTubeExtension R W hspec hP))
    (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W n α f = η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) f' := by
  have h_base := h_tloc n α (tubeBasePoint n) (tubeBasePoint_mem_forward_tube_n n)
  change vladimirov_H W n α (-(tubeBasePoint n ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) (tubeBasePoint n) at h_base
  rw [vladimirov_H_eq_zero_eval hspec n α (-(tubeBasePoint n ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) (tubeBasePoint n)] at h_base
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f,
      W_n_eq_vladimirov_H_zero_mul_integral hspec n (α ∘ Fin.rev) f']
  have h_int : (∫ x, f x) = ∫ x, f' x := by
    have h_f_eq : (fun x : Fin n → Fin 4 → ℝ => f x) =
        (fun x => f' (fun i => x (Fin.rev i))) := by
      ext x
      exact (hf' x).symm
    rw [h_f_eq]
    exact integral_comp_rev n f'
  rw [h_base, h_int, mul_assoc]

theorem weakLocality_of_vladimirov_tubeWeakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (h_tloc : TubeWeakLocality η (vladimirovTubeExtension R W hspec hP)) :
    WeakLocality η W := by
  intro n α f f' _hf_jost hf'
  exact global_weakLocality_of_tubeWeakLocality R W hspec hP h_tloc n α f f' hf'

theorem jost_theorem_vladimirov (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W) :
    WeakLocality η W ↔ TubeWeakLocality η (vladimirovTubeExtension R W hspec hP) :=
  ⟨vladimirov_tubeWeakLocality R W hspec hP,
   weakLocality_of_vladimirov_tubeWeakLocality R W hspec hP⟩

theorem global_weakLocality_of_weakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W n α f = η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) f' :=
  global_weakLocality_of_tubeWeakLocality R W hspec hP
    (vladimirov_tubeWeakLocality R W hspec hP hloc) n α f f' hf'

lemma forward_tube_zero_mem : (0 : Fin 0 → Fin 4 → ℂ) ∈ forward_tube_n 0 :=
  fun i _ => Fin.elim0 i

lemma mem_orbit_domain_zero (Λ : SpecialSpecialComplexLorentzGroup) :
    Λ ∈ orbit_domain 0 0 :=
  fun i _ => Fin.elim0 i

lemma vector_bhw_diff_eq_of_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ)
    (h_const : ∀ (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ), E.H n α w = E.H n α 0)
    (w1 w2 : Fin n → Fin 4 → ℂ) (α : Fin n → ι) (x : Fin 6 → ℂ) :
    vector_bhw_diff R W E n w1 α x = vector_bhw_diff R W E n w2 α x := by
  unfold vector_bhw_diff
  simp_rw [h_const]

lemma local_nbhd_of_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ)
    (h_const : ∀ (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ), E.H n α w = E.H n α 0)
    (g1 : SL2C × SL2C) :
    ∀ᶠ Λ in 𝓝 (spinorPhi g1), ∃ x : Fin 6 → ℂ, Λ = spinorPhi (gcart x * g1) ∧
      ∀ α, vector_bhw_diff R W E n (spinorPhi g1 • tubeBasePoint n) α x = 0 := by
  have h_ev0 : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (tubeBasePoint n) α x = 0 :=
    Filter.eventually_all.mpr (fun α =>
      vector_bhw_diff_eq_zero_near_zero R W E h_cov n (tubeBasePoint n)
        (tubeBasePoint_mem_forward_tube_n n) α)
  have h_ev : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (spinorPhi g1 • tubeBasePoint n) α x = 0 := by
    apply Filter.Eventually.mono h_ev0
    intro x hx α
    rw [vector_bhw_diff_eq_of_const R W E n h_const _ (tubeBasePoint n)]
    exact hx α
  obtain ⟨U, hU, hUeq⟩ := eventually_iff_exists_mem.mp h_ev
  have h_img := local_chart_isOpenMap_at_zero U hU
  have h_mult : Tendsto (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)
      (𝓝 (spinorPhi g1)) (𝓝 1) := by
    have h0 := (continuous_mul_const (spinorPhi g1)⁻¹ : Continuous
      (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)).tendsto (spinorPhi g1)
    rwa [mul_inv_cancel] at h0
  filter_upwards [h_mult h_img] with Λ hΛ
  obtain ⟨x, hx, hxe⟩ := hΛ
  refine ⟨x, ?_, hUeq x hx⟩
  rw [map_mul, ← local_chart_eq, hxe, inv_mul_cancel_right]

lemma complex_covariance_of_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ)
    (h_const : ∀ (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ), E.H n α w = E.H n α 0)
    (A B : SL2C) (α : Fin n → ι) :
    E.H n α 0 = ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β 0 := by
  let z := tubeBasePoint n
  have hz_tube : z ∈ forward_tube_n n := tubeBasePoint_mem_forward_tube_n n
  let D := orbit_domain 0 0
  have hD_conn : IsConnected D := is_connected_orbit_domain 0 0 forward_tube_zero_mem
  have hD_open : IsOpen D := orbit_domain_isOpen 0 0
  let u : Set SpecialSpecialComplexLorentzGroup :=
    {Λ | Λ ∈ D ∧ ∃ g, spinorPhi g = Λ ∧ ∀ α, dd R W E n z g α = 0}
  let v : Set SpecialSpecialComplexLorentzGroup := D \ u
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ0 ⟨hΛ0D, g0, hg0, hd0⟩
    subst hg0
    have h_loc := local_nbhd_of_const R W E h_cov n h_const g0
    have h_D : D ∈ 𝓝 (spinorPhi g0) := hD_open.mem_nhds hΛ0D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, gcart x * g0, hΛx.symm, ?_⟩
    intro α'
    rw [dd_mul]
    have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g0 • z)) -
        ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g0 • z) =
        vector_bhw_diff R W E n (spinorPhi g0 • z) α' x := rfl
    rw [h1, hx0 α']
    simp [hd0]
  have hv_open : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ1 ⟨hΛ1D, hΛ1u⟩
    obtain ⟨g1, hg1⟩ := spinorPhi_surjective Λ1
    subst hg1
    have h_loc := local_nbhd_of_const R W E h_cov n h_const g1
    have h_D : D ∈ 𝓝 (spinorPhi g1) := hD_open.mem_nhds hΛ1D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, ?_⟩
    rintro ⟨_, g', hg', hd'⟩
    apply hΛ1u
    refine ⟨hΛ1D, g1, rfl, ?_⟩
    have hphi : spinorPhi (gcart x * g1) = spinorPhi g' := by rw [← hΛx, hg']
    have hzero : ∀ α', dd R W E n z (gcart x * g1) α' = 0 := by
      intro α'
      rw [dd_eq_of_phi_eq R W E h_cov n z hz_tube _ _ hphi.symm α']
      exact hd' α'
    have hzero' : ∀ α', ∑ β, Tm R n (gcart x) α' β * dd R W E n z g1 β = 0 := by
      intro α'
      have := hzero α'
      rw [dd_mul] at this
      have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g1 • z)) -
          ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g1 • z) =
          vector_bhw_diff R W E n (spinorPhi g1 • z) α' x := rfl
      rw [h1, hx0 α', zero_add] at this
      exact this
    exact Tm_injective R n (gcart x) _ hzero'
  have huv : Disjoint u v := by
    rw [Set.disjoint_iff]
    rintro Λ ⟨hu, hv⟩
    exact hv.2 hu
  have h_union : D ⊆ u ∪ v := by
    intro Λ hΛ
    by_cases h : Λ ∈ u
    · exact Or.inl h
    · exact Or.inr ⟨hΛ, h⟩
  have h_nonempty : (D ∩ u).Nonempty := by
    have h1 : (1 : SpecialSpecialComplexLorentzGroup) ∈ D := mem_orbit_domain_zero 1
    refine ⟨1, h1, h1, 1, map_one _, ?_⟩
    intro α'
    unfold dd
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [map_one, e]
    simp [Tm_one]
  have h_sub : D ⊆ u :=
    hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have hmem : spinorPhi (A, B) ∈ u := h_sub (mem_orbit_domain_zero (spinorPhi (A, B)))
  obtain ⟨_, g, hg, hd⟩ := hmem
  have h_dd := dd_eq_of_phi_eq R W E h_cov n z hz_tube g (A, B) hg α
  rw [hd α] at h_dd
  unfold dd Tm at h_dd
  have h_eq := sub_eq_zero.mp h_dd
  simp_rw [h_const] at h_eq
  exact h_eq

theorem vladimirov_H_zero_complexCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (A B : SL2C) (α : Fin n → ι) :
    vladimirov_H W n α 0 =
      ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * vladimirov_H W n β 0 :=
  complex_covariance_of_const R W
    (vladimirovTubeExtension R W hspec hP)
    (vladimirov_tubeCovariant R W hspec hP)
    n (vladimirov_H_eq_zero_eval hspec n) A B α

theorem vladimirov_H_complexCovariant_all (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (A B : SL2C) (z w : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    vladimirov_H W n α z =
      ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * vladimirov_H W n β w := by
  rw [vladimirov_H_eq_zero_eval hspec n α z]
  simp_rw [vladimirov_H_eq_zero_eval hspec n _ w]
  exact vladimirov_H_zero_complexCovariant R W hspec hP n A B α

def revIndexEquiv (n : ℕ) (ι : Type*) : (Fin n → ι) ≃ (Fin n → ι) where
  toFun β := β ∘ Fin.rev
  invFun β := β ∘ Fin.rev
  left_inv β := by ext i; simp [Fin.rev_rev]
  right_inv β := by ext i; simp [Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
lemma prod_rev_comp (n : ℕ) (M : ι → ι → ℂ) (α β : Fin n → ι) :
    (∏ i : Fin n, M (α (Fin.rev i)) (β (Fin.rev i))) = ∏ i : Fin n, M (α i) (β i) :=
  Equiv.prod_comp Fin.revPerm (fun i => M (α i) (β i))

omit [DecidableEq ι] in
lemma sum_prod_revIndex (n : ℕ) (M : ι → ι → ℂ) (F : (Fin n → ι) → ℂ) (α : Fin n → ι) :
    (∑ β : Fin n → ι, (∏ i : Fin n, M ((α ∘ Fin.rev) i) (β i)) * F β) =
      ∑ β : Fin n → ι, (∏ i : Fin n, M (α i) (β i)) * F (β ∘ Fin.rev) := by
  rw [← (revIndexEquiv n ι).sum_comp]
  apply Finset.sum_congr rfl
  intro β _
  change (∏ i : Fin n, M (α (Fin.rev i)) (β (Fin.rev i))) * F (β ∘ Fin.rev) =
    (∏ i : Fin n, M (α i) (β i)) * F (β ∘ Fin.rev)
  rw [prod_rev_comp n M α β]

theorem vladimirov_tube_pct_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    vladimirov_H W n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) * vladimirov_H W n (β ∘ Fin.rev) z := by
  have h_loc := vladimirov_tubeWeakLocality R W hspec hP hloc n α z hz
  change vladimirov_H W n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z at h_loc
  rw [h_loc,
      vladimirov_H_complexCovariant_all R W hspec hP n (-1) 1 z z (α ∘ Fin.rev),
      sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => vladimirov_H W n β z) α]

def WightmanPCT (η : ℂ) (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => -x (Fin.rev i)) = f x) →
    W n α f =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * W n (β ∘ Fin.rev) f'

theorem wightman_pct_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) :
    WightmanPCT η R W := by
  intro n α f f' hf'
  have h_pct_z := vladimirov_tube_pct_theorem R W hspec hP hloc n
    (tubeBasePoint n) (tubeBasePoint_mem_forward_tube_n n) α
  rw [vladimirov_H_eq_zero_eval hspec n α (-(tubeBasePoint n ∘ Fin.rev))] at h_pct_z
  simp_rw [vladimirov_H_eq_zero_eval hspec n _ (tubeBasePoint n)] at h_pct_z
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f]
  simp_rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n _ f']
  have h_int : (∫ x, f x) = ∫ x, f' x := by
    have h_f_eq : (fun x : Fin n → Fin 4 → ℝ => f x) =
        (fun x => f' (fun i => -x (Fin.rev i))) := by
      ext x
      exact (hf' x).symm
    rw [h_f_eq]
    exact integral_comp_pct n f'
  rw [h_pct_z, h_int, mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem weakLocality_of_wightman_pct (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W)
    (hpct : WightmanPCT η R W) :
    WeakLocality η W := by
  apply weakLocality_of_vladimirov_tubeWeakLocality R W hspec hP
  intro n α z _hz
  change vladimirov_H W n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z
  rw [vladimirov_H_eq_zero_eval hspec n α (-(z ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) z]
  let f := jostSchwartz n
  let f' := schwartzPCTCLM n f
  have hf'_pct : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => -x (Fin.rev i)) = f x := by
    intro x
    dsimp [f']
    congr 1
    ext i k
    simp [Fin.rev_rev]
  have hW := hpct n α f f' hf'_pct
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f] at hW
  simp_rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n _ f'] at hW
  have h_int_eq : (∫ x, f' x) = ∫ x, f x :=
    integral_comp_pct n f
  rw [h_int_eq] at hW
  have h_factor :
      (∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * (vladimirov_H W n (β ∘ Fin.rev) 0 * ∫ x, f x)) =
      (∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * vladimirov_H W n (β ∘ Fin.rev) 0) * ∫ x, f x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [h_factor, ← mul_assoc] at hW
  have h_cancel := mul_right_cancel₀ (integral_jostSchwartz_ne_zero n) hW
  have h_cov := vladimirov_H_zero_complexCovariant R W hspec hP n (-1) 1 (α ∘ Fin.rev)
  rw [sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => vladimirov_H W n β 0) α] at h_cov
  rw [h_cancel, ← h_cov]

theorem wightman_pct_iff_weakLocality (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : ZeroMomentumSpectrumCondition W) (hP : PoincareCovariant R W) :
    WeakLocality η W ↔ WightmanPCT η R W :=
  ⟨wightman_pct_theorem R W hspec hP, weakLocality_of_wightman_pct R W hspec hP⟩

lemma sigma_pt_mul_sigma_tp (R : HolomorphicLorentzRep ι) :
    R.σ (-1, 1) * R.σ (1, -1) = R.σ (-1, -1) := by
  rw [← map_mul]
  congr 1
  ext <;> simp

lemma sigma_tp_mul_sigma_pt (R : HolomorphicLorentzRep ι) :
    R.σ (1, -1) * R.σ (-1, 1) = R.σ (-1, -1) := by
  rw [← map_mul]
  congr 1
  ext <;> simp

theorem sigma_pt_mul_sigma_tp_eq_spinParity (R : HolomorphicLorentzRep ι) (ε : ℂ)
    (hε : R.HasSpinParity ε) :
    R.σ (-1, 1) * R.σ (1, -1) = ε • (1 : Matrix ι ι ℂ) := by
  rw [sigma_pt_mul_sigma_tp, hε.1]

theorem sigma_tp_mul_sigma_pt_eq_spinParity (R : HolomorphicLorentzRep ι) (ε : ℂ)
    (hε : R.HasSpinParity ε) :
    R.σ (1, -1) * R.σ (-1, 1) = ε • (1 : Matrix ι ι ℂ) := by
  rw [sigma_tp_mul_sigma_pt, hε.1]

lemma starStructure_intertwine_pt {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    S.C * R.σ (-1, 1) = (R.σ (1, -1)).map star * S.C := by
  have h := S.intertwine (-1) 1
  have h1 : sl2c_conj (1 : SL2C) = 1 := sl2c_conj_one
  have h2 : sl2c_conj (-1 : SL2C) = -1 := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
  rwa [h1, h2] at h

lemma two_mul_two_sub_one_div_two : 2 * (2 - 1) / 2 = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma tubeWeakLocality_two {W : WightmanFamily ι} {η : ℂ} {E : TubeExtension W}
    (h_tloc : TubeWeakLocality η E)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = η * E.H 2 (α ∘ Fin.rev) z := by
  have h := h_tloc 2 α z hz
  rwa [two_mul_two_sub_one_div_two, pow_one] at h

omit [Fintype ι] [DecidableEq ι] in
lemma weakLocality_two {W : WightmanFamily ι} {η : ℂ}
    (hloc : WeakLocality η W)
    (α : Fin 2 → ι) (f f' : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ)
    (hf_jost : tsupport (f : (Fin 2 → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n 2)
    (hf'_rev : ∀ x : Fin 2 → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W 2 α f = η * W 2 (α ∘ Fin.rev) f' := by
  have h := hloc 2 α f f' hf_jost hf'_rev
  rwa [two_mul_two_sub_one_div_two, pow_one] at h

def spacetimeFlatLinearEquiv (n : ℕ) :
    (Fin n → Fin 4 → ℝ) ≃ₗ[ℝ] (Fin (n * 4) → ℝ) where
  toFun x p := x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y i μ := y (finProdFinEquiv (i, μ))
  left_inv x := by
    ext i μ
    simp
  right_inv y := by
    ext p
    dsimp only
    rw [Prod.mk.eta, Equiv.apply_symm_apply]

noncomputable def spacetimeFlatCLE (n : ℕ) :
    (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin (n * 4) → ℝ) :=
  (spacetimeFlatLinearEquiv n).toContinuousLinearEquiv

@[simp]
lemma spacetimeFlatCLE_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) (p : Fin (n * 4)) :
    spacetimeFlatCLE n x p = x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 := rfl

@[simp]
lemma spacetimeFlatCLE_symm_apply (n : ℕ) (y : Fin (n * 4) → ℝ) (i : Fin n) (μ : Fin 4) :
    (spacetimeFlatCLE n).symm y i μ = y (finProdFinEquiv (i, μ)) := rfl

lemma norm_spacetimeFlatCLE (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    ‖spacetimeFlatCLE n x‖ = ‖x‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun p => ?_)
    exact (norm_le_pi_norm (x (finProdFinEquiv.symm p).1) (finProdFinEquiv.symm p).2).trans
      (norm_le_pi_norm x (finProdFinEquiv.symm p).1)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg (spacetimeFlatCLE n x))).mpr (fun i => ?_)
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg (spacetimeFlatCLE n x))).mpr (fun μ => ?_)
    have h_eq : x i μ = spacetimeFlatCLE n x (finProdFinEquiv (i, μ)) := by simp
    rw [h_eq]
    exact norm_le_pi_norm (spacetimeFlatCLE n x) (finProdFinEquiv (i, μ))

lemma norm_spacetimeFlatCLE_symm (n : ℕ) (y : Fin (n * 4) → ℝ) :
    ‖(spacetimeFlatCLE n).symm y‖ = ‖y‖ := by
  have h := norm_spacetimeFlatCLE n ((spacetimeFlatCLE n).symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

lemma measurePreserving_spacetimeFlatCLE (n : ℕ) :
    MeasurePreserving (spacetimeFlatCLE n) volume volume where
  measurable := (spacetimeFlatCLE n).continuous.measurable
  map_eq := by
    refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
    rw [MeasureTheory.Measure.map_apply (spacetimeFlatCLE n).continuous.measurable
        (MeasurableSet.univ_pi hs)]
    have h_pre : (spacetimeFlatCLE n) ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i : Fin n => Set.univ.pi
          (fun μ : Fin 4 => s (finProdFinEquiv (i, μ)))) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
        spacetimeFlatCLE_apply]
      constructor
      · intro h i μ
        simpa using h (finProdFinEquiv (i, μ))
      · intro h p
        have hp := h (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
        rwa [Prod.mk.eta, Equiv.apply_symm_apply] at hp
    rw [h_pre, MeasureTheory.volume_pi_pi]
    simp_rw [MeasureTheory.volume_pi_pi]
    rw [← Fintype.prod_prod_type (fun q : Fin n × Fin 4 => volume (s (finProdFinEquiv q)))]
    exact finProdFinEquiv.prod_comp (fun p => volume (s p))

lemma integral_comp_spacetimeFlatCLE (n : ℕ) (g : (Fin (n * 4) → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (spacetimeFlatCLE n x)) = ∫ y : Fin (n * 4) → ℝ, g y := by
  have h_mp := measurePreserving_spacetimeFlatCLE n
  have h_emb : MeasurableEmbedding (spacetimeFlatCLE n) :=
    (spacetimeFlatCLE n).toHomeomorph.isClosedEmbedding.measurableEmbedding
  exact h_mp.integral_comp h_emb g

def spacetimeFlatLinearEquivC (n : ℕ) :
    (Fin n → Fin 4 → ℂ) ≃ₗ[ℂ] (Fin (n * 4) → ℂ) where
  toFun z p := z (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w i μ := w (finProdFinEquiv (i, μ))
  left_inv z := by
    ext i μ
    simp
  right_inv w := by
    ext p
    dsimp only
    rw [Prod.mk.eta, Equiv.apply_symm_apply]

noncomputable def spacetimeFlatCLE_C (n : ℕ) :
    (Fin n → Fin 4 → ℂ) ≃L[ℂ] (Fin (n * 4) → ℂ) :=
  (spacetimeFlatLinearEquivC n).toContinuousLinearEquiv

@[simp]
lemma spacetimeFlatCLE_C_apply (n : ℕ) (z : Fin n → Fin 4 → ℂ) (p : Fin (n * 4)) :
    spacetimeFlatCLE_C n z p = z (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 := rfl

@[simp]
lemma spacetimeFlatCLE_C_symm_apply (n : ℕ) (w : Fin (n * 4) → ℂ) (i : Fin n) (μ : Fin 4) :
    (spacetimeFlatCLE_C n).symm w i μ = w (finProdFinEquiv (i, μ)) := rfl

lemma spacetimeFlatCLE_C_coeReal (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    spacetimeFlatCLE_C n (coeReal n x) = fun p => (spacetimeFlatCLE n x p : ℂ) := rfl

lemma spacetimeFlatCLE_C_symm_ofReal (n : ℕ) (u : Fin (n * 4) → ℝ) :
    (spacetimeFlatCLE_C n).symm (fun p => (u p : ℂ)) = coeReal n ((spacetimeFlatCLE n).symm u) :=
  rfl

def forwardTubeConeFlat (n : ℕ) : Set (Fin (n * 4) → ℝ) :=
  { y | ∀ (i : Fin n) (hi : i.val + 1 < n),
    (fun k => -((spacetimeFlatCLE n).symm y i k -
      (spacetimeFlatCLE n).symm y ⟨i.val + 1, hi⟩ k)) ∈ forward_light_cone }

lemma mem_tubeDomain_forwardTubeConeFlat_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spacetimeFlatCLE_C n z ∈ TubeDomain (forwardTubeConeFlat n) ↔
      z ∈ forward_tube_n n := by
  change (fun p => (spacetimeFlatCLE_C n z p).im) ∈ forwardTubeConeFlat n ↔
    z ∈ forward_tube_n n
  have h_im : ∀ i k,
      (spacetimeFlatCLE n).symm (fun p => (spacetimeFlatCLE_C n z p).im) i k = (z i k).im := by
    intro i k
    rw [spacetimeFlatCLE_symm_apply, spacetimeFlatCLE_C_apply, Equiv.symm_apply_apply]
  simp only [forwardTubeConeFlat, forward_tube_n, Set.mem_setOf_eq, Pi.sub_apply,
    Complex.sub_im, h_im]

lemma symm_mem_forward_tube_of_mem_tubeDomain (n : ℕ) {w : Fin (n * 4) → ℂ}
    (hw : w ∈ TubeDomain (forwardTubeConeFlat n)) :
    (spacetimeFlatCLE_C n).symm w ∈ forward_tube_n n := by
  rw [← mem_tubeDomain_forwardTubeConeFlat_iff n]
  simpa using hw

lemma mem_tubeDomain_neg_forwardTubeConeFlat_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spacetimeFlatCLE_C n z ∈
      TubeDomain ((fun y => -y) '' forwardTubeConeFlat n) ↔
      z ∈ backward_tube_n n := by
  rw [← neg_mem_forward_tube_n_iff n z, ← mem_tubeDomain_forwardTubeConeFlat_iff n (-z)]
  change (fun p => (spacetimeFlatCLE_C n z p).im) ∈ (fun y => -y) '' forwardTubeConeFlat n ↔
    (fun p => (spacetimeFlatCLE_C n (-z) p).im) ∈ forwardTubeConeFlat n
  have h_neg : (fun p => (spacetimeFlatCLE_C n (-z) p).im) =
      -(fun p => (spacetimeFlatCLE_C n z p).im) := by
    ext p
    simp
  rw [h_neg]
  constructor
  · rintro ⟨y, hy, hy_eq⟩
    have h1 : -(fun p => (spacetimeFlatCLE_C n z p).im) = y := by
      rw [← hy_eq, neg_neg]
    rwa [h1]
  · intro hy
    refine ⟨-(fun p => (spacetimeFlatCLE_C n z p).im), hy, ?_⟩
    simp

lemma symm_rev_mem_forward_tube_of_mem_neg_tubeDomain (n : ℕ) {w : Fin (n * 4) → ℂ}
    (hw : w ∈ TubeDomain ((fun y => -y) '' forwardTubeConeFlat n)) :
    (((spacetimeFlatCLE_C n).symm w) ∘ Fin.rev) ∈ forward_tube_n n := by
  have h_back : (spacetimeFlatCLE_C n).symm w ∈ backward_tube_n n := by
    rw [← mem_tubeDomain_neg_forwardTubeConeFlat_iff n]
    simpa using hw
  have h_neg : -((spacetimeFlatCLE_C n).symm w) ∈ forward_tube_n n :=
    (neg_mem_forward_tube_n_iff n _).mpr h_back
  have h_nr := neg_rev_mem_forward_tube_n n (-((spacetimeFlatCLE_C n).symm w)) h_neg
  have h_eq : -((-((spacetimeFlatCLE_C n).symm w)) ∘ Fin.rev) =
      (((spacetimeFlatCLE_C n).symm w) ∘ Fin.rev) := by
    ext i μ
    simp
  rwa [h_eq] at h_nr

lemma isOpen_forwardTubeConeFlat (n : ℕ) :
    IsOpen (forwardTubeConeFlat n) := by
  let emb : (Fin (n * 4) → ℝ) → (Fin n → Fin 4 → ℂ) :=
    fun y i k => Complex.I * (((spacetimeFlatCLE n).symm y i k : ℝ) : ℂ)
  have hemb_cont : Continuous emb := by
    refine continuous_pi (fun i => continuous_pi (fun k => ?_))
    exact continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_apply k).comp ((continuous_apply i).comp (spacetimeFlatCLE n).symm.continuous)))
  have h_eq : forwardTubeConeFlat n = emb ⁻¹' forward_tube_n n := by
    ext y
    have h_im : ∀ (i : Fin n) (hi : i.val + 1 < n) (k : Fin 4),
        -((Complex.I * (((spacetimeFlatCLE n).symm y i k : ℝ) : ℂ) -
          Complex.I * (((spacetimeFlatCLE n).symm y ⟨i.val + 1, hi⟩ k : ℝ) : ℂ)).im) =
        -((spacetimeFlatCLE n).symm y i k -
          (spacetimeFlatCLE n).symm y ⟨i.val + 1, hi⟩ k) := by
      intro i hi k
      simp [Complex.sub_im, Complex.mul_im]
    simp only [forwardTubeConeFlat, forward_tube_n, emb, Set.mem_setOf_eq, Set.mem_preimage,
      Pi.sub_apply, h_im]
  rw [h_eq]
  exact (forward_tube_n_isOpen n).preimage hemb_cont

lemma convex_forwardTubeConeFlat (n : ℕ) :
    Convex ℝ (forwardTubeConeFlat n) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab i hi
  have h_lin :
      (fun k => -((spacetimeFlatCLE n).symm (a • y₁ + b • y₂) i k -
        (spacetimeFlatCLE n).symm (a • y₁ + b • y₂) ⟨i.val + 1, hi⟩ k)) =
      a • (fun k => -((spacetimeFlatCLE n).symm y₁ i k -
        (spacetimeFlatCLE n).symm y₁ ⟨i.val + 1, hi⟩ k)) +
      b • (fun k => -((spacetimeFlatCLE n).symm y₂ i k -
        (spacetimeFlatCLE n).symm y₂ ⟨i.val + 1, hi⟩ k)) := by
    ext k
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_lin]
  exact forward_light_cone_convex (hy₁ i hi) (hy₂ i hi) ha hb hab

lemma smul_mem_forwardTubeConeFlat (n : ℕ) {t : ℝ} (ht : 0 < t)
    {y : Fin (n * 4) → ℝ} (hy : y ∈ forwardTubeConeFlat n) :
    t • y ∈ forwardTubeConeFlat n := by
  intro i hi
  have h_lin :
      (fun k => -((spacetimeFlatCLE n).symm (t • y) i k -
        (spacetimeFlatCLE n).symm (t • y) ⟨i.val + 1, hi⟩ k)) =
      t • (fun k => -((spacetimeFlatCLE n).symm y i k -
        (spacetimeFlatCLE n).symm y ⟨i.val + 1, hi⟩ k)) := by
    ext k
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h_lin]
  exact forward_light_cone_smul t ht _ (hy i hi)

noncomputable def tubeBaseImFlat (n : ℕ) : Fin (n * 4) → ℝ :=
  spacetimeFlatCLE n (fun i k => (i.val : ℝ) * unit_time_vector k)

lemma tubeBaseImFlat_mem_forwardTubeConeFlat (n : ℕ) :
    tubeBaseImFlat n ∈ forwardTubeConeFlat n := by
  have h_mem := (mem_tubeDomain_forwardTubeConeFlat_iff n (tubeBasePoint n)).mpr
    (tubeBasePoint_mem_forward_tube_n n)
  have h_eq : (fun p => (spacetimeFlatCLE_C n (tubeBasePoint n) p).im) = tubeBaseImFlat n := by
    ext p
    simp [tubeBaseImFlat, tubeBasePoint]
  rwa [← h_eq]

lemma zero_mem_closure_forwardTubeConeFlat (n : ℕ) :
    (0 : Fin (n * 4) → ℝ) ∈ closure (forwardTubeConeFlat n) := by
  have h_tend : Tendsto (fun t : ℝ => t • tubeBaseImFlat n) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t • tubeBaseImFlat n) (𝓝 0) (𝓝 ((0 : ℝ) • tubeBaseImFlat n)) :=
      (continuous_id.smul continuous_const).tendsto 0
    rw [zero_smul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto h_tend ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  exact smul_mem_forwardTubeConeFlat n ht (tubeBaseImFlat_mem_forwardTubeConeFlat n)

noncomputable def jostBallFlatOpens (n : ℕ) : TopologicalSpace.Opens (Fin (n * 4) → ℝ) :=
  ⟨Metric.ball (spacetimeFlatCLE n (jostCenter n)) (1 / 4), Metric.isOpen_ball⟩

lemma jostCenterFlat_mem_jostBallFlatOpens (n : ℕ) :
    spacetimeFlatCLE n (jostCenter n) ∈ jostBallFlatOpens n :=
  Metric.mem_ball_self (by norm_num)

lemma jostBallFlatOpens_nonempty (n : ℕ) :
    (jostBallFlatOpens n : Set (Fin (n * 4) → ℝ)).Nonempty :=
  ⟨spacetimeFlatCLE n (jostCenter n), jostCenterFlat_mem_jostBallFlatOpens n⟩

lemma symm_mem_jost_points_of_mem_jostBallFlat (n : ℕ) {u : Fin (n * 4) → ℝ}
    (hu : u ∈ jostBallFlatOpens n) :
    (spacetimeFlatCLE n).symm u ∈ jost_points_n n := by
  apply ball_jostCenter_subset_jost_points_n n
  rw [Metric.mem_ball, dist_eq_norm]
  have hu' : ‖u - spacetimeFlatCLE n (jostCenter n)‖ < 1 / 4 := by
    simpa [jostBallFlatOpens, Metric.mem_ball, dist_eq_norm] using hu
  have h_sub : (spacetimeFlatCLE n).symm u - jostCenter n =
      (spacetimeFlatCLE n).symm (u - spacetimeFlatCLE n (jostCenter n)) := by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  rw [h_sub, norm_spacetimeFlatCLE_symm]
  exact hu'

noncomputable def schwartzFlatCLM (n : ℕ) :
    SchwartzMap (Fin (n * 4) → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (spacetimeFlatCLE n)

@[simp]
lemma schwartzFlatCLM_apply (n : ℕ) (ψ : SchwartzMap (Fin (n * 4) → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzFlatCLM n ψ x = ψ (spacetimeFlatCLE n x) := rfl

noncomputable def wightmanFlatTD (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι) :
    TemperedDistribution (Fin (n * 4) → ℝ) ℂ :=
  (W n α).comp (schwartzFlatCLM n)

noncomputable def wightmanRevFlatTD (η : ℂ) (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι) :
    TemperedDistribution (Fin (n * 4) → ℝ) ℂ :=
  (η ^ (n * (n - 1) / 2)) •
    ((W n (α ∘ Fin.rev)).comp ((schwartzRevCLM n).comp (schwartzFlatCLM n)))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanFlatTD_apply (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (ψ : SchwartzMap (Fin (n * 4) → ℝ) ℂ) :
    wightmanFlatTD W n α ψ = W n α (schwartzFlatCLM n ψ) := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma wightmanRevFlatTD_apply (η : ℂ) (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (ψ : SchwartzMap (Fin (n * 4) → ℝ) ℂ) :
    wightmanRevFlatTD η W n α ψ =
      η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) (schwartzRevCLM n (schwartzFlatCLM n ψ)) := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem weakLocality_equalOn_jostBallFlat {η : ℂ} {W : WightmanFamily ι}
    (hloc : WeakLocality η W) (n : ℕ) (α : Fin n → ι) :
    Distribution.EqualOn (jostBallFlatOpens n)
      (Distribution.temperedToDistribution (jostBallFlatOpens n) (wightmanFlatTD W n α))
      (Distribution.temperedToDistribution (jostBallFlatOpens n) (wightmanRevFlatTD η W n α))
      (jostBallFlatOpens n) subset_rfl := by
  refine Distribution.equalOn_temperedToDistribution_of_schwartz_eq subset_rfl (fun ψ hψ => ?_)
  rw [wightmanFlatTD_apply, wightmanRevFlatTD_apply]
  refine hloc n α (schwartzFlatCLM n ψ) (schwartzRevCLM n (schwartzFlatCLM n ψ)) ?_ ?_
  · intro x hx
    have h_cl : IsClosed ((spacetimeFlatCLE n) ⁻¹' tsupport (fun u => ψ u)) :=
      (isClosed_tsupport _).preimage (spacetimeFlatCLE n).continuous
    have h_sub : Function.support (schwartzFlatCLM n ψ : (Fin n → Fin 4 → ℝ) → ℂ) ⊆
        (spacetimeFlatCLE n) ⁻¹' tsupport (fun u => ψ u) :=
      fun y hy => subset_tsupport (fun u => ψ u) hy
    have hu : spacetimeFlatCLE n x ∈ jostBallFlatOpens n :=
      hψ ((closure_minimal h_sub h_cl) hx)
    have h_symm := symm_mem_jost_points_of_mem_jostBallFlat n hu
    rwa [ContinuousLinearEquiv.symm_apply_apply] at h_symm
  · intro x
    simp only [schwartzRevCLM_apply]
    congr 1
    ext i μ
    simp [Fin.rev_rev]

noncomputable def tubeForwardFlat {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι) (w : Fin (n * 4) → ℂ) : ℂ :=
  E.H n α ((spacetimeFlatCLE_C n).symm w)

noncomputable def tubeBackwardRevFlat (η : ℂ) {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι) (w : Fin (n * 4) → ℂ) : ℂ :=
  η ^ (n * (n - 1) / 2) * E.H n (α ∘ Fin.rev) (((spacetimeFlatCLE_C n).symm w) ∘ Fin.rev)

omit [Fintype ι] [DecidableEq ι] in
lemma differentiableOn_tubeForwardFlat {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι) :
    DifferentiableOn ℂ (tubeForwardFlat E n α)
      (TubeDomain (forwardTubeConeFlat n)) := by
  have h_an : AnalyticOnNhd ℂ (tubeForwardFlat E n α)
      (TubeDomain (forwardTubeConeFlat n)) := by
    intro w hw
    have hw_tube : (spacetimeFlatCLE_C n).symm w ∈ forward_tube_n n :=
      symm_mem_forward_tube_of_mem_tubeDomain n hw
    have hH : AnalyticAt ℂ (E.H n α) ((spacetimeFlatCLE_C n).symm w) :=
      (E.analytic n α).analyticAt ((forward_tube_n_isOpen n).mem_nhds hw_tube)
    exact hH.comp ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
  exact h_an.differentiableOn

omit [Fintype ι] [DecidableEq ι] in
lemma differentiableOn_tubeBackwardRevFlat (η : ℂ) {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι) :
    DifferentiableOn ℂ (tubeBackwardRevFlat η E n α)
      (TubeDomain ((fun y => -y) '' forwardTubeConeFlat n)) := by
  let revCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun z => z ∘ Fin.rev
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let gCLM : (Fin (n * 4) → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    revCLM.comp (spacetimeFlatCLE_C n).symm.toContinuousLinearMap
  have h_an : AnalyticOnNhd ℂ (tubeBackwardRevFlat η E n α)
      (TubeDomain ((fun y => -y) '' forwardTubeConeFlat n)) := by
    intro w hw
    have hw_tube : gCLM w ∈ forward_tube_n n :=
      symm_rev_mem_forward_tube_of_mem_neg_tubeDomain n hw
    have hH : AnalyticAt ℂ (E.H n (α ∘ Fin.rev)) (gCLM w) :=
      (E.analytic n (α ∘ Fin.rev)).analyticAt ((forward_tube_n_isOpen n).mem_nhds hw_tube)
    exact analyticAt_const.mul (hH.comp (gCLM.analyticAt w))
  exact h_an.differentiableOn

omit [Fintype ι] [DecidableEq ι] in
lemma entire_W_eq_integral_of_hasCompactSupport {W : WightmanFamily ι} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (z : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) z)
    (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf_supp : HasCompactSupport (fun x => f x)) :
    W n α f = ∫ x : Fin n → Fin 4 → ℝ, E.H n α (coeReal n x) * f x := by
  let v := unit_time_vector
  have hv : v ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  let line : ℝ → (Fin n → Fin 4 → ℝ) → (Fin n → Fin 4 → ℂ) :=
    fun t x i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)
  have hH_cont : Continuous (E.H n α) :=
    continuous_iff_continuousAt.mpr (fun z => (h_entire n α z).continuousAt)
  have hline_cont : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) => line p.1 p.2) := by
    refine continuous_pi (fun i => continuous_pi (fun k => ?_))
    have h1 : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) => (p.2 i k : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply k).comp
        ((continuous_apply i).comp continuous_snd))
    have h2 : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) =>
        Complex.I * ((p.1 * (i : ℕ) * v k : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_fst.mul continuous_const).mul continuous_const))
    exact h1.add h2
  have h_norm_cont : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) => ‖E.H n α (line p.1 p.2)‖) :=
    continuous_norm.comp (hH_cont.comp hline_cont)
  let K : Set (Fin n → Fin 4 → ℝ) := tsupport (fun x => f x)
  have hS_comp : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hf_supp
  rcases hS_comp.bddAbove_image h_norm_cont.continuousOn with ⟨M₀, hM₀⟩
  let M : ℝ := max M₀ 0
  have hM_nonneg : 0 ≤ M := le_max_right M₀ 0
  have hM_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ‖E.H n α (line t x)‖ ≤ M := by
    intro t ht x hx
    exact (hM₀ ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left M₀ 0)
  have h_dom : Tendsto
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, E.H n α (line t x) * f x)
      (𝓝[>] 0)
      (𝓝 (∫ x : Fin n → Fin 4 → ℝ, E.H n α (coeReal n x) * f x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => M * ‖f x‖) ?_ ?_ (f.integrable.norm.const_mul M) ?_
    · refine Filter.Eventually.of_forall (fun t => ?_)
      have ht_cont : Continuous (fun x => line t x) :=
        hline_cont.comp (continuous_const.prodMk continuous_id)
      exact ((hH_cont.comp ht_cont).mul f.continuous).aestronglyMeasurable
    · have h_nhds : Metric.ball (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        Filter.inter_mem
          (nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one))
          self_mem_nhdsWithin
      filter_upwards [h_nhds] with t ⟨ht_ball, ht_pos⟩
      have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
        have ht_lt : |t| < 1 := by simpa [Real.dist_eq] using ht_ball
        have ht1 : t < 1 := (abs_lt.mp ht_lt).2
        exact ⟨le_of_lt ht_pos, le_of_lt ht1⟩
      refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ K
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM_bound t ht_Icc x hx) (norm_nonneg (f x))
      · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hfx]
    · refine Filter.Eventually.of_forall (fun x => ?_)
      have hx_cont : Continuous (fun t : ℝ => E.H n α (line t x) * f x) :=
        (hH_cont.comp (hline_cont.comp (continuous_id.prodMk continuous_const))).mul
          continuous_const
      have hx0 : E.H n α (line 0 x) * f x = E.H n α (coeReal n x) * f x := by
        congr 2
        ext i k
        simp [line, coeReal]
      rw [← hx0]
      exact (hx_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  have h_bdy := E.boundary n α f v hv
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique h_bdy h_dom

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_schwartzFlatCLM (n : ℕ) {ψ : SchwartzMap (Fin (n * 4) → ℝ) ℂ}
    (hψ : HasCompactSupport (fun u => ψ u)) :
    HasCompactSupport (fun x => schwartzFlatCLM n ψ x) :=
  hψ.comp_homeomorph (spacetimeFlatCLE n).toHomeomorph

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_schwartzRevCLM (n : ℕ) {f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ}
    (hf : HasCompactSupport (fun x => f x)) :
    HasCompactSupport (fun x => schwartzRevCLM n f x) :=
  hf.comp_homeomorph (revCLE n).toHomeomorph

omit [Fintype ι] [DecidableEq ι] in
lemma entire_hasBoundaryValue_forwardTubeFlat {W : WightmanFamily ι} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (z : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) z)
    (n : ℕ) (α : Fin n → ι) (Ω : TopologicalSpace.Opens (Fin (n * 4) → ℝ)) :
    Distribution.HasBoundaryValue Ω (tubeForwardFlat E n α) (forwardTubeConeFlat n)
      (Distribution.temperedToDistribution Ω (wightmanFlatTD W n α)) := by
  have hf_cont : Continuous (tubeForwardFlat E n α) := by
    have hH : Continuous (E.H n α) :=
      continuous_iff_continuousAt.mpr (fun z => (h_entire n α z).continuousAt)
    exact hH.comp (spacetimeFlatCLE_C n).symm.continuous
  have h_bv := Distribution.hasBoundaryValue_of_continuousOn Ω (forwardTubeConeFlat n)
    (tubeForwardFlat E n α) hf_cont.continuousOn
  have h_dist_eq : Distribution.ofLocallyIntegrableOn Ω
      (fun u => tubeForwardFlat E n α (fun p => (u p : ℂ))) =
      Distribution.temperedToDistribution Ω (wightmanFlatTD W n α) := by
    ext φ
    have hg_cont : ContinuousOn
        (fun u : Fin (n * 4) → ℝ => tubeForwardFlat E n α (fun p => (u p : ℂ))) Ω :=
      (hf_cont.comp (continuous_pi fun p =>
        Complex.continuous_ofReal.comp (continuous_apply p))).continuousOn
    rw [Distribution.ofLocallyIntegrableOn_apply
        (hg_cont.locallyIntegrableOn Ω.isOpen.measurableSet),
        Distribution.temperedToDistribution_apply, wightmanFlatTD_apply]
    let ψ := Distribution.testFunctionToSchwartzCLM Ω φ
    have hψ_supp : HasCompactSupport (fun u => ψ u) :=
      φ.hasCompactSupport'.comp_left Complex.ofReal_zero
    rw [entire_W_eq_integral_of_hasCompactSupport E h_entire n α (schwartzFlatCLM n ψ)
        (hasCompactSupport_schwartzFlatCLM n hψ_supp)]
    rw [← integral_comp_spacetimeFlatCLE n]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp [tubeForwardFlat, ψ]
    have h_symm :
        ((spacetimeFlatCLE_C n).symm fun p =>
          (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
          coeReal n x :=
      (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
    rw [h_symm]
  rwa [← h_dist_eq]

omit [Fintype ι] [DecidableEq ι] in
lemma entire_hasBoundaryValue_backwardRevFlat (η : ℂ) {W : WightmanFamily ι} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (z : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) z)
    (n : ℕ) (α : Fin n → ι) (Ω : TopologicalSpace.Opens (Fin (n * 4) → ℝ)) :
    Distribution.HasBoundaryValue Ω (tubeBackwardRevFlat η E n α)
      ((fun y => -y) '' forwardTubeConeFlat n)
      (Distribution.temperedToDistribution Ω (wightmanRevFlatTD η W n α)) := by
  have hf_cont : Continuous (tubeBackwardRevFlat η E n α) := by
    have hH : Continuous (E.H n (α ∘ Fin.rev)) :=
      continuous_iff_continuousAt.mpr (fun z => (h_entire n (α ∘ Fin.rev) z).continuousAt)
    have h_rev_cont : Continuous (fun z : Fin n → Fin 4 → ℂ => z ∘ Fin.rev) :=
      continuous_pi (fun i => continuous_apply (Fin.rev i))
    exact continuous_const.mul (hH.comp (h_rev_cont.comp (spacetimeFlatCLE_C n).symm.continuous))
  have h_bv := Distribution.hasBoundaryValue_of_continuousOn Ω
    ((fun y => -y) '' forwardTubeConeFlat n)
    (tubeBackwardRevFlat η E n α) hf_cont.continuousOn
  have h_dist_eq : Distribution.ofLocallyIntegrableOn Ω
      (fun u => tubeBackwardRevFlat η E n α (fun p => (u p : ℂ))) =
      Distribution.temperedToDistribution Ω (wightmanRevFlatTD η W n α) := by
    ext φ
    have hg_cont : ContinuousOn
        (fun u : Fin (n * 4) → ℝ => tubeBackwardRevFlat η E n α (fun p => (u p : ℂ))) Ω :=
      (hf_cont.comp (continuous_pi fun p =>
        Complex.continuous_ofReal.comp (continuous_apply p))).continuousOn
    rw [Distribution.ofLocallyIntegrableOn_apply
        (hg_cont.locallyIntegrableOn Ω.isOpen.measurableSet),
        Distribution.temperedToDistribution_apply, wightmanRevFlatTD_apply]
    let ψ := Distribution.testFunctionToSchwartzCLM Ω φ
    have hψ_supp : HasCompactSupport (fun u => ψ u) :=
      φ.hasCompactSupport'.comp_left Complex.ofReal_zero
    have hf_supp : HasCompactSupport (fun x => schwartzRevCLM n (schwartzFlatCLM n ψ) x) :=
      hasCompactSupport_schwartzRevCLM n (hasCompactSupport_schwartzFlatCLM n hψ_supp)
    rw [entire_W_eq_integral_of_hasCompactSupport E h_entire n (α ∘ Fin.rev)
        (schwartzRevCLM n (schwartzFlatCLM n ψ)) hf_supp]
    have h_rev_int := integral_comp_rev n (fun x : Fin n → Fin 4 → ℝ =>
      E.H n (α ∘ Fin.rev) (coeReal n x) * schwartzRevCLM n (schwartzFlatCLM n ψ) x)
    rw [← h_rev_int, ← MeasureTheory.integral_const_mul, ← integral_comp_spacetimeFlatCLE n]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp [tubeBackwardRevFlat, ψ]
    have h_symm :
        ((spacetimeFlatCLE_C n).symm fun p =>
          (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
          coeReal n x :=
      (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
    have h_coe_rev : (coeReal n x ∘ Fin.rev) = coeReal n (fun i => x (Fin.rev i)) := rfl
    have h_inv_x : (fun i : Fin n => x (Fin.rev (Fin.rev i))) = x := by
      ext i μ
      simp [Fin.rev_rev]
    rw [h_symm, h_coe_rev, h_inv_x, mul_assoc]
  rwa [← h_dist_eq]

omit [Fintype ι] [DecidableEq ι] in
theorem entire_H_rev_of_weakLocality {η : ℂ} {W : WightmanFamily ι} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (z : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) z)
    (hloc : WeakLocality η W)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) :
    E.H n α z = η ^ (n * (n - 1) / 2) * E.H n (α ∘ Fin.rev) (z ∘ Fin.rev) := by
  let revCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun w => w ∘ Fin.rev
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let gCLM : (Fin (n * 4) → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    revCLM.comp (spacetimeFlatCLE_C n).symm.toContinuousLinearMap
  have hf_plus_an : AnalyticOnNhd ℂ (tubeForwardFlat E n α) Set.univ := fun w _ =>
    (h_entire n α ((spacetimeFlatCLE_C n).symm w)).comp
      ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
  have hf_minus_an : AnalyticOnNhd ℂ (tubeBackwardRevFlat η E n α) Set.univ := fun w _ =>
    analyticAt_const.mul ((h_entire n (α ∘ Fin.rev) (gCLM w)).comp (gCLM.analyticAt w))
  have h_bdy_eq : ∀ u ∈ jostBallFlatOpens n,
      tubeForwardFlat E n α (fun p => (u p : ℂ)) =
        tubeBackwardRevFlat η E n α (fun p => (u p : ℂ)) :=
    Distribution.eqOn_boundary_of_hasBoundaryValue_equalOn subset_rfl rfl
      (zero_mem_closure_forwardTubeConeFlat n)
      (hf_plus_an.continuousOn.mono (fun _ _ => Set.mem_univ _))
      (hf_minus_an.continuousOn.mono (fun _ _ => Set.mem_univ _))
      (entire_hasBoundaryValue_forwardTubeFlat E h_entire n α (jostBallFlatOpens n))
      (entire_hasBoundaryValue_backwardRevFlat η E h_entire n α (jostBallFlatOpens n))
      (weakLocality_equalOn_jostBallFlat hloc n α)
  have h_all : EqOn (tubeForwardFlat E n α) (tubeBackwardRevFlat η E n α) Set.univ :=
    Distribution.analyticOnNhd_eqOn_of_real_open isOpen_univ isPreconnected_univ
      hf_plus_an hf_minus_an
      (jostBallFlatOpens n).isOpen (jostBallFlatOpens_nonempty n)
      (fun _ _ => Set.mem_univ _) h_bdy_eq
  have hz := h_all (Set.mem_univ (spacetimeFlatCLE_C n z))
  dsimp [tubeForwardFlat, tubeBackwardRevFlat] at hz
  rwa [ContinuousLinearEquiv.symm_apply_apply] at hz

lemma entire_vector_bhw_diff_analytic (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    AnalyticAt ℂ (vector_bhw_diff R W E n z α) 0 := by
  have h1 : AnalyticAt ℂ (fun x => E.H n α (local_chart x • z)) 0 :=
    local_chart_analytic n (E.H n α) z (h_entire n α z)
  have h2 : AnalyticAt ℂ (fun x => ∑ β : Fin n → ι,
      (∏ i, R.σ (sl2c_chart_invFun (local_chart_e x).1,
        sl2c_chart_invFun (local_chart_e x).2) (α i) (β i)) * E.H n β z) 0 := by
    apply fintype_sum_analyticAt
    intro β
    apply AnalyticAt.mul
    · apply fintype_prod_analyticAt
      intro i
      exact rep_sigma_analytic R (α i) (β i)
    · exact analyticAt_const
  exact AnalyticAt.sub h1 h2

lemma entire_sum_prod_S_eq_H (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    E.H n α z = ∑ β : Fin n → ι, (∏ i, R.σ (-1, -1) (α i) (β i)) * E.H n β z := by
  have hlhs : AnalyticOnNhd ℂ (E.H n α) Set.univ := fun w _ => h_entire n α w
  have hrhs : AnalyticOnNhd ℂ
      (fun w => ∑ β : Fin n → ι, (∏ i, R.σ (-1, -1) (α i) (β i)) * E.H n β w) Set.univ :=
    fun w _ => fintype_sum_analyticAt _ w (fun β => analyticAt_const.mul (h_entire n β w))
  let z₀ := tubeBasePoint n
  have hz₀ : z₀ ∈ forward_tube_n n := tubeBasePoint_mem_forward_tube_n n
  have h_ev : E.H n α =ᶠ[𝓝 z₀]
      fun w => ∑ β : Fin n → ι, (∏ i, R.σ (-1, -1) (α i) (β i)) * E.H n β w := by
    filter_upwards [(forward_tube_n_isOpen n).mem_nhds hz₀] with w hw
    exact sum_prod_S_eq_H R W E h_cov n w hw α
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs isPreconnected_univ
    (Set.mem_univ z₀) h_ev (Set.mem_univ z)

lemma entire_G_eq_G_neg (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) (A B : SL2C) :
    ∑ β : Fin n → ι, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β z =
      ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z := by
  have hlhs : AnalyticOnNhd ℂ
      (fun w => ∑ β : Fin n → ι, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β w) Set.univ :=
    fun w _ => fintype_sum_analyticAt _ w (fun β => analyticAt_const.mul (h_entire n β w))
  have hrhs : AnalyticOnNhd ℂ
      (fun w => ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β w) Set.univ :=
    fun w _ => fintype_sum_analyticAt _ w (fun β => analyticAt_const.mul (h_entire n β w))
  let z₀ := tubeBasePoint n
  have hz₀ : z₀ ∈ forward_tube_n n := tubeBasePoint_mem_forward_tube_n n
  have h_ev : (fun w => ∑ β : Fin n → ι, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β w) =ᶠ[𝓝 z₀]
      (fun w => ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β w) := by
    filter_upwards [(forward_tube_n_isOpen n).mem_nhds hz₀] with w hw
    exact G_eq_G_neg R W E h_cov n w hw α A B
  exact hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs isPreconnected_univ
    (Set.mem_univ z₀) h_ev (Set.mem_univ z)

lemma entire_dd_eq_of_phi_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (g g' : SL2C × SL2C) (h : spinorPhi g = spinorPhi g') (α : Fin n → ι) :
    dd R W E n z g' α = dd R W E n z g α := by
  have hk : spinorPhi (g⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hg' : g' = g * (g⁻¹ * g') := by simp
  rcases spinorPhi_eq_one_imp (g⁻¹ * g').1 (g⁻¹ * g').2 hk with h1 | h1
  · have h_id : g⁻¹ * g' = 1 := h1
    rw [h_id, mul_one] at hg'
    rw [← hg']
  · have h2 : g⁻¹ * g' = (-1, -1) := h1
    rw [h2] at hg'
    have h3 : g' = (-g.1, -g.2) := by
      rw [hg']
      refine Prod.ext ?_ ?_ <;> simp
    rw [h3]
    obtain ⟨A, B⟩ := g
    unfold dd Tm
    rw [Geometry.PolarDecomposition.spinorPhi_neg_neg A B,
        entire_G_eq_G_neg R W E h_entire h_cov n z α A B]

lemma entire_vector_bhw_diff_eq_zero_near_zero (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), vector_bhw_diff R W E n z α x = 0 := by
  let z₀ := tubeBasePoint n
  have hz₀ : z₀ ∈ forward_tube_n n := tubeBasePoint_mem_forward_tube_n n
  let my_ofReal6 : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℂ) :=
    ContinuousLinearMap.pi (fun i =>
      ContinuousLinearMap.comp Complex.ofRealCLM (ContinuousLinearMap.proj i))
  have h_cont_R : ContinuousAt
      (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z₀) 0 := by
    have h_comp : (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z₀) =
        (fun x => local_chart x • z₀) ∘ my_ofReal6 := rfl
    rw [h_comp]
    apply ContinuousAt.comp
    · exact local_chart_action_continuous n z₀
    · exact my_ofReal6.continuous.continuousAt
  have h_tube_nhds :
      ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, local_chart (fun i => (x i : ℂ)) • z₀ ∈ forward_tube_n n := by
    have h0 : (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z₀) 0 = z₀ := by
      have hz_zero : (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) = 0 := by ext i; simp
      dsimp only
      rw [hz_zero, local_chart_zero]
      exact one_smul _ z₀
    have hz_nhds : forward_tube_n n ∈
        𝓝 ((fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z₀) 0) := by
      rw [h0]
      exact (forward_tube_n_isOpen n).mem_nhds hz₀
    exact h_cont_R.preimage_mem_nhds hz_nhds
  have h_real_ev :
      ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, vector_bhw_diff R W E n z α (fun i => (x i : ℂ)) = 0 := by
    filter_upwards [h_tube_nhds] with x hx
    let x_c : Fin 6 → ℂ := fun i => (x i : ℂ)
    let Λ := local_chart x_c
    let smulCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun w => Λ • w
          map_add' := fun u v => by
            ext i μ
            change (Λ.val.val.mulVec (u i + v i)) μ =
              (Λ.val.val.mulVec (u i)) μ + (Λ.val.val.mulVec (v i)) μ
            rw [Matrix.mulVec_add, Pi.add_apply]
          map_smul' := fun c u => by
            ext i μ
            change (Λ.val.val.mulVec (c • u i)) μ = c * (Λ.val.val.mulVec (u i)) μ
            rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] }
    have hFx_an : AnalyticOnNhd ℂ (fun w => vector_bhw_diff R W E n w α x_c) Set.univ := by
      intro w _
      have h1 : AnalyticAt ℂ (fun u => E.H n α (smulCLM u)) w :=
        (h_entire n α (smulCLM w)).comp (smulCLM.analyticAt w)
      have h2 : AnalyticAt ℂ (fun u => ∑ β : Fin n → ι,
          (∏ i, R.σ (sl2c_chart_invFun (local_chart_e x_c).1,
            sl2c_chart_invFun (local_chart_e x_c).2) (α i) (β i)) * E.H n β u) w :=
        fintype_sum_analyticAt _ w (fun β => analyticAt_const.mul (h_entire n β w))
      exact h1.sub h2
    have hFx_ev : (fun w => vector_bhw_diff R W E n w α x_c) =ᶠ[𝓝 z₀] 0 := by
      have h_open_pre : IsOpen (smulCLM ⁻¹' forward_tube_n n) :=
        (forward_tube_n_isOpen n).preimage smulCLM.continuous
      have h_mem_nhds : (forward_tube_n n ∩ smulCLM ⁻¹' forward_tube_n n) ∈ 𝓝 z₀ :=
        Filter.inter_mem ((forward_tube_n_isOpen n).mem_nhds hz₀) (h_open_pre.mem_nhds hx)
      filter_upwards [h_mem_nhds] with w ⟨hw1, hw2⟩
      exact vector_bhw_diff_eq_zero_on_real R W E h_cov n w hw1 α x hw2
    exact hFx_an.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      isPreconnected_univ (Set.mem_univ z₀) hFx_ev (Set.mem_univ z)
  rcases Metric.eventually_nhds_iff_ball.mp h_real_ev with ⟨r₁, hr₁_pos, hr₁⟩
  rcases Metric.eventually_nhds_iff_ball.mp
    (entire_vector_bhw_diff_analytic R W E h_entire n z α).eventually_analyticAt
    with ⟨r₂, hr₂_pos, hr₂⟩
  let r : ℝ := min r₁ r₂
  have hr_pos : 0 < r := lt_min hr₁_pos hr₂_pos
  have h_an_ball : AnalyticOnNhd ℂ (vector_bhw_diff R W E n z α) (Metric.ball 0 r) :=
    fun w hw => hr₂ w (Metric.ball_subset_ball (min_le_right r₁ r₂) hw)
  have h_zero_ball : EqOn (vector_bhw_diff R W E n z α) 0 (Metric.ball 0 r) :=
    Distribution.analyticOnNhd_eqOn_zero_of_real_open
      Metric.isOpen_ball (convex_ball (0 : Fin 6 → ℂ) r).isPreconnected h_an_ball
      (U := Metric.ball (0 : Fin 6 → ℝ) r) Metric.isOpen_ball ⟨0, Metric.mem_ball_self hr_pos⟩
      (fun x hx => by
        rw [Metric.mem_ball, dist_zero_right] at hx ⊢
        have h_norm : ‖(fun i : Fin 6 => (x i : ℂ))‖ = ‖x‖ := by
          apply le_antisymm
          · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr (fun i => ?_)
            simpa using norm_le_pi_norm x i
          · refine (pi_norm_le_iff_of_nonneg
              (norm_nonneg (fun i : Fin 6 => (x i : ℂ)))).mpr (fun i => ?_)
            simpa using norm_le_pi_norm (fun j : Fin 6 => (x j : ℂ)) i
        rwa [h_norm])
      (fun x hx => hr₁ x (Metric.ball_subset_ball (min_le_left r₁ r₂) hx))
  filter_upwards [Metric.ball_mem_nhds 0 hr_pos] with w hw
  exact h_zero_ball hw

lemma entire_local_nbhd (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (g1 : SL2C × SL2C) :
    ∀ᶠ Λ in 𝓝 (spinorPhi g1), ∃ x : Fin 6 → ℂ, Λ = spinorPhi (gcart x * g1) ∧
      ∀ α, vector_bhw_diff R W E n (spinorPhi g1 • z) α x = 0 := by
  have h_ev : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (spinorPhi g1 • z) α x = 0 :=
    Filter.eventually_all.mpr (fun α =>
      entire_vector_bhw_diff_eq_zero_near_zero R W E h_entire h_cov n (spinorPhi g1 • z) α)
  obtain ⟨U, hU, hUeq⟩ := eventually_iff_exists_mem.mp h_ev
  have h_img := local_chart_isOpenMap_at_zero U hU
  have h_mult : Tendsto (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)
      (𝓝 (spinorPhi g1)) (𝓝 1) := by
    have h0 := (continuous_mul_const (spinorPhi g1)⁻¹ : Continuous
      (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)).tendsto (spinorPhi g1)
    rwa [mul_inv_cancel] at h0
  filter_upwards [h_mult h_img] with Λ hΛ
  obtain ⟨x, hx, hxe⟩ := hΛ
  refine ⟨x, ?_, hUeq x hx⟩
  rw [map_mul, ← local_chart_eq, hxe, inv_mul_cancel_right]

theorem entire_complexCovariant_all (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E)
    (n : ℕ) (A B : SL2C) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    E.H n α (spinorPhi (A, B) • z) =
      ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z := by
  let D := orbit_domain 0 0
  have hD_conn : IsConnected D := is_connected_orbit_domain 0 0 forward_tube_zero_mem
  have hD_open : IsOpen D := orbit_domain_isOpen 0 0
  let u : Set SpecialSpecialComplexLorentzGroup :=
    {Λ | Λ ∈ D ∧ ∃ g, spinorPhi g = Λ ∧ ∀ α', dd R W E n z g α' = 0}
  let v : Set SpecialSpecialComplexLorentzGroup := D \ u
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ0 ⟨hΛ0D, g0, hg0, hd0⟩
    subst hg0
    have h_loc := entire_local_nbhd R W E h_entire h_cov n z g0
    have h_D : D ∈ 𝓝 (spinorPhi g0) := hD_open.mem_nhds hΛ0D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, gcart x * g0, hΛx.symm, ?_⟩
    intro α'
    rw [dd_mul]
    have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g0 • z)) -
        ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g0 • z) =
        vector_bhw_diff R W E n (spinorPhi g0 • z) α' x := rfl
    rw [h1, hx0 α']
    simp [hd0]
  have hv_open : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ1 ⟨hΛ1D, hΛ1u⟩
    obtain ⟨g1, hg1⟩ := spinorPhi_surjective Λ1
    subst hg1
    have h_loc := entire_local_nbhd R W E h_entire h_cov n z g1
    have h_D : D ∈ 𝓝 (spinorPhi g1) := hD_open.mem_nhds hΛ1D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, ?_⟩
    rintro ⟨_, g', hg', hd'⟩
    apply hΛ1u
    refine ⟨hΛ1D, g1, rfl, ?_⟩
    have hphi : spinorPhi (gcart x * g1) = spinorPhi g' := by rw [← hΛx, hg']
    have hzero : ∀ α', dd R W E n z (gcart x * g1) α' = 0 := by
      intro α'
      rw [entire_dd_eq_of_phi_eq R W E h_entire h_cov n z _ _ hphi.symm α']
      exact hd' α'
    have hzero' : ∀ α', ∑ β, Tm R n (gcart x) α' β * dd R W E n z g1 β = 0 := by
      intro α'
      have h_mul := hzero α'
      rw [dd_mul] at h_mul
      have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g1 • z)) -
          ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g1 • z) =
          vector_bhw_diff R W E n (spinorPhi g1 • z) α' x := rfl
      rw [h1, hx0 α', zero_add] at h_mul
      exact h_mul
    exact Tm_injective R n (gcart x) _ hzero'
  have huv : Disjoint u v := by
    rw [Set.disjoint_iff]
    rintro Λ ⟨hu, hv⟩
    exact hv.2 hu
  have h_union : D ⊆ u ∪ v := by
    intro Λ hΛ
    by_cases h : Λ ∈ u
    · exact Or.inl h
    · exact Or.inr ⟨hΛ, h⟩
  have h_nonempty : (D ∩ u).Nonempty := by
    have h1 : (1 : SpecialSpecialComplexLorentzGroup) ∈ D := mem_orbit_domain_zero 1
    refine ⟨1, h1, h1, 1, map_one _, ?_⟩
    intro α'
    unfold dd
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [map_one, e]
    simp [Tm_one]
  have h_sub : D ⊆ u :=
    hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have hmem : spinorPhi (A, B) ∈ u := h_sub (mem_orbit_domain_zero (spinorPhi (A, B)))
  obtain ⟨_, g, hg, hd⟩ := hmem
  have h_dd := entire_dd_eq_of_phi_eq R W E h_entire h_cov n z g (A, B) hg α
  rw [hd α] at h_dd
  unfold dd Tm at h_dd
  exact sub_eq_zero.mp h_dd

lemma entire_H_neg_eq_sum_sigma_pt (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    E.H n α (-z) = ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n β z := by
  have h := entire_complexCovariant_all R W E h_entire h_cov n (-1) 1 z α
  rwa [spinorPhi_neg_one_one_smul] at h

lemma sigma_pt_mul_self (R : HolomorphicLorentzRep ι) :
    R.σ (-1, 1) * R.σ (-1, 1) = 1 := by
  rw [← map_mul]
  have h : ((-1 : SL2C), (1 : SL2C)) * ((-1 : SL2C), (1 : SL2C)) = 1 := by
    ext1 <;> simp
  rw [h, map_one]

lemma sum_prod_sigma_pt_involution (R : HolomorphicLorentzRep ι)
    (n : ℕ) (F : (Fin n → ι) → ℂ) (α : Fin n → ι) :
    (∑ β : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
      (∑ γ : Fin n → ι, (∏ i : Fin n, R.σ (-1, 1) (β i) (γ i)) * F γ)) = F α := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  have h_orth : ∀ γ : Fin n → ι,
      (∑ β : Fin n → ι,
        (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
        (∏ i : Fin n, R.σ (-1, 1) (β i) (γ i))) =
      if α = γ then 1 else 0 := by
    intro γ
    simp_rw [← Finset.prod_mul_distrib]
    have h_sum_prod := (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ι))
      (fun i b => R.σ (-1, 1) (α i) b * R.σ (-1, 1) b (γ i))).symm
    rw [Fintype.piFinset_univ] at h_sum_prod
    rw [h_sum_prod]
    have h_entry : ∀ i : Fin n,
        (∑ b : ι, R.σ (-1, 1) (α i) b * R.σ (-1, 1) b (γ i)) =
          (1 : Matrix ι ι ℂ) (α i) (γ i) := by
      intro i
      have h_sq := congrFun (congrFun (sigma_pt_mul_self R) (α i)) (γ i)
      simpa [Matrix.mul_apply] using h_sq
    simp_rw [h_entry]
    by_cases h : α = γ
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ γ i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
  have h_term : ∀ γ : Fin n → ι,
      (∑ β : Fin n → ι,
        (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) *
        (∏ i : Fin n, R.σ (-1, 1) (β i) (γ i)) * F γ) =
      (if α = γ then 1 else 0) * F γ := by
    intro γ
    rw [← Finset.sum_mul, h_orth γ]
  simp_rw [h_term]
  simp

theorem entire_H_rev_of_tube_pct (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E)
    (h_pct : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n →
      E.H n α (-(z ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) *
          ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n (β ∘ Fin.rev) z)
    (n : ℕ) (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ) :
    E.H n α w = η ^ (n * (n - 1) / 2) * E.H n (α ∘ Fin.rev) (w ∘ Fin.rev) := by
  let negRevCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun z => -(z ∘ Fin.rev)
        map_add' := fun x y => by ext i μ; simp [add_comm]
        map_smul' := fun c x => by ext i μ; simp }
  have hlhs : AnalyticOnNhd ℂ (fun z => E.H n α (negRevCLM z)) Set.univ := fun z _ =>
    (h_entire n α (negRevCLM z)).comp (negRevCLM.analyticAt z)
  have hrhs : AnalyticOnNhd ℂ
      (fun z => η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n (β ∘ Fin.rev) z) Set.univ :=
    fun z _ => analyticAt_const.mul
      (fintype_sum_analyticAt _ z (fun β => analyticAt_const.mul (h_entire n (β ∘ Fin.rev) z)))
  let z₀ := tubeBasePoint n
  have hz₀ : z₀ ∈ forward_tube_n n := tubeBasePoint_mem_forward_tube_n n
  have h_ev : (fun z => E.H n α (negRevCLM z)) =ᶠ[𝓝 z₀]
      (fun z => η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n (β ∘ Fin.rev) z) := by
    filter_upwards [(forward_tube_n_isOpen n).mem_nhds hz₀] with z hz
    exact h_pct n α z hz
  have h_all := hlhs.eqOn_of_preconnected_of_eventuallyEq hrhs isPreconnected_univ
    (Set.mem_univ z₀) h_ev (Set.mem_univ (-(w ∘ Fin.rev)))
  dsimp [negRevCLM] at h_all
  rw [neg_rev_involutive n w] at h_all
  rw [h_all]
  congr 1
  have h_expand : ∀ β : Fin n → ι,
      E.H n (β ∘ Fin.rev) (-(w ∘ Fin.rev)) =
        ∑ γ : Fin n → ι, (∏ i, R.σ (-1, 1) (β i) (γ i)) * E.H n (γ ∘ Fin.rev) (w ∘ Fin.rev) := by
    intro β
    rw [entire_H_neg_eq_sum_sigma_pt R W E h_entire h_cov n (w ∘ Fin.rev) (β ∘ Fin.rev),
        sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun γ => E.H n γ (w ∘ Fin.rev)) β]
  simp_rw [h_expand]
  exact sum_prod_sigma_pt_involution R n (fun γ => E.H n (γ ∘ Fin.rev) (w ∘ Fin.rev)) α

def TubePTScalar (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι} (E : TubeExtension W) :
    Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n →
    ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n β z = E.H n α z

lemma tubePTScalar_of_sigma_pt_eq_one (R : HolomorphicLorentzRep ι)
    (hσ : R.σ (-1, 1) = 1) {W : WightmanFamily ι} (E : TubeExtension W) :
    TubePTScalar R E := by
  intro n α z _hz
  rw [hσ]
  have h_prod : ∀ β : Fin n → ι,
      (∏ i : Fin n, (1 : Matrix ι ι ℂ) (α i) (β i)) = if α = β then 1 else 0 := by
    intro β
    by_cases h : α = β
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
  simp_rw [h_prod, ite_mul, one_mul, zero_mul]
  simp

lemma tubePTScalar_of_sigma_pt_eq_neg_one_fermion (R : HolomorphicLorentzRep ι)
    (hσ : R.σ (-1, 1) = (-1 : ℂ) • (1 : Matrix ι ι ℂ))
    (hε : R.HasSpinParity (-1))
    {W : WightmanFamily ι} (E : TubeExtension W) (h_cov : TubeCovariant R E) :
    TubePTScalar R E := by
  intro n α z hz
  have h_prod : ∀ β : Fin n → ι,
      (∏ i : Fin n, R.σ (-1, 1) (α i) (β i)) = if α = β then (-1 : ℂ) ^ n else 0 := by
    intro β
    rw [hσ]
    by_cases h : α = β
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply_ne hi])
  simp_rw [h_prod, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rcases Nat.even_or_odd n with hn | hn
  · rw [Even.neg_one_pow hn, one_mul]
  · rw [tube_eq_zero_of_odd_fermion R W E h_cov hε n hn z hz α, mul_zero]

lemma tubePTScalar_trivialRep {W : WightmanFamily Unit} (E : TubeExtension W) :
    TubePTScalar trivialRep E :=
  tubePTScalar_of_sigma_pt_eq_one trivialRep rfl E

lemma tubePTScalar_leftWeylRep {W : WightmanFamily (Fin 2)} (E : TubeExtension W)
    (h_cov : TubeCovariant leftWeylRep E) :
    TubePTScalar leftWeylRep E :=
  tubePTScalar_of_sigma_pt_eq_neg_one_fermion leftWeylRep
    (by
      change ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
        (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      simp [Matrix.SpecialLinearGroup.coe_neg])
    leftWeylRep_spinParity E h_cov

theorem analyticOnNhd_univ_eq_of_schwartz_integral_eq
    (n : ℕ) {G₁ G₂ : (Fin n → Fin 4 → ℂ) → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ Set.univ) (hG₂ : AnalyticOnNhd ℂ G₂ Set.univ)
    (h_int : ∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      (∫ x : Fin n → Fin 4 → ℝ, G₁ (coeReal n x) * f x) =
        ∫ x : Fin n → Fin 4 → ℝ, G₂ (coeReal n x) * f x)
    (z : Fin n → Fin 4 → ℂ) :
    G₁ z = G₂ z := by
  let F₁ : (Fin (n * 4) → ℂ) → ℂ := fun w => G₁ ((spacetimeFlatCLE_C n).symm w)
  let F₂ : (Fin (n * 4) → ℂ) → ℂ := fun w => G₂ ((spacetimeFlatCLE_C n).symm w)
  have hF₁_an : AnalyticOnNhd ℂ F₁ Set.univ := fun w _ =>
    (hG₁ _ (Set.mem_univ _)).comp ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
  have hF₂_an : AnalyticOnNhd ℂ F₂ Set.univ := fun w _ =>
    (hG₂ _ (Set.mem_univ _)).comp ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
  have hF₁_cont : Continuous F₁ :=
    continuous_iff_continuousAt.mpr (fun w => (hF₁_an w (Set.mem_univ w)).continuousAt)
  have hF₂_cont : Continuous F₂ :=
    continuous_iff_continuousAt.mpr (fun w => (hF₂_an w (Set.mem_univ w)).continuousAt)
  let g₁ : (Fin (n * 4) → ℝ) → ℂ := fun u => F₁ (fun p => (u p : ℂ))
  let g₂ : (Fin (n * 4) → ℝ) → ℂ := fun u => F₂ (fun p => (u p : ℂ))
  have hg₁_cont : Continuous g₁ :=
    hF₁_cont.comp (continuous_pi fun p => Complex.continuous_ofReal.comp (continuous_apply p))
  have hg₂_cont : Continuous g₂ :=
    hF₂_cont.comp (continuous_pi fun p => Complex.continuous_ofReal.comp (continuous_apply p))
  let Ω_top : TopologicalSpace.Opens (Fin (n * 4) → ℝ) := ⊤
  have hg₁_loc : LocallyIntegrableOn g₁ Ω_top volume :=
    hg₁_cont.continuousOn.locallyIntegrableOn Ω_top.isOpen.measurableSet
  have hg₂_loc : LocallyIntegrableOn g₂ Ω_top volume :=
    hg₂_cont.continuousOn.locallyIntegrableOn Ω_top.isOpen.measurableSet
  have h_eq_dist : Distribution.EqualOn Ω_top
      (Distribution.ofLocallyIntegrableOn Ω_top g₁)
      (Distribution.ofLocallyIntegrableOn Ω_top g₂) Ω_top subset_rfl := by
    intro φ _hφ
    rw [Distribution.ofLocallyIntegrableOn_apply hg₁_loc,
        Distribution.ofLocallyIntegrableOn_apply hg₂_loc,
        ← integral_comp_spacetimeFlatCLE n, ← integral_comp_spacetimeFlatCLE n]
    let f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
      schwartzFlatCLM n (Distribution.testFunctionToSchwartzCLM Ω_top φ)
    have h1 : (∫ x : Fin n → Fin 4 → ℝ,
        g₁ (spacetimeFlatCLE n x) * (φ (spacetimeFlatCLE n x) : ℂ)) =
        ∫ x : Fin n → Fin 4 → ℝ, G₁ (coeReal n x) * f x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp [g₁, F₁, f]
      have h_symm :
          ((spacetimeFlatCLE_C n).symm fun p =>
            (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
            coeReal n x :=
        (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
      rw [h_symm]
    have h2 : (∫ x : Fin n → Fin 4 → ℝ,
        g₂ (spacetimeFlatCLE n x) * (φ (spacetimeFlatCLE n x) : ℂ)) =
        ∫ x : Fin n → Fin 4 → ℝ, G₂ (coeReal n x) * f x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp [g₂, F₂, f]
      have h_symm :
          ((spacetimeFlatCLE_C n).symm fun p =>
            (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
            coeReal n x :=
        (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
      rw [h_symm]
    rw [h1, h2]
    exact h_int f
  have h_real_eq : EqOn g₁ g₂ (Ω_top : Set (Fin (n * 4) → ℝ)) :=
    Distribution.eqOn_of_equalOn_continuousOn subset_rfl
      hg₁_loc hg₂_loc hg₁_cont.continuousOn hg₂_cont.continuousOn h_eq_dist
  have h_all : EqOn F₁ F₂ Set.univ :=
    Distribution.analyticOnNhd_eqOn_of_real_open isOpen_univ isPreconnected_univ
      hF₁_an hF₂_an isOpen_univ ⟨0, Set.mem_univ 0⟩ (fun _ _ => Set.mem_univ _)
      (fun u _ => h_real_eq (Set.mem_univ u))
  have hz := h_all (Set.mem_univ (spacetimeFlatCLE_C n z))
  dsimp [F₁, F₂] at hz
  rwa [ContinuousLinearEquiv.symm_apply_apply] at hz

noncomputable def schwartzCutoffFun (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (k : ℕ) (x : Fin n → Fin 4 → ℝ) : ℂ :=
  vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • x) * f x

lemma schwartzCutoffFun_hasCompactSupport (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (k : ℕ) :
    HasCompactSupport (schwartzCutoffFun n f k) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk_ne : (k : ℝ) + 1 ≠ 0 := ne_of_gt hk_pos
  let e : (Fin n → Fin 4 → ℝ) ≃ₜ (Fin n → Fin 4 → ℝ) :=
    { toFun := fun x => (((k : ℝ) + 1)⁻¹) • x
      invFun := fun x => ((k : ℝ) + 1) • x
      left_inv := fun x => by dsimp; rw [smul_smul, mul_inv_cancel₀ hk_ne, one_smul]
      right_inv := fun x => by dsimp; rw [smul_smul, inv_mul_cancel₀ hk_ne, one_smul]
      continuous_toFun := (continuous_const (y := (((k : ℝ) + 1)⁻¹))).smul continuous_id
      continuous_invFun := (continuous_const (y := ((k : ℝ) + 1))).smul continuous_id }
  have h_bump : HasCompactSupport
      (fun x : Fin n → Fin 4 → ℝ => vladimirov_cutoff_bump_schwartz n x) :=
    ((vladimirovCutoffBump n 1 Real.zero_lt_one).hasCompactSupport).comp_left Complex.ofReal_zero
  have h_comp : HasCompactSupport
      (fun x : Fin n → Fin 4 → ℝ =>
        vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • x)) :=
    h_bump.comp_homeomorph e
  exact h_comp.mul_right

lemma schwartzCutoffFun_contDiff (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (schwartzCutoffFun n f k) := by
  have h_scale : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → Fin 4 → ℝ => (((k : ℝ) + 1)⁻¹) • x) :=
    (contDiff_const (c := (((k : ℝ) + 1)⁻¹))).smul contDiff_id
  exact ((vladimirov_cutoff_bump_schwartz n).smooth ⊤ |>.comp h_scale).mul (f.smooth ⊤)

noncomputable def schwartzCutoffSeq (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (k : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (schwartzCutoffFun_hasCompactSupport n f k).toSchwartzMap (schwartzCutoffFun_contDiff n f k)

@[simp]
lemma schwartzCutoffSeq_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (k : ℕ) (x : Fin n → Fin 4 → ℝ) :
    schwartzCutoffSeq n f k x =
      vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • x) * f x := rfl

lemma schwartzCutoffSeq_hasCompactSupport (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (k : ℕ) :
    HasCompactSupport (schwartzCutoffSeq n f k : (Fin n → Fin 4 → ℝ) → ℂ) :=
  schwartzCutoffFun_hasCompactSupport n f k

lemma norm_iteratedFDeriv_cutoffDiff_le (n : ℕ) (k i : ℕ) (x : Fin n → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i
      (fun y : Fin n → Fin 4 → ℝ =>
        vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • y) - 1) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) + 1 := by
  let r : ℝ := ((k : ℝ) + 1)⁻¹
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_le_one : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
  cases i with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have h_le := SchwartzMap.norm_le_seminorm ℝ (vladimirov_cutoff_bump_schwartz n) (r • x)
    calc ‖vladimirov_cutoff_bump_schwartz n (r • x) - 1‖
        ≤ ‖vladimirov_cutoff_bump_schwartz n (r • x)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖vladimirov_cutoff_bump_schwartz n (r • x)‖ + 1 := by simp
      _ ≤ SchwartzMap.seminorm ℝ 0 0 (vladimirov_cutoff_bump_schwartz n) + 1 := by linarith
  | succ j =>
    have h_smooth : ContDiff ℝ (j + 1 : ℕ)
        (vladimirov_cutoff_bump_schwartz n : (Fin n → Fin 4 → ℝ) → ℂ) :=
      ((vladimirov_cutoff_bump_schwartz n).smooth ⊤).of_le (WithTop.coe_le_coe.mpr le_top)
    have h_const : ContDiff ℝ (j + 1 : ℕ) (fun _ : Fin n → Fin 4 → ℝ => (1 : ℂ)) :=
      contDiff_const
    have h_comp_smooth : ContDiff ℝ (j + 1 : ℕ)
        (fun y : Fin n → Fin 4 → ℝ => vladimirov_cutoff_bump_schwartz n (r • y)) :=
      h_smooth.comp ((contDiff_const (c := r)).smul contDiff_id)
    change ‖iteratedFDeriv ℝ (j + 1)
      ((fun y : Fin n → Fin 4 → ℝ => vladimirov_cutoff_bump_schwartz n (r • y)) -
        fun _ => (1 : ℂ)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply h_comp_smooth.contDiffAt h_const.contDiffAt,
        iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j) (1 : ℂ), Pi.zero_apply, sub_zero]
    have h_scale := congrFun (iteratedFDeriv_comp_const_smul r h_smooth) x
    rw [h_scale, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hr_nonneg]
    have h_pow : r ^ (j + 1) ≤ 1 := pow_le_one₀ hr_nonneg hr_le_one
    have h_sem := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ
      (vladimirov_cutoff_bump_schwartz n) (j + 1) (r • x)
    have h_prod :
        r ^ (j + 1) * ‖iteratedFDeriv ℝ (j + 1) (vladimirov_cutoff_bump_schwartz n) (r • x)‖ ≤
          1 * SchwartzMap.seminorm ℝ 0 (j + 1) (vladimirov_cutoff_bump_schwartz n) :=
      mul_le_mul h_pow h_sem (norm_nonneg _) zero_le_one
    linarith

theorem schwartzCutoffSeq_tendsto (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    Tendsto (schwartzCutoffSeq n f) Filter.atTop (𝓝 f) := by
  have h_sub : Tendsto (fun k => schwartzCutoffSeq n f k - f) Filter.atTop (𝓝 0) := by
    rw [(schwartz_withSeminorms ℝ (Fin n → Fin 4 → ℝ) ℂ).tendsto_nhds _ 0]
    rintro ⟨l, m⟩ ε hε
    let C : ℝ := ∑ i ∈ Finset.range (m + 1),
      (m.choose i : ℝ) *
        (SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) + 1) *
        SchwartzMap.seminorm ℝ (l + 1) (m - i) f
    have hC_nonneg : 0 ≤ C := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (add_nonneg (apply_nonneg _ _) zero_le_one))
        (apply_nonneg _ _)
    have h_bound_k : ∀ k : ℕ,
        SchwartzMap.seminorm ℝ l m (schwartzCutoffSeq n f k - f) ≤
          C * (((k : ℝ) + 1)⁻¹) := by
      intro k
      have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      refine SchwartzMap.seminorm_le_bound ℝ l m (schwartzCutoffSeq n f k - f)
        (mul_nonneg hC_nonneg (inv_nonneg.mpr hk_pos.le)) (fun x => ?_)
      by_cases hx : ‖x‖ < (k : ℝ) + 1
      · have h_ev :
            ((schwartzCutoffSeq n f k - f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
              (Fin n → Fin 4 → ℝ) → ℂ) =ᶠ[𝓝 x]
              (fun _ => (0 : ℂ)) := by
          filter_upwards [Metric.isOpen_ball.mem_nhds
            (show x ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) ((k : ℝ) + 1) by
              simpa [Metric.mem_ball, dist_zero_right] using hx)] with y hy
          rw [Metric.mem_ball, dist_zero_right] at hy
          have hy_ball : (((k : ℝ) + 1)⁻¹) • y ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) 1 := by
            rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
                abs_of_pos (inv_pos.mpr hk_pos), inv_mul_lt_iff₀ hk_pos, mul_one]
            exact hy
          have h_one : vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • y) = 1 := by
            change ((vladimirovCutoffBump n 1 Real.zero_lt_one
              ((((k : ℝ) + 1)⁻¹) • y) : ℝ) : ℂ) = 1
            rw [vladimirov_cutoff_bump_one_of_mem_ball_gen n 1 le_rfl _ hy_ball]
            simp
          change schwartzCutoffSeq n f k y - f y = 0
          rw [schwartzCutoffSeq_apply, h_one, one_mul, sub_self]
        rw [(Filter.EventuallyEq.iteratedFDeriv ℝ h_ev m).eq_of_nhds,
            iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
        exact mul_nonneg hC_nonneg (inv_nonneg.mpr hk_pos.le)
      · push Not at hx
        let g : (Fin n → Fin 4 → ℝ) → ℂ :=
          fun y => vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • y) - 1
        have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
          have h_scale : ContDiff ℝ (⊤ : ℕ∞)
              (fun y : Fin n → Fin 4 → ℝ => (((k : ℝ) + 1)⁻¹) • y) :=
            (contDiff_const (c := (((k : ℝ) + 1)⁻¹))).smul contDiff_id
          exact ((vladimirov_cutoff_bump_schwartz n).smooth ⊤ |>.comp h_scale).sub contDiff_const
        have h_fn_eq :
            ((schwartzCutoffSeq n f k - f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
              (Fin n → Fin 4 → ℝ) → ℂ) =
            fun y => g y * f y := by
          ext y
          change vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • y) * f y - f y =
            (vladimirov_cutoff_bump_schwartz n ((((k : ℝ) + 1)⁻¹) • y) - 1) * f y
          ring
        rw [h_fn_eq]
        have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
          (f := g) (g := (f : (Fin n → Fin 4 → ℝ) → ℂ)) (n := m) (N := (⊤ : ℕ∞))
          hg_smooth (f.smooth ⊤) x (WithTop.coe_le_coe.mpr le_top)
        have h_norm_pow : ‖x‖ ^ l ≤ (((k : ℝ) + 1)⁻¹) * ‖x‖ ^ (l + 1) := by
          rw [le_inv_mul_iff₀ hk_pos]
          have h_mul : ((k : ℝ) + 1) * ‖x‖ ^ l ≤ ‖x‖ * ‖x‖ ^ l :=
            mul_le_mul_of_nonneg_right hx (pow_nonneg (norm_nonneg x) l)
          rwa [pow_succ']
        calc ‖x‖ ^ l * ‖iteratedFDeriv ℝ m (fun y => g y * f y) x‖
            ≤ ((((k : ℝ) + 1)⁻¹) * ‖x‖ ^ (l + 1)) *
                ∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
                    ‖iteratedFDeriv ℝ (m - i) (f : (Fin n → Fin 4 → ℝ) → ℂ) x‖ :=
              mul_le_mul h_norm_pow h_leib (norm_nonneg _)
                (mul_nonneg (inv_nonneg.mpr hk_pos.le) (pow_nonneg (norm_nonneg x) (l + 1)))
          _ = (((k : ℝ) + 1)⁻¹) *
                ∑ i ∈ Finset.range (m + 1),
                  (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ *
                    (‖x‖ ^ (l + 1) *
                      ‖iteratedFDeriv ℝ (m - i) (f : (Fin n → Fin 4 → ℝ) → ℂ) x‖) := by
              rw [mul_assoc, Finset.mul_sum]
              congr 1
              refine Finset.sum_congr rfl (fun i _ => by ring)
          _ ≤ (((k : ℝ) + 1)⁻¹) * C := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => ?_))
                (inv_nonneg.mpr hk_pos.le)
              have h_gi := norm_iteratedFDeriv_cutoffDiff_le n k i x
              have h_fi := SchwartzMap.le_seminorm ℝ (l + 1) (m - i) f x
              have h1 : (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ ≤
                  (m.choose i : ℝ) *
                    (SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) + 1) :=
                mul_le_mul_of_nonneg_left h_gi (Nat.cast_nonneg _)
              exact mul_le_mul h1 h_fi
                (mul_nonneg (pow_nonneg (norm_nonneg x) (l + 1)) (norm_nonneg _))
                (mul_nonneg (Nat.cast_nonneg _)
                  (add_nonneg (apply_nonneg _ _) zero_le_one))
          _ = C * (((k : ℝ) + 1)⁻¹) := mul_comm _ _
    have h_lim : Tendsto (fun k : ℕ => C * (((k : ℝ) + 1)⁻¹)) Filter.atTop (𝓝 0) := by
      have h_inv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      simpa [mul_zero] using (tendsto_const_nhds (x := C)).mul h_inv
    filter_upwards [(tendsto_order.mp h_lim).2 ε hε] with k hk
    rw [SchwartzMap.schwartzSeminormFamily_apply, sub_zero]
    exact (h_bound_k k).trans_lt hk
  simpa using h_sub.add (tendsto_const_nhds (x := f))

lemma sl2c_isUnit (A : SL2C) : IsUnit A.1 := by
  rw [Matrix.isUnit_iff_isUnit_det, A.2]
  exact isUnit_one

lemma vec_to_spinor_lorentzOfSL2C_coe (A : SL2C) (v : Fin 4 → ℝ) :
    vec_to_spinor (fun μ => ((lorentzOfSL2C A).mulVec v μ : ℂ)) =
      A.1 * vec_to_spinor (fun μ => (v μ : ℂ)) * star A.1 := by
  rw [lorentzOfSL2C_mulVec_coe A v]
  have h_act : spinorPhi (A, sl2c_conj A) • (fun μ => (v μ : ℂ)) =
      spinor_action A.1 (sl2c_conj A).1 (fun μ => (v μ : ℂ)) :=
    spinorPhi_matrix_mulVec A (sl2c_conj A) (fun μ => (v μ : ℂ))
  rw [h_act]
  dsimp [spinor_action]
  rw [vec_to_spinor_right_inv]
  have h_conj : (sl2c_conj A).1ᵀ = star A.1 := by
    ext i j
    simp [sl2c_conj]
  rw [h_conj]

lemma spinorPhi_real_im_eq (A : SL2C) (w : Fin 4 → ℂ) :
    (fun μ => ((spinorPhi (A, sl2c_conj A) • w) μ).im) =
      (lorentzOfSL2C A).mulVec (fun μ => (w μ).im) := by
  ext μ
  have h_map := (lorentzOfSL2C_map A).symm
  change (((spinorPhi (A, sl2c_conj A)).val.val.mulVec w) μ).im =
    ((lorentzOfSL2C A).mulVec (fun ν => (w ν).im)) μ
  rw [h_map]
  simp [Matrix.mulVec, dotProduct, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

theorem spinorPhi_real_preserves_forward_tube_n (n : ℕ) (A : SL2C)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    spinorPhi (A, sl2c_conj A) • z ∈ forward_tube_n n := by
  intro i hi
  have h_im :
      (fun μ =>
        -(((spinorPhi (A, sl2c_conj A) • z) i -
          (spinorPhi (A, sl2c_conj A) • z) ⟨i.val + 1, hi⟩) μ).im) =
      (lorentzOfSL2C A).mulVec
        (fun μ => -((z i - z ⟨i.val + 1, hi⟩) μ).im) := by
    ext μ
    have h1 := congrFun (spinorPhi_real_im_eq A (z i)) μ
    have h2 := congrFun (spinorPhi_real_im_eq A (z ⟨i.val + 1, hi⟩)) μ
    simp only [Pi.sub_apply, Complex.sub_im]
    change -(((spinorPhi (A, sl2c_conj A) • z i) μ).im -
        ((spinorPhi (A, sl2c_conj A) • z ⟨i.val + 1, hi⟩) μ).im) =
      ((lorentzOfSL2C A).mulVec (fun ν => -((z i ν).im - (z ⟨i.val + 1, hi⟩ ν).im))) μ
    rw [h1, h2]
    simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
  change (fun k =>
      -(((spinorPhi (A, sl2c_conj A) • z) i -
        (spinorPhi (A, sl2c_conj A) • z) ⟨i.val + 1, hi⟩) k).im) ∈
    forward_light_cone
  rw [h_im]
  exact lorentzOfSL2C_preserves_forward_light_cone A (hz i hi)

theorem spinorPhi_real_mem_forward_tube_n_iff (n : ℕ) (A : SL2C)
    (z : Fin n → Fin 4 → ℂ) :
    spinorPhi (A, sl2c_conj A) • z ∈ forward_tube_n n ↔ z ∈ forward_tube_n n := by
  constructor
  · intro hAz
    have h_inv := spinorPhi_real_preserves_forward_tube_n n A⁻¹ hAz
    have h_conj_inv : sl2c_conj A⁻¹ = (sl2c_conj A)⁻¹ := map_inv sl2cConjHom A
    have h_inv_phi : spinorPhi (A⁻¹, sl2c_conj A⁻¹) = (spinorPhi (A, sl2c_conj A))⁻¹ := by
      rw [h_conj_inv]
      exact map_inv spinorPhi (A, sl2c_conj A)
    have h_smul : spinorPhi (A⁻¹, sl2c_conj A⁻¹) • (spinorPhi (A, sl2c_conj A) • z) = z := by
      rw [h_inv_phi]
      exact inv_smul_smul (spinorPhi (A, sl2c_conj A)) z
    rwa [h_smul] at h_inv
  · exact spinorPhi_real_preserves_forward_tube_n n A

lemma tubeCovariant_apply (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (α : Fin n → ι) :
    E.H n α (spinorPhi (A, sl2c_conj A) • z) =
      ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * E.H n β z :=
  h_cov n A z hz (spinorPhi_real_preserves_forward_tube_n n A hz) α

lemma wightman_lorentz_cov_of_tubeCovariant_compactSupport
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (A : SL2C)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf_supp : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ))
    (α : Fin n → ι) :
    W n α (schwartzLorentzCLM n A⁻¹ f) =
      ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * W n β f := by
  let v₀ : Fin 4 → ℝ := unit_time_vector
  have hv₀ : v₀ ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  let v' : Fin 4 → ℝ := (lorentzOfSL2C A).mulVec v₀
  have hv' : v' ∈ forward_light_cone := lorentzOfSL2C_preserves_forward_light_cone A hv₀
  have hb_lhs := E.boundary n α (schwartzLorentzCLM n A⁻¹ f) v' hv'
  have hb_rhs : Tendsto
      (fun t : ℝ => ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) *
        ∫ x : Fin n → Fin 4 → ℝ,
          E.H n β (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v₀ k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0)
      (𝓝 (∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * W n β f)) :=
    tendsto_finsetSum Finset.univ
      (fun β _ => (E.boundary n β f v₀ hv₀).const_mul (∏ i, R.rep A (α i) (β i)))
  have h_ev :
      (fun t : ℝ => ∫ y : Fin n → Fin 4 → ℝ,
        E.H n α (fun i k => (y i k : ℂ) + Complex.I * ((t * (i : ℕ) * v' k : ℝ) : ℂ)) *
          schwartzLorentzCLM n A⁻¹ f y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) *
        ∫ x : Fin n → Fin 4 → ℝ,
          E.H n β (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v₀ k : ℝ) : ℂ)) * f x) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    let line₀ : (Fin n → Fin 4 → ℝ) → (Fin n → Fin 4 → ℂ) :=
      fun x i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v₀ k : ℝ) : ℂ)
    have h_line₀_cont : Continuous line₀ := by
      refine continuous_pi (fun i => continuous_pi (fun k => ?_))
      exact (Complex.continuous_ofReal.comp ((continuous_apply k).comp (continuous_apply i))).add
        continuous_const
    have h_line₀_mem : ∀ x, line₀ x ∈ forward_tube_n n :=
      fun x => line_mem_forward_tube n x v₀ hv₀ t ht
    have h_int_β : ∀ β : Fin n → ι,
        Integrable (fun x : Fin n → Fin 4 → ℝ => E.H n β (line₀ x) * f x) volume := by
      intro β
      have h_cont : Continuous (fun x : Fin n → Fin 4 → ℝ => E.H n β (line₀ x) * f x) := by
        refine (continuous_iff_continuousAt.mpr (fun x => ?_)).mul f.continuous
        exact ((E.analytic n β).continuousOn.continuousAt
          ((forward_tube_n_isOpen n).mem_nhds (h_line₀_mem x))).comp h_line₀_cont.continuousAt
      exact h_cont.integrable_of_hasCompactSupport hf_supp.mul_left
    have h_mp := measurePreserving_lorentzEquiv_n n A
    have h_emb := (lorentzEquiv n A).toHomeomorph.measurableEmbedding
    rw [← h_mp.integral_comp h_emb
      (fun y : Fin n → Fin 4 → ℝ =>
        E.H n α (fun i k => (y i k : ℂ) + Complex.I * ((t * (i : ℕ) * v' k : ℝ) : ℂ)) *
          schwartzLorentzCLM n A⁻¹ f y)]
    simp_rw [← MeasureTheory.integral_const_mul]
    rw [← integral_finsetSum Finset.univ
      (fun β _ => (h_int_β β).const_mul (∏ i, R.rep A (α i) (β i)))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only [Function.comp_def]
    have h_line_eq :
        (fun i k => ((lorentzEquiv n A x) i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * v' k : ℝ) : ℂ)) =
        spinorPhi (A, sl2c_conj A) • line₀ x := by
      ext i k
      have h_re := congrFun (lorentzOfSL2C_mulVec_coe A (x i)) k
      have h_im := congrFun (lorentzOfSL2C_mulVec_coe A v₀) k
      change (((lorentzOfSL2C A).mulVec (x i) k : ℂ) +
          Complex.I * ((t * (i : ℕ) * v' k : ℝ) : ℂ)) =
        ((spinorPhi (A, sl2c_conj A)).val.val.mulVec (line₀ x i)) k
      have h_lin :
          line₀ x i =
            (fun μ => (x i μ : ℂ)) +
              (Complex.I * ((t * (i : ℕ) : ℝ) : ℂ)) • (fun μ => (v₀ μ : ℂ)) := by
        ext μ
        dsimp [line₀]
        push_cast
        ring
      rw [h_lin, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply]
      change (((lorentzOfSL2C A).mulVec (x i) k : ℂ) +
          Complex.I * ((t * (i : ℕ) * v' k : ℝ) : ℂ)) =
        (spinorPhi (A, sl2c_conj A) • (fun μ => (x i μ : ℂ))) k +
          (Complex.I * ((t * (i : ℕ) : ℝ) : ℂ)) *
            (spinorPhi (A, sl2c_conj A) • (fun μ => (v₀ μ : ℂ))) k
      rw [← h_re, ← h_im]
      dsimp [v']
      push_cast
      ring
    have h_rel : schwartzLorentzCLM n A⁻¹ f (lorentzEquiv n A x) = f x :=
      schwartzLorentz_rel n A f x
    rw [h_line_eq, h_rel, tubeCovariant_apply R E h_cov n A (line₀ x) (h_line₀_mem x) α,
        Finset.sum_mul]
    refine Finset.sum_congr rfl (fun β _ => mul_assoc _ _ _)
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique (hb_lhs.congr' h_ev) hb_rhs

theorem wightman_lorentz_cov_of_tubeCovariant
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (A : SL2C)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (α : Fin n → ι) :
    W n α (schwartzLorentzCLM n A⁻¹ f) =
      ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * W n β f := by
  have h_seq := schwartzCutoffSeq_tendsto n f
  have h_lhs : Tendsto
      (fun k : ℕ => W n α (schwartzLorentzCLM n A⁻¹ (schwartzCutoffSeq n f k)))
      Filter.atTop
      (𝓝 (W n α (schwartzLorentzCLM n A⁻¹ f))) :=
    ((W n α).continuous.tendsto _).comp
      ((schwartzLorentzCLM n A⁻¹).continuous.tendsto f |>.comp h_seq)
  have h_rhs : Tendsto
      (fun k : ℕ => ∑ β : Fin n → ι,
        (∏ i, R.rep A (α i) (β i)) * W n β (schwartzCutoffSeq n f k))
      Filter.atTop
      (𝓝 (∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * W n β f)) :=
    tendsto_finsetSum Finset.univ
      (fun β _ => (((W n β).continuous.tendsto f).comp h_seq).const_mul (∏ i, R.rep A (α i) (β i)))
  have h_eq :
      (fun k : ℕ => W n α (schwartzLorentzCLM n A⁻¹ (schwartzCutoffSeq n f k))) =
      (fun k : ℕ => ∑ β : Fin n → ι,
        (∏ i, R.rep A (α i) (β i)) * W n β (schwartzCutoffSeq n f k)) := by
    ext k
    exact wightman_lorentz_cov_of_tubeCovariant_compactSupport R W E h_cov n A
      (schwartzCutoffSeq n f k) (schwartzCutoffSeq_hasCompactSupport n f k) α
  exact tendsto_nhds_unique h_lhs (h_eq ▸ h_rhs)

omit [Fintype ι] [DecidableEq ι] in
lemma wightman_translationInvariant_of_tube_shift {W : WightmanFamily ι}
    (E : TubeExtension W)
    (h_trans : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
      z ∈ forward_tube_n n → E.H n α (fun i => z i + a) = E.H n α z)
    (n : ℕ) (α : Fin n → ι) (a : Fin 4 → ℝ)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    W n α f' = W n α f := by
  have hv : unit_time_vector ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  have hb_lhs := E.boundary n α f' unit_time_vector hv
  have hb_rhs := E.boundary n α f unit_time_vector hv
  have h_ev :
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        E.H n α (fun i k => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f' x) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        E.H n α (fun i k => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f x) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h_shift := (MeasureTheory.integral_add_right_eq_self (μ := volume)
      (fun x : Fin n → Fin 4 → ℝ =>
        E.H n α (fun i k => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) * f' x)
      (fun _ : Fin n => a)).symm
    rw [h_shift]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    dsimp only
    have h_line_add :
        (fun (i : Fin n) (k : Fin 4) => (((x + fun _ : Fin n => a) i k : ℝ) : ℂ) +
          Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) =
        fun i : Fin n => (fun k : Fin 4 => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * unit_time_vector k : ℝ) : ℂ)) + (fun k => (a k : ℂ)) := by
      ext i k
      simp [Pi.add_apply]
      ring
    rw [h_line_add,
        h_trans n α _ (fun k => (a k : ℂ)) (line_mem_forward_tube n x unit_time_vector hv t ht),
        show (x + fun _ : Fin n => a) = (fun i => x i + a) from rfl,
        hf' x]
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique (hb_lhs.congr' h_ev) hb_rhs

theorem poincareCovariant_of_tubeCovariant_general
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E)
    (h_trans : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
      z ∈ forward_tube_n n → E.H n α (fun i => z i + a) = E.H n α z) :
    PoincareCovariant R W := by
  intro n a A f f' hf' α
  have h_shift : ∀ y : Fin n → Fin 4 → ℝ,
      f' (fun i => y i + a) = schwartzLorentzCLM n A⁻¹ f y := by
    intro y
    have h_rel := hf' (lorentzEquiv n A⁻¹ y)
    have h_act : (fun i => poincareAct a A (lorentzEquiv n A⁻¹ y i)) =
        fun i => y i + a := by
      ext i μ
      have h_mul : lorentzEquiv n A (lorentzEquiv n A⁻¹ y) = y :=
        (lorentzEquiv n A).apply_symm_apply y
      have hi : (lorentzOfSL2C A).mulVec (lorentzEquiv n A⁻¹ y i) μ = y i μ :=
        congrFun (congrFun h_mul i) μ
      dsimp [poincareAct]
      rw [hi]
    rw [h_act] at h_rel
    exact h_rel
  rw [wightman_translationInvariant_of_tube_shift E h_trans n α a
        (schwartzLorentzCLM n A⁻¹ f) f' h_shift,
      wightman_lorentz_cov_of_tubeCovariant R W E h_cov n A f α]

lemma forward_tube_n_of_le_one {n : ℕ} (hn : n ≤ 1) (z : Fin n → Fin 4 → ℂ) :
    z ∈ forward_tube_n n := by
  intro i hi
  omega

lemma forward_tube_subset_extended_tube_n (n : ℕ) :
    forward_tube_n n ⊆ extended_tube_n n := by
  intro z hz
  dsimp [extended_tube_n]
  rw [Set.mem_iUnion]
  exact ⟨1, z, hz, one_smul _ z⟩

lemma extended_tube_n_smul_iff (n : ℕ) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) :
    Λ • z ∈ extended_tube_n n ↔ z ∈ extended_tube_n n := by
  constructor
  · intro h
    dsimp [extended_tube_n] at h ⊢
    rw [Set.mem_iUnion] at h ⊢
    rcases h with ⟨Λ₀, w, hw, hw_eq⟩
    dsimp at hw_eq
    refine ⟨Λ⁻¹ * Λ₀, w, hw, ?_⟩
    calc (Λ⁻¹ * Λ₀) • w = Λ⁻¹ • (Λ₀ • w) := mul_smul _ _ _
      _ = Λ⁻¹ • (Λ • z) := by rw [hw_eq]
      _ = z := inv_smul_smul Λ z
  · intro h
    dsimp [extended_tube_n] at h ⊢
    rw [Set.mem_iUnion] at h ⊢
    rcases h with ⟨Λ₀, w, hw, hw_eq⟩
    dsimp at hw_eq
    refine ⟨Λ * Λ₀, w, hw, ?_⟩
    calc (Λ * Λ₀) • w = Λ • (Λ₀ • w) := mul_smul _ _ _
      _ = Λ • z := by rw [hw_eq]

lemma rev_mem_extended_tube_n_of_mem (n : ℕ) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ extended_tube_n n) :
    (z ∘ Fin.rev) ∈ extended_tube_n n := by
  dsimp [extended_tube_n] at hz
  rw [Set.mem_iUnion] at hz
  rcases hz with ⟨Λ, w, hw, rfl⟩
  change Λ • (w ∘ Fin.rev) ∈ extended_tube_n n
  rw [extended_tube_n_smul_iff]
  exact rev_mem_extended_tube_n n w hw

lemma neg_mem_extended_tube_n_of_mem (n : ℕ) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ extended_tube_n n) :
    -z ∈ extended_tube_n n := by
  rw [← spinorPhi_neg_one_one_smul n z, extended_tube_n_smul_iff]
  exact hz

lemma neg_rev_mem_extended_tube_n_of_mem (n : ℕ) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ extended_tube_n n) :
    -(z ∘ Fin.rev) ∈ extended_tube_n n :=
  neg_mem_extended_tube_n_of_mem n (rev_mem_extended_tube_n_of_mem n hz)

lemma coeReal_mem_extended_tube_of_mem_jost_points (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ jost_points_n n) :
    coeReal n x ∈ extended_tube_n n := by
  by_cases hn : n ≤ 1
  · exact forward_tube_subset_extended_tube_n n (forward_tube_n_of_le_one hn (coeReal n x))
  · exact (jost_theorem n x (Nat.lt_of_not_ge hn)).mp hx

open Classical in
noncomputable def spinor_H_ext (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) : ℂ :=
  if hz : z ∈ extended_tube_n n then
    let Λ := Classical.choose (Set.mem_iUnion.mp hz)
    let w := Classical.choose (Classical.choose_spec (Set.mem_iUnion.mp hz))
    let g := Classical.choose (spinorPhi_surjective Λ)
    ∑ β : Fin n → ι, Tm R n g α β * E.H n β w
  else 0

lemma spinor_H_ext_eq_zero_of_notMem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ) (α : Fin n → ι) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∉ extended_tube_n n) :
    spinor_H_ext R W E n α z = 0 := by
  dsimp [spinor_H_ext]
  exact dif_neg hz

lemma spinor_H_ext_eq_of_mem_orbit (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (α : Fin n → ι) (g : SL2C × SL2C)
    {z w : Fin n → Fin 4 → ℂ} (hw : w ∈ forward_tube_n n)
    (h_eq : z = spinorPhi g • w) :
    spinor_H_ext R W E n α z = ∑ β : Fin n → ι, Tm R n g α β * E.H n β w := by
  have hz : z ∈ extended_tube_n n := by
    dsimp [extended_tube_n]
    rw [Set.mem_iUnion]
    exact ⟨spinorPhi g, w, hw, h_eq.symm⟩
  dsimp [spinor_H_ext]
  rw [dif_pos hz]
  let h_ex_Λ := Set.mem_iUnion.mp hz
  let Λ_c := Classical.choose h_ex_Λ
  let h_ex_w := Classical.choose_spec h_ex_Λ
  let w_c := Classical.choose h_ex_w
  have hw_c : w_c ∈ forward_tube_n n := (Classical.choose_spec h_ex_w).1
  have hz_c : z = Λ_c • w_c := (Classical.choose_spec h_ex_w).2.symm
  let g_c := Classical.choose (spinorPhi_surjective Λ_c)
  have hg_c : spinorPhi g_c = Λ_c := Classical.choose_spec (spinorPhi_surjective Λ_c)
  have h_rel : spinorPhi (g_c⁻¹ * g) • w = w_c := by
    calc spinorPhi (g_c⁻¹ * g) • w
        = (spinorPhi g_c)⁻¹ • (spinorPhi g • w) := by
          rw [map_mul, map_inv]
          exact mul_smul (spinorPhi g_c)⁻¹ (spinorPhi g) w
      _ = Λ_c⁻¹ • z := by rw [hg_c, ← h_eq]
      _ = Λ_c⁻¹ • (Λ_c • w_c) := by rw [hz_c]
      _ = w_c := inv_smul_smul Λ_c w_c
  have h_ccov := complex_covariance_of_real R W E h_cov
  have h_step : ∀ γ : Fin n → ι,
      E.H n γ w_c = ∑ β : Fin n → ι, Tm R n (g_c⁻¹ * g) γ β * E.H n β w := by
    intro γ
    have h_trans_mem : spinorPhi ((g_c⁻¹ * g).1, (g_c⁻¹ * g).2) • w ∈ forward_tube_n n := by
      rwa [Prod.mk.eta, h_rel]
    have hc := h_ccov n (g_c⁻¹ * g).1 (g_c⁻¹ * g).2 w hw h_trans_mem γ
    rw [Prod.mk.eta, h_rel] at hc
    exact hc
  change (∑ γ : Fin n → ι, Tm R n g_c α γ * E.H n γ w_c) =
    ∑ β : Fin n → ι, Tm R n g α β * E.H n β w
  simp_rw [h_step, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  have h_mul := (Tm_mul R n g_c (g_c⁻¹ * g) α β).symm
  rw [mul_inv_cancel_left] at h_mul
  calc (∑ γ : Fin n → ι, Tm R n g_c α γ * (Tm R n (g_c⁻¹ * g) γ β * E.H n β w))
      = (∑ γ : Fin n → ι, Tm R n g_c α γ * Tm R n (g_c⁻¹ * g) γ β) * E.H n β w := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun γ _ => by ring)
    _ = Tm R n g α β * E.H n β w := by rw [h_mul]

lemma spinor_H_ext_eq_on_forward_tube (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (α : Fin n → ι) {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    spinor_H_ext R W E n α z = E.H n α z := by
  have h_eq : z = spinorPhi 1 • z := by
    rw [map_one]
    exact (one_smul SpecialSpecialComplexLorentzGroup z).symm
  rw [spinor_H_ext_eq_of_mem_orbit R W E h_cov n α 1 hz h_eq]
  simp_rw [Tm_one, ite_mul, one_mul, zero_mul]
  simp

theorem spinor_H_ext_complexCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (g : SL2C × SL2C) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    spinor_H_ext R W E n α (spinorPhi g • z) =
      ∑ β : Fin n → ι, (∏ i, R.σ g (α i) (β i)) * spinor_H_ext R W E n β z := by
  by_cases hz : z ∈ extended_tube_n n
  · have hz_copy := hz
    dsimp [extended_tube_n] at hz_copy
    rw [Set.mem_iUnion] at hz_copy
    rcases hz_copy with ⟨Λ₀, w, hw, hw_eq⟩
    dsimp at hw_eq
    obtain ⟨g₀, rfl⟩ := spinorPhi_surjective Λ₀
    have hz_eq : z = spinorPhi g₀ • w := hw_eq.symm
    have hgz_eq : spinorPhi g • z = spinorPhi (g * g₀) • w := by
      rw [hz_eq, map_mul]
      exact (mul_smul (spinorPhi g) (spinorPhi g₀) w).symm
    rw [spinor_H_ext_eq_of_mem_orbit R W E h_cov n α (g * g₀) hw hgz_eq]
    have hβ : ∀ β : Fin n → ι,
        spinor_H_ext R W E n β z = ∑ γ : Fin n → ι, Tm R n g₀ β γ * E.H n γ w :=
      fun β => spinor_H_ext_eq_of_mem_orbit R W E h_cov n β g₀ hw hz_eq
    simp_rw [hβ, show ∀ β, (∏ i, R.σ g (α i) (β i)) = Tm R n g α β from fun _ => rfl,
      Tm_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun β _ => Finset.sum_congr rfl (fun γ _ => by ring))
  · have hgz : spinorPhi g • z ∉ extended_tube_n n := by
      rwa [extended_tube_n_smul_iff]
    rw [spinor_H_ext_eq_zero_of_notMem R W E n α hgz]
    simp_rw [spinor_H_ext_eq_zero_of_notMem R W E n _ hz, mul_zero, Finset.sum_const_zero]

theorem spinor_H_ext_analyticOnNhd (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (α : Fin n → ι) :
    AnalyticOnNhd ℂ (spinor_H_ext R W E n α) (extended_tube_n n) := by
  intro z hz
  dsimp [extended_tube_n] at hz
  rw [Set.mem_iUnion] at hz
  rcases hz with ⟨Λ, z_in, hz_in, hz_eq⟩
  dsimp at hz_eq
  obtain ⟨g, rfl⟩ := spinorPhi_surjective Λ
  let L : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun w => (spinorPhi g)⁻¹ • w
        map_add' := fun x y => smul_add _ _ _
        map_smul' := fun c x => by
          simp only [RingHom.id_apply]
          exact smul_comm _ _ _ }
  have hLz : L z = z_in := by
    change (spinorPhi g)⁻¹ • z = z_in
    rw [← hz_eq]
    exact inv_smul_smul (spinorPhi g) z_in
  let F : (Fin n → Fin 4 → ℂ) → ℂ :=
    fun w => ∑ β : Fin n → ι, Tm R n g α β * E.H n β (L w)
  have hF_an : AnalyticAt ℂ F z := by
    refine fintype_sum_analyticAt _ z (fun β => analyticAt_const.mul ?_)
    have hH_an : AnalyticAt ℂ (E.H n β) (L z) := by
      rw [hLz]
      exact (E.analytic n β).analyticAt ((forward_tube_n_isOpen n).mem_nhds hz_in)
    exact hH_an.comp (L.analyticAt z)
  have h_open_inv : L ⁻¹' (forward_tube_n n) ∈ 𝓝 z := by
    apply L.continuous.tendsto
    rw [hLz]
    exact (forward_tube_n_isOpen n).mem_nhds hz_in
  have h_eq_near : F =ᶠ[𝓝 z] spinor_H_ext R W E n α := by
    filter_upwards [h_open_inv] with w hw
    have hw_in : L w ∈ forward_tube_n n := hw
    have hw_eq : w = spinorPhi g • L w := (smul_inv_smul (spinorPhi g) w).symm
    exact (spinor_H_ext_eq_of_mem_orbit R W E h_cov n α g hw_in hw_eq).symm
  exact hF_an.congr h_eq_near

theorem spinor_H_ext_analytic (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (α : Fin n → ι) :
    AnalyticOn ℂ (spinor_H_ext R W E n α) (extended_tube_n n) :=
  (spinor_H_ext_analyticOnNhd R W E h_cov n α).analyticOn

omit [Fintype ι] [DecidableEq ι] in
theorem spinor_bhw_uniqueness (W : WightmanFamily ι) (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι)
    (H₁ H₂ : (Fin n → Fin 4 → ℂ) → ℂ)
    (h₁_an : AnalyticOn ℂ H₁ (extended_tube_n n))
    (h₁_eq : ∀ z ∈ forward_tube_n n, H₁ z = E.H n α z)
    (h₂_an : AnalyticOn ℂ H₂ (extended_tube_n n))
    (h₂_eq : ∀ z ∈ forward_tube_n n, H₂ z = E.H n α z) :
    Set.EqOn H₁ H₂ (extended_tube_n n) :=
  bhw_uniqueness n (E.H n α) H₁ H₂ h₁_an h₁_eq h₂_an h₂_eq

theorem spinor_bhw_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) :
    ∃! H_ext : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ,
      (∀ n α, AnalyticOn ℂ (H_ext n α) (extended_tube_n n)) ∧
      (∀ n (g : SL2C × SL2C) z α,
        H_ext n α (spinorPhi g • z) =
          ∑ β : Fin n → ι, (∏ i, R.σ g (α i) (β i)) * H_ext n β z) ∧
      (∀ n α, ∀ z ∈ forward_tube_n n, H_ext n α z = E.H n α z) ∧
      (∀ n α, ∀ z ∉ extended_tube_n n, H_ext n α z = 0) := by
  refine ⟨spinor_H_ext R W E,
    ⟨fun n α => spinor_H_ext_analytic R W E h_cov n α,
     fun n g z α => spinor_H_ext_complexCovariant R W E h_cov n g z α,
     fun n α _ hz => spinor_H_ext_eq_on_forward_tube R W E h_cov n α hz,
     fun n α _ hz => spinor_H_ext_eq_zero_of_notMem R W E n α hz⟩, ?_⟩
  intro H' hH'
  funext n α z
  by_cases hz : z ∈ extended_tube_n n
  · exact (spinor_bhw_uniqueness W E n α (H' n α) (spinor_H_ext R W E n α)
      (hH'.1 n α) (hH'.2.2.1 n α)
      (spinor_H_ext_analytic R W E h_cov n α)
      (fun w hw => spinor_H_ext_eq_on_forward_tube R W E h_cov n α hw) hz)
  · rw [hH'.2.2.2 n α z hz, spinor_H_ext_eq_zero_of_notMem R W E n α hz]

def ExtendedTubeWeakLocality (η : ℂ)
    (H_ext : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι), ∀ z ∈ extended_tube_n n,
    H_ext n α z = η ^ (n * (n - 1) / 2) * H_ext n (α ∘ Fin.rev) (z ∘ Fin.rev)

def TubePCT (η : ℂ) (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι), ∀ z ∈ forward_tube_n n,
    E.H n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n (β ∘ Fin.rev) z

lemma W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf_supp : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ))
    (hf_ext : ∀ x ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ),
      coeReal n x ∈ extended_tube_n n) :
    W n α f = ∫ x : Fin n → Fin 4 → ℝ, spinor_H_ext R W E n α (coeReal n x) * f x := by
  let v := unit_time_vector
  have hv : v ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  let line : ℝ → (Fin n → Fin 4 → ℝ) → (Fin n → Fin 4 → ℂ) :=
    fun t x i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)
  have hline_cont : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) => line p.1 p.2) := by
    refine continuous_pi (fun i => continuous_pi (fun k => ?_))
    have h1 : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) => (p.2 i k : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_apply k).comp
        ((continuous_apply i).comp continuous_snd))
    have h2 : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) =>
        Complex.I * ((p.1 * (i : ℕ) * v k : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_fst.mul continuous_const).mul continuous_const))
    exact h1.add h2
  let K : Set (Fin n → Fin 4 → ℝ) := tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)
  have h_maps : Set.MapsTo (fun p : ℝ × (Fin n → Fin 4 → ℝ) => line p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ K) (extended_tube_n n) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    dsimp only at ht hx ⊢
    rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · have h0 : line 0 x = coeReal n x := by
        ext i k
        simp [line, coeReal]
      rw [h0]
      exact hf_ext x hx
    · exact forward_tube_subset_extended_tube_n n (line_mem_forward_tube n x v hv t ht_pos)
  have hH_contOn : ContinuousOn (spinor_H_ext R W E n α) (extended_tube_n n) :=
    (spinor_H_ext_analyticOnNhd R W E h_cov n α).continuousOn
  have h_norm_contOn : ContinuousOn
      (fun p : ℝ × (Fin n → Fin 4 → ℝ) => ‖spinor_H_ext R W E n α (line p.1 p.2)‖)
      (Set.Icc (0 : ℝ) 1 ×ˢ K) :=
    continuous_norm.comp_continuousOn (hH_contOn.comp hline_cont.continuousOn h_maps)
  have hS_comp : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hf_supp
  rcases hS_comp.bddAbove_image h_norm_contOn with ⟨M₀, hM₀⟩
  let M : ℝ := max M₀ 0
  have hM_bound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K,
      ‖spinor_H_ext R W E n α (line t x)‖ ≤ M := by
    intro t ht x hx
    exact (hM₀ ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left M₀ 0)
  have h_dom : Tendsto
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, E.H n α (line t x) * f x)
      (𝓝[>] 0)
      (𝓝 (∫ x : Fin n → Fin 4 → ℝ, spinor_H_ext R W E n α (coeReal n x) * f x)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun x => M * ‖f x‖) ?_ ?_ (f.integrable.norm.const_mul M) ?_
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have ht_cont : Continuous (fun x => line t x) :=
        hline_cont.comp (continuous_const.prodMk continuous_id)
      have h_cont : Continuous (fun x : Fin n → Fin 4 → ℝ => E.H n α (line t x) * f x) := by
        refine (continuous_iff_continuousAt.mpr (fun x => ?_)).mul f.continuous
        exact ((E.analytic n α).continuousOn.continuousAt
          ((forward_tube_n_isOpen n).mem_nhds (line_mem_forward_tube n x v hv t ht))).comp
          ht_cont.continuousAt
      exact h_cont.aestronglyMeasurable
    · have h_nhds : Metric.ball (0 : ℝ) 1 ∩ Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        Filter.inter_mem
          (nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one))
          self_mem_nhdsWithin
      filter_upwards [h_nhds] with t ⟨ht_ball, ht_pos⟩
      have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
        have ht_lt : |t| < 1 := by simpa [Real.dist_eq] using ht_ball
        exact ⟨le_of_lt ht_pos, le_of_lt (abs_lt.mp ht_lt).2⟩
      refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ K
      · have h_eq_H : E.H n α (line t x) = spinor_H_ext R W E n α (line t x) :=
          (spinor_H_ext_eq_on_forward_tube R W E h_cov n α
            (line_mem_forward_tube n x v hv t ht_pos)).symm
        rw [h_eq_H, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM_bound t ht_Icc x hx) (norm_nonneg (f x))
      · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hfx]
    · refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : x ∈ K
      · have h0_eq : line 0 x = coeReal n x := by
          ext i k
          simp [line, coeReal]
        have h_contAt : ContinuousAt (spinor_H_ext R W E n α) (line 0 x) := by
          rw [h0_eq]
          exact hH_contOn.continuousAt ((extended_tube_is_open n).mem_nhds (hf_ext x hx))
        have ht_line : Continuous (fun t : ℝ => line t x) :=
          hline_cont.comp (continuous_id.prodMk continuous_const)
        have h_lim0 : Tendsto
            (fun t : ℝ => spinor_H_ext R W E n α (line t x) * f x)
            (𝓝[>] 0)
            (𝓝 (spinor_H_ext R W E n α (coeReal n x) * f x)) := by
          have ht_at : ContinuousAt (fun t : ℝ => line t x) 0 := ht_line.continuousAt
          have h1 := ((h_contAt.tendsto.comp ht_at.tendsto).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).mul_const (f x)
          rwa [h0_eq] at h1
        refine h_lim0.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        rw [spinor_H_ext_eq_on_forward_tube R W E h_cov n α
          (line_mem_forward_tube n x v hv t ht)]
      · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hfx]
  have h_bdy := E.boundary n α f v hv
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique h_bdy h_dom

lemma mem_tsupport_of_comp_continuous {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Zero Z] {g : Y → Z} {h : X → Y} (hh : Continuous h) {x : X}
    (hx : x ∈ tsupport (fun a => g (h a))) :
    h x ∈ tsupport g := by
  have h_sub : tsupport (fun a => g (h a)) ⊆ h ⁻¹' tsupport g :=
    closure_minimal (fun a ha => subset_tsupport g ha) (isClosed_tsupport g |>.preimage hh)
  exact h_sub hx

lemma isPreconnected_flat_extended_tube (n : ℕ) :
    IsPreconnected ((spacetimeFlatCLE_C n).symm ⁻¹' extended_tube_n n) := by
  have h_img : spacetimeFlatCLE_C n '' extended_tube_n n =
      (spacetimeFlatCLE_C n).symm ⁻¹' extended_tube_n n := by
    ext w
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rwa [ContinuousLinearEquiv.symm_apply_apply]
    · intro hw
      exact ⟨(spacetimeFlatCLE_C n).symm w, hw, ContinuousLinearEquiv.apply_symm_apply _ w⟩
  rw [← h_img]
  exact (extended_tube_is_connected n).isPreconnected.image _
    (spacetimeFlatCLE_C n).continuous.continuousOn

lemma spinor_H_ext_rev_eq_of_jost_locality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (c : ℂ)
    (h_jost_loc : ∀ (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) ⊆ jost_points_n n →
      (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) →
      W n α f = c * W n (α ∘ Fin.rev) f')
    (α : Fin n → ι) {z : Fin n → Fin 4 → ℂ} (hz : z ∈ extended_tube_n n) :
    spinor_H_ext R W E n α z = c * spinor_H_ext R W E n (α ∘ Fin.rev) (z ∘ Fin.rev) := by
  let U_flat : Set (Fin (n * 4) → ℂ) := (spacetimeFlatCLE_C n).symm ⁻¹' extended_tube_n n
  have hU_open : IsOpen U_flat :=
    (extended_tube_is_open n).preimage (spacetimeFlatCLE_C n).symm.continuous
  have hU_preconn : IsPreconnected U_flat := isPreconnected_flat_extended_tube n
  let revCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun w => w ∘ Fin.rev
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let gCLM : (Fin (n * 4) → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    revCLM.comp (spacetimeFlatCLE_C n).symm.toContinuousLinearMap
  let F₁ : (Fin (n * 4) → ℂ) → ℂ :=
    fun w => spinor_H_ext R W E n α ((spacetimeFlatCLE_C n).symm w)
  let F₂ : (Fin (n * 4) → ℂ) → ℂ :=
    fun w => c * spinor_H_ext R W E n (α ∘ Fin.rev) (gCLM w)
  have hF₁_an : AnalyticOnNhd ℂ F₁ U_flat := fun w hw =>
    (spinor_H_ext_analyticOnNhd R W E h_cov n α ((spacetimeFlatCLE_C n).symm w) hw).comp
      ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
  have hF₂_an : AnalyticOnNhd ℂ F₂ U_flat := fun w hw =>
    analyticAt_const.mul ((spinor_H_ext_analyticOnNhd R W E h_cov n (α ∘ Fin.rev) (gCLM w)
      (rev_mem_extended_tube_n_of_mem n hw)).comp (gCLM.analyticAt w))
  have h_real_mem : ∀ u ∈ (jostBallFlatOpens n : Set (Fin (n * 4) → ℝ)),
      (fun p => (u p : ℂ)) ∈ U_flat := by
    intro u hu
    change (spacetimeFlatCLE_C n).symm (fun p => (u p : ℂ)) ∈ extended_tube_n n
    rw [spacetimeFlatCLE_C_symm_ofReal]
    exact coeReal_mem_extended_tube_of_mem_jost_points n
      (symm_mem_jost_points_of_mem_jostBallFlat n hu)
  let g₁ : (Fin (n * 4) → ℝ) → ℂ := fun u => F₁ (fun p => (u p : ℂ))
  let g₂ : (Fin (n * 4) → ℝ) → ℂ := fun u => F₂ (fun p => (u p : ℂ))
  have h_emb_cont : Continuous (fun u : Fin (n * 4) → ℝ => (fun p => (u p : ℂ))) :=
    continuous_pi (fun p => Complex.continuous_ofReal.comp (continuous_apply p))
  have hg₁_contOn : ContinuousOn g₁ (jostBallFlatOpens n) :=
    hF₁_an.continuousOn.comp h_emb_cont.continuousOn h_real_mem
  have hg₂_contOn : ContinuousOn g₂ (jostBallFlatOpens n) :=
    hF₂_an.continuousOn.comp h_emb_cont.continuousOn h_real_mem
  have hg₁_loc : LocallyIntegrableOn g₁ (jostBallFlatOpens n) volume :=
    hg₁_contOn.locallyIntegrableOn (jostBallFlatOpens n).isOpen.measurableSet
  have hg₂_loc : LocallyIntegrableOn g₂ (jostBallFlatOpens n) volume :=
    hg₂_contOn.locallyIntegrableOn (jostBallFlatOpens n).isOpen.measurableSet
  have h_eq_dist : Distribution.EqualOn (jostBallFlatOpens n)
      (Distribution.ofLocallyIntegrableOn (jostBallFlatOpens n) g₁)
      (Distribution.ofLocallyIntegrableOn (jostBallFlatOpens n) g₂)
      (jostBallFlatOpens n) subset_rfl := by
    intro φ _hφ
    rw [Distribution.ofLocallyIntegrableOn_apply hg₁_loc,
        Distribution.ofLocallyIntegrableOn_apply hg₂_loc,
        ← integral_comp_spacetimeFlatCLE n, ← integral_comp_spacetimeFlatCLE n]
    let ψ := Distribution.testFunctionToSchwartzCLM (jostBallFlatOpens n) φ
    let f := schwartzFlatCLM n ψ
    let f' := schwartzRevCLM n f
    have hψ_supp : HasCompactSupport (fun u => ψ u) :=
      φ.hasCompactSupport'.comp_left Complex.ofReal_zero
    have hf_supp : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hasCompactSupport_schwartzFlatCLM n hψ_supp
    have hf'_supp : HasCompactSupport (f' : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hasCompactSupport_schwartzRevCLM n hf_supp
    have hψ_tsupp : tsupport (fun u => ψ u) ⊆ jostBallFlatOpens n := by
      refine (closure_mono (fun u hu => ?_)).trans φ.tsupport_subset'
      intro h0
      apply hu
      have h0' : φ u = 0 := h0
      change (φ u : ℂ) = 0
      rw [h0', Complex.ofReal_zero]
    have hf_jost_tsupp : ∀ x ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ),
        x ∈ jost_points_n n := by
      intro x hx
      have hu : spacetimeFlatCLE n x ∈ jostBallFlatOpens n :=
        hψ_tsupp (mem_tsupport_of_comp_continuous (spacetimeFlatCLE n).continuous hx)
      have h_symm := symm_mem_jost_points_of_mem_jostBallFlat n hu
      rwa [ContinuousLinearEquiv.symm_apply_apply] at h_symm
    have hf_ext : ∀ x ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n x ∈ extended_tube_n n :=
      fun x hx => coeReal_mem_extended_tube_of_mem_jost_points n (hf_jost_tsupp x hx)
    have hf'_ext : ∀ y ∈ tsupport (f' : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n y ∈ extended_tube_n n := by
      intro y hy
      have hy_rev : revCLE n y ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) :=
        mem_tsupport_of_comp_continuous (revCLE n).continuous hy
      have h_rev_mem := rev_mem_extended_tube_n_of_mem n (hf_ext (revCLE n y) hy_rev)
      have h_coe : ((coeReal n (revCLE n y)) ∘ Fin.rev) = coeReal n y := by
        ext i k
        simp [coeReal, revCLE_apply, Fin.rev_rev]
      rwa [h_coe] at h_rev_mem
    have h_int₁ : (∫ x : Fin n → Fin 4 → ℝ,
        g₁ (spacetimeFlatCLE n x) * (φ (spacetimeFlatCLE n x) : ℂ)) = W n α f := by
      rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
        R W E h_cov n α f hf_supp hf_ext]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp [g₁, F₁, f, ψ]
      have h_symm :
          ((spacetimeFlatCLE_C n).symm fun p =>
            (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
            coeReal n x :=
        (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
      rw [h_symm]
    have h_int₂ : (∫ x : Fin n → Fin 4 → ℝ,
        g₂ (spacetimeFlatCLE n x) * (φ (spacetimeFlatCLE n x) : ℂ)) =
        c * W n (α ∘ Fin.rev) f' := by
      rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
        R W E h_cov n (α ∘ Fin.rev) f' hf'_supp hf'_ext,
        ← integral_comp_rev n (fun y : Fin n → Fin 4 → ℝ =>
          spinor_H_ext R W E n (α ∘ Fin.rev) (coeReal n y) * f' y),
        ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp [g₂, F₂, gCLM, revCLM, f', f, ψ]
      have h_symm :
          ((spacetimeFlatCLE_C n).symm fun p =>
            (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
            coeReal n x :=
        (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
      have h_coe_rev : (coeReal n x ∘ Fin.rev) = coeReal n (fun i => x (Fin.rev i)) := rfl
      have h_inv_x : (fun i : Fin n => x (Fin.rev (Fin.rev i))) = x := by
        ext i μ
        simp [Fin.rev_rev]
      rw [h_symm, h_coe_rev, h_inv_x, mul_assoc]
    rw [h_int₁, h_int₂]
    refine h_jost_loc α f f' hf_jost_tsupp (fun x => ?_)
    dsimp [f']
    congr 1
    ext i μ
    simp [Fin.rev_rev]
  have h_real_eq : EqOn g₁ g₂ (jostBallFlatOpens n) :=
    Distribution.eqOn_of_equalOn_continuousOn subset_rfl
      hg₁_loc hg₂_loc hg₁_contOn hg₂_contOn h_eq_dist
  have h_all : EqOn F₁ F₂ U_flat :=
    Distribution.analyticOnNhd_eqOn_of_real_open hU_open hU_preconn hF₁_an hF₂_an
      (jostBallFlatOpens n).isOpen (jostBallFlatOpens_nonempty n) h_real_mem h_real_eq
  have hz_mem : spacetimeFlatCLE_C n z ∈ U_flat := by
    change (spacetimeFlatCLE_C n).symm (spacetimeFlatCLE_C n z) ∈ extended_tube_n n
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  have h_eval := h_all hz_mem
  dsimp [F₁, F₂, gCLM, revCLM] at h_eval
  rwa [ContinuousLinearEquiv.symm_apply_apply] at h_eval

theorem extendedTubeWeakLocality_of_weakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (hloc : WeakLocality η W) :
    ExtendedTubeWeakLocality η (spinor_H_ext R W E) :=
  fun n α _ hz => spinor_H_ext_rev_eq_of_jost_locality R W E h_cov n
    (η ^ (n * (n - 1) / 2)) (hloc n) α hz

theorem tubePCT_iff_extendedTubeWeakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) :
    TubePCT η R E ↔ ExtendedTubeWeakLocality η (spinor_H_ext R W E) := by
  constructor
  · intro hpct n α w hw
    let revCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun z => z ∘ Fin.rev
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    have hlhs_an : AnalyticOn ℂ (spinor_H_ext R W E n α) (extended_tube_n n) :=
      spinor_H_ext_analytic R W E h_cov n α
    have hrhs_an : AnalyticOn ℂ
        (fun z => η ^ (n * (n - 1) / 2) *
          spinor_H_ext R W E n (α ∘ Fin.rev) (z ∘ Fin.rev))
        (extended_tube_n n) := by
      have h_nhd : AnalyticOnNhd ℂ
          (fun z => η ^ (n * (n - 1) / 2) *
            spinor_H_ext R W E n (α ∘ Fin.rev) (revCLM z))
          (extended_tube_n n) := fun z hz =>
        analyticAt_const.mul ((spinor_H_ext_analyticOnNhd R W E h_cov n (α ∘ Fin.rev) (revCLM z)
          (rev_mem_extended_tube_n_of_mem n hz)).comp (revCLM.analyticAt z))
      exact h_nhd.analyticOn
    have h_eqOn : Set.EqOn (spinor_H_ext R W E n α)
        (fun z => η ^ (n * (n - 1) / 2) *
          spinor_H_ext R W E n (α ∘ Fin.rev) (z ∘ Fin.rev))
        (extended_tube_n n) := by
      refine scv_identity_theorem n (extended_tube_n n) (extended_tube_is_open n)
        (extended_tube_is_connected n) _ _ hlhs_an hrhs_an
        (forward_tube_n n) (forward_tube_n_isOpen n) (forward_tube_n_nonempty n)
        (forward_tube_subset_extended_tube_n n) (fun u hu => ?_)
      let z := -(u ∘ Fin.rev)
      have hz : z ∈ forward_tube_n n := neg_rev_mem_forward_tube_n n u hu
      have hu_eq : -(z ∘ Fin.rev) = u := neg_rev_involutive n u
      have h_rev_u : (u ∘ Fin.rev) = spinorPhi ((-1 : SL2C), (1 : SL2C)) • z := by
        rw [spinorPhi_neg_one_one_smul]
        ext i k
        simp [z]
      rw [h_rev_u, spinor_H_ext_eq_on_forward_tube R W E h_cov n α hu,
          ← hu_eq, hpct n α z hz,
          spinor_H_ext_complexCovariant R W E h_cov n (-1, 1) z (α ∘ Fin.rev)]
      simp_rw [spinor_H_ext_eq_on_forward_tube R W E h_cov n _ hz]
      rw [sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => E.H n β z) α]
    exact h_eqOn hw
  · intro hexloc n α z hz
    have h_nr : -(z ∘ Fin.rev) ∈ forward_tube_n n := neg_rev_mem_forward_tube_n n z hz
    have h_rev_nr : ((-(z ∘ Fin.rev)) ∘ Fin.rev) = spinorPhi ((-1 : SL2C), (1 : SL2C)) • z := by
      rw [spinorPhi_neg_one_one_smul]
      ext i k
      simp [Fin.rev_rev]
    rw [← spinor_H_ext_eq_on_forward_tube R W E h_cov n α h_nr,
        hexloc n α (-(z ∘ Fin.rev)) (forward_tube_subset_extended_tube_n n h_nr),
        h_rev_nr,
        spinor_H_ext_complexCovariant R W E h_cov n (-1, 1) z (α ∘ Fin.rev)]
    simp_rw [spinor_H_ext_eq_on_forward_tube R W E h_cov n _ hz]
    rw [sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => E.H n β z) α]

theorem tubePCT_of_weakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (hloc : WeakLocality η W) :
    TubePCT η R E :=
  (tubePCT_iff_extendedTubeWeakLocality R W E h_cov).mpr
    (extendedTubeWeakLocality_of_weakLocality R W E h_cov hloc)

theorem tubeWeakLocality_of_weakLocality_general (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (h_pt : TubePTScalar R E) (hloc : WeakLocality η W) :
    TubeWeakLocality η E := by
  intro n α z hz
  rw [tubePCT_of_weakLocality R W E h_cov hloc n α z hz,
      ← sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => E.H n β z) α,
      h_pt n (α ∘ Fin.rev) z hz]

theorem tubePCT_of_tubeWeakLocality_general (R : HolomorphicLorentzRep ι)
    {W : WightmanFamily ι} {η : ℂ} (E : TubeExtension W)
    (h_pt : TubePTScalar R E) (h_tloc : TubeWeakLocality η E) :
    TubePCT η R E := by
  intro n α z hz
  rw [h_tloc n α z hz,
      ← sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => E.H n β z) α,
      h_pt n (α ∘ Fin.rev) z hz]

lemma wightman_pct_of_tubePCT_compactSupport (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (hpct : TubePCT η R E)
    (h_trans : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
      z ∈ forward_tube_n n → E.H n α (fun i => z i + a) = E.H n α z)
    (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf_supp : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :
    W n α f =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) * W n (β ∘ Fin.rev) (schwartzPCTCLM n f) := by
  let v := unit_time_vector
  have hv : v ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  let f' := schwartzPCTCLM n f
  have hf'_supp : HasCompactSupport (f' : (Fin n → Fin 4 → ℝ) → ℂ) :=
    hf_supp.comp_homeomorph (pctCLE n).toHomeomorph
  have hb_lhs := E.boundary n α f v hv
  have hb_rhs : Tendsto
      (fun t : ℝ => η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) *
          ∫ x : Fin n → Fin 4 → ℝ,
            E.H n (β ∘ Fin.rev)
              (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f' x)
      (𝓝[>] 0)
      (𝓝 (η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) * W n (β ∘ Fin.rev) f')) :=
    (tendsto_finsetSum Finset.univ (fun β _ =>
      (E.boundary n (β ∘ Fin.rev) f' v hv).const_mul
        (∏ i, R.σ (-1, 1) (α i) (β i)))).const_mul (η ^ (n * (n - 1) / 2))
  have h_ev :
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        E.H n α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =ᶠ[
          𝓝[>] (0 : ℝ)]
      (fun t : ℝ => η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) *
          ∫ x : Fin n → Fin 4 → ℝ,
            E.H n (β ∘ Fin.rev)
              (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f' x) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    let line : (Fin n → Fin 4 → ℝ) → (Fin n → Fin 4 → ℂ) :=
      fun x i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)
    have h_line_cont : Continuous line := by
      refine continuous_pi (fun i => continuous_pi (fun k => ?_))
      exact (Complex.continuous_ofReal.comp ((continuous_apply k).comp (continuous_apply i))).add
        continuous_const
    have h_int_β : ∀ β : Fin n → ι,
        Integrable (fun x : Fin n → Fin 4 → ℝ =>
          E.H n (β ∘ Fin.rev) (line x) * f' x) volume := by
      intro β
      have h_cont : Continuous (fun x : Fin n → Fin 4 → ℝ =>
          E.H n (β ∘ Fin.rev) (line x) * f' x) := by
        refine (continuous_iff_continuousAt.mpr (fun x => ?_)).mul f'.continuous
        exact ((E.analytic n (β ∘ Fin.rev)).continuousOn.continuousAt
          ((forward_tube_n_isOpen n).mem_nhds (line_mem_forward_tube n x v hv t ht))).comp
          h_line_cont.continuousAt
      exact h_cont.integrable_of_hasCompactSupport hf'_supp.mul_left
    have h_comp := (integral_comp_pct n
      (fun x : Fin n → Fin 4 → ℝ => E.H n α (line x) * f x)).symm
    change (∫ x : Fin n → Fin 4 → ℝ, E.H n α (line x) * f x) =
      ∫ x : Fin n → Fin 4 → ℝ, E.H n α (line (pctCLE n x)) * f' x at h_comp
    rw [h_comp]
    simp_rw [← MeasureTheory.integral_const_mul]
    rw [← integral_finsetSum Finset.univ
          (fun β _ => (h_int_β β).const_mul (∏ i, R.σ (-1, 1) (α i) (β i))),
        ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have h_shift_eq :
        line (pctCLE n x) =
          fun i : Fin n => (-(line x ∘ Fin.rev)) i +
            fun k : Fin 4 => Complex.I * ((t * ((n - 1 : ℕ) : ℝ) * v k : ℝ) : ℂ) := by
      ext i k
      have h_rev : ((Fin.rev i : ℕ) : ℝ) = ((n - 1 : ℕ) : ℝ) - (i : ℕ) := by
        have h_eq : (Fin.rev i : ℕ) = n - 1 - (i : ℕ) := by
          rw [Fin.val_rev]
          omega
        rw [h_eq, Nat.cast_sub (Nat.le_sub_one_of_lt i.isLt)]
      dsimp only [line, pctCLE_apply, Pi.add_apply, Pi.neg_apply, Function.comp_apply]
      rw [h_rev]
      push_cast
      ring
    have h_nr_mem : -(line x ∘ Fin.rev) ∈ forward_tube_n n :=
      neg_rev_mem_forward_tube_n n (line x) (line_mem_forward_tube n x v hv t ht)
    dsimp only
    rw [h_shift_eq,
        h_trans n α (-(line x ∘ Fin.rev))
          (fun k : Fin 4 => Complex.I * ((t * ((n - 1 : ℕ) : ℝ) * v k : ℝ) : ℂ)) h_nr_mem,
        hpct n α (line x) (line_mem_forward_tube n x v hv t ht),
        mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun β _ => mul_assoc _ _ _)
  haveI : Filter.NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique (hb_lhs.congr' h_ev) hb_rhs

theorem wightman_pct_of_tubePCT_general (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (hpct : TubePCT η R E)
    (h_trans : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
      z ∈ forward_tube_n n → E.H n α (fun i => z i + a) = E.H n α z) :
    WightmanPCT η R W := by
  intro n α f f' hf'
  have hf'_eq : f' = schwartzPCTCLM n f := by
    ext x
    have h_inv := hf' (pctCLE n x)
    have h_pct_inv : (fun i => -(pctCLE n x) (Fin.rev i)) = x := pctCLE_involutive n x
    rw [h_pct_inv] at h_inv
    exact h_inv
  rw [hf'_eq]
  have h_seq := schwartzCutoffSeq_tendsto n f
  have h_lhs : Tendsto (fun k : ℕ => W n α (schwartzCutoffSeq n f k))
      Filter.atTop (𝓝 (W n α f)) :=
    ((W n α).continuous.tendsto f).comp h_seq
  have h_rhs : Tendsto
      (fun k : ℕ => η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) *
            W n (β ∘ Fin.rev) (schwartzPCTCLM n (schwartzCutoffSeq n f k)))
      Filter.atTop
      (𝓝 (η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) * W n (β ∘ Fin.rev) (schwartzPCTCLM n f))) :=
    (tendsto_finsetSum Finset.univ (fun β _ =>
      (((W n (β ∘ Fin.rev)).continuous.tendsto _).comp
        (((schwartzPCTCLM n).continuous.tendsto f).comp h_seq)).const_mul
        (∏ i, R.σ (-1, 1) (α i) (β i)))).const_mul (η ^ (n * (n - 1) / 2))
  have h_eq :
      (fun k : ℕ => W n α (schwartzCutoffSeq n f k)) =
      (fun k : ℕ => η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) *
            W n (β ∘ Fin.rev) (schwartzPCTCLM n (schwartzCutoffSeq n f k))) := by
    ext k
    exact wightman_pct_of_tubePCT_compactSupport R W E hpct h_trans n α
      (schwartzCutoffSeq n f k) (schwartzCutoffSeq_hasCompactSupport n f k)
  exact tendsto_nhds_unique h_lhs (h_eq ▸ h_rhs)

theorem tubePCT_of_wightmanPCT (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (hpct : WightmanPCT η R W) :
    TubePCT η R E := by
  intro n α z hz
  let U_flat : Set (Fin (n * 4) → ℂ) := (spacetimeFlatCLE_C n).symm ⁻¹' extended_tube_n n
  have hU_open : IsOpen U_flat :=
    (extended_tube_is_open n).preimage (spacetimeFlatCLE_C n).symm.continuous
  have hU_preconn : IsPreconnected U_flat := isPreconnected_flat_extended_tube n
  let negRevCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    LinearMap.toContinuousLinearMap
      { toFun := fun w => -(w ∘ Fin.rev)
        map_add' := fun x y => by ext i μ; simp [add_comm]
        map_smul' := fun c x => by ext i μ; simp }
  let pCLM : (Fin (n * 4) → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
    negRevCLM.comp (spacetimeFlatCLE_C n).symm.toContinuousLinearMap
  let F₁ : (Fin (n * 4) → ℂ) → ℂ :=
    fun w => spinor_H_ext R W E n α ((spacetimeFlatCLE_C n).symm w)
  let F₂ : (Fin (n * 4) → ℂ) → ℂ :=
    fun w => η ^ (n * (n - 1) / 2) *
      ∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * spinor_H_ext R W E n (β ∘ Fin.rev) (pCLM w)
  have hF₁_an : AnalyticOnNhd ℂ F₁ U_flat := fun w hw =>
    (spinor_H_ext_analyticOnNhd R W E h_cov n α ((spacetimeFlatCLE_C n).symm w) hw).comp
      ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
  have hF₂_an : AnalyticOnNhd ℂ F₂ U_flat := fun w hw =>
    analyticAt_const.mul (fintype_sum_analyticAt _ w (fun β =>
      analyticAt_const.mul ((spinor_H_ext_analyticOnNhd R W E h_cov n (β ∘ Fin.rev) (pCLM w)
        (neg_rev_mem_extended_tube_n_of_mem n hw)).comp (pCLM.analyticAt w))))
  have h_real_mem : ∀ u ∈ (jostBallFlatOpens n : Set (Fin (n * 4) → ℝ)),
      (fun p => (u p : ℂ)) ∈ U_flat := by
    intro u hu
    change (spacetimeFlatCLE_C n).symm (fun p => (u p : ℂ)) ∈ extended_tube_n n
    rw [spacetimeFlatCLE_C_symm_ofReal]
    exact coeReal_mem_extended_tube_of_mem_jost_points n
      (symm_mem_jost_points_of_mem_jostBallFlat n hu)
  let g₁ : (Fin (n * 4) → ℝ) → ℂ := fun u => F₁ (fun p => (u p : ℂ))
  let g₂ : (Fin (n * 4) → ℝ) → ℂ := fun u => F₂ (fun p => (u p : ℂ))
  have h_emb_cont : Continuous (fun u : Fin (n * 4) → ℝ => (fun p => (u p : ℂ))) :=
    continuous_pi (fun p => Complex.continuous_ofReal.comp (continuous_apply p))
  have hg₁_contOn : ContinuousOn g₁ (jostBallFlatOpens n) :=
    hF₁_an.continuousOn.comp h_emb_cont.continuousOn h_real_mem
  have hg₂_contOn : ContinuousOn g₂ (jostBallFlatOpens n) :=
    hF₂_an.continuousOn.comp h_emb_cont.continuousOn h_real_mem
  have hg₁_loc : LocallyIntegrableOn g₁ (jostBallFlatOpens n) volume :=
    hg₁_contOn.locallyIntegrableOn (jostBallFlatOpens n).isOpen.measurableSet
  have hg₂_loc : LocallyIntegrableOn g₂ (jostBallFlatOpens n) volume :=
    hg₂_contOn.locallyIntegrableOn (jostBallFlatOpens n).isOpen.measurableSet
  have h_eq_dist : Distribution.EqualOn (jostBallFlatOpens n)
      (Distribution.ofLocallyIntegrableOn (jostBallFlatOpens n) g₁)
      (Distribution.ofLocallyIntegrableOn (jostBallFlatOpens n) g₂)
      (jostBallFlatOpens n) subset_rfl := by
    intro φ _hφ
    rw [Distribution.ofLocallyIntegrableOn_apply hg₁_loc,
        Distribution.ofLocallyIntegrableOn_apply hg₂_loc,
        ← integral_comp_spacetimeFlatCLE n, ← integral_comp_spacetimeFlatCLE n]
    let ψ := Distribution.testFunctionToSchwartzCLM (jostBallFlatOpens n) φ
    let f := schwartzFlatCLM n ψ
    let f' := schwartzPCTCLM n f
    have hψ_supp : HasCompactSupport (fun u => ψ u) :=
      φ.hasCompactSupport'.comp_left Complex.ofReal_zero
    have hf_supp : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hasCompactSupport_schwartzFlatCLM n hψ_supp
    have hf'_supp : HasCompactSupport (f' : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hf_supp.comp_homeomorph (pctCLE n).toHomeomorph
    have hψ_tsupp : tsupport (fun u => ψ u) ⊆ jostBallFlatOpens n := by
      refine (closure_mono (fun u hu => ?_)).trans φ.tsupport_subset'
      intro h0
      apply hu
      have h0' : φ u = 0 := h0
      change (φ u : ℂ) = 0
      rw [h0', Complex.ofReal_zero]
    have hf_ext : ∀ x ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n x ∈ extended_tube_n n := by
      intro x hx
      have hu : spacetimeFlatCLE n x ∈ jostBallFlatOpens n :=
        hψ_tsupp (mem_tsupport_of_comp_continuous (spacetimeFlatCLE n).continuous hx)
      have h_symm := symm_mem_jost_points_of_mem_jostBallFlat n hu
      rw [ContinuousLinearEquiv.symm_apply_apply] at h_symm
      exact coeReal_mem_extended_tube_of_mem_jost_points n h_symm
    have hf'_ext : ∀ y ∈ tsupport (f' : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n y ∈ extended_tube_n n := by
      intro y hy
      have hy_pct : pctCLE n y ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) :=
        mem_tsupport_of_comp_continuous (pctCLE n).continuous hy
      have h_nr_mem := neg_rev_mem_extended_tube_n_of_mem n (hf_ext (pctCLE n y) hy_pct)
      have h_coe : -((coeReal n (pctCLE n y)) ∘ Fin.rev) = coeReal n y := by
        ext i k
        simp [coeReal, pctCLE_apply, Fin.rev_rev]
      rwa [h_coe] at h_nr_mem
    have h_int₁ : (∫ x : Fin n → Fin 4 → ℝ,
        g₁ (spacetimeFlatCLE n x) * (φ (spacetimeFlatCLE n x) : ℂ)) = W n α f := by
      rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
        R W E h_cov n α f hf_supp hf_ext]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp [g₁, F₁, f, ψ]
      have h_symm :
          ((spacetimeFlatCLE_C n).symm fun p =>
            (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
            coeReal n x :=
        (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
      rw [h_symm]
    have h_int_β : ∀ β : Fin n → ι,
        Integrable (fun x : Fin n → Fin 4 → ℝ =>
          spinor_H_ext R W E n (β ∘ Fin.rev) (-(coeReal n x ∘ Fin.rev)) * f x) volume := by
      intro β
      have h_maps_K : Set.MapsTo
          (fun x : Fin n → Fin 4 → ℝ => -(coeReal n x ∘ Fin.rev))
          (tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) (extended_tube_n n) :=
        fun x hx => neg_rev_mem_extended_tube_n_of_mem n (hf_ext x hx)
      have h_coe_cont : Continuous (fun x : Fin n → Fin 4 → ℝ => -(coeReal n x ∘ Fin.rev)) := by
        refine continuous_pi (fun i => continuous_pi (fun k => ?_))
        exact (Complex.continuous_ofReal.comp
          ((continuous_apply k).comp (continuous_apply (Fin.rev i)))).neg
      have h_contOn : ContinuousOn
          (fun x : Fin n → Fin 4 → ℝ =>
            spinor_H_ext R W E n (β ∘ Fin.rev) (-(coeReal n x ∘ Fin.rev)) * f x)
          (tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)) :=
        (((spinor_H_ext_analyticOnNhd R W E h_cov n (β ∘ Fin.rev)).continuousOn.comp
          h_coe_cont.continuousOn h_maps_K).mul f.continuous.continuousOn)
      have h_cont : Continuous
          (fun x : Fin n → Fin 4 → ℝ =>
            spinor_H_ext R W E n (β ∘ Fin.rev) (-(coeReal n x ∘ Fin.rev)) * f x) := by
        refine continuous_iff_continuousAt.mpr (fun x => ?_)
        by_cases hx : x ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ)
        · have hH_at : ContinuousAt (spinor_H_ext R W E n (β ∘ Fin.rev))
              (-(coeReal n x ∘ Fin.rev)) :=
            (spinor_H_ext_analyticOnNhd R W E h_cov n (β ∘ Fin.rev)).continuousOn.continuousAt
              ((extended_tube_is_open n).mem_nhds (h_maps_K hx))
          have hc_at : ContinuousAt (fun y : Fin n → Fin 4 → ℝ => -(coeReal n y ∘ Fin.rev)) x :=
            h_coe_cont.continuousAt
          have hcomp_at : ContinuousAt
              (fun y : Fin n → Fin 4 → ℝ =>
                spinor_H_ext R W E n (β ∘ Fin.rev) (-(coeReal n y ∘ Fin.rev))) x :=
            hH_at.tendsto.comp hc_at.tendsto
          exact hcomp_at.mul f.continuous.continuousAt
        · have h_zero :
              (fun y : Fin n → Fin 4 → ℝ =>
                spinor_H_ext R W E n (β ∘ Fin.rev) (-(coeReal n y ∘ Fin.rev)) * f y) =ᶠ[𝓝 x]
              fun _ => 0 := by
            filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx] with y hy
            rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
          exact continuousAt_const.congr h_zero.symm
      exact h_cont.integrable_of_hasCompactSupport hf_supp.mul_left
    have h_int₂ : (∫ x : Fin n → Fin 4 → ℝ,
        g₂ (spacetimeFlatCLE n x) * (φ (spacetimeFlatCLE n x) : ℂ)) =
        η ^ (n * (n - 1) / 2) *
          ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * W n (β ∘ Fin.rev) f' := by
      have h_each : ∀ β : Fin n → ι,
          W n (β ∘ Fin.rev) f' =
            ∫ x : Fin n → Fin 4 → ℝ,
              spinor_H_ext R W E n (β ∘ Fin.rev) (-(coeReal n x ∘ Fin.rev)) * f x := by
        intro β
        rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
              R W E h_cov n (β ∘ Fin.rev) f' hf'_supp hf'_ext,
            ← integral_comp_pct n (fun y : Fin n → Fin 4 → ℝ =>
              spinor_H_ext R W E n (β ∘ Fin.rev) (coeReal n y) * f' y)]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        dsimp [f']
        have h_coe : coeReal n (fun i => -x (Fin.rev i)) = -(coeReal n x ∘ Fin.rev) := by
          ext i k
          simp [coeReal]
        have h_inv_x : (fun i : Fin n => -(-x (Fin.rev (Fin.rev i)))) = x := by
          ext i k
          simp [Fin.rev_rev]
        rw [h_coe, h_inv_x]
      simp_rw [h_each, ← MeasureTheory.integral_const_mul]
      rw [← integral_finsetSum Finset.univ
            (fun β _ => (h_int_β β).const_mul (∏ i, R.σ (-1, 1) (α i) (β i))),
          ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      dsimp [g₂, F₂, pCLM, negRevCLM, f, ψ]
      have h_symm :
          ((spacetimeFlatCLE_C n).symm fun p =>
            (x (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2 : ℂ)) =
            coeReal n x :=
        (spacetimeFlatCLE_C n).symm_apply_apply (coeReal n x)
      rw [h_symm, mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun β _ => mul_assoc _ _ _)
    rw [h_int₁, h_int₂]
    refine hpct n α f f' (fun x => ?_)
    dsimp [f']
    congr 1
    ext i k
    simp [Fin.rev_rev]
  have h_real_eq : EqOn g₁ g₂ (jostBallFlatOpens n) :=
    Distribution.eqOn_of_equalOn_continuousOn subset_rfl
      hg₁_loc hg₂_loc hg₁_contOn hg₂_contOn h_eq_dist
  have h_all : EqOn F₁ F₂ U_flat :=
    Distribution.analyticOnNhd_eqOn_of_real_open hU_open hU_preconn hF₁_an hF₂_an
      (jostBallFlatOpens n).isOpen (jostBallFlatOpens_nonempty n) h_real_mem h_real_eq
  have h_nr : -(z ∘ Fin.rev) ∈ forward_tube_n n := neg_rev_mem_forward_tube_n n z hz
  have h_mem : spacetimeFlatCLE_C n (-(z ∘ Fin.rev)) ∈ U_flat := by
    change (spacetimeFlatCLE_C n).symm (spacetimeFlatCLE_C n (-(z ∘ Fin.rev))) ∈ extended_tube_n n
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact forward_tube_subset_extended_tube_n n h_nr
  have h_eval := h_all h_mem
  dsimp [F₁, F₂, pCLM, negRevCLM] at h_eval
  rw [ContinuousLinearEquiv.symm_apply_apply, neg_rev_involutive n z,
      spinor_H_ext_eq_on_forward_tube R W E h_cov n α h_nr] at h_eval
  simp_rw [spinor_H_ext_eq_on_forward_tube R W E h_cov n _ hz] at h_eval
  exact h_eval

theorem tubePCT_iff_wightmanPCT_general (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E)
    (h_trans : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
      z ∈ forward_tube_n n → E.H n α (fun i => z i + a) = E.H n α z) :
    TubePCT η R E ↔ WightmanPCT η R W :=
  ⟨fun hpct => wightman_pct_of_tubePCT_general R W E hpct h_trans,
   tubePCT_of_wightmanPCT R W E h_cov⟩

theorem wightman_pct_of_weakLocality_general (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E)
    (h_trans : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
      z ∈ forward_tube_n n → E.H n α (fun i => z i + a) = E.H n α z)
    (hloc : WeakLocality η W) :
    WightmanPCT η R W :=
  wightman_pct_of_tubePCT_general R W E
    (tubePCT_of_weakLocality R W E h_cov hloc) h_trans

theorem entire_weakLocality_of_tubePCT (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) (hpct : TubePCT η R E) :
    WeakLocality η W := by
  intro n α f f' _hf_jost hf'
  have hf'_eq : f' = schwartzRevCLM n f := by
    ext x
    have h_inv := hf' (revCLE n x)
    have h_rev_inv : (fun i => (revCLE n x) (Fin.rev i)) = x := revCLE_involutive n x
    rw [h_rev_inv] at h_inv
    exact h_inv
  rw [hf'_eq]
  have h_compact : ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      HasCompactSupport (g : (Fin n → Fin 4 → ℝ) → ℂ) →
      W n α g = η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) (schwartzRevCLM n g) := by
    intro g hg_supp
    rw [entire_W_eq_integral_of_hasCompactSupport E h_entire n α g hg_supp,
        entire_W_eq_integral_of_hasCompactSupport E h_entire n (α ∘ Fin.rev)
          (schwartzRevCLM n g) (hasCompactSupport_schwartzRevCLM n hg_supp),
        ← integral_comp_rev n (fun y : Fin n → Fin 4 → ℝ =>
          E.H n (α ∘ Fin.rev) (coeReal n y) * schwartzRevCLM n g y),
        ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have h_rev := entire_H_rev_of_tube_pct R W E h_entire h_cov hpct n α (coeReal n x)
    have h_coe_rev : (coeReal n x ∘ Fin.rev) = coeReal n (fun i => x (Fin.rev i)) := rfl
    have h_inv_x : (fun i : Fin n => x (Fin.rev (Fin.rev i))) = x := by
      ext i k
      simp [Fin.rev_rev]
    dsimp [schwartzRevCLM_apply]
    rw [h_rev, h_coe_rev, h_inv_x, mul_assoc]
  have h_seq := schwartzCutoffSeq_tendsto n f
  have h_lhs : Tendsto (fun k : ℕ => W n α (schwartzCutoffSeq n f k))
      Filter.atTop (𝓝 (W n α f)) :=
    ((W n α).continuous.tendsto f).comp h_seq
  have h_rhs : Tendsto
      (fun k : ℕ => η ^ (n * (n - 1) / 2) *
        W n (α ∘ Fin.rev) (schwartzRevCLM n (schwartzCutoffSeq n f k)))
      Filter.atTop
      (𝓝 (η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) (schwartzRevCLM n f))) :=
    (((W n (α ∘ Fin.rev)).continuous.tendsto _).comp
      (((schwartzRevCLM n).continuous.tendsto f).comp h_seq)).const_mul (η ^ (n * (n - 1) / 2))
  have h_eq :
      (fun k : ℕ => W n α (schwartzCutoffSeq n f k)) =
      (fun k : ℕ => η ^ (n * (n - 1) / 2) *
        W n (α ∘ Fin.rev) (schwartzRevCLM n (schwartzCutoffSeq n f k))) := by
    ext k
    exact h_compact (schwartzCutoffSeq n f k) (schwartzCutoffSeq_hasCompactSupport n f k)
  exact tendsto_nhds_unique h_lhs (h_eq ▸ h_rhs)

theorem entire_tubePCT_iff_weakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_entire : ∀ (m : ℕ) (β : Fin m → ι) (w : Fin m → Fin 4 → ℂ), AnalyticAt ℂ (E.H m β) w)
    (h_cov : TubeCovariant R E) :
    TubePCT η R E ↔ WeakLocality η W :=
  ⟨entire_weakLocality_of_tubePCT R W E h_entire h_cov,
   tubePCT_of_weakLocality R W E h_cov⟩

theorem isEmpty_starStructure_leftWeylRep : IsEmpty (StarStructure leftWeylRep) := by
  refine ⟨fun S => ?_⟩
  have h := S.intertwine (-1) 1
  have hL : leftWeylRep.σ (-1, 1) = -1 := by
    change ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = -1
    simp [Matrix.SpecialLinearGroup.coe_neg]
  have hR : (leftWeylRep.σ (sl2c_conj 1, sl2c_conj (-1))).map star = 1 := by
    rw [sl2c_conj_one]
    change ((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ).map star = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hL, hR, Matrix.mul_neg, Matrix.mul_one, Matrix.one_mul] at h
  have h_inv : -(S.C * S.C.map star) = S.C * S.C.map star := by
    rw [← Matrix.neg_mul, h]
  rw [S.involutive] at h_inv
  have h00 : (-1 : ℂ) = 1 := by
    simpa using congr_fun (congr_fun h_inv 0) 0
  norm_num at h00

lemma neg_mem_extended_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    -z ∈ extended_tube_n n := by
  apply backward_tube_subset_extended_tube_n n
  rw [← neg_mem_forward_tube_n_iff n (-z), neg_neg]
  exact hz

theorem spinor_H_ext_neg_one_one (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    spinor_H_ext R W E n α (-z) =
      ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n β z := by
  have h_smul : spinorPhi ((-1 : SL2C), (1 : SL2C)) • z = -z :=
    spinorPhi_neg_one_one_smul n z
  rw [← h_smul, spinor_H_ext_complexCovariant R W E h_cov n (-1, 1) z α]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [spinor_H_ext_eq_on_forward_tube R W E h_cov n β hz]

theorem spinor_H_ext_neg_rev (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α (-(z ∘ Fin.rev)) =
      ∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * spinor_H_ext R W E n β (z ∘ Fin.rev) := by
  rw [← spinor_H_ext_eq_on_forward_tube R W E h_cov n α (neg_rev_mem_forward_tube_n n z hz)]
  have h_smul : spinorPhi ((-1 : SL2C), (1 : SL2C)) • (z ∘ Fin.rev) = -(z ∘ Fin.rev) :=
    spinorPhi_neg_one_one_smul n (z ∘ Fin.rev)
  rw [← h_smul]
  exact spinor_H_ext_complexCovariant R W E h_cov n (-1, 1) (z ∘ Fin.rev) α

theorem tubePCT_two_of_scalar_pt (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    {η δ : ℂ} (E : TubeExtension W)
    (hδ : R.σ (-1, 1) = δ • (1 : Matrix ι ι ℂ)) (hδ_sq : δ ^ 2 = 1)
    (hpct : TubePCT η R E)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = η * E.H 2 (α ∘ Fin.rev) z := by
  have h := hpct 2 α z hz
  rw [two_mul_two_sub_one_div_two, pow_one] at h
  have h_prod : ∀ β : Fin 2 → ι,
      (∏ i : Fin 2, R.σ (-1, 1) (α i) (β i)) = if α = β then 1 else 0 := by
    intro β
    rw [hδ]
    by_cases hab : α = β
    · subst hab
      simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hδ_sq]
    · rw [if_neg hab]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact hab (funext hc)
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [Matrix.smul_apply, Matrix.one_apply_ne hi, smul_zero]
  simp_rw [h_prod] at h
  simpa using h

lemma stdRep_sigma_neg_one_one :
    stdRep.σ (-1, 1) = (-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j
  change spinorPhi_matrix (-1) 1 i j = ((-1 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) i j
  have hval : spinorPhi_matrix (-1) 1 = spinorPT.val.val := rfl
  rw [hval, spinorPT_val]
  by_cases hij : i = j <;> simp [hij]

lemma leftWeylRep_sigma_neg_one_one :
    leftWeylRep.σ (-1, 1) = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  change ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • 1
  simp [Matrix.SpecialLinearGroup.coe_neg]

noncomputable def sl2c_iSigma3 : SL2C :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by rw [Matrix.det_fin_two]; simp⟩

noncomputable def sl2c_iSigma1 : SL2C :=
  ⟨!![0, Complex.I; Complex.I, 0], by rw [Matrix.det_fin_two]; simp⟩

def timeAxisVecC (c : ℂ) : Fin 4 → ℂ := ![c, 0, 0, 0]

lemma vec_to_spinor_timeAxisVecC (c : ℂ) :
    vec_to_spinor (timeAxisVecC c) = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [timeAxisVecC, vec_to_spinor, sigma_0, sigma_1, sigma_2, sigma_3]

lemma origin_timeAxisVecC_mem_forward_tube_two {t : ℝ} (ht : 0 < t) :
    ![0, timeAxisVecC (Complex.I * (t : ℂ))] ∈ forward_tube_n 2 := by
  intro i hi
  fin_cases i
  · change (fun k => -((![0, timeAxisVecC (Complex.I * (t : ℂ))] (0 : Fin 2) -
        ![0, timeAxisVecC (Complex.I * (t : ℂ))] (1 : Fin 2)) k).im) ∈ forward_light_cone
    have hv : (fun k : Fin 4 => -((![0, timeAxisVecC (Complex.I * (t : ℂ))] (0 : Fin 2) -
        ![0, timeAxisVecC (Complex.I * (t : ℂ))] (1 : Fin 2)) k).im) = ![t, 0, 0, 0] := by
      ext k
      fin_cases k <;> simp [timeAxisVecC]
    rw [hv]
    refine ⟨ht, ?_⟩
    rw [minkowskiInner_explicit]
    change t * t - (0 : ℝ) * 0 - 0 * 0 - 0 * 0 > 0
    nlinarith
  · simp at hi

lemma spinorPhi_smul_origin_pair (A B : SL2C) (w : Fin 4 → ℂ) :
    spinorPhi (A, B) • (![0, w] : Fin 2 → Fin 4 → ℂ) =
      ![0, spinor_action A.1 B.1 w] := by
  ext i k
  fin_cases i
  · change ((spinorPhi_matrix A B).mulVec 0) k = 0
    rw [Matrix.mulVec_zero]
    rfl
  · change ((spinorPhi_matrix A B).mulVec w) k = spinor_action A.1 B.1 w k
    rw [spinorPhi_matrix_mulVec]

lemma spinor_action_timeAxisVecC_of_mul_transpose_eq_one (A B : SL2C)
    (hAB : A.1 * B.1ᵀ = 1) (c : ℂ) :
    spinor_action A.1 B.1 (timeAxisVecC c) = timeAxisVecC c := by
  dsimp [spinor_action]
  rw [vec_to_spinor_timeAxisVecC]
  have hmul : A.1 * (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * B.1ᵀ =
      vec_to_spinor (timeAxisVecC c) := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hAB, vec_to_spinor_timeAxisVecC]
  rw [hmul, spinor_to_vec_left_inv]

lemma sl2c_iSigma3_mul_neg_transpose :
    sl2c_iSigma3.1 * (-sl2c_iSigma3 : SL2C).1ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2c_iSigma3, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_apply,
      Fin.sum_univ_two]

lemma sl2c_iSigma1_mul_neg_transpose :
    sl2c_iSigma1.1 * (-sl2c_iSigma1 : SL2C).1ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2c_iSigma1, Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_apply,
      Fin.sum_univ_two]

lemma stdRep_sigma_iSigma3 :
    stdRep.σ (sl2c_iSigma3, -sl2c_iSigma3) = Matrix.diagonal ![1, -1, -1, 1] := by
  change spinorPhi_matrix sl2c_iSigma3 (-sl2c_iSigma3) = Matrix.diagonal ![1, -1, -1, 1]
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_three, Complex.I_mul_I, mul_neg_one]
  have hd2 : (![1, -1, -1, 1] : Fin 4 → ℂ) 2 = -1 := rfl
  have hd3 : (![1, -1, -1, 1] : Fin 4 → ℂ) 3 = 1 := rfl
  have h_act : sl2c_iSigma3.1 * vec_to_spinor x * (-sl2c_iSigma3 : SL2C).1ᵀ =
      vec_to_spinor ((Matrix.diagonal ![1, -1, -1, 1]).mulVec x) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      { simp only [sl2c_iSigma3, Matrix.SpecialLinearGroup.coe_neg, vec_to_spinor,
          sigma_0, sigma_1, sigma_2, sigma_3, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.mulVec_diagonal, Fin.sum_univ_two, Fin.isValue]
        repeat rw [Fin.zero_eta]
        repeat rw [Fin.mk_one]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        repeat rw [hd2]
        repeat rw [hd3]
        ring_nf
        repeat rw [Complex.I_sq]
        repeat rw [hI3]
        ring }
  unfold spinor_action
  rw [h_act, spinor_to_vec_left_inv]

lemma stdRep_sigma_iSigma1 :
    stdRep.σ (sl2c_iSigma1, -sl2c_iSigma1) = Matrix.diagonal ![1, 1, -1, -1] := by
  change spinorPhi_matrix sl2c_iSigma1 (-sl2c_iSigma1) = Matrix.diagonal ![1, 1, -1, -1]
  apply matrix_eq_of_mulVec_eq
  intro x
  rw [spinorPhi_matrix_mulVec]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_three, Complex.I_mul_I, mul_neg_one]
  have hd2 : (![1, 1, -1, -1] : Fin 4 → ℂ) 2 = -1 := rfl
  have hd3 : (![1, 1, -1, -1] : Fin 4 → ℂ) 3 = -1 := rfl
  have h_act : sl2c_iSigma1.1 * vec_to_spinor x * (-sl2c_iSigma1 : SL2C).1ᵀ =
      vec_to_spinor ((Matrix.diagonal ![1, 1, -1, -1]).mulVec x) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      { simp only [sl2c_iSigma1, Matrix.SpecialLinearGroup.coe_neg, vec_to_spinor,
          sigma_0, sigma_1, sigma_2, sigma_3, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.neg_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.mulVec_diagonal, Fin.sum_univ_two, Fin.isValue]
        repeat rw [Fin.zero_eta]
        repeat rw [Fin.mk_one]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        repeat rw [hd2]
        repeat rw [hd3]
        ring_nf
        repeat rw [Complex.I_sq]
        repeat rw [hI3]
        ring }
  unfold spinor_action
  rw [h_act, spinor_to_vec_left_inv]

lemma H_two_timeAxis_eq_of_diagonal_stabilizer {W : WightmanFamily ι}
    {R : HolomorphicLorentzRep ι} (E : TubeExtension W) (h_ccov : ComplexCovariant R E)
    (A B : SL2C) (hAB : A.1 * B.1ᵀ = 1) (d : ι → ℂ)
    (hd : R.σ (A, B) = Matrix.diagonal d)
    {t : ℝ} (ht : 0 < t) (α : Fin 2 → ι) :
    E.H 2 α ![0, timeAxisVecC (Complex.I * (t : ℂ))] =
      (d (α 0) * d (α 1)) * E.H 2 α ![0, timeAxisVecC (Complex.I * (t : ℂ))] := by
  let z_t : Fin 2 → Fin 4 → ℂ := ![0, timeAxisVecC (Complex.I * (t : ℂ))]
  have hz_t : z_t ∈ forward_tube_n 2 := origin_timeAxisVecC_mem_forward_tube_two ht
  have h_fix : spinorPhi (A, B) • z_t = z_t := by
    dsimp [z_t]
    rw [spinorPhi_smul_origin_pair, spinor_action_timeAxisVecC_of_mul_transpose_eq_one A B hAB]
  have h_cov := h_ccov 2 A B z_t hz_t (by rwa [h_fix]) α
  rw [h_fix] at h_cov
  have h_prod : ∀ β : Fin 2 → ι,
      (∏ i : Fin 2, R.σ (A, B) (α i) (β i)) =
        if α = β then d (α 0) * d (α 1) else 0 := by
    intro β
    rw [hd, Fin.prod_univ_two]
    by_cases h : α = β
    · subst h
      simp
    · rw [if_neg h]
      by_cases h0 : α 0 = β 0
      · have h1 : α 1 ≠ β 1 := by
          intro h1
          apply h
          ext i
          fin_cases i <;> assumption
        rw [Matrix.diagonal_apply_ne _ h1, mul_zero]
      · rw [Matrix.diagonal_apply_ne _ h0, zero_mul]
  simp_rw [h_prod] at h_cov
  simpa using h_cov

lemma stdRep_H_two_timeAxis_offDiag_eq_zero {W : WightmanFamily (Fin 4)}
    (E : TubeExtension W) (h_ccov : ComplexCovariant stdRep E)
    {t : ℝ} (ht : 0 < t) (β : Fin 2 → Fin 4) (hne : β 0 ≠ β 1) :
    E.H 2 β ![0, timeAxisVecC (Complex.I * (t : ℂ))] = 0 := by
  have h3 := H_two_timeAxis_eq_of_diagonal_stabilizer E h_ccov
    sl2c_iSigma3 (-sl2c_iSigma3) sl2c_iSigma3_mul_neg_transpose
    ![1, -1, -1, 1] stdRep_sigma_iSigma3 ht β
  have h1 := H_two_timeAxis_eq_of_diagonal_stabilizer E h_ccov
    sl2c_iSigma1 (-sl2c_iSigma1) sl2c_iSigma1_mul_neg_transpose
    ![1, 1, -1, -1] stdRep_sigma_iSigma1 ht β
  have : ∀ a b : Fin 4, a ≠ b →
      ((![1, -1, -1, 1] : Fin 4 → ℂ) a * (![1, -1, -1, 1] : Fin 4 → ℂ) b = -1) ∨
      ((![1, 1, -1, -1] : Fin 4 → ℂ) a * (![1, 1, -1, -1] : Fin 4 → ℂ) b = -1) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
  rcases this (β 0) (β 1) hne with hs3 | hs1
  · rw [hs3] at h3
    linear_combination (1 / 2 : ℂ) * h3
  · rw [hs1] at h1
    linear_combination (1 / 2 : ℂ) * h1

lemma leftWeylRep_H_two_timeAxis_antisymm {W : WightmanFamily (Fin 2)}
    (E : TubeExtension W) (h_ccov : ComplexCovariant leftWeylRep E)
    {t : ℝ} (ht : 0 < t) :
    E.H 2 ![0, 0] ![0, timeAxisVecC (Complex.I * (t : ℂ))] = 0 ∧
    E.H 2 ![1, 1] ![0, timeAxisVecC (Complex.I * (t : ℂ))] = 0 ∧
    E.H 2 ![0, 1] ![0, timeAxisVecC (Complex.I * (t : ℂ))] =
      - E.H 2 ![1, 0] ![0, timeAxisVecC (Complex.I * (t : ℂ))] := by
  let z_t : Fin 2 → Fin 4 → ℂ := ![0, timeAxisVecC (Complex.I * (t : ℂ))]
  have hd3 : leftWeylRep.σ (sl2c_iSigma3, -sl2c_iSigma3) =
      Matrix.diagonal ![Complex.I, -Complex.I] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h00 := H_two_timeAxis_eq_of_diagonal_stabilizer E h_ccov
    sl2c_iSigma3 (-sl2c_iSigma3) sl2c_iSigma3_mul_neg_transpose
    ![Complex.I, -Complex.I] hd3 ht ![0, 0]
  have h11 := H_two_timeAxis_eq_of_diagonal_stabilizer E h_ccov
    sl2c_iSigma3 (-sl2c_iSigma3) sl2c_iSigma3_mul_neg_transpose
    ![Complex.I, -Complex.I] hd3 ht ![1, 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul_neg, Complex.I_mul_I] at h00 h11
  have hz_t : z_t ∈ forward_tube_n 2 := origin_timeAxisVecC_mem_forward_tube_two ht
  have h_fix1 : spinorPhi (sl2c_iSigma1, -sl2c_iSigma1) • z_t = z_t := by
    dsimp [z_t]
    rw [spinorPhi_smul_origin_pair,
      spinor_action_timeAxisVecC_of_mul_transpose_eq_one _ _ sl2c_iSigma1_mul_neg_transpose]
  have h01 := h_ccov 2 sl2c_iSigma1 (-sl2c_iSigma1) z_t hz_t (by rwa [h_fix1]) ![0, 1]
  rw [h_fix1] at h01
  refine ⟨by linear_combination (1 / 2 : ℂ) * h00, by linear_combination (1 / 2 : ℂ) * h11, ?_⟩
  let e2 : (Fin 2 × Fin 2) ≃ (Fin 2 → Fin 2) :=
    { toFun := fun p => ![p.1, p.2]
      invFun := fun β => (β 0, β 1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun β => by ext i; fin_cases i <;> rfl }
  rw [← e2.sum_comp, Fintype.sum_prod_type] at h01
  simp_rw [Fin.sum_univ_two] at h01
  simp only [e2, Equiv.coe_fn_mk, Fin.prod_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h01
  have h_s00 : leftWeylRep.σ (sl2c_iSigma1, -sl2c_iSigma1) 0 0 = 0 := rfl
  have h_s11 : leftWeylRep.σ (sl2c_iSigma1, -sl2c_iSigma1) 1 1 = 0 := rfl
  have h_s01 : leftWeylRep.σ (sl2c_iSigma1, -sl2c_iSigma1) 0 1 = Complex.I := rfl
  have h_s10 : leftWeylRep.σ (sl2c_iSigma1, -sl2c_iSigma1) 1 0 = Complex.I := rfl
  rw [h_s00, h_s11, h_s01, h_s10] at h01
  simp only [zero_mul, mul_zero, zero_add, add_zero, Complex.I_mul_I, neg_one_mul] at h01
  exact h01

lemma imagConeVec_mem_forward_tube_two {y : Fin 4 → ℝ} (hy : y ∈ forward_light_cone) :
    ![0, fun k => Complex.I * (y k : ℂ)] ∈ forward_tube_n 2 := by
  intro i hi
  fin_cases i
  · change (fun k : Fin 4 =>
      -((![0, fun k => Complex.I * (y k : ℂ)] (0 : Fin 2) -
        ![0, fun k => Complex.I * (y k : ℂ)] (1 : Fin 2)) k).im) ∈ forward_light_cone
    have h_im : (fun k : Fin 4 =>
        -((![0, fun k => Complex.I * (y k : ℂ)] (0 : Fin 2) -
          ![0, fun k => Complex.I * (y k : ℂ)] (1 : Fin 2)) k).im) = y := by
      ext k
      simp
    rwa [h_im]
  · simp at hi

lemma exists_sl2c_left_orbit_imagCone {y : Fin 4 → ℝ} (hy : y ∈ forward_light_cone) :
    ∃ (t : ℝ) (_ : 0 < t) (A : SL2C),
      spinorPhi (A, 1) • (![0, timeAxisVecC (Complex.I * (t : ℂ))] : Fin 2 → Fin 4 → ℂ) =
        ![0, fun k => Complex.I * (y k : ℂ)] := by
  let t : ℝ := Real.sqrt (minkowskiInner y y)
  have ht : 0 < t := Real.sqrt_pos.mpr hy.2
  let c : ℂ := Complex.I * (t : ℂ)
  have hc_ne : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  let ζ : Fin 4 → ℂ := fun k => Complex.I * (y k : ℂ)
  have hdet : (vec_to_spinor ζ).det = c ^ 2 := by
    rw [vec_to_spinor_det]
    dsimp [ζ, c, t]
    have hsq : (Real.sqrt (minkowskiInner y y)) ^ 2 = minkowskiInner y y :=
      Real.sq_sqrt hy.2.le
    have hm := minkowskiInner_explicit y
    calc (Complex.I * ↑(y 0)) ^ 2 - (Complex.I * ↑(y 1)) ^ 2 -
          (Complex.I * ↑(y 2)) ^ 2 - (Complex.I * ↑(y 3)) ^ 2
      _ = Complex.I ^ 2 * ((y 0 : ℂ) ^ 2 - (y 1 : ℂ) ^ 2 - (y 2 : ℂ) ^ 2 - (y 3 : ℂ) ^ 2) := by
          ring
      _ = Complex.I ^ 2 * ((minkowskiInner y y : ℝ) : ℂ) := by
          rw [hm]
          push_cast
          ring
      _ = (Complex.I * ↑(Real.sqrt (minkowskiInner y y))) ^ 2 := by
          rw [mul_pow, ← Complex.ofReal_pow, hsq]
  have hA_det : (c⁻¹ • vec_to_spinor ζ).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hdet, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hc_ne)]
  let A : SL2C := ⟨c⁻¹ • vec_to_spinor ζ, hA_det⟩
  refine ⟨t, ht, A, ?_⟩
  rw [spinorPhi_smul_origin_pair]
  have h_act : spinor_action A.1 (1 : SL2C).1 (timeAxisVecC c) = ζ := by
    unfold spinor_action
    have hA_val : A.1 = c⁻¹ • vec_to_spinor ζ := rfl
    have h1_val : (1 : SL2C).1ᵀ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := Matrix.transpose_one
    rw [hA_val, h1_val, vec_to_spinor_timeAxisVecC, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
      mul_inv_cancel₀ hc_ne, one_smul, spinor_to_vec_left_inv]
  rw [h_act]

lemma exists_sl2c_right_orbit_imagCone {y : Fin 4 → ℝ} (hy : y ∈ forward_light_cone) :
    ∃ (t : ℝ) (_ : 0 < t) (B : SL2C),
      spinorPhi (1, B) • (![0, timeAxisVecC (Complex.I * (t : ℂ))] : Fin 2 → Fin 4 → ℂ) =
        ![0, fun k => Complex.I * (y k : ℂ)] := by
  let t : ℝ := Real.sqrt (minkowskiInner y y)
  have ht : 0 < t := Real.sqrt_pos.mpr hy.2
  let c : ℂ := Complex.I * (t : ℂ)
  have hc_ne : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')
  let ζ : Fin 4 → ℂ := fun k => Complex.I * (y k : ℂ)
  have hdet : (vec_to_spinor ζ).det = c ^ 2 := by
    rw [vec_to_spinor_det]
    dsimp [ζ, c, t]
    have hsq : (Real.sqrt (minkowskiInner y y)) ^ 2 = minkowskiInner y y :=
      Real.sq_sqrt hy.2.le
    have hm := minkowskiInner_explicit y
    calc (Complex.I * ↑(y 0)) ^ 2 - (Complex.I * ↑(y 1)) ^ 2 -
          (Complex.I * ↑(y 2)) ^ 2 - (Complex.I * ↑(y 3)) ^ 2
      _ = Complex.I ^ 2 * ((y 0 : ℂ) ^ 2 - (y 1 : ℂ) ^ 2 - (y 2 : ℂ) ^ 2 - (y 3 : ℂ) ^ 2) := by
          ring
      _ = Complex.I ^ 2 * ((minkowskiInner y y : ℝ) : ℂ) := by
          rw [hm]
          push_cast
          ring
      _ = (Complex.I * ↑(Real.sqrt (minkowskiInner y y))) ^ 2 := by
          rw [mul_pow, ← Complex.ofReal_pow, hsq]
  have hB_det : ((c⁻¹ • vec_to_spinor ζ)ᵀ).det = 1 := by
    rw [Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, hdet, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero 2 hc_ne)]
  let B : SL2C := ⟨(c⁻¹ • vec_to_spinor ζ)ᵀ, hB_det⟩
  refine ⟨t, ht, B, ?_⟩
  rw [spinorPhi_smul_origin_pair]
  have h_act : spinor_action (1 : SL2C).1 B.1 (timeAxisVecC c) = ζ := by
    unfold spinor_action
    have h1_val : (1 : SL2C).1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := rfl
    have hB_val : B.1ᵀ = c⁻¹ • vec_to_spinor ζ := Matrix.transpose_transpose _
    rw [h1_val, hB_val, vec_to_spinor_timeAxisVecC, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      inv_mul_cancel₀ hc_ne, one_smul, spinor_to_vec_left_inv]
  rw [h_act]

omit [Fintype ι] [DecidableEq ι] in
theorem H_two_origin_exchange_of_imagCone {W : WightmanFamily ι}
    (E : TubeExtension W) (ε : ℂ)
    (h_cone : ∀ y ∈ forward_light_cone, ∀ α : Fin 2 → ι,
      E.H 2 α ![0, fun k => Complex.I * (y k : ℂ)] =
        ε * E.H 2 (α ∘ Fin.rev) ![0, fun k => Complex.I * (y k : ℂ)])
    (α : Fin 2 → ι) (w : Fin 4 → ℂ) (hw : ![0, w] ∈ forward_tube_n 2) :
    E.H 2 α ![0, w] = ε * E.H 2 (α ∘ Fin.rev) ![0, w] := by
  let reMap : (Fin 4 → ℂ) → (Fin 4 → ℝ) := fun u k => (u k).re
  have h_reMap_cont : Continuous reMap :=
    continuous_pi fun k => Complex.continuous_re.comp (continuous_apply k)
  let Ω : Set (Fin 4 → ℂ) := reMap ⁻¹' forward_light_cone
  have hΩ_open : IsOpen Ω := forward_light_cone_isOpen.preimage h_reMap_cont
  have hΩ_conv : Convex ℝ Ω := by
    intro u₁ hu₁ u₂ hu₂ a b ha hb hab
    have h_lin : reMap (a • u₁ + b • u₂) = a • reMap u₁ + b • reMap u₂ := by
      ext k
      simp [reMap]
    change reMap (a • u₁ + b • u₂) ∈ forward_light_cone
    rw [h_lin]
    exact forward_light_cone_convex hu₁ hu₂ ha hb hab
  let embedL : (Fin 4 → ℂ) →L[ℂ] (Fin 2 → Fin 4 → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      if i = 0 then 0 else Complex.I • ContinuousLinearMap.id ℂ (Fin 4 → ℂ)
  have h_embed_eq : ∀ u : Fin 4 → ℂ,
      embedL u = ![0, fun k => Complex.I * u k] := by
    intro u
    ext i k
    fin_cases i <;> simp [embedL]
  have h_embed_tube : ∀ u ∈ Ω, embedL u ∈ forward_tube_n 2 := by
    intro u hu
    rw [h_embed_eq]
    intro i hi
    fin_cases i
    · change (fun k : Fin 4 =>
        -((![0, fun k => Complex.I * u k] (0 : Fin 2) -
          ![0, fun k => Complex.I * u k] (1 : Fin 2)) k).im) ∈ forward_light_cone
      have h_im : (fun k : Fin 4 =>
          -((![0, fun k => Complex.I * u k] (0 : Fin 2) -
            ![0, fun k => Complex.I * u k] (1 : Fin 2)) k).im) = reMap u := by
        ext k
        simp [reMap]
      rw [h_im]
      exact hu
    · simp at hi
  let F : (Fin 4 → ℂ) → ℂ :=
    fun u => E.H 2 α (embedL u) - ε * E.H 2 (α ∘ Fin.rev) (embedL u)
  have hF_an : AnalyticOnNhd ℂ F Ω := by
    intro u hu
    have h1 : AnalyticAt ℂ (E.H 2 α) (embedL u) :=
      (E.analytic 2 α).analyticAt ((forward_tube_n_isOpen 2).mem_nhds (h_embed_tube u hu))
    have h2 : AnalyticAt ℂ (E.H 2 (α ∘ Fin.rev)) (embedL u) :=
      (E.analytic 2 (α ∘ Fin.rev)).analyticAt
        ((forward_tube_n_isOpen 2).mem_nhds (h_embed_tube u hu))
    exact (h1.comp (embedL.analyticAt u)).sub
      (analyticAt_const.mul (h2.comp (embedL.analyticAt u)))
  have hF_zero : Set.EqOn F 0 Ω := by
    refine Distribution.analyticOnNhd_eqOn_zero_of_real_open hΩ_open hΩ_conv.isPreconnected
      hF_an forward_light_cone_isOpen ⟨unit_time_vector, unit_time_vector_mem_forward_light_cone⟩
      (fun y hy => ?_) (fun y hy => ?_)
    · change (fun k => ((y k : ℂ)).re) ∈ forward_light_cone
      simpa using hy
    · dsimp [F]
      rw [h_embed_eq]
      exact sub_eq_zero.mpr (h_cone y hy α)
  let u₀ : Fin 4 → ℂ := fun k => -Complex.I * w k
  have hu₀ : u₀ ∈ Ω := by
    have hw_cone : (fun k => -((![0, w] (0 : Fin 2) - ![0, w] (1 : Fin 2)) k).im) ∈
        forward_light_cone := hw (0 : Fin 2) (by decide)
    have h_eq : reMap u₀ = fun k => -((![0, w] (0 : Fin 2) - ![0, w] (1 : Fin 2)) k).im := by
      ext k
      simp [reMap, u₀]
    change reMap u₀ ∈ forward_light_cone
    rwa [h_eq]
  have h_emb_u₀ : embedL u₀ = ![0, w] := by
    rw [h_embed_eq]
    ext i k
    fin_cases i
    · rfl
    · simp [u₀, ← mul_assoc]
  have hz0 := hF_zero hu₀
  dsimp [F] at hz0
  rw [h_emb_u₀] at hz0
  exact sub_eq_zero.mp hz0

theorem stdRep_H_two_origin_symm {W : WightmanFamily (Fin 4)}
    (E : TubeExtension W) (h_cov : TubeCovariant stdRep E)
    (α : Fin 2 → Fin 4) (w : Fin 4 → ℂ) (hw : ![0, w] ∈ forward_tube_n 2) :
    E.H 2 α ![0, w] = E.H 2 (α ∘ Fin.rev) ![0, w] := by
  have h_ccov := complex_covariance_of_real stdRep W E h_cov
  have h1 := H_two_origin_exchange_of_imagCone E 1 (fun y hy β => ?_) α w hw
  · simpa using h1
  · obtain ⟨t, ht, A, hA⟩ := exists_sl2c_left_orbit_imagCone hy
    let z_t : Fin 2 → Fin 4 → ℂ := ![0, timeAxisVecC (Complex.I * (t : ℂ))]
    have hz_t : z_t ∈ forward_tube_n 2 := origin_timeAxisVecC_mem_forward_tube_two ht
    have hz_y : ![0, fun k => Complex.I * (y k : ℂ)] ∈ forward_tube_n 2 :=
      imagConeVec_mem_forward_tube_two hy
    have h_lhs := h_ccov 2 A 1 z_t hz_t (by rwa [hA]) β
    have h_rhs := h_ccov 2 A 1 z_t hz_t (by rwa [hA]) (β ∘ Fin.rev)
    rw [hA] at h_lhs h_rhs
    rw [one_mul, h_lhs, h_rhs]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    by_cases hγ : γ 0 = γ 1
    · rw [Fin.prod_univ_two, Fin.prod_univ_two]
      have hrev0 : (β ∘ Fin.rev) 0 = β 1 := rfl
      have hrev1 : (β ∘ Fin.rev) 1 = β 0 := rfl
      rw [hrev0, hrev1, ← hγ]
      ring
    · rw [stdRep_H_two_timeAxis_offDiag_eq_zero E h_ccov ht γ hγ, mul_zero, mul_zero]

theorem leftWeylRep_H_two_origin_antisymm {W : WightmanFamily (Fin 2)}
    (E : TubeExtension W) (h_cov : TubeCovariant leftWeylRep E)
    (α : Fin 2 → Fin 2) (w : Fin 4 → ℂ) (hw : ![0, w] ∈ forward_tube_n 2) :
    E.H 2 α ![0, w] = (-1 : ℂ) * E.H 2 (α ∘ Fin.rev) ![0, w] := by
  have h_ccov := complex_covariance_of_real leftWeylRep W E h_cov
  refine H_two_origin_exchange_of_imagCone E (-1) (fun y hy β => ?_) α w hw
  obtain ⟨t, ht, A, hA⟩ := exists_sl2c_left_orbit_imagCone hy
  let z_t : Fin 2 → Fin 4 → ℂ := ![0, timeAxisVecC (Complex.I * (t : ℂ))]
  have hz_t : z_t ∈ forward_tube_n 2 := origin_timeAxisVecC_mem_forward_tube_two ht
  have hz_y : ![0, fun k => Complex.I * (y k : ℂ)] ∈ forward_tube_n 2 :=
    imagConeVec_mem_forward_tube_two hy
  obtain ⟨h00, h11, h01⟩ := leftWeylRep_H_two_timeAxis_antisymm E h_ccov ht
  have h_lhs := h_ccov 2 A 1 z_t hz_t (by rwa [hA]) β
  have h_rhs := h_ccov 2 A 1 z_t hz_t (by rwa [hA]) (β ∘ Fin.rev)
  rw [hA] at h_lhs h_rhs
  have h_eval : ∀ γ : Fin 2 → Fin 2,
      (∑ δ : Fin 2 → Fin 2, (∏ i : Fin 2, leftWeylRep.σ (A, 1) (γ i) (δ i)) * E.H 2 δ z_t) =
        (A.1 (γ 0) 1 * A.1 (γ 1) 0 - A.1 (γ 0) 0 * A.1 (γ 1) 1) * E.H 2 ![1, 0] z_t := by
    intro γ
    let e2 : (Fin 2 × Fin 2) ≃ (Fin 2 → Fin 2) :=
      { toFun := fun p => ![p.1, p.2]
        invFun := fun δ => (δ 0, δ 1)
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun δ => by ext i; fin_cases i <;> rfl }
    rw [← e2.sum_comp, Fintype.sum_prod_type]
    simp_rw [Fin.sum_univ_two]
    dsimp only [e2, Equiv.coe_fn_mk, z_t]
    simp only [Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      h00, h11, h01]
    have hL : ∀ p q : Fin 2, leftWeylRep.σ (A, 1) p q = A.1 p q := fun _ _ => rfl
    simp only [hL]
    ring
  rw [h_lhs, h_rhs, h_eval β, h_eval (β ∘ Fin.rev)]
  have hrev0 : (β ∘ Fin.rev) 0 = β 1 := rfl
  have hrev1 : (β ∘ Fin.rev) 1 = β 0 := rfl
  rw [hrev0, hrev1]
  ring

lemma tubePTScalar_of_hasPTScalar_one (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    (h : R.HasPTScalar 1) (E : TubeExtension W) : TubePTScalar R E := by
  intro n α z _hz
  rw [h]
  have h_prod : ∀ β : Fin n → ι,
      (∏ i : Fin n, ((1 : ℂ) • (1 : Matrix ι ι ℂ)) (α i) (β i)) =
        if α = β then 1 else 0 := by
    intro β
    by_cases hab : α = β
    · subst hab
      simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one, Finset.prod_const_one]
    · rw [if_neg hab]
      obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
        by_contra hc
        push Not at hc
        exact hab (funext hc)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [Matrix.smul_apply, Matrix.one_apply_ne hi, smul_zero]
  simp_rw [h_prod]
  simp

lemma tubePCT_two_of_hasPTScalar (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    {η δ : ℂ} (hδ : R.HasPTScalar δ) (hδ_sq : δ ^ 2 = 1) (E : TubeExtension W)
    (hpct : TubePCT η R E) (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = η * E.H 2 (α ∘ Fin.rev) z :=
  tubePCT_two_of_scalar_pt R E hδ hδ_sq hpct α z hz

lemma tubePCT_two_diag_of_hasDiagInvolutivePT (R : HolomorphicLorentzRep ι) {W : WightmanFamily ι}
    {η : ℂ} (hpt : R.HasDiagInvolutivePT) (E : TubeExtension W)
    (hpct : TubePCT η R E) (c : ι) (z : Fin 2 → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n 2) :
    E.H 2 (fun _ => c) (-(z ∘ Fin.rev)) = η * E.H 2 (fun _ => c) z := by
  obtain ⟨δ, hδ_sq, hδ_entry⟩ := hpt
  have h := hpct 2 (fun _ => c) z hz
  rw [two_mul_two_sub_one_div_two, pow_one] at h
  have h_prod : ∀ β : Fin 2 → ι,
      (∏ i : Fin 2, R.σ (-1, 1) c (β i)) = if β = fun _ => c then 1 else 0 := by
    intro β
    by_cases hbc : β = fun _ => c
    · subst hbc
      simp only [↓reduceIte, hδ_entry c c, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hδ_sq c]
    · rw [if_neg hbc]
      obtain ⟨i, hi⟩ : ∃ i, c ≠ β i := by
        by_contra hc
        push Not at hc
        exact hbc (funext fun j => (hc j).symm)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hδ_entry c (β i), if_neg hi]
  simp_rw [h_prod, ite_mul, one_mul, zero_mul] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  exact h

theorem wightman_pct_of_spectrumCondition (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) :
    WightmanPCT η R W := by
  obtain ⟨E, hcov, htrans⟩ := exists_tube_extension_of_spectrumCondition R W hspec hP
  exact wightman_pct_of_weakLocality_general R W E hcov htrans hloc

section UnconditionalSpinStatistics

open scoped ComplexOrder

lemma StarStructure.map_star_mul_self {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    S.C.map star * S.C = 1 :=
  mul_eq_one_comm.mp S.involutive

lemma StarStructure.mul_sigma_pt_eq_spinParity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) {ε : ℂ} (hε : R.HasSpinParity ε) :
    S.C * R.σ (-1, 1) = ε • ((R.σ (-1, 1)).map star * S.C) := by
  have h_tp : R.σ (1, -1) = ε • R.σ (-1, 1) := by
    calc R.σ (1, -1)
        = 1 * R.σ (1, -1) := (Matrix.one_mul _).symm
      _ = (R.σ (-1, 1) * R.σ (-1, 1)) * R.σ (1, -1) := by rw [sigma_pt_mul_self]
      _ = R.σ (-1, 1) * (R.σ (-1, 1) * R.σ (1, -1)) := Matrix.mul_assoc _ _ _
      _ = R.σ (-1, 1) * (ε • 1) := by rw [sigma_pt_mul_sigma_tp_eq_spinParity R ε hε]
      _ = ε • R.σ (-1, 1) := by rw [Matrix.mul_smul, Matrix.mul_one]
  have h_star_ε : star ε = ε := by
    rcases hε.2 with rfl | rfl <;> simp
  have h_map : (R.σ (1, -1)).map star = ε • (R.σ (-1, 1)).map star := by
    rw [h_tp]
    ext i j
    change star (ε * R.σ (-1, 1) i j) = ε * star (R.σ (-1, 1) i j)
    rw [star_mul', h_star_ε]
  rw [starStructure_intertwine_pt S, h_map, Matrix.smul_mul]

omit [DecidableEq ι] in
def matrixSesq (H : Matrix ι ι ℂ) (u v : ι → ℂ) : ℂ :=
  ∑ a : ι, ∑ c : ι, star (u a) * H a c * v c

lemma matrixSesq_single (H : Matrix ι ι ℂ) (a c : ι) :
    matrixSesq H (Pi.single a 1) (Pi.single c 1) = H a c := by
  unfold matrixSesq
  rw [Fintype.sum_eq_single a (fun r hr => by simp [Pi.single_eq_of_ne hr]),
    Fintype.sum_eq_single c (fun s hs => by simp [Pi.single_eq_of_ne hs])]
  simp

omit [DecidableEq ι] in
lemma matrixSesq_linear_comb (H : Matrix ι ι ℂ) (u v : ι → ℂ) (z : ℂ) :
    matrixSesq H (fun a => z * u a + v a) (fun a => z * u a + v a) =
      (star z * z) * matrixSesq H u u + star z * matrixSesq H u v +
        z * matrixSesq H v u + matrixSesq H v v := by
  unfold matrixSesq
  have h_term : ∀ a c : ι,
      star (z * u a + v a) * H a c * (z * u c + v c) =
        (star z * z) * (star (u a) * H a c * u c) +
          star z * (star (u a) * H a c * v c) +
          z * (star (v a) * H a c * u c) +
          (star (v a) * H a c * v c) := by
    intro a c
    rw [star_add, star_mul']
    ring
  simp_rw [h_term, Finset.sum_add_distrib, ← Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in
lemma star_eq_self_of_complex_nonneg {w : ℂ} (hw : 0 ≤ w) : star w = w := by
  have him : w.im = 0 := (Complex.nonneg_iff.mp hw).2.symm
  rw [Complex.star_def]
  exact Complex.ext (Complex.conj_re w) (by rw [Complex.conj_im, him, neg_zero])

omit [DecidableEq ι] in
lemma matrix_conjTranspose_eq_self_of_matrixSesq_nonneg {H : Matrix ι ι ℂ}
    (hH : ∀ u : ι → ℂ, 0 ≤ matrixSesq H u u) :
    H.conjTranspose = H := by
  classical
  have h_sesq_symm : ∀ u v : ι → ℂ, star (matrixSesq H u v) = matrixSesq H v u := by
    intro u v
    let X := matrixSesq H u v
    let Y := matrixSesq H v u
    have huu : star (matrixSesq H u u) = matrixSesq H u u :=
      star_eq_self_of_complex_nonneg (hH u)
    have hvv : star (matrixSesq H v v) = matrixSesq H v v :=
      star_eq_self_of_complex_nonneg (hH v)
    have h1 : star X + star Y = X + Y := by
      have hw := star_eq_self_of_complex_nonneg (hH (fun a => (1 : ℂ) * u a + v a))
      rw [matrixSesq_linear_comb] at hw
      simp only [star_one, one_mul, star_add, huu, hvv] at hw
      dsimp only [X, Y]
      linear_combination hw
    have h2 : Complex.I * star X - Complex.I * star Y = -Complex.I * X + Complex.I * Y := by
      have hw := star_eq_self_of_complex_nonneg (hH (fun a => Complex.I * u a + v a))
      rw [matrixSesq_linear_comb] at hw
      have hI_star : star Complex.I = -Complex.I := by
        rw [Complex.star_def, Complex.conj_I]
      have hI_norm : star Complex.I * Complex.I = 1 := by
        rw [hI_star, neg_mul, Complex.I_mul_I, neg_neg]
      rw [hI_norm, one_mul] at hw
      simp only [star_add, star_mul', hI_star, star_neg, neg_neg, huu, hvv] at hw
      dsimp only [X, Y]
      linear_combination hw
    have h2' : -star X + star Y = X - Y := by
      have hmul := congr_arg (Complex.I * ·) h2
      have hL : Complex.I * (Complex.I * star X - Complex.I * star Y) = -star X + star Y := by
        calc Complex.I * (Complex.I * star X - Complex.I * star Y)
            = (Complex.I * Complex.I) * star X - (Complex.I * Complex.I) * star Y := by ring
          _ = -star X + star Y := by rw [Complex.I_mul_I]; ring
      have hR : Complex.I * (-Complex.I * X + Complex.I * Y) = X - Y := by
        calc Complex.I * (-Complex.I * X + Complex.I * Y)
            = -(Complex.I * Complex.I) * X + (Complex.I * Complex.I) * Y := by ring
          _ = X - Y := by rw [Complex.I_mul_I]; ring
      rwa [hL, hR] at hmul
    change star X = Y
    linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2'
  ext i j
  rw [Matrix.conjTranspose_apply, ← matrixSesq_single H j i,
    h_sesq_symm (Pi.single j 1) (Pi.single i 1), matrixSesq_single]

omit [DecidableEq ι] in
lemma matrix_eq_zero_of_matrixSesq_eq_zero {H : Matrix ι ι ℂ}
    (hH : ∀ u : ι → ℂ, matrixSesq H u u = 0) :
    H = 0 := by
  classical
  ext i j
  rw [Matrix.zero_apply, ← matrixSesq_single H i j]
  let u : ι → ℂ := Pi.single i 1
  let v : ι → ℂ := Pi.single j 1
  let X := matrixSesq H u v
  let Y := matrixSesq H v u
  have h1 : X + Y = 0 := by
    have hw := hH (fun a => (1 : ℂ) * u a + v a)
    rw [matrixSesq_linear_comb, hH u, hH v] at hw
    simp only [star_one, one_mul, mul_zero, zero_add, add_zero] at hw
    exact hw
  have h2 : -Complex.I * X + Complex.I * Y = 0 := by
    have hw := hH (fun a => Complex.I * u a + v a)
    rw [matrixSesq_linear_comb, hH u, hH v] at hw
    have hI_star : star Complex.I = -Complex.I := by
      rw [Complex.star_def, Complex.conj_I]
    rw [hI_star] at hw
    simp only [mul_zero, zero_add, add_zero] at hw
    exact hw
  have h2' : X - Y = 0 := by
    have hmul := congr_arg (Complex.I * ·) h2
    have hL : Complex.I * (-Complex.I * X + Complex.I * Y) = X - Y := by
      calc Complex.I * (-Complex.I * X + Complex.I * Y)
          = -(Complex.I * Complex.I) * X + (Complex.I * Complex.I) * Y := by ring
        _ = X - Y := by rw [Complex.I_mul_I]; ring
    rwa [hL, mul_zero] at hmul
  change X = 0
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2'

omit [DecidableEq ι] in
lemma matrixSesq_congr_map_star_nonneg {H : Matrix ι ι ℂ}
    (hH : ∀ u : ι → ℂ, 0 ≤ matrixSesq H u u) (Q : Matrix ι ι ℂ) (u : ι → ℂ) :
    0 ≤ matrixSesq (Q * H.map star * Q.conjTranspose) u u := by
  let v : ι → ℂ := fun b => ∑ a : ι, star (u a) * Q a b
  have h_eq : matrixSesq (Q * H.map star * Q.conjTranspose) u u = star (matrixSesq H v v) := by
    have hL : matrixSesq (Q * H.map star * Q.conjTranspose) u u =
        ∑ b : ι, ∑ d : ι, v b * star (H b d) * star (v d) := by
      unfold matrixSesq
      have h_inner : ∀ a : ι,
          (∑ c : ι, star (u a) * (Q * H.map star * Q.conjTranspose) a c * u c) =
            ∑ b : ι, ∑ d : ι, (star (u a) * Q a b) * star (H b d) * star (v d) := by
        intro a
        have h_ac : ∀ c : ι,
            star (u a) * (Q * H.map star * Q.conjTranspose) a c * u c =
              ∑ b : ι, ∑ d : ι,
                (star (u a) * Q a b) * star (H b d) * (u c * star (Q c d)) := by
          intro c
          have h_mat : (Q * H.map star * Q.conjTranspose) a c =
              ∑ b : ι, ∑ d : ι, Q a b * star (H b d) * star (Q c d) := by
            simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
              Finset.sum_mul]
            exact Finset.sum_comm
          rw [h_mat, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
        simp_rw [h_ac]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        change (∑ c : ι, u c * star (Q c d)) = star (∑ c : ι, star (u c) * Q c d)
        rw [star_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [star_mul, star_star, mul_comm]
      simp_rw [h_inner]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hR : star (matrixSesq H v v) =
        ∑ b : ι, ∑ d : ι, v b * star (H b d) * star (v d) := by
      unfold matrixSesq
      rw [star_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [star_mul, star_star]
      ring
    exact hL.trans hR.symm
  rw [h_eq, star_eq_self_of_complex_nonneg (hH v)]
  exact hH v

theorem eq_zero_of_psd_pct_pair_ne_spinParity
    {C P M₁ M₂ : Matrix ι ι ℂ} {η ε : ℂ}
    (hC : C.map star * C = 1)
    (hP_sq : P * P = 1)
    (hCP : C * P = ε • (P.map star * C))
    (hε : ε = 1 ∨ ε = -1)
    (hM₁ : M₁ = η • (P * M₂.transpose * P.transpose))
    (hM₂ : M₂ = η • (P * M₁.transpose * P.transpose))
    (hH₁ : ∀ u : ι → ℂ, 0 ≤ matrixSesq (C * M₁) u u)
    (hH₂ : ∀ u : ι → ℂ, 0 ≤ matrixSesq (C * M₂) u u)
    (h_wrong : η ≠ ε) :
    M₁ = 0 := by
  have hM₁_sq : M₁ = (η ^ 2) • M₁ := by
    have hM₂_tr : M₂.transpose = η • (P * M₁ * P.transpose) := by
      rw [hM₂, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
    have hP_tr_sq : P.transpose * P.transpose = 1 := by
      rw [← Matrix.transpose_mul, hP_sq, Matrix.transpose_one]
    calc M₁
        = η • (P * M₂.transpose * P.transpose) := hM₁
      _ = η • (P * (η • (P * M₁ * P.transpose)) * P.transpose) := by rw [hM₂_tr]
      _ = (η ^ 2) • ((P * P) * M₁ * (P.transpose * P.transpose)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, sq, Matrix.mul_assoc]
      _ = (η ^ 2) • M₁ := by rw [hP_sq, hP_tr_sq, Matrix.one_mul, Matrix.mul_one]
  by_cases hη_sq : η ^ 2 = 1
  · have hη_pm : η = 1 ∨ η = -1 := sq_eq_one_iff.mp hη_sq
    have hηε : η * ε = -1 := by
      rcases hη_pm with rfl | rfl <;> rcases hε with rfl | rfl
      · exact absurd rfl h_wrong
      · norm_num
      · norm_num
      · exact absurd rfl h_wrong
    let H₁ := C * M₁
    let H₂ := C * M₂
    let Q := P.map star * C
    have hH₂_herm : H₂.conjTranspose = H₂ := matrix_conjTranspose_eq_self_of_matrixSesq_nonneg hH₂
    have hH₂_tr : H₂.transpose = H₂.map star := by
      ext i j
      have hij := congr_fun (congr_fun hH₂_herm j) i
      rw [Matrix.conjTranspose_apply] at hij
      exact hij.symm
    have hC_map_tr : (C.map star).transpose = C.conjTranspose := by
      ext i j
      rfl
    have hM₂_tr : M₂.transpose = H₂.map star * C.conjTranspose := by
      have hM₂_eq : M₂ = C.map star * H₂ := by
        calc M₂
            = 1 * M₂ := (Matrix.one_mul _).symm
          _ = (C.map star * C) * M₂ := by rw [hC]
          _ = C.map star * H₂ := Matrix.mul_assoc _ _ _
      calc M₂.transpose
          = (C.map star * H₂).transpose := by rw [hM₂_eq]
        _ = H₂.transpose * (C.map star).transpose := Matrix.transpose_mul _ _
        _ = H₂.map star * C.conjTranspose := by rw [hH₂_tr, hC_map_tr]
    have hQ_ct : Q.conjTranspose = C.conjTranspose * P.transpose := by
      dsimp [Q]
      rw [Matrix.conjTranspose_mul]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.map_apply]
    have hH₁_neg : H₁ = -(Q * H₂.map star * Q.conjTranspose) := by
      calc H₁
          = C * (η • (P * M₂.transpose * P.transpose)) := by dsimp [H₁]; rw [hM₁]
        _ = η • ((C * P) * M₂.transpose * P.transpose) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
        _ = η • ((ε • Q) * (H₂.map star * C.conjTranspose) * P.transpose) := by
            rw [hCP, hM₂_tr]
        _ = (η * ε) • (Q * H₂.map star * (C.conjTranspose * P.transpose)) := by
            simp only [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        _ = (-1 : ℂ) • (Q * H₂.map star * Q.conjTranspose) := by rw [hηε, hQ_ct]
        _ = -(Q * H₂.map star * Q.conjTranspose) := neg_one_smul _ _
    have hH₁_sesq_zero : ∀ u : ι → ℂ, matrixSesq H₁ u u = 0 := by
      intro u
      have h_pos1 : 0 ≤ matrixSesq H₁ u u := hH₁ u
      have h_pos2 : 0 ≤ matrixSesq (Q * H₂.map star * Q.conjTranspose) u u :=
        matrixSesq_congr_map_star_nonneg hH₂ Q u
      have h_neg_sesq : matrixSesq H₁ u u =
          -matrixSesq (Q * H₂.map star * Q.conjTranspose) u u := by
        rw [hH₁_neg]
        unfold matrixSesq
        simp [Matrix.neg_apply, Finset.sum_neg_distrib]
      have h_le0 : matrixSesq H₁ u u ≤ 0 := by
        rw [h_neg_sesq]
        exact neg_nonpos.mpr h_pos2
      exact le_antisymm h_le0 h_pos1
    have hH₁_zero : H₁ = 0 := matrix_eq_zero_of_matrixSesq_eq_zero hH₁_sesq_zero
    calc M₁
        = 1 * M₁ := (Matrix.one_mul _).symm
      _ = (C.map star * C) * M₁ := by rw [hC]
      _ = C.map star * H₁ := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hH₁_zero, Matrix.mul_zero]
  · have h_sub_zero : (1 - η ^ 2) • M₁ = 0 := by
      rw [sub_smul, one_smul, ← hM₁_sq, sub_self]
    have h_ne : 1 - η ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hη_sq)
    exact (smul_eq_zero.mp h_sub_zero).resolve_left h_ne

omit [Fintype ι] [DecidableEq ι] in
def twoPointIdx (b c : ι) : Fin 2 → ι :=
  Fin.append (fun _ : Fin 1 => b) (fun _ : Fin 1 => c)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma twoPointIdx_zero (b c : ι) : twoPointIdx b c 0 = b := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma twoPointIdx_one (b c : ι) : twoPointIdx b c 1 = c := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma fin2_eq_twoPointIdx (γ : Fin 2 → ι) : γ = twoPointIdx (γ 0) (γ 1) := by
  ext r
  fin_cases r <;> rfl

omit [Fintype ι] [DecidableEq ι] in
noncomputable def twoPointPosMat (W : WightmanFamily ι)
    (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) : Matrix ι ι ℂ :=
  fun b c => W 2 (twoPointIdx b c) (schwartzSplitRevMul 1 1 φ φ)

noncomputable def schwartzConjNeg
    (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  schwartzConj (schwartzNeg 1 φ)

@[simp]
lemma schwartzConjNeg_involutive (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    schwartzConjNeg (schwartzConjNeg φ) = φ := by
  ext x
  simp [schwartzConjNeg]

lemma twoPointPosMat_psd_of_positivity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (W : WightmanFamily ι) (hpos : Positivity S W)
    (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (u : ι → ℂ) :
    0 ≤ matrixSesq (S.C * twoPointPosMat W φ) u u := by
  let F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ := fun j α =>
    match j with
    | 1 => u (α 0) • φ
    | _ => 0
  let G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ :=
    fun j k α α' => schwartzSplitRevMul j k (F j α) (F k α')
  have h0_pos := hpos 1 F G (fun j k α α' x => schwartzSplitRevMul_apply j k (F j α) (F k α') x)
  have hG_zero_left : ∀ (k : ℕ) (α : Fin 0 → ι) (α' : Fin k → ι), G 0 k α α' = 0 := by
    intro k α α'
    ext x
    change schwartzSplitRevMul 0 k (0 : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) (F k α') x = 0
    rw [schwartzSplitRevMul_apply]
    simp
  have hG_zero_right : ∀ (j : ℕ) (α : Fin j → ι) (α' : Fin 0 → ι), G j 0 α α' = 0 := by
    intro j α α'
    ext x
    change schwartzSplitRevMul j 0 (F j α) (0 : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) x = 0
    rw [schwartzSplitRevMul_apply]
    simp
  have h_range2 : ∀ g : ℕ → ℂ, ∑ m ∈ Finset.range (1 + 1), g m = g 0 + g 1 := by
    intro g
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [h_range2, h_range2, h_range2] at h0_pos
  simp only [hG_zero_left, hG_zero_right, map_zero, mul_zero, Finset.sum_const_zero,
    zero_add, add_zero] at h0_pos
  have hG_one : ∀ α α' : Fin 1 → ι,
      G 1 1 α α' = (star (u (α 0)) * u (α' 0)) • schwartzSplitRevMul 1 1 φ φ := by
    intro α α'
    ext x
    change schwartzSplitRevMul 1 1 (u (α 0) • φ) (u (α' 0) • φ) x =
      ((star (u (α 0)) * u (α' 0)) • schwartzSplitRevMul 1 1 φ φ) x
    simp only [schwartzSplitRevMul_apply, smul_apply, smul_eq_mul, map_mul, Complex.star_def]
    ring
  have h_sum_eq : (∑ α : Fin 1 → ι, ∑ α' : Fin 1 → ι, ∑ β : Fin 1 → ι,
      (∏ i : Fin 1, S.C (α i) (β i)) *
        W 2 (Fin.append (β ∘ Fin.rev) α') (G 1 1 α α')) =
      matrixSesq (S.C * twoPointPosMat W φ) u u := by
    rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    simp_rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    unfold matrixSesq
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hG_one, map_smul, smul_eq_mul, Fin.prod_univ_one]
    have h_app : Fin.append (((Equiv.funUnique (Fin 1) ι).symm b) ∘ Fin.rev)
        ((Equiv.funUnique (Fin 1) ι).symm c) = twoPointIdx b c := by
      ext r
      fin_cases r <;> rfl
    have h_fu : ∀ y : ι, (Equiv.funUnique (Fin 1) ι).symm y 0 = y := fun _ => rfl
    rw [h_app]
    simp_rw [h_fu]
    dsimp [twoPointPosMat]
    ring
  rwa [h_sum_eq] at h0_pos

lemma twoPointPosMat_pct_of_wightmanPCT (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hpct : WightmanPCT η R W) (φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    twoPointPosMat W φ =
      η • (R.σ (-1, 1) * (twoPointPosMat W (schwartzConjNeg φ)).transpose *
        (R.σ (-1, 1)).transpose) := by
  ext b c
  have hf_rev : ∀ x : Fin 2 → Fin 4 → ℝ,
      schwartzSplitRevMul 1 1 (schwartzConjNeg φ) (schwartzConjNeg φ) (fun i => -x (Fin.rev i)) =
        schwartzSplitRevMul 1 1 φ φ x := by
    intro x
    rw [schwartzSplitRevMul_apply, schwartzSplitRevMul_apply]
    have hL : (fun i : Fin 1 => -x (Fin.rev (Fin.castAdd 1 (Fin.rev i)))) =
        fun _ => -x 1 := by
      ext i; rw [Subsingleton.elim i 0]; rfl
    have hR : (fun i : Fin 1 => -x (Fin.rev (Fin.natAdd 1 i))) =
        fun _ => -x 0 := by
      ext i; rw [Subsingleton.elim i 0]; rfl
    have h1 : - (fun _ : Fin 1 => -x 1) = fun i : Fin 1 => x (Fin.natAdd 1 i) := by
      ext i; rw [Subsingleton.elim i 0]; simp
    have h0 : - (fun _ : Fin 1 => -x 0) = fun i : Fin 1 => x (Fin.castAdd 1 (Fin.rev i)) := by
      ext i; rw [Subsingleton.elim i 0]; simp
    rw [hL, hR]
    dsimp [schwartzConjNeg]
    rw [h1, h0, ← Complex.star_def, star_star, mul_comm]
  have h_lhs : twoPointPosMat W φ b c =
      η * ∑ β : Fin 2 → ι,
        (∏ i : Fin 2, R.σ (-1, 1) (twoPointIdx b c i) (β i)) *
          twoPointPosMat W (schwartzConjNeg φ) (β 1) (β 0) := by
    change W 2 (twoPointIdx b c) (schwartzSplitRevMul 1 1 φ φ) = _
    rw [hpct 2 (twoPointIdx b c) _ _ hf_rev, two_mul_two_sub_one_div_two, pow_one]
    congr 1
    refine Finset.sum_congr rfl fun β _ => ?_
    congr 1
    have h_rev : β ∘ Fin.rev = twoPointIdx (β 1) (β 0) := by
      ext r
      fin_cases r <;> rfl
    rw [h_rev]
    rfl
  have h_rhs :
      (η • (R.σ (-1, 1) * (twoPointPosMat W (schwartzConjNeg φ)).transpose *
        (R.σ (-1, 1)).transpose)) b c =
      η * ∑ d₁ : ι, ∑ d₀ : ι,
        R.σ (-1, 1) b d₀ * twoPointPosMat W (schwartzConjNeg φ) d₁ d₀ * R.σ (-1, 1) c d₁ := by
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Finset.sum_mul]
  rw [h_lhs, h_rhs]
  congr 1
  let e2 : (ι × ι) ≃ (Fin 2 → ι) :=
    { toFun := fun p => twoPointIdx p.1 p.2
      invFun := fun β => (β 0, β 1)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun β => (fin2_eq_twoPointIdx β).symm }
  rw [← e2.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d₁ _ => Finset.sum_congr rfl fun d₀ _ => ?_
  rw [Fin.prod_univ_two]
  dsimp [e2]
  ring

theorem wrong_statistics_wightman_two_eq_zero {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (W : WightmanFamily ι) {η ε : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hpos : Positivity S W) (hε : R.HasSpinParity ε)
    (hloc : WeakLocality η W) (h_wrong : η ≠ ε) (β : Fin 2 → ι) :
    W 2 β = 0 := by
  have hpct : WightmanPCT η R W := wightman_pct_of_spectrumCondition R W hspec hP hloc
  have h_mat_zero : ∀ φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ, twoPointPosMat W φ = 0 := by
    intro φ
    refine eq_zero_of_psd_pct_pair_ne_spinParity
      S.map_star_mul_self (sigma_pt_mul_self R) (S.mul_sigma_pt_eq_spinParity hε) hε.2
      (twoPointPosMat_pct_of_wightmanPCT R W hpct φ)
      (by simpa [schwartzConjNeg_involutive] using
        twoPointPosMat_pct_of_wightmanPCT R W hpct (schwartzConjNeg φ))
      (twoPointPosMat_psd_of_positivity S W hpos φ)
      (twoPointPosMat_psd_of_positivity S W hpos (schwartzConjNeg φ))
      h_wrong
  have h_diag_zero : ∀ φ : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ,
      W 2 β (schwartzProdSplit 1 1 (schwartzConj φ) φ) = 0 := by
    intro φ
    rw [fin2_eq_twoPointIdx β]
    exact congr_fun (congr_fun (h_mat_zero φ) (β 0)) (β 1)
  refine wightman_two_eq_zero_of_schwartzProdSplit_eq_zero R W hspec hP β fun ψ₁ ψ₂ => ?_
  let u := schwartzConj ψ₁
  let X := W 2 β (schwartzProdSplit 1 1 (schwartzConj u) ψ₂)
  let Y := W 2 β (schwartzProdSplit 1 1 (schwartzConj ψ₂) u)
  have h1 : X + Y = 0 := by
    have h0 := h_diag_zero (u + ψ₂)
    rw [schwartzConj_add, schwartzProdSplit_add_left, schwartzProdSplit_add_right,
      schwartzProdSplit_add_right, map_add, map_add, map_add,
      h_diag_zero u, h_diag_zero ψ₂] at h0
    dsimp [X, Y]
    linear_combination h0
  have h2 : Complex.I * X - Complex.I * Y = 0 := by
    have h0 := h_diag_zero (u + Complex.I • ψ₂)
    have hI_star : star Complex.I = -Complex.I := by
      rw [Complex.star_def, Complex.conj_I]
    have hI_prod : schwartzProdSplit 1 1 (schwartzConj (Complex.I • ψ₂)) (Complex.I • ψ₂) =
        schwartzProdSplit 1 1 (schwartzConj ψ₂) ψ₂ := by
      rw [schwartzConj_smul, schwartzProdSplit_smul_left, schwartzProdSplit_smul_right,
        smul_smul, hI_star, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    rw [schwartzConj_add, schwartzProdSplit_add_left, schwartzProdSplit_add_right,
      schwartzProdSplit_add_right, hI_prod, schwartzConj_smul,
      schwartzProdSplit_smul_left, schwartzProdSplit_smul_right, hI_star,
      map_add, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      h_diag_zero u, h_diag_zero ψ₂] at h0
    dsimp [X, Y]
    linear_combination h0
  have h2' : -X + Y = 0 := by
    have hmul := congr_arg (Complex.I * ·) h2
    have hL : Complex.I * (Complex.I * X - Complex.I * Y) = -X + Y := by
      calc Complex.I * (Complex.I * X - Complex.I * Y)
          = (Complex.I * Complex.I) * X - (Complex.I * Complex.I) * Y := by ring
        _ = -X + Y := by rw [Complex.I_mul_I]; ring
    rwa [hL, mul_zero] at hmul
  have hX : X = 0 := by
    linear_combination (1 / 2 : ℂ) * h1 - (1 / 2 : ℂ) * h2'
  dsimp [X, u] at hX
  rwa [schwartzConj_conj] at hX

theorem spin_statistics_of_spectrumCondition {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (W : WightmanFamily ι) {η ε : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hpos : Positivity S W) (hε : R.HasSpinParity ε)
    (hloc : WeakLocality η W)
    (h_nondeg : ∃ β : Fin 2 → ι, W 2 β ≠ 0) :
    η = ε := by
  by_contra h_wrong
  obtain ⟨β, hW_ne⟩ := h_nondeg
  exact hW_ne (wrong_statistics_wightman_two_eq_zero S W hspec hP hpos hε hloc h_wrong β)

end UnconditionalSpinStatistics

section GeneralDimensionJostEOW

open scoped Distributions ContDiff

lemma zero_notMem_forwardTubeConeFlat {n : ℕ} (hn : ¬ n ≤ 1) :
    (0 : Fin (n * 4) → ℝ) ∉ forwardTubeConeFlat n := by
  intro h0
  have hn1 : (0 : ℕ) + 1 < n := by omega
  have hcone := h0 ⟨0, by omega⟩ hn1
  have h00 : (0 : ℝ) < 0 := by simpa using hcone.1
  exact lt_irrefl 0 h00

lemma isOpen_jost_points_n (n : ℕ) : IsOpen (jost_points_n n) := by
  by_cases hn : n ≤ 1
  · have h_univ : jost_points_n n = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      intro v hv
      have h_emp : jost_differences_n n x = ∅ := by
        ext w
        simp only [jost_differences_n, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨i, hi, -⟩
        omega
      rw [jost_convex_hull, h_emp, convexHull_empty] at hv
      exact False.elim hv
    rw [h_univ]
    exact isOpen_univ
  · rw [Metric.isOpen_iff]
    intro x hx
    have hn1 : (0 : ℕ) + 1 < n := by omega
    have h_ne : jost_convex_hull n x ≠ ∅ := by
      apply Set.nonempty_iff_ne_empty.mp
      refine ⟨x ⟨0, by omega⟩ - x ⟨1, hn1⟩, subset_convexHull ℝ _ ⟨⟨0, by omega⟩, hn1, rfl⟩⟩
    rcases spacelike_margin (jost_convex_hull_compact n x) (jost_convex_hull_convex n x) hx with
      h_emp | ⟨ε, hε_pos, hε_margin⟩
    · exact False.elim (h_ne h_emp)
    have h_norm_hull : ∀ v ∈ jost_convex_hull n x, ‖v‖ ≤ 2 * ‖x‖ := by
      have h_sub : jost_differences_n n x ⊆ Metric.closedBall (0 : Fin 4 → ℝ) (2 * ‖x‖) := by
        rintro v ⟨i, hi, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        calc ‖x i - x ⟨i.val + 1, hi⟩‖
            ≤ ‖x i‖ + ‖x ⟨i.val + 1, hi⟩‖ := norm_sub_le _ _
          _ ≤ ‖x‖ + ‖x‖ := add_le_add (norm_le_pi_norm x i) (norm_le_pi_norm x ⟨i.val + 1, hi⟩)
          _ = 2 * ‖x‖ := by ring
      intro v hv
      have hv_cb := convexHull_min h_sub (convex_closedBall (0 : Fin 4 → ℝ) (2 * ‖x‖)) hv
      rwa [Metric.mem_closedBall, dist_zero_right] at hv_cb
    let δ : ℝ := min (1 / 4) (ε / (128 * (‖x‖ + 1)))
    have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
    refine ⟨δ, hδ_pos, fun x' hx' w hw => ?_⟩
    have hx'_lt : ‖x' - x‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hx'
    let S : Set (Fin 4 → ℝ) :=
      { u | ∃ v ∈ jost_convex_hull n x, ‖u - v‖ ≤ 2 * ‖x' - x‖ }
    have hS_conv : Convex ℝ S := by
      rintro u₁ ⟨v₁, hv₁, h₁⟩ u₂ ⟨v₂, hv₂, h₂⟩ a b ha hb hab
      refine ⟨a • v₁ + b • v₂, (jost_convex_hull_convex n x) hv₁ hv₂ ha hb hab, ?_⟩
      have h_lin : (a • u₁ + b • u₂) - (a • v₁ + b • v₂) =
          a • (u₁ - v₁) + b • (u₂ - v₂) := by
        ext μ; simp; ring
      rw [h_lin]
      calc ‖a • (u₁ - v₁) + b • (u₂ - v₂)‖
          ≤ ‖a • (u₁ - v₁)‖ + ‖b • (u₂ - v₂)‖ := norm_add_le _ _
        _ = a * ‖u₁ - v₁‖ + b * ‖u₂ - v₂‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
        _ ≤ a * (2 * ‖x' - x‖) + b * (2 * ‖x' - x‖) :=
            add_le_add (mul_le_mul_of_nonneg_left h₁ ha) (mul_le_mul_of_nonneg_left h₂ hb)
        _ = (a + b) * (2 * ‖x' - x‖) := by ring
        _ = 2 * ‖x' - x‖ := by rw [hab, one_mul]
    have h_diff_sub : jost_differences_n n x' ⊆ S := by
      rintro u ⟨i, hi, rfl⟩
      refine ⟨x i - x ⟨i.val + 1, hi⟩, subset_convexHull ℝ _ ⟨i, hi, rfl⟩, ?_⟩
      have h_eq : (x' i - x' ⟨i.val + 1, hi⟩) - (x i - x ⟨i.val + 1, hi⟩) =
          (x' - x) i - (x' - x) ⟨i.val + 1, hi⟩ := by
        ext μ; simp; ring
      rw [h_eq]
      calc ‖(x' - x) i - (x' - x) ⟨i.val + 1, hi⟩‖
          ≤ ‖(x' - x) i‖ + ‖(x' - x) ⟨i.val + 1, hi⟩‖ := norm_sub_le _ _
        _ ≤ ‖x' - x‖ + ‖x' - x‖ :=
            add_le_add (norm_le_pi_norm (x' - x) i) (norm_le_pi_norm (x' - x) ⟨i.val + 1, hi⟩)
        _ = 2 * ‖x' - x‖ := by ring
    obtain ⟨v, hv_mem, h_uv⟩ := convexHull_min h_diff_sub hS_conv hw
    let d : Fin 4 → ℝ := w - v
    have hw_eq : w = v + d := by ext μ; simp [d]
    have hd_lt : ‖d‖ < 2 * δ := lt_of_le_of_lt h_uv (by linarith)
    have hv_le : ‖v‖ ≤ 2 * (‖x‖ + 1) := (h_norm_hull v hv_mem).trans (by linarith)
    have h_bilin : minkowskiInner w w ≤
        minkowskiInner v v + 8 * ‖v‖ * ‖d‖ + 4 * ‖d‖ ^ 2 := by
      have hexp : minkowskiInner (v + d) (v + d) =
          minkowskiInner v v + 2 * minkowskiInner v d + minkowskiInner d d := by
        simp only [minkowskiInner_explicit, Pi.add_apply]
        ring
      rw [hw_eq, hexp]
      have hvd := (le_abs_self (minkowskiInner v d)).trans (minkowskiInner_le_norm v d)
      have hdd := (le_abs_self (minkowskiInner d d)).trans (minkowskiInner_le_norm d d)
      nlinarith
    have hδ1 : δ ≤ 1 / 4 := min_le_left _ _
    have hδ2 : δ ≤ ε / (128 * (‖x‖ + 1)) := min_le_right _ _
    have h_prod : 128 * (‖x‖ + 1) * δ ≤ ε := by
      have hpos : (0 : ℝ) < 128 * (‖x‖ + 1) := by positivity
      calc 128 * (‖x‖ + 1) * δ
          ≤ 128 * (‖x‖ + 1) * (ε / (128 * (‖x‖ + 1))) := mul_le_mul_of_nonneg_left hδ2 hpos.le
        _ = ε := mul_div_cancel₀ ε hpos.ne'
    have h_vv := hε_margin v hv_mem
    dsimp [is_spacelike]
    have hd_sq : 4 * ‖d‖ ^ 2 ≤ 8 * δ := by
      have hd_nn : 0 ≤ ‖d‖ := norm_nonneg d
      nlinarith
    have hvd_bd : 8 * ‖v‖ * ‖d‖ ≤ 32 * (‖x‖ + 1) * δ := by
      nlinarith [norm_nonneg v, norm_nonneg d, norm_nonneg x]
    have hδ_le_x : 8 * δ ≤ 32 * (‖x‖ + 1) * δ := by
      nlinarith [norm_nonneg x, hδ_pos]
    linarith

lemma jost_inter_perm_nonempty (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (jost_points_n n ∩ { x | (x ∘ σ) ∈ jost_points_n n }).Nonempty := by
  let x : Fin n → Fin 4 → ℝ := fun i => ![0, (i.val : ℝ), ((σ.symm i).val : ℝ), 0]
  refine ⟨x, ⟨?_, ?_⟩⟩
  · let H₁ : Set (Fin 4 → ℝ) := { v | v 0 = 0 ∧ v 1 ≤ -1 }
    have hH₁_conv : Convex ℝ H₁ := by
      rintro v₁ ⟨h₁0, h₁1⟩ v₂ ⟨h₂0, h₂1⟩ a b ha hb hab
      refine ⟨by simp [h₁0, h₂0], ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    have h_sub₁ : jost_differences_n n x ⊆ H₁ := by
      rintro v ⟨i, hi, rfl⟩
      refine ⟨by simp [x], ?_⟩
      change (i.val : ℝ) - ((i.val + 1 : ℕ) : ℝ) ≤ -1
      push_cast
      linarith
    intro v hv
    obtain ⟨hv0, hv1⟩ := convexHull_min h_sub₁ hH₁_conv hv
    dsimp [is_spacelike]
    rw [minkowskiInner_explicit, hv0]
    nlinarith [sq_nonneg (v 2), sq_nonneg (v 3)]
  · let H₂ : Set (Fin 4 → ℝ) := { v | v 0 = 0 ∧ v 2 ≤ -1 }
    have hH₂_conv : Convex ℝ H₂ := by
      rintro v₁ ⟨h₁0, h₁2⟩ v₂ ⟨h₂0, h₂2⟩ a b ha hb hab
      refine ⟨by simp [h₁0, h₂0], ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    have h_sub₂ : jost_differences_n n (x ∘ σ) ⊆ H₂ := by
      rintro v ⟨i, hi, rfl⟩
      refine ⟨by simp [x], ?_⟩
      change ((σ.symm (σ i)).val : ℝ) - ((σ.symm (σ ⟨i.val + 1, hi⟩)).val : ℝ) ≤ -1
      simp only [Equiv.symm_apply_apply]
      push_cast
      linarith
    intro v hv
    obtain ⟨hv0, hv2⟩ := convexHull_min h_sub₂ hH₂_conv hv
    dsimp [is_spacelike]
    rw [minkowskiInner_explicit, hv0]
    nlinarith [sq_nonneg (v 1), sq_nonneg (v 3)]

lemma measurePreserving_permCoordCLE (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasureTheory.MeasurePreserving (permCoordCLE n σ)
      MeasureTheory.volume MeasureTheory.volume where
  measurable := (permCoordCLE n σ).continuous.measurable
  map_eq := by
    refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
    rw [MeasureTheory.Measure.map_apply (permCoordCLE n σ).continuous.measurable
        (MeasurableSet.univ_pi hs)]
    have h_pre : (permCoordCLE n σ) ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i : Fin n => s (σ.symm i)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
      change (∀ j : Fin n, x (σ j) ∈ s j) ↔ ∀ i : Fin n, x i ∈ s (σ.symm i)
      constructor
      · intro h i
        simpa using h (σ.symm i)
      · intro h j
        simpa using h (σ j)
    rw [h_pre, MeasureTheory.volume_pi_pi]
    exact σ.symm.prod_comp (fun i => MeasureTheory.volume (s i))

lemma integral_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (x ∘ σ)) = ∫ x, g x := by
  have h_mp := measurePreserving_permCoordCLE n σ
  have h_emb : MeasurableEmbedding (permCoordCLE n σ) :=
    (permCoordCLE n σ).toHomeomorph.isClosedEmbedding.measurableEmbedding
  exact h_mp.integral_comp h_emb g

theorem spinor_H_ext_perm_eq_on_jost_inter (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (hloc : LocalCommutativity η W)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (α : Fin n → ι)
    {x : Fin n → Fin 4 → ℝ} (hx₁ : x ∈ jost_points_n n) (hx₂ : (x ∘ σ) ∈ jost_points_n n) :
    spinor_H_ext R W E n α (coeReal n x) =
      η ^ permInversions σ * spinor_H_ext R W E n (α ∘ σ) (coeReal n (x ∘ σ)) := by
  have hperm_loc : PermSpacelikeLocality η W := PermSpacelikeLocality.of_localCommutativity hloc
  let J_σ : Set (Fin n → Fin 4 → ℝ) := jost_points_n n ∩ { y | (y ∘ σ) ∈ jost_points_n n }
  have hJ_open : IsOpen J_σ :=
    (isOpen_jost_points_n n).inter
      ((isOpen_jost_points_n n).preimage (permCoordCLE n σ).continuous)
  let O_σ : TopologicalSpace.Opens (Fin (n * 4) → ℝ) :=
    ⟨(spacetimeFlatCLE n).symm ⁻¹' J_σ, hJ_open.preimage (spacetimeFlatCLE n).symm.continuous⟩
  let g₁ : (Fin (n * 4) → ℝ) → ℂ :=
    fun u => spinor_H_ext R W E n α (coeReal n ((spacetimeFlatCLE n).symm u))
  let g₂ : (Fin (n * 4) → ℝ) → ℂ :=
    fun u => η ^ permInversions σ *
      spinor_H_ext R W E n (α ∘ σ) (coeReal n (((spacetimeFlatCLE n).symm u) ∘ σ))
  have h_coe_cont : Continuous (fun y : Fin n → Fin 4 → ℝ => coeReal n y) :=
    continuous_pi fun i => continuous_pi fun μ =>
      Complex.continuous_ofReal.comp ((continuous_apply μ).comp (continuous_apply i))
  have hg₁_contOn : ContinuousOn g₁ O_σ :=
    (spinor_H_ext_analyticOnNhd R W E h_cov n α).continuousOn.comp
      (h_coe_cont.comp (spacetimeFlatCLE n).symm.continuous).continuousOn
      (fun u hu => coeReal_mem_extended_tube_of_mem_jost_points n hu.1)
  have hg₂_contOn : ContinuousOn g₂ O_σ :=
    continuousOn_const.mul
      ((spinor_H_ext_analyticOnNhd R W E h_cov n (α ∘ σ)).continuousOn.comp
        (h_coe_cont.comp ((permCoordCLE n σ).continuous.comp
          (spacetimeFlatCLE n).symm.continuous)).continuousOn
        (fun u hu => coeReal_mem_extended_tube_of_mem_jost_points n hu.2))
  have hg₁_loc : MeasureTheory.LocallyIntegrableOn g₁ O_σ MeasureTheory.volume :=
    hg₁_contOn.locallyIntegrableOn O_σ.isOpen.measurableSet
  have hg₂_loc : MeasureTheory.LocallyIntegrableOn g₂ O_σ MeasureTheory.volume :=
    hg₂_contOn.locallyIntegrableOn O_σ.isOpen.measurableSet
  have h_eq_dist : Distribution.EqualOn O_σ
      (Distribution.ofLocallyIntegrableOn O_σ g₁)
      (Distribution.ofLocallyIntegrableOn O_σ g₂)
      O_σ subset_rfl := by
    intro φ _hφ
    rw [Distribution.ofLocallyIntegrableOn_apply hg₁_loc,
        Distribution.ofLocallyIntegrableOn_apply hg₂_loc,
        ← integral_comp_spacetimeFlatCLE n, ← integral_comp_spacetimeFlatCLE n]
    let ψ := Distribution.testFunctionToSchwartzCLM O_σ φ
    let f := schwartzFlatCLM n ψ
    let f' := schwartzPermCLM n σ.symm f
    have hψ_supp : HasCompactSupport (fun u => ψ u) :=
      φ.hasCompactSupport'.comp_left Complex.ofReal_zero
    have hf_supp : HasCompactSupport (f : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hasCompactSupport_schwartzFlatCLM n hψ_supp
    have hf'_supp : HasCompactSupport (f' : (Fin n → Fin 4 → ℝ) → ℂ) :=
      hf_supp.comp_homeomorph (permCoordCLE n σ.symm).toHomeomorph
    have hψ_tsupp : tsupport (fun u => ψ u) ⊆ O_σ := by
      refine (closure_mono (fun u hu => ?_)).trans φ.tsupport_subset'
      intro h0
      apply hu
      have h0' : φ u = 0 := h0
      change (φ u : ℂ) = 0
      rw [h0', Complex.ofReal_zero]
    have hf_J : ∀ y ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ), y ∈ J_σ := by
      intro y hy
      have hu : spacetimeFlatCLE n y ∈ O_σ :=
        hψ_tsupp (mem_tsupport_of_comp_continuous (spacetimeFlatCLE n).continuous hy)
      have h_symm : (spacetimeFlatCLE n).symm (spacetimeFlatCLE n y) ∈ J_σ := hu
      rwa [ContinuousLinearEquiv.symm_apply_apply] at h_symm
    have hf_ext : ∀ y ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n y ∈ extended_tube_n n :=
      fun y hy => coeReal_mem_extended_tube_of_mem_jost_points n (hf_J y hy).1
    have hf'_ext : ∀ y ∈ tsupport (f' : (Fin n → Fin 4 → ℝ) → ℂ),
        coeReal n y ∈ extended_tube_n n := by
      intro y hy
      have hy_pre : permCoordCLE n σ.symm y ∈ tsupport (f : (Fin n → Fin 4 → ℝ) → ℂ) :=
        mem_tsupport_of_comp_continuous (permCoordCLE n σ.symm).continuous hy
      have h_jost : ((permCoordCLE n σ.symm y) ∘ σ) ∈ jost_points_n n :=
        (hf_J (permCoordCLE n σ.symm y) hy_pre).2
      have h_id : ((permCoordCLE n σ.symm y) ∘ σ) = y := by
        ext i μ
        change y (σ.symm (σ i)) μ = y i μ
        simp
      rw [h_id] at h_jost
      exact coeReal_mem_extended_tube_of_mem_jost_points n h_jost
    have h_int₁ : (∫ y : Fin n → Fin 4 → ℝ,
        g₁ (spacetimeFlatCLE n y) * (φ (spacetimeFlatCLE n y) : ℂ)) = W n α f := by
      rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
        R W E h_cov n α f hf_supp hf_ext]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp [g₁, f, ψ]
      rw [ContinuousLinearEquiv.symm_apply_apply]
    have h_int₂ : (∫ y : Fin n → Fin 4 → ℝ,
        g₂ (spacetimeFlatCLE n y) * (φ (spacetimeFlatCLE n y) : ℂ)) =
        η ^ permInversions σ * W n (α ∘ σ) f' := by
      rw [W_eq_integral_spinor_H_ext_of_compactSupport_subset_extended_tube
        R W E h_cov n (α ∘ σ) f' hf'_supp hf'_ext,
        ← integral_comp_perm n σ (fun z : Fin n → Fin 4 → ℝ =>
          spinor_H_ext R W E n (α ∘ σ) (coeReal n z) * f' z),
        ← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp [g₂, f', f, ψ]
      rw [ContinuousLinearEquiv.symm_apply_apply, schwartzPermCLM_apply]
      have h_inv : (y ∘ σ) ∘ σ.symm = y := by
        ext i μ
        simp
      rw [h_inv, mul_assoc]
      rfl
    rw [h_int₁, h_int₂]
    refine hperm_loc n σ α f f'
      (fun y hy => jost_points_subset_pairwiseSpacelike n (hf_J y hy).1) (fun y => ?_)
    rw [schwartzPermCLM_apply]
    have h_inv : (y ∘ σ) ∘ σ.symm = y := by
      ext i μ
      simp
    rw [h_inv]
  have h_real_eq : EqOn g₁ g₂ O_σ :=
    Distribution.eqOn_of_equalOn_continuousOn subset_rfl
      hg₁_loc hg₂_loc hg₁_contOn hg₂_contOn h_eq_dist
  have hu_mem : spacetimeFlatCLE n x ∈ O_σ := by
    change (spacetimeFlatCLE n).symm (spacetimeFlatCLE n x) ∈ J_σ
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ⟨hx₁, hx₂⟩
  have h_eval := h_real_eq hu_mem
  dsimp [g₁, g₂] at h_eval
  rwa [ContinuousLinearEquiv.symm_apply_apply] at h_eval

lemma continuous_coneGap : Continuous coneGap := by
  unfold coneGap
  refine (continuous_apply 0).sub (Real.continuous_sqrt.comp ?_)
  exact (((continuous_apply 1).pow 2).add ((continuous_apply 2).pow 2)).add
    ((continuous_apply 3).pow 2)

lemma coneGap_smul {s : ℝ} (hs : 0 ≤ s) (v : Fin 4 → ℝ) :
    coneGap (s • v) = s * coneGap v := by
  unfold coneGap
  simp only [Pi.smul_apply, smul_eq_mul]
  have h_sq : (s * v 1) ^ 2 + (s * v 2) ^ 2 + (s * v 3) ^ 2 =
      s ^ 2 * (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) := by ring
  rw [h_sq, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]
  ring

lemma cone_vladimirov_kernel_uniform_exp_decay {n : ℕ} (hn : ¬ n ≤ 1)
    {R_z γ : ℝ} (hR_nn : 0 ≤ R_z) (hγ_pos : 0 < γ)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) (hz_norm : ‖z‖ ≤ R_z)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (hγ_le : ∀ (i : Fin n) (hi : i.val + 1 < n), s * γ ≤ coneGap (diff_im n z i hi)) :
    ∀ p ∈ tsupport (coneSpectralCutoff n),
      ‖vladimirov_kernel n z p‖ ≤
        Real.exp ((8 * R_z + 6 * (n : ℝ) * R_z + (γ / 2) * (2 + 12 * (n : ℝ))) -
          (s * γ / 2) * ‖p‖) := by
  let B₀ : ℝ := 8 * R_z + 6 * (n : ℝ) * R_z + (γ / 2) * (2 + 12 * (n : ℝ))
  have h_supp : ∀ p ∈ Function.support (coneSpectralCutoff n),
      ‖vladimirov_kernel n z p‖ ≤ Real.exp (B₀ - (s * γ / 2) * ‖p‖) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    intro p hp
    rw [vladimirov_kernel_norm]
    apply Real.exp_le_exp.mpr
    rw [abel_summation_minkowskiInner_general m p z]
    obtain ⟨htot, hstep⟩ := coneSpectralCutoff_support_bounds (m + 1) hp
    have h_last_bound :
        minkowskiInner (total_momentum_LM (m + 1) p) (fun μ => (z (Fin.last m) μ).im) ≤
          8 * R_z := by
      have h1 := minkowskiInner_le_norm (total_momentum_LM (m + 1) p)
        (fun μ => (z (Fin.last m) μ).im)
      have h_im_norm : ‖(fun μ : Fin 4 => (z (Fin.last m) μ).im)‖ ≤ R_z := by
        rw [pi_norm_le_iff_of_nonneg hR_nn]
        intro μ
        rw [Real.norm_eq_abs]
        exact ((Complex.abs_im_le_norm (z (Fin.last m) μ)).trans
          ((norm_le_pi_norm (z (Fin.last m)) μ).trans
            (norm_le_pi_norm z (Fin.last m)))).trans hz_norm
      have h_le_abs := le_abs_self
        (minkowskiInner (total_momentum_LM (m + 1) p) (fun μ => (z (Fin.last m) μ).im))
      have h_prod : 4 * ‖total_momentum_LM (m + 1) p‖ *
          ‖(fun μ : Fin 4 => (z (Fin.last m) μ).im)‖ ≤ 8 * R_z := by
        calc 4 * ‖total_momentum_LM (m + 1) p‖ * ‖(fun μ : Fin 4 => (z (Fin.last m) μ).im)‖
            ≤ 4 * 2 * R_z := by gcongr
          _ = 8 * R_z := by ring
      linarith
    rw [totalConePairing_succ]
    have h_diff0_le : ∀ i : Fin m,
        diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt) 0 ≤ 2 * R_z := by
      intro i
      have h1 : |(z i.castSucc 0).im| ≤ R_z :=
        ((Complex.abs_im_le_norm _).trans
          ((norm_le_pi_norm _ 0).trans (norm_le_pi_norm z _))).trans hz_norm
      have h2 : |(z ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ 0).im| ≤ R_z :=
        ((Complex.abs_im_le_norm _).trans
          ((norm_le_pi_norm _ 0).trans (norm_le_pi_norm z _))).trans hz_norm
      change -((z i.castSucc 0).im - (z ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ 0).im) ≤ 2 * R_z
      linarith [neg_abs_le (z i.castSucc 0).im,
        le_abs_self (z ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ 0).im]
    have h_each : ∀ i : Fin m,
        -minkowskiInner (partial_sum_p (m + 1) p i.castSucc)
            (diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt)) ≤
          6 * R_z - (s * γ) * (partial_sum_p (m + 1) p i.castSucc 0 + 3) := by
      intro i
      let q := partial_sum_p (m + 1) p i.castSucc
      let v := diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt)
      have hq_cone := (shifted_mem_closed_cone_of_coneStepArg_pos
        (hstep i.castSucc (Nat.succ_lt_succ i.isLt))).1
      have h_gap := minkowskiInner_ge_coneGap v (q + (3 : ℝ) • unit_time_vector) hq_cone
      have h_lin : minkowskiInner (q + (3 : ℝ) • unit_time_vector) v =
          minkowskiInner q v + 3 * v 0 := by
        simp [minkowskiInner_explicit, unit_time_vector]
        ring
      have h_q0 : (q + (3 : ℝ) • unit_time_vector) 0 = q 0 + 3 := by
        simp [unit_time_vector]
      rw [h_lin, h_q0] at h_gap
      have hq0_nn : 0 ≤ q 0 + 3 := by
        have h0 := hq_cone.1
        rwa [h_q0] at h0
      have hγ_i := hγ_le i.castSucc (Nat.succ_lt_succ i.isLt)
      have h_mul : (s * γ) * (q 0 + 3) ≤ coneGap v * (q 0 + 3) :=
        mul_le_mul_of_nonneg_right hγ_i hq0_nn
      have hv0 := h_diff0_le i
      linarith
    have h_sum_neg : -(∑ i : Fin m, minkowskiInner (partial_sum_p (m + 1) p i.castSucc)
          (diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt))) ≤
        6 * ((m + 1 : ℕ) : ℝ) * R_z -
          (s * γ) * ∑ i : Fin m, (partial_sum_p (m + 1) p i.castSucc 0 + 3) := by
      rw [← Finset.sum_neg_distrib]
      have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_each i)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum Finset.univ _ (s * γ)] at h1
      have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
      nlinarith
    have h_filt_eq : (∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => k.val + 1 < m + 1),
          (partial_sum_p (m + 1) p k 0 + 3)) =
        ∑ i : Fin m, (partial_sum_p (m + 1) p i.castSucc 0 + 3) := by
      refine Finset.sum_bij (fun (k : Fin (m + 1)) hk => ⟨k.val, by
          rw [Finset.mem_filter] at hk; omega⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun k1 _ k2 _ h => Fin.ext (congr_arg (Fin.val : Fin m → ℕ) h))
        (fun i _ => ⟨i.castSucc, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Nat.succ_lt_succ i.isLt⟩, Fin.ext rfl⟩)
        (fun _ _ => by congr 2)
    have h_norm_p := norm_p_le_on_coneSpectralCutoff_support hn hp
    rw [h_filt_eq] at h_norm_p
    have h_mul_p : (s * γ / 2) * ‖p‖ ≤ (γ / 2) * (2 + 12 * ((m + 1 : ℕ) : ℝ)) +
        (s * γ) * ∑ i : Fin m, (partial_sum_p (m + 1) p i.castSucc 0 + 3) := by
      have h1 := mul_le_mul_of_nonneg_left h_norm_p (by positivity : 0 ≤ s * γ / 2)
      have hs_term : (s * γ / 2) * (2 + 12 * ((m + 1 : ℕ) : ℝ)) ≤
          (γ / 2) * (2 + 12 * ((m + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hs1, hγ_pos]) (by positivity)
      linarith
    dsimp [B₀]
    linarith
  have h_closed : IsClosed { p : Fin n → Fin 4 → ℝ |
      ‖vladimirov_kernel n z p‖ ≤ Real.exp (B₀ - (s * γ / 2) * ‖p‖) } :=
    isClosed_le (vladimirov_kernel_contDiff n z).continuous.norm
      (Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul continuous_norm)))
  exact closure_minimal h_supp h_closed

lemma poly_mul_neg_scaled_exp_bound (D : ℕ) {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s r : ℝ), 0 < s → s ≤ 1 → 0 ≤ r →
      (1 + r) ^ D * Real.exp (-(s * γ₀) * r) ≤ M / s ^ D := by
  let M : ℝ := (2 : ℝ) ^ D * (1 + (D.factorial : ℝ) / γ₀ ^ D)
  refine ⟨M, by positivity, fun s r hs0 hs1 hr => ?_⟩
  have h1 := pow_one_add_le_two_pow_mul r hr D D le_rfl
  have hα : 0 < s * γ₀ := mul_pos hs0 hγ₀
  have hαr : 0 ≤ (s * γ₀) * r := mul_nonneg hα.le hr
  have h_rk : r ^ D * Real.exp (-(s * γ₀) * r) ≤ ((D.factorial : ℝ) / γ₀ ^ D) / s ^ D := by
    have h_term : ((s * γ₀) * r) ^ D / (D.factorial : ℝ) ≤ Real.exp ((s * γ₀) * r) := by
      have h_in : D ∈ Finset.range (D + 1) := Finset.self_mem_range_succ D
      have h_le_sum : ((s * γ₀) * r) ^ D / (D.factorial : ℝ) ≤
          ∑ i ∈ Finset.range (D + 1), ((s * γ₀) * r) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (fun i _ => div_nonneg (pow_nonneg hαr i) (Nat.cast_nonneg _)) h_in
      exact h_le_sum.trans (Real.sum_le_exp_of_nonneg hαr (D + 1))
    have h_exp_mul : Real.exp ((s * γ₀) * r) * Real.exp (-(s * γ₀) * r) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have h_mul := mul_le_mul_of_nonneg_right h_term (Real.exp_pos (-(s * γ₀) * r)).le
    rw [h_exp_mul, mul_pow, mul_pow] at h_mul
    have h_pos_fac : (0 : ℝ) < (D.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos D)
    have h_pos_sD : (0 : ℝ) < s ^ D := pow_pos hs0 D
    have h_pos_gD : (0 : ℝ) < γ₀ ^ D := pow_pos hγ₀ D
    rw [div_mul_eq_mul_div, div_le_one h_pos_fac] at h_mul
    rw [le_div_iff₀ h_pos_sD, le_div_iff₀ h_pos_gD]
    nlinarith
  have h_exp_le : Real.exp (-(s * γ₀) * r) ≤ 1 / s ^ D := by
    have he1 : Real.exp (-(s * γ₀) * r) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hsD_le1 : s ^ D ≤ 1 := pow_le_one₀ hs0.le hs1
    have hsD_pos : 0 < s ^ D := pow_pos hs0 D
    have h_one_le : 1 ≤ 1 / s ^ D := (le_div_iff₀ hsD_pos).mpr (by linarith)
    exact he1.trans h_one_le
  calc (1 + r) ^ D * Real.exp (-(s * γ₀) * r)
      ≤ (2 ^ D * (1 + r ^ D)) * Real.exp (-(s * γ₀) * r) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 ^ D * (Real.exp (-(s * γ₀) * r) + r ^ D * Real.exp (-(s * γ₀) * r)) := by ring
    _ ≤ 2 ^ D * (1 / s ^ D + ((D.factorial : ℝ) / γ₀ ^ D) / s ^ D) := by gcongr
    _ = M / s ^ D := by dsimp [M]; ring

lemma cone_psi_seminorm_poly_growth {n : ℕ} (hn : ¬ n ≤ 1)
    {R_z γ : ℝ} (hR_nn : 0 ≤ R_z) (hγ_pos : 0 < γ) (k m : ℕ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n), ‖z‖ ≤ R_z →
        ∀ (s : ℝ), 0 < s → s ≤ 1 →
          (∀ (i : Fin n) (hi : i.val + 1 < n), s * γ ≤ coneGap (diff_im n z i hi)) →
          SchwartzMap.seminorm ℝ k m (cone_psi_schwartz n hn z hz) ≤ C / s ^ N := by
  let cutC : (Fin n → Fin 4 → ℝ) → ℂ := fun p => ((coneSpectralCutoff n p : ℝ) : ℂ)
  have h_cut_temp : Function.HasTemperateGrowth cutC :=
    Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_coneSpectralCutoff n)
  obtain ⟨k_c, C_c, hCc_nn, h_cut_deriv⟩ := h_cut_temp.norm_iteratedFDeriv_le_uniform m
  obtain ⟨C_L, hCL_nn, hCL⟩ := vladimirov_phase_clm_norm_le_all n
  let N : ℕ := k + k_c
  obtain ⟨M_poly, hM_nn, hM_poly⟩ := poly_mul_neg_scaled_exp_bound N (hγ₀ := half_pos hγ_pos)
  let B₀ : ℝ := 8 * R_z + 6 * (n : ℝ) * R_z + (γ / 2) * (2 + 12 * (n : ℝ))
  let C : ℝ := ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * C_c * M_poly * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)
  refine ⟨N, C, Finset.sum_nonneg (fun i _ => by positivity),
    fun z hz hz_norm s hs0 hs1 hγ_le => ?_⟩
  have hsN_pos : 0 < s ^ N := pow_pos hs0 N
  refine SchwartzMap.seminorm_le_bound ℝ k m _
    (div_nonneg (Finset.sum_nonneg fun i _ => by positivity) hsN_pos.le) fun p => ?_
  by_cases hp_ts : p ∈ tsupport (coneSpectralCutoff n)
  · have h_ker_tsupp :=
      cone_vladimirov_kernel_uniform_exp_decay hn hR_nn hγ_pos hz hz_norm hs0 hs1 hγ_le p hp_ts
    have h_le := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := cutC) (g := vladimirov_kernel n z)
      (n := m) (N := (⊤ : ℕ∞)) h_cut_temp.1 (vladimirov_kernel_contDiff n z) p
      (WithTop.coe_le_coe.mpr le_top)
    have h_eq : (fun q => cutC q * vladimirov_kernel n z q) =
        ⇑(cone_psi_schwartz n hn z hz) := rfl
    rw [← h_eq]
    have h_pk : ‖p‖ ^ k ≤ (1 + ‖p‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg p) (by linarith) k
    have h_step : ∀ i ∈ Finset.range (m + 1),
        (1 + ‖p‖) ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i cutC p‖ *
          ‖iteratedFDeriv ℝ (m - i) (vladimirov_kernel n z) p‖) ≤
        ((m.choose i : ℝ) * C_c * M_poly * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)) /
          s ^ N := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hf_i := h_cut_deriv i (by omega) p
      have hg_i : ‖iteratedFDeriv ℝ (m - i) (vladimirov_kernel n z) p‖ ≤
          Real.exp (B₀ - (s * (γ / 2)) * ‖p‖) * (C_L * R_z + 1) ^ (m - i) := by
        have h_comp : vladimirov_kernel n z = Complex.exp ∘ (vladimirov_phase_CLM n z) := rfl
        rw [h_comp]
        have h1 := norm_iteratedFDeriv_comp_clm_le (vladimirov_phase_CLM n z)
          Complex.exp Complex.contDiff_exp p (m - i)
        rw [norm_iteratedFDeriv_real_exp, ← Complex.norm_exp] at h1
        have h2 : ‖Complex.exp (vladimirov_phase_CLM n z p)‖ ≤
            Real.exp (B₀ - (s * (γ / 2)) * ‖p‖) := by
          have h_ar : s * γ / 2 = s * (γ / 2) := by ring
          rwa [← h_ar]
        have h_clm : ‖vladimirov_phase_CLM n z‖ ≤ C_L * R_z + 1 :=
          (hCL z).trans (by nlinarith [hCL_nn])
        have h_pow : ‖vladimirov_phase_CLM n z‖ ^ (m - i) ≤ (C_L * R_z + 1) ^ (m - i) :=
          pow_le_pow_left₀ (norm_nonneg _) h_clm (m - i)
        exact h1.trans (mul_le_mul h2 h_pow (by positivity) (Real.exp_pos _).le)
      have h_exp_split : Real.exp (B₀ - (s * (γ / 2)) * ‖p‖) =
          Real.exp B₀ * Real.exp (-(s * (γ / 2)) * ‖p‖) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h_poly := hM_poly s ‖p‖ hs0 hs1 (norm_nonneg p)
      have h_pow_add : (1 + ‖p‖) ^ k * (1 + ‖p‖) ^ k_c = (1 + ‖p‖) ^ N :=
        (pow_add (1 + ‖p‖) k k_c).symm
      calc (1 + ‖p‖) ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i cutC p‖ *
              ‖iteratedFDeriv ℝ (m - i) (vladimirov_kernel n z) p‖)
          ≤ (1 + ‖p‖) ^ k * ((m.choose i : ℝ) * (C_c * (1 + ‖p‖) ^ k_c) *
              (Real.exp (B₀ - (s * (γ / 2)) * ‖p‖) * (C_L * R_z + 1) ^ (m - i))) := by
            have ha : (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i cutC p‖ ≤
                (m.choose i : ℝ) * (C_c * (1 + ‖p‖) ^ k_c) :=
              mul_le_mul_of_nonneg_left hf_i (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul ha hg_i (norm_nonneg _) (by positivity)) (by positivity)
        _ = ((m.choose i : ℝ) * C_c * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)) *
              (((1 + ‖p‖) ^ k * (1 + ‖p‖) ^ k_c) * Real.exp (-(s * (γ / 2)) * ‖p‖)) := by
            rw [h_exp_split]
            ring
        _ = ((m.choose i : ℝ) * C_c * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)) *
              ((1 + ‖p‖) ^ N * Real.exp (-(s * (γ / 2)) * ‖p‖)) := by
            rw [h_pow_add]
        _ ≤ ((m.choose i : ℝ) * C_c * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)) *
              (M_poly / s ^ N) :=
            mul_le_mul_of_nonneg_left h_poly (by positivity)
        _ = ((m.choose i : ℝ) * C_c * M_poly * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)) /
              s ^ N := by ring
    calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ m (fun q => cutC q * vladimirov_kernel n z q) p‖
        ≤ (1 + ‖p‖) ^ k * ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i cutC p‖ *
              ‖iteratedFDeriv ℝ (m - i) (vladimirov_kernel n z) p‖ :=
          mul_le_mul h_pk h_le (norm_nonneg _) (by positivity)
      _ = ∑ i ∈ Finset.range (m + 1),
            (1 + ‖p‖) ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i cutC p‖ *
              ‖iteratedFDeriv ℝ (m - i) (vladimirov_kernel n z) p‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (m + 1),
            ((m.choose i : ℝ) * C_c * M_poly * Real.exp B₀ * (C_L * R_z + 1) ^ (m - i)) /
              s ^ N := Finset.sum_le_sum h_step
      _ = C / s ^ N := (Finset.sum_div _ _ _).symm
  · have hp_not : p ∉ tsupport (cone_psi n z) := fun h => hp_ts (cone_psi_tsupport_subset n z h)
    have h_zero : iteratedFDeriv ℝ m (⇑(cone_psi_schwartz n hn z hz)) p = 0 := by
      by_contra h_ne
      exact hp_not (support_iteratedFDeriv_subset m (Function.mem_support.mpr h_ne))
    rw [h_zero, norm_zero, mul_zero]
    exact div_nonneg (Finset.sum_nonneg fun i _ => by positivity) hsN_pos.le

theorem coneVladimirov_hasPolynomialTubeGrowth_forward
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    {n : ℕ} (hn : ¬ n ≤ 1) (α : Fin n → ι) :
    Distribution.HasPolynomialTubeGrowth (forwardTubeConeFlat n)
      (tubeForwardFlat (coneVladimirovTubeExtension R W hspec hP) n α) := by
  intro K L hK hL hLV
  by_cases hKL : K = ∅ ∨ L = ∅
  · refine ⟨0, 0, le_rfl, fun x hx y hy _ _ _ => ?_⟩
    rcases hKL with rfl | rfl
    · exact False.elim hx
    · exact False.elim hy
  push Not at hKL
  have hK_ne : K.Nonempty := hKL.1
  have hL_ne : L.Nonempty := hKL.2
  obtain ⟨R_K, hRK⟩ := hK.isBounded.subset_closedBall (0 : Fin (n * 4) → ℝ)
  obtain ⟨R_L, hRL⟩ := hL.isBounded.subset_closedBall (0 : Fin (n * 4) → ℝ)
  let R_z : ℝ := max R_K 0 + max R_L 0
  have hRz_nn : 0 ≤ R_z := by positivity
  let Idx := { i : Fin n // i.val + 1 < n }
  have hn1 : (0 : ℕ) + 1 < n := by omega
  haveI : Nonempty Idx := ⟨⟨⟨0, by omega⟩, hn1⟩⟩
  let gap_fn : (Fin (n * 4) → ℝ) → ℝ := fun y =>
    Finset.univ.inf' Finset.univ_nonempty (fun j : Idx =>
      coneGap (fun μ => -((spacetimeFlatCLE n).symm y j.1 μ -
        (spacetimeFlatCLE n).symm y ⟨j.1.val + 1, j.2⟩ μ)))
  have hgap_cont : Continuous gap_fn := by
    refine Continuous.finset_inf'_apply Finset.univ_nonempty (fun j _ => ?_)
    refine continuous_coneGap.comp (continuous_pi fun μ => Continuous.neg (Continuous.sub ?_ ?_))
    · exact (continuous_apply μ).comp ((continuous_apply j.1).comp
        (spacetimeFlatCLE n).symm.continuous)
    · exact (continuous_apply μ).comp
        ((continuous_apply (⟨j.1.val + 1, j.2⟩ : Fin n)).comp
          (spacetimeFlatCLE n).symm.continuous)
  obtain ⟨y_min, hy_min_L, hy_min_le⟩ := hL.exists_isMinOn hL_ne hgap_cont.continuousOn
  let γ : ℝ := gap_fn y_min
  have hγ_pos : 0 < γ := by
    dsimp [γ, gap_fn]
    rw [Finset.lt_inf'_iff]
    intro j _
    exact coneGap_pos _ (hLV hy_min_L j.1 j.2)
  let T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    (W n α).comp (invMinkowskiFourierCLM n)
  obtain ⟨S_sem, C_T, hCT_pos, hT_bound⟩ := schwartz_clm_bound n T
  let h_sem := fun km : ℕ × ℕ => cone_psi_seminorm_poly_growth hn hRz_nn hγ_pos km.1 km.2
  let N_max : ℕ := S_sem.sup (fun km => (h_sem km).choose)
  let C_tot : ℝ := C_T * ∑ km ∈ S_sem, (h_sem km).choose_spec.choose
  have hCtot_nn : 0 ≤ C_tot :=
    mul_nonneg hCT_pos.le (Finset.sum_nonneg fun km _ => (h_sem km).choose_spec.choose_spec.1)
  refine ⟨N_max, C_tot, hCtot_nn, fun x hx y hy s hs0 hs1 => ?_⟩
  let w : Fin (n * 4) → ℂ := fun p => (x p : ℂ) + ((s * y p : ℝ) : ℂ) * Complex.I
  let z : Fin n → Fin 4 → ℂ := (spacetimeFlatCLE_C n).symm w
  have hw_im : (fun p => (w p).im) = s • y := by
    ext p
    simp [w]
  have hw_tube : w ∈ TubeDomain (forwardTubeConeFlat n) := by
    change (fun p => (w p).im) ∈ forwardTubeConeFlat n
    rw [hw_im]
    exact smul_mem_forwardTubeConeFlat n hs0 (hLV hy)
  have hz_tube : z ∈ forward_tube_n n :=
    symm_mem_forward_tube_of_mem_tubeDomain n hw_tube
  have hx_norm : ‖x‖ ≤ max R_K 0 := by
    have h1 := hRK hx
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    exact h1.trans (le_max_left _ _)
  have hy_norm : ‖y‖ ≤ max R_L 0 := by
    have h1 := hRL hy
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    exact h1.trans (le_max_left _ _)
  have hz_norm : ‖z‖ ≤ R_z := by
    refine (pi_norm_le_iff_of_nonneg hRz_nn).mpr fun i => ?_
    refine (pi_norm_le_iff_of_nonneg hRz_nn).mpr fun μ => ?_
    let p := finProdFinEquiv (i, μ)
    change ‖(x p : ℂ) + ((s * y p : ℝ) : ℂ) * Complex.I‖ ≤ R_z
    have h_tri := norm_add_le (x p : ℂ) (((s * y p : ℝ) : ℂ) * Complex.I)
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hs0] at h_tri
    have hxp : |x p| ≤ max R_K 0 :=
      (Real.norm_eq_abs (x p) ▸ norm_le_pi_norm x p).trans hx_norm
    have hyp : |y p| ≤ max R_L 0 :=
      (Real.norm_eq_abs (y p) ▸ norm_le_pi_norm y p).trans hy_norm
    have hsyp : s * |y p| ≤ max R_L 0 := by nlinarith [abs_nonneg (y p)]
    dsimp [R_z]
    linarith
  have hγ_le : ∀ (i : Fin n) (hi : i.val + 1 < n), s * γ ≤ coneGap (diff_im n z i hi) := by
    intro i hi
    have h_diff_eq : diff_im n z i hi =
        s • (fun μ => -((spacetimeFlatCLE n).symm y i μ -
          (spacetimeFlatCLE n).symm y ⟨i.val + 1, hi⟩ μ)) := by
      ext μ
      dsimp [diff_im, diff_z, z, w, spacetimeFlatCLE_C, spacetimeFlatLinearEquivC,
        spacetimeFlatCLE, spacetimeFlatLinearEquiv]
      simp only [Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, zero_add]
      ring
    rw [h_diff_eq, coneGap_smul hs0.le]
    have h_inf_le : gap_fn y ≤ coneGap (fun μ => -((spacetimeFlatCLE n).symm y i μ -
        (spacetimeFlatCLE n).symm y ⟨i.val + 1, hi⟩ μ)) :=
      Finset.inf'_le _ (Finset.mem_univ (⟨i, hi⟩ : Idx))
    have hy_ge : γ ≤ gap_fn y := hy_min_le hy
    exact mul_le_mul_of_nonneg_left (hy_ge.trans h_inf_le) hs0.le
  have hH_eq : tubeForwardFlat (coneVladimirovTubeExtension R W hspec hP) n α w =
      T (cone_psi_schwartz n hn z hz_tube) := by
    change cone_H W n α z = T (cone_psi_schwartz n hn z hz_tube)
    dsimp [cone_H, T]
    rw [dif_neg hn, cone_psi_schwartz_total_eq hn hz_tube]
    rfl
  rw [hH_eq]
  have h_sup_le : (S_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
      (cone_psi_schwartz n hn z hz_tube) ≤
      (∑ km ∈ S_sem, (h_sem km).choose_spec.choose) / s ^ N_max := by
    have h_sum_le : ∀ U : Finset (ℕ × ℕ), U ⊆ S_sem →
        (U.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
          (cone_psi_schwartz n hn z hz_tube) ≤
        ∑ km ∈ U, (h_sem km).choose_spec.choose / s ^ N_max := by
      intro U
      induction U using Finset.induction_on with
      | empty =>
        intro _
        rw [Finset.sup_empty, Seminorm.bot_eq_zero, _root_.zero_apply, Finset.sum_empty]
      | @insert a U ha ih =>
        intro hU
        rw [Finset.sup_insert, Seminorm.sup_apply, Finset.sum_insert ha]
        have ha_S : a ∈ S_sem := hU (Finset.mem_insert_self a U)
        have ha_N : (h_sem a).choose ≤ N_max :=
          Finset.le_sup (f := fun km => (h_sem km).choose) ha_S
        have ha_bd := (h_sem a).choose_spec.choose_spec.2 z hz_tube hz_norm s hs0 hs1 hγ_le
        have h_pow_le : s ^ N_max ≤ s ^ (h_sem a).choose :=
          pow_le_pow_of_le_one hs0.le hs1 ha_N
        have h_div_le : (h_sem a).choose_spec.choose / s ^ (h_sem a).choose ≤
            (h_sem a).choose_spec.choose / s ^ N_max :=
          div_le_div_of_nonneg_left (h_sem a).choose_spec.choose_spec.1
            (pow_pos hs0 N_max) h_pow_le
        have ha_le : (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ a)
            (cone_psi_schwartz n hn z hz_tube) ≤
            (h_sem a).choose_spec.choose / s ^ N_max := ha_bd.trans h_div_le
        have hU_nn : 0 ≤ ∑ km ∈ U, (h_sem km).choose_spec.choose / s ^ N_max :=
          Finset.sum_nonneg fun km _ =>
            div_nonneg (h_sem km).choose_spec.choose_spec.1 (pow_pos hs0 N_max).le
        have ha_nn : 0 ≤ (h_sem a).choose_spec.choose / s ^ N_max :=
          div_nonneg (h_sem a).choose_spec.choose_spec.1 (pow_pos hs0 N_max).le
        exact max_le (ha_le.trans (le_add_of_nonneg_right hU_nn))
          ((ih fun km hkm => hU (Finset.mem_insert_of_mem hkm)).trans
            (le_add_of_nonneg_left ha_nn))
    exact (h_sum_le S_sem subset_rfl).trans (le_of_eq (Finset.sum_div _ _ _).symm)
  calc ‖T (cone_psi_schwartz n hn z hz_tube)‖
      ≤ C_T * (S_sem.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
          (cone_psi_schwartz n hn z hz_tube) := hT_bound _
    _ ≤ C_T * ((∑ km ∈ S_sem, (h_sem km).choose_spec.choose) / s ^ N_max) :=
        mul_le_mul_of_nonneg_left h_sup_le hCT_pos.le
    _ = C_tot / s ^ N_max := by dsimp [C_tot]; ring

noncomputable def revFlatCLE (n : ℕ) : (Fin (n * 4) → ℝ) ≃L[ℝ] (Fin (n * 4) → ℝ) :=
  ((spacetimeFlatCLE n).symm.trans (revCLE n)).trans (spacetimeFlatCLE n)

lemma revFlatCLE_involutive (n : ℕ) (u : Fin (n * 4) → ℝ) :
    revFlatCLE n (revFlatCLE n u) = u := by
  dsimp [revFlatCLE]
  rw [ContinuousLinearEquiv.symm_apply_apply, revCLE_involutive,
    ContinuousLinearEquiv.apply_symm_apply]

lemma revFlatCLE_mem_forwardTubeConeFlat_of_mem_neg (n : ℕ) {y : Fin (n * 4) → ℝ}
    (hy : y ∈ (fun v => -v) '' forwardTubeConeFlat n) :
    revFlatCLE n y ∈ forwardTubeConeFlat n := by
  let w : Fin (n * 4) → ℂ := fun p => (y p : ℂ) * Complex.I
  have hw : w ∈ TubeDomain ((fun v => -v) '' forwardTubeConeFlat n) := by
    simpa [TubeDomain, w] using hy
  have h_rev := symm_rev_mem_forward_tube_of_mem_neg_tubeDomain n hw
  have h_im : (fun p => (spacetimeFlatCLE_C n (((spacetimeFlatCLE_C n).symm w) ∘ Fin.rev) p).im) =
      revFlatCLE n y := by
    ext p
    dsimp [revFlatCLE, revCLE, revLinearEquiv, w]
    simp
  have h_td := (mem_tubeDomain_forwardTubeConeFlat_iff n _).mpr h_rev
  change (fun p => (spacetimeFlatCLE_C n (((spacetimeFlatCLE_C n).symm w) ∘ Fin.rev) p).im) ∈
    forwardTubeConeFlat n at h_td
  rwa [h_im] at h_td

theorem coneVladimirov_hasPolynomialTubeGrowth_backward
    (η : ℂ) (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    {n : ℕ} (hn : ¬ n ≤ 1) (α : Fin n → ι) :
    Distribution.HasPolynomialTubeGrowth ((fun y => -y) '' forwardTubeConeFlat n)
      (tubeBackwardRevFlat η (coneVladimirovTubeExtension R W hspec hP) n α) := by
  intro K L hK hL hLV
  let K' := revFlatCLE n '' K
  let L' := revFlatCLE n '' L
  have hK' : IsCompact K' := hK.image (revFlatCLE n).continuous
  have hL' : IsCompact L' := hL.image (revFlatCLE n).continuous
  have hL'V : L' ⊆ forwardTubeConeFlat n := by
    rintro _ ⟨y, hy, rfl⟩
    exact revFlatCLE_mem_forwardTubeConeFlat_of_mem_neg n (hLV hy)
  obtain ⟨N, C, hC_nn, hbd⟩ :=
    coneVladimirov_hasPolynomialTubeGrowth_forward R W hspec hP hn (α ∘ Fin.rev) K' L' hK' hL' hL'V
  let C' : ℝ := ‖η ^ (n * (n - 1) / 2)‖ * C
  refine ⟨N, C', mul_nonneg (norm_nonneg _) hC_nn, fun x hx y hy s hs0 hs1 => ?_⟩
  have h_eq : tubeBackwardRevFlat η (coneVladimirovTubeExtension R W hspec hP) n α
      (fun p => (x p : ℂ) + ((s * y p : ℝ) : ℂ) * Complex.I) =
      η ^ (n * (n - 1) / 2) *
        tubeForwardFlat (coneVladimirovTubeExtension R W hspec hP) n (α ∘ Fin.rev)
          (fun p => (revFlatCLE n x p : ℂ) + ((s * revFlatCLE n y p : ℝ) : ℂ) * Complex.I) := by
    dsimp [tubeBackwardRevFlat, tubeForwardFlat]
    congr 2
    ext i μ
    dsimp [revFlatCLE, revCLE, revLinearEquiv]
    simp
  rw [h_eq, norm_mul]
  calc ‖η ^ (n * (n - 1) / 2)‖ *
        ‖tubeForwardFlat (coneVladimirovTubeExtension R W hspec hP) n (α ∘ Fin.rev)
          (fun p => (revFlatCLE n x p : ℂ) + ((s * revFlatCLE n y p : ℝ) : ℂ) * Complex.I)‖
      ≤ ‖η ^ (n * (n - 1) / 2)‖ * (C / s ^ N) :=
        mul_le_mul_of_nonneg_left
          (hbd _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ s hs0 hs1) (norm_nonneg _)
    _ = C' / s ^ N := by dsimp [C']; ring

lemma differentiableOn_eqOn_zero_polydisc {M : ℕ}
    {F : (Fin M → ℂ) → ℂ} {r : ℝ} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball (0 : Fin M → ℂ) r))
    (hF_real : ∀ u : Fin M → ℝ, F (fun p => (u p : ℂ)) = 0) :
    ∀ z ∈ Metric.ball (0 : Fin M → ℂ) r, F z = 0 := by
  suffices h_step : ∀ m : ℕ, m ≤ M → ∀ z ∈ Metric.ball (0 : Fin M → ℂ) r,
      (∀ p : Fin M, m ≤ p.val → (z p).im = 0) → F z = 0 by
    exact fun z hz => h_step M le_rfl z hz (fun p hp => absurd p.isLt (not_lt_of_ge hp))
  intro m hm
  induction m with
  | zero =>
    intro z _hz hz_im
    have hzx : (fun p => ((z p).re : ℂ)) = z := by
      ext p
      exact Complex.ext rfl (hz_im p (Nat.zero_le p.val)).symm
    rw [← hzx]
    exact hF_real (fun p => (z p).re)
  | succ m ih =>
    let idx : Fin M := ⟨m, hm⟩
    intro z hz hz_im
    let D : Set ℂ := Metric.ball (0 : ℂ) r
    let upd : ℂ → (Fin M → ℂ) := fun ζ => Function.update z idx ζ
    have hupd_diff : Differentiable ℂ upd := by
      rw [differentiable_pi]
      intro p
      by_cases hp : p = idx
      · subst hp; simp [upd]
      · simp [upd, hp]
    have hupd_maps : ∀ ζ ∈ D, upd ζ ∈ Metric.ball (0 : Fin M → ℂ) r := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_pi_lt_iff hr] at hz ⊢
      intro p
      by_cases hp : p = idx
      · subst hp; simpa [upd] using Metric.mem_ball.mp hζ
      · simpa [upd, hp] using hz p
    let g : ℂ → ℂ := fun ζ => F (upd ζ)
    have hg_an : AnalyticOnNhd ℂ g D :=
      (hF.comp hupd_diff.differentiableOn hupd_maps).analyticOnNhd Metric.isOpen_ball
    have hD_conn : IsPreconnected D := (convex_ball (0 : ℂ) r).isPreconnected
    have h0_mem : (0 : ℂ) ∈ D := Metric.mem_ball_self hr
    have hg_freq : ∃ᶠ ζ in 𝓝[≠] (0 : ℂ), g ζ = 0 := by
      rw [Filter.frequently_iff]
      intro V hV
      rw [mem_nhdsWithin] at hV
      rcases hV with ⟨O, hO_open, h0O, hOV⟩
      rcases Metric.isOpen_iff.mp hO_open (0 : ℂ) h0O with ⟨δ, hδ_pos, hδO⟩
      let ε : ℝ := min (r / 2) (δ / 2)
      have hε_pos : 0 < ε := lt_min (half_pos hr) (half_pos hδ_pos)
      have hε_O : (ε : ℂ) ∈ O := by
        apply hδO
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hε_pos]
        exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ_pos)
      have hε_ne : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε_pos.ne'
      have hε_D : (ε : ℂ) ∈ D := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hε_pos]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr)
      refine ⟨(ε : ℂ), hOV ⟨hε_O, hε_ne⟩, ih (Nat.le_of_succ_le hm) (upd (ε : ℂ))
        (hupd_maps (ε : ℂ) hε_D) fun p hp_ge => ?_⟩
      by_cases hp : p = idx
      · subst hp; simp [upd]
      · have hp_ne : p.val ≠ m := fun hv => hp (Fin.ext hv)
        have hp_succ : m + 1 ≤ p.val := Nat.succ_le_of_lt (lt_of_le_of_ne hp_ge hp_ne.symm)
        simpa [upd, hp] using hz_im p hp_succ
    have hg_zero : EqOn g 0 D :=
      hg_an.eqOn_zero_of_preconnected_of_frequently_eq_zero hD_conn h0_mem hg_freq
    have hz_idx : z idx ∈ D := by
      rw [Metric.mem_ball, dist_pi_lt_iff hr] at hz
      simpa [D, Metric.mem_ball] using hz idx
    have h_val := hg_zero hz_idx
    dsimp [g, upd] at h_val
    rwa [Function.update_eq_self] at h_val

lemma differentiableOn_eq_zero_of_convex_shifted_real {M : ℕ}
    {U : Set (Fin M → ℂ)} (hU_open : IsOpen U) (hU_conv : Convex ℝ U)
    {w₀ : Fin M → ℂ} (hw₀ : w₀ ∈ U)
    {G : (Fin M → ℂ) → ℂ} (hG : DifferentiableOn ℂ G U)
    (hG_real : ∀ u : Fin M → ℝ, G ((fun p => (u p : ℂ)) + w₀) = 0) :
    ∀ w ∈ U, G w = 0 := by
  let H : (Fin M → ℂ) → ℂ := fun z => G (z + w₀)
  let U' : Set (Fin M → ℂ) := { z | z + w₀ ∈ U }
  have hU'_open : IsOpen U' := hU_open.preimage (continuous_id.add continuous_const)
  have h0_U' : (0 : Fin M → ℂ) ∈ U' := by simpa [U'] using hw₀
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU'_open 0 h0_U'
  have hH_diff : DifferentiableOn ℂ H U' :=
    hG.comp (differentiable_id.add (differentiable_const w₀)).differentiableOn (fun _ hz => hz)
  have hH_ball : ∀ z ∈ Metric.ball (0 : Fin M → ℂ) r, H z = 0 :=
    differentiableOn_eqOn_zero_polydisc hr_pos (hH_diff.mono hr_sub) hG_real
  intro w hw
  let d : Fin M → ℂ := w - w₀
  let D : Set ℂ := { ζ : ℂ | ζ • d + w₀ ∈ U }
  have h_line_cont : Continuous (fun ζ : ℂ => ζ • d + w₀) :=
    (continuous_id.smul continuous_const).add continuous_const
  have hD_open : IsOpen D := hU_open.preimage h_line_cont
  have hD_conv : Convex ℝ D := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ a b ha hb hab
    change (a • ζ₁ + b • ζ₂) • d + w₀ ∈ U
    have h_lin : (a • ζ₁ + b • ζ₂) • d + w₀ =
        a • (ζ₁ • d + w₀) + b • (ζ₂ • d + w₀) := by
      ext p
      simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul]
      have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      calc ((a : ℂ) * ζ₁ + (b : ℂ) * ζ₂) * d p + w₀ p
          = ((a : ℂ) * ζ₁ + (b : ℂ) * ζ₂) * d p + 1 * w₀ p := by rw [one_mul]
        _ = ((a : ℂ) * ζ₁ + (b : ℂ) * ζ₂) * d p + ((a : ℂ) + (b : ℂ)) * w₀ p := by rw [habC]
        _ = (a : ℂ) * (ζ₁ * d p + w₀ p) + (b : ℂ) * (ζ₂ * d p + w₀ p) := by ring
    rw [h_lin]
    exact hU_conv hζ₁ hζ₂ ha hb hab
  have h0_D : (0 : ℂ) ∈ D := by simpa [D] using hw₀
  have h1_D : (1 : ℂ) ∈ D := by simpa [D, d] using hw
  let h : ℂ → ℂ := fun ζ => G (ζ • d + w₀)
  have hh_diff : DifferentiableOn ℂ h D :=
    hG.comp ((differentiable_id.smul_const d).add (differentiable_const w₀)).differentiableOn
      (fun _ hζ => hζ)
  have hh_an : AnalyticOnNhd ℂ h D := hh_diff.analyticOnNhd hD_open
  have h_ball_ζ : ∀ᶠ ζ : ℂ in 𝓝 0, h ζ = 0 := by
    have h_pre : (fun ζ : ℂ => ζ • d) ⁻¹' Metric.ball (0 : Fin M → ℂ) r ∈ 𝓝 (0 : ℂ) :=
      (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using Metric.ball_mem_nhds (0 : Fin M → ℂ) hr_pos)
    filter_upwards [h_pre] with ζ hζ
    exact hH_ball (ζ • d) hζ
  have hh_zero : EqOn h 0 D :=
    hh_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD_conv.isPreconnected h0_D h_ball_ζ
  have h_at_1 := hh_zero h1_D
  simpa [h, d] using h_at_1

lemma cone_vladimirov_phase_re_uniform_le {n : ℕ} (hn : ¬ n ≤ 1)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) (hz1 : ‖z‖ ≤ 1) :
    ∀ p ∈ tsupport (coneSpectralCutoff n),
      (vladimirov_phase_CLM n z p).re ≤ 8 + 6 * (n : ℝ) := by
  have h_supp : ∀ p ∈ Function.support (coneSpectralCutoff n),
      (vladimirov_phase_CLM n z p).re ≤ 8 + 6 * (n : ℝ) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    intro p hp
    have h_exp : Real.exp (vladimirov_phase_CLM (m + 1) z p).re =
        ‖vladimirov_kernel (m + 1) z p‖ := (Complex.norm_exp _).symm
    rw [vladimirov_kernel_norm] at h_exp
    have h_re_eq := Real.exp_injective h_exp
    rw [h_re_eq, abel_summation_minkowskiInner_general m p z, totalConePairing_succ]
    obtain ⟨htot, hstep⟩ := coneSpectralCutoff_support_bounds (m + 1) hp
    have h_last :
        minkowskiInner (total_momentum_LM (m + 1) p) (fun μ => (z (Fin.last m) μ).im) ≤ 8 := by
      have h1 := minkowskiInner_le_norm (total_momentum_LM (m + 1) p)
        (fun μ => (z (Fin.last m) μ).im)
      have h_im : ‖(fun μ : Fin 4 => (z (Fin.last m) μ).im)‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro μ
        rw [Real.norm_eq_abs]
        exact ((Complex.abs_im_le_norm _).trans
          ((norm_le_pi_norm _ μ).trans (norm_le_pi_norm z _))).trans hz1
      have h_le := le_abs_self
        (minkowskiInner (total_momentum_LM (m + 1) p) (fun μ => (z (Fin.last m) μ).im))
      nlinarith [norm_nonneg (total_momentum_LM (m + 1) p),
        norm_nonneg (fun μ : Fin 4 => (z (Fin.last m) μ).im)]
    have h_each : ∀ i : Fin m,
        -minkowskiInner (partial_sum_p (m + 1) p i.castSucc)
            (diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt)) ≤ 6 := by
      intro i
      let q := partial_sum_p (m + 1) p i.castSucc
      let v := diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt)
      have hq_cone := (shifted_mem_closed_cone_of_coneStepArg_pos
        (hstep i.castSucc (Nat.succ_lt_succ i.isLt))).1
      have h_gap := minkowskiInner_ge_coneGap v (q + (3 : ℝ) • unit_time_vector) hq_cone
      have h_lin : minkowskiInner (q + (3 : ℝ) • unit_time_vector) v =
          minkowskiInner q v + 3 * v 0 := by
        simp [minkowskiInner_explicit, unit_time_vector]; ring
      have h_q0 : (q + (3 : ℝ) • unit_time_vector) 0 = q 0 + 3 := by
        simp [unit_time_vector]
      rw [h_lin, h_q0] at h_gap
      have hq0_nn : 0 ≤ q 0 + 3 := by
        have h0 := hq_cone.1; rwa [h_q0] at h0
      have hγ_pos := coneGap_pos v (hz i.castSucc (Nat.succ_lt_succ i.isLt))
      have h_nn : 0 ≤ coneGap v * (q 0 + 3) := mul_nonneg hγ_pos.le hq0_nn
      have hv0 : v 0 ≤ 2 := by
        have h1 : |(z i.castSucc 0).im| ≤ 1 :=
          ((Complex.abs_im_le_norm _).trans
            ((norm_le_pi_norm _ 0).trans (norm_le_pi_norm z _))).trans hz1
        have h2 : |(z ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ 0).im| ≤ 1 :=
          ((Complex.abs_im_le_norm _).trans
            ((norm_le_pi_norm _ 0).trans (norm_le_pi_norm z _))).trans hz1
        change -((z i.castSucc 0).im - (z ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ 0).im) ≤ 2
        linarith [neg_abs_le (z i.castSucc 0).im,
          le_abs_self (z ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ 0).im]
      linarith
    have h_sum : -(∑ i : Fin m, minkowskiInner (partial_sum_p (m + 1) p i.castSucc)
          (diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt))) ≤
        6 * ((m + 1 : ℕ) : ℝ) := by
      rw [← Finset.sum_neg_distrib]
      have h1 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_each i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
      have hm_le : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
      linarith
    linarith
  have h_cont : Continuous (fun q => (vladimirov_phase_CLM n z q).re) :=
    Complex.continuous_re.comp (vladimirov_phase_CLM n z).continuous
  exact (isClosed_le h_cont continuous_const).closure_subset_iff.mpr h_supp

open Classical in
lemma cone_psi_mul_fourier_seminorm_tendsto {n : ℕ} (hn : ¬ n ≤ 1)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (km : ℕ × ℕ) :
    Tendsto (fun y : Fin (n * 4) → ℝ =>
      if hy : y ∈ forwardTubeConeFlat n then
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
          (SchwartzMap.smulLeftCLM ℂ (fun p => minkowskiFourierCLM n f p)
            (cone_psi_schwartz n hn
              ((spacetimeFlatCLE_C n).symm (fun p => (y p : ℂ) * Complex.I))
              (symm_mem_forward_tube_of_mem_tubeDomain n (by simpa [TubeDomain] using hy))) -
            cone_limit_schwartz n f)
      else 0) (𝓝[forwardTubeConeFlat n] 0) (𝓝 0) := by
  obtain ⟨C_L, hCL_nn, hCL⟩ := vladimirov_phase_clm_norm_le_all n
  let B : ℝ := 8 + 6 * (n : ℝ)
  have hB_nn : 0 ≤ B := by positivity
  let limit_s := cone_limit_schwartz n f
  let k := km.1
  let m := km.2
  let C_km : ℝ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
    (if m - i = 0 then 2 * Real.exp B * C_L * SchwartzMap.seminorm ℝ (k + 1) i limit_s
     else Real.exp B * (C_L + 1) ^ (m - i) * SchwartzMap.seminorm ℝ k i limit_s)
  have h_ball : { y : Fin (n * 4) → ℝ | ‖y‖ < 1 } ∈ 𝓝 (0 : Fin (n * 4) → ℝ) := by
    simpa [Metric.ball, dist_zero_right] using
      Metric.ball_mem_nhds (0 : Fin (n * 4) → ℝ) zero_lt_one
  have h_ev : ∀ᶠ y : Fin (n * 4) → ℝ in 𝓝[forwardTubeConeFlat n] 0,
      y ∈ forwardTubeConeFlat n ∧ ‖y‖ < 1 :=
    Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds h_ball)
  have h_bound : ∀ᶠ y : Fin (n * 4) → ℝ in 𝓝[forwardTubeConeFlat n] 0,
      (if hy : y ∈ forwardTubeConeFlat n then
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
          (SchwartzMap.smulLeftCLM ℂ (fun p => minkowskiFourierCLM n f p)
            (cone_psi_schwartz n hn
              ((spacetimeFlatCLE_C n).symm (fun p => (y p : ℂ) * Complex.I))
              (symm_mem_forward_tube_of_mem_tubeDomain n (by simpa [TubeDomain] using hy))) -
            limit_s)
      else 0) ≤ ‖y‖ * C_km := by
    refine h_ev.mono fun y ⟨hy, hy_lt1⟩ => ?_
    rw [dif_pos hy]
    let z_y : Fin n → Fin 4 → ℂ :=
      (spacetimeFlatCLE_C n).symm (fun p => (y p : ℂ) * Complex.I)
    have hz_y : z_y ∈ forward_tube_n n :=
      symm_mem_forward_tube_of_mem_tubeDomain n (by simpa [TubeDomain] using hy)
    have hz_norm : ‖z_y‖ ≤ ‖y‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun i => ?_
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr fun μ => ?_
      let p := finProdFinEquiv (i, μ)
      change ‖(y p : ℂ) * Complex.I‖ ≤ ‖y‖
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
      exact norm_le_pi_norm y p
    have hz_le1 : ‖z_y‖ ≤ 1 := hz_norm.trans hy_lt1.le
    let L_y := vladimirov_phase_CLM n z_y
    have hL_norm : ‖L_y‖ ≤ C_L * ‖y‖ :=
      (hCL z_y).trans (mul_le_mul_of_nonneg_left hz_norm hCL_nn)
    change SchwartzMap.seminorm ℝ k m _ ≤ ‖y‖ * C_km
    refine SchwartzMap.seminorm_le_bound ℝ k m _
      (mul_nonneg (norm_nonneg y) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity))
      fun p => ?_
    let htg_f : Function.HasTemperateGrowth (fun q => minkowskiFourierCLM n f q) :=
      (minkowskiFourierCLM n f).hasTemperateGrowth
    by_cases hp_supp : p ∈ tsupport (coneSpectralCutoff n)
    · let δ_y : (Fin n → Fin 4 → ℝ) → ℂ := fun q => Complex.exp (L_y q) - 1
      have h_fn : ⇑(SchwartzMap.smulLeftCLM ℂ (fun q => minkowskiFourierCLM n f q)
          (cone_psi_schwartz n hn z_y hz_y) - limit_s) = fun q => limit_s q * δ_y q := by
        ext q
        change SchwartzMap.smulLeftCLM ℂ (fun r => minkowskiFourierCLM n f r)
          (cone_psi_schwartz n hn z_y hz_y) q - cone_limit_schwartz n f q = _
        rw [SchwartzMap.smulLeftCLM_apply_apply htg_f, smul_eq_mul,
          minkowskiFourierCLM_apply, cone_limit_schwartz_apply]
        change minkowskiFourier f q * cone_psi n z_y q - _ = _
        dsimp [cone_psi, δ_y, L_y]
        have hker : vladimirov_kernel n z_y q = Complex.exp (vladimirov_phase_CLM n z_y q) := rfl
        rw [hker]
        ring
      rw [h_fn]
      have hδ_cd : ContDiff ℝ (⊤ : ℕ∞) δ_y :=
        (Complex.contDiff_exp.comp L_y.contDiff).sub contDiff_const
      have h_leib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ⇑limit_s) (g := δ_y)
        (n := m) (N := (⊤ : ℕ∞)) limit_s.smooth' hδ_cd p (WithTop.coe_le_coe.mpr le_top)
      have h_re : (L_y p).re ≤ B :=
        cone_vladimirov_phase_re_uniform_le hn hz_y hz_le1 p hp_supp
      have h_step : ∀ i ∈ Finset.range (m + 1),
          ‖p‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ *
            ‖iteratedFDeriv ℝ (m - i) δ_y p‖) ≤
          ‖y‖ * ((m.choose i : ℝ) *
            (if m - i = 0 then 2 * Real.exp B * C_L * SchwartzMap.seminorm ℝ (k + 1) i limit_s
             else Real.exp B * (C_L + 1) ^ (m - i) * SchwartzMap.seminorm ℝ k i limit_s)) := by
        intro i _hi
        by_cases hmi : m - i = 0
        · rw [if_pos hmi, hmi, norm_iteratedFDeriv_zero]
          have hδ0 := complex_norm_exp_sub_one_le_of_re_le hB_nn h_re
          have h_Lp : ‖L_y p‖ ≤ C_L * ‖y‖ * ‖p‖ :=
            (L_y.le_opNorm p).trans (mul_le_mul_of_nonneg_right hL_norm (norm_nonneg p))
          have h_bnd : ‖δ_y p‖ ≤ ‖y‖ * (2 * Real.exp B * C_L * ‖p‖) := by
            calc ‖δ_y p‖ ≤ 2 * Real.exp B * ‖L_y p‖ := hδ0
              _ ≤ 2 * Real.exp B * (C_L * ‖y‖ * ‖p‖) :=
                  mul_le_mul_of_nonneg_left h_Lp (by positivity)
              _ = ‖y‖ * (2 * Real.exp B * C_L * ‖p‖) := by ring
          have h_pk1 := SchwartzMap.le_seminorm ℝ (k + 1) i limit_s p
          have h_ppow : ‖p‖ ^ k * ‖p‖ = ‖p‖ ^ (k + 1) := (pow_succ ‖p‖ k).symm
          calc ‖p‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ * ‖δ_y p‖)
              ≤ ‖p‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ *
                  (‖y‖ * (2 * Real.exp B * C_L * ‖p‖))) := by gcongr
            _ = ‖y‖ * ((m.choose i : ℝ) * (2 * Real.exp B * C_L *
                  (‖p‖ ^ (k + 1) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖))) := by
                rw [← h_ppow]; ring
            _ ≤ ‖y‖ * ((m.choose i : ℝ) * (2 * Real.exp B * C_L *
                  SchwartzMap.seminorm ℝ (k + 1) i limit_s)) := by gcongr
        · rw [if_neg hmi]
          obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hmi
          have h_id : iteratedFDeriv ℝ (m - i) δ_y p =
              iteratedFDeriv ℝ (m - i) (Complex.exp ∘ L_y) p := by
            have h_sub_fn : δ_y = (Complex.exp ∘ L_y) - fun _ => (1 : ℂ) := rfl
            rw [h_sub_fn]
            have h_cd1 : ContDiffAt ℝ (m - i) (Complex.exp ∘ L_y) p :=
              (Complex.contDiff_exp.comp L_y.contDiff).contDiffAt
            have h_cd2 : ContDiffAt ℝ (m - i) (fun _ : Fin n → Fin 4 → ℝ => (1 : ℂ)) p :=
              contDiff_const.contDiffAt
            have h_sub := iteratedFDeriv_sub_apply h_cd1 h_cd2
            have h_zero :
                iteratedFDeriv ℝ (m - i) (fun _ : Fin n → Fin 4 → ℝ => (1 : ℂ)) p = 0 := by
              rw [hj, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
              rfl
            rw [h_sub, h_zero, sub_zero]
          rw [h_id]
          have h_le := norm_iteratedFDeriv_comp_clm_le L_y Complex.exp Complex.contDiff_exp
            p (m - i)
          rw [norm_iteratedFDeriv_real_exp] at h_le
          have h_exp_le : Real.exp (L_y p).re ≤ Real.exp B := Real.exp_le_exp.mpr h_re
          have h_pow_y : ‖L_y‖ ^ (m - i) ≤ ‖y‖ * (C_L + 1) ^ (m - i) := by
            rw [hj, pow_succ, pow_succ]
            have hL1 : ‖L_y‖ ≤ C_L + 1 := hL_norm.trans (by nlinarith [hy_lt1, hCL_nn])
            have h1 : ‖L_y‖ ^ j ≤ (C_L + 1) ^ j := pow_le_pow_left₀ (norm_nonneg L_y) hL1 j
            have h2 : ‖L_y‖ ≤ ‖y‖ * (C_L + 1) := hL_norm.trans (by nlinarith [norm_nonneg y])
            calc ‖L_y‖ ^ j * ‖L_y‖ ≤ (C_L + 1) ^ j * (‖y‖ * (C_L + 1)) :=
                  mul_le_mul h1 h2 (norm_nonneg L_y) (by positivity)
              _ = ‖y‖ * ((C_L + 1) ^ j * (C_L + 1)) := by ring
          have h_bnd : ‖iteratedFDeriv ℝ (m - i) (Complex.exp ∘ L_y) p‖ ≤
              ‖y‖ * (Real.exp B * (C_L + 1) ^ (m - i)) := by
            calc ‖iteratedFDeriv ℝ (m - i) (Complex.exp ∘ L_y) p‖
                ≤ Real.exp (L_y p).re * ‖L_y‖ ^ (m - i) := h_le
              _ ≤ Real.exp B * (‖y‖ * (C_L + 1) ^ (m - i)) :=
                  mul_le_mul h_exp_le h_pow_y (by positivity) (Real.exp_pos B).le
              _ = ‖y‖ * (Real.exp B * (C_L + 1) ^ (m - i)) := by ring
          have h_pk := SchwartzMap.le_seminorm ℝ k i limit_s p
          calc ‖p‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ *
                  ‖iteratedFDeriv ℝ (m - i) (Complex.exp ∘ L_y) p‖)
              ≤ ‖p‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ *
                  (‖y‖ * (Real.exp B * (C_L + 1) ^ (m - i)))) := by gcongr
            _ = ‖y‖ * ((m.choose i : ℝ) * (Real.exp B * (C_L + 1) ^ (m - i) *
                  (‖p‖ ^ k * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖))) := by ring
            _ ≤ ‖y‖ * ((m.choose i : ℝ) * (Real.exp B * (C_L + 1) ^ (m - i) *
                  SchwartzMap.seminorm ℝ k i limit_s)) := by gcongr
      calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ m (fun q => limit_s q * δ_y q) p‖
          ≤ ‖p‖ ^ k * ∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ *
                ‖iteratedFDeriv ℝ (m - i) δ_y p‖ :=
            mul_le_mul_of_nonneg_left h_leib (pow_nonneg (norm_nonneg p) k)
        _ = ∑ i ∈ Finset.range (m + 1),
              ‖p‖ ^ k * ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (⇑limit_s) p‖ *
                ‖iteratedFDeriv ℝ (m - i) δ_y p‖) := Finset.mul_sum _ _ _
        _ ≤ ∑ i ∈ Finset.range (m + 1), ‖y‖ * ((m.choose i : ℝ) *
              (if m - i = 0 then 2 * Real.exp B * C_L * SchwartzMap.seminorm ℝ (k + 1) i limit_s
               else Real.exp B * (C_L + 1) ^ (m - i) * SchwartzMap.seminorm ℝ k i limit_s)) :=
            Finset.sum_le_sum h_step
        _ = ‖y‖ * C_km := (Finset.mul_sum _ _ _).symm
    · have h_open : (tsupport (coneSpectralCutoff n))ᶜ ∈ 𝓝 p :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hp_supp
      have h_ev0 : (⇑(SchwartzMap.smulLeftCLM ℂ (fun q => minkowskiFourierCLM n f q)
          (cone_psi_schwartz n hn z_y hz_y) - limit_s)) =ᶠ[𝓝 p]
          (fun _ : Fin n → Fin 4 → ℝ => (0 : ℂ)) := by
        filter_upwards [h_open] with q hq
        have h_cut0 : coneSpectralCutoff n q = 0 := image_eq_zero_of_notMem_tsupport hq
        change SchwartzMap.smulLeftCLM ℂ (fun r => minkowskiFourierCLM n f r)
          (cone_psi_schwartz n hn z_y hz_y) q - cone_limit_schwartz n f q = 0
        rw [SchwartzMap.smulLeftCLM_apply_apply htg_f, smul_eq_mul,
          minkowskiFourierCLM_apply, cone_limit_schwartz_apply]
        change minkowskiFourier f q * cone_psi n z_y q - _ = 0
        dsimp [cone_psi]
        rw [h_cut0]
        simp
      rw [(h_ev0.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_fun_zero]
      simp only [Pi.zero_apply, norm_zero, mul_zero]
      exact mul_nonneg (norm_nonneg y) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  have h_tend0 : Tendsto (fun y : Fin (n * 4) → ℝ => ‖y‖ * C_km)
      (𝓝[forwardTubeConeFlat n] 0) (𝓝 0) := by
    have h1 : Tendsto (fun y : Fin (n * 4) → ℝ => ‖y‖ * C_km)
        (𝓝[forwardTubeConeFlat n] 0) (𝓝 (‖(0 : Fin (n * 4) → ℝ)‖ * C_km)) :=
      ((continuous_norm.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    rwa [norm_zero, zero_mul] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_tend0 ?_ h_bound
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [dif_pos hy]
  exact apply_nonneg _ _

open Classical in
theorem coneVladimirov_hasBoundaryValue_forward
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    {n : ℕ} (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (Ω : TopologicalSpace.Opens (Fin (n * 4) → ℝ)) :
    Distribution.HasBoundaryValue Ω
      (tubeForwardFlat (coneVladimirovTubeExtension R W hspec hP) n α)
      (forwardTubeConeFlat n)
      (Distribution.temperedToDistribution Ω (wightmanFlatTD W n α)) := by
  let E := coneVladimirovTubeExtension R W hspec hP
  intro φ
  let ψ : SchwartzMap (Fin (n * 4) → ℝ) ℂ := Distribution.testFunctionToSchwartzCLM Ω φ
  let f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ := schwartzFlatCLM n ψ
  have hW_target : Distribution.temperedToDistribution Ω (wightmanFlatTD W n α) φ = W n α f := rfl
  rw [hW_target]
  let T₀ : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    (W n α).comp (invMinkowskiFourierCLM n)
  let M_f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ (fun p => minkowskiFourierCLM n f p)
  let T_f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ := T₀.comp M_f
  let U_flat : Set (Fin (n * 4) → ℂ) := TubeDomain (forwardTubeConeFlat n)
  have hU_open : IsOpen U_flat := isOpen_TubeDomain (isOpen_forwardTubeConeFlat n)
  have hU_conv : Convex ℝ U_flat := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    have h_im : (fun p => ((a • w₁ + b • w₂) p).im) =
        a • (fun p => (w₁ p).im) + b • (fun p => (w₂ p).im) := by
      ext p; simp
    change (fun p => ((a • w₁ + b • w₂) p).im) ∈ forwardTubeConeFlat n
    rw [h_im]
    exact convex_forwardTubeConeFlat n hw₁ hw₂ ha hb hab
  let F_L : (Fin (n * 4) → ℂ) → ℂ :=
    fun w => T_f (cone_psi_schwartz_total n hn ((spacetimeFlatCLE_C n).symm w))
  let F_R : (Fin (n * 4) → ℂ) → ℂ :=
    fun w => ∫ u : Fin (n * 4) → ℝ,
      tubeForwardFlat E n α (fun p => (u p : ℂ) + w p) * (φ u : ℂ)
  have hFL_diff : DifferentiableOn ℂ F_L U_flat := by
    have h_an : AnalyticOnNhd ℂ F_L U_flat := fun w hw =>
      (cone_psi_schwartz_analyticAt hn (symm_mem_forward_tube_of_mem_tubeDomain n hw) T_f).comp
        ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
    exact h_an.differentiableOn
  let φ_neg : (Fin (n * 4) → ℝ) → ℝ := fun t => φ (-t)
  have hφ_neg_cd : ContDiff ℝ (⊤ : ℕ∞) φ_neg := φ.contDiff'.comp contDiff_neg
  have hφ_neg_supp : HasCompactSupport φ_neg :=
    φ.hasCompactSupport'.comp_homeomorph (Homeomorph.neg _)
  have hFR_eq_tc : F_R = Distribution.tubeConv (tubeForwardFlat E n α) φ_neg := by
    ext w
    dsimp [F_R, Distribution.tubeConv, φ_neg]
    rw [← MeasureTheory.integral_neg_eq_self]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    have h_pt : (fun p => ((-u) p : ℂ) + w p) = fun p => w p - (u p : ℂ) := by
      ext p
      simp [sub_eq_add_neg, add_comm]
    rw [h_pt]
  have hFR_diff : DifferentiableOn ℂ F_R U_flat := by
    rw [hFR_eq_tc]
    exact Distribution.differentiableOn_tubeConv (isOpen_forwardTubeConeFlat n)
      (differentiableOn_tubeForwardFlat E n α) hφ_neg_cd.continuous hφ_neg_supp
  let v := unit_time_vector
  have hv : v ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
  let z₀ : Fin n → Fin 4 → ℂ := tubeApproach n 0 v 1
  have hz₀ : z₀ ∈ forward_tube_n n := tubeApproach_mem_forward_tube_n n 0 v hv 1 one_pos
  let w₀ : Fin (n * 4) → ℂ := spacetimeFlatCLE_C n z₀
  have hw₀ : w₀ ∈ U_flat := (mem_tubeDomain_forwardTubeConeFlat_iff n z₀).mpr hz₀
  have h_eq_shifted_real : ∀ u₀ : Fin (n * 4) → ℝ, F_L ((fun p => (u₀ p : ℂ)) + w₀) =
      F_R ((fun p => (u₀ p : ℂ)) + w₀) := by
    intro u₀
    let x₀ : Fin n → Fin 4 → ℝ := (spacetimeFlatCLE n).symm u₀
    have h_symm_w : (spacetimeFlatCLE_C n).symm ((fun p => (u₀ p : ℂ)) + w₀) =
        tubeApproach n x₀ v 1 := by
      ext i μ
      rw [map_add, spacetimeFlatCLE_C_symm_ofReal]
      have hw₀_symm : (spacetimeFlatCLE_C n).symm w₀ = z₀ :=
        ContinuousLinearEquiv.symm_apply_apply (spacetimeFlatCLE_C n) z₀
      rw [hw₀_symm]
      dsimp [coeReal, x₀, z₀, tubeApproach]
      simp
    have h_mf_eq : M_f (cone_psi_schwartz n hn (tubeApproach n x₀ v 1)
        (tubeApproach_mem_forward_tube_n n x₀ v hv 1 one_pos)) =
        conv_schwartz n hn (schwartzTranslateN n x₀ f) v hv 1 one_pos := by
      ext p
      have htg_f : Function.HasTemperateGrowth (fun q => minkowskiFourierCLM n f q) :=
        (minkowskiFourierCLM n f).hasTemperateGrowth
      rw [SchwartzMap.smulLeftCLM_apply_apply htg_f, smul_eq_mul,
        minkowskiFourierCLM_apply, conv_schwartz_apply, minkowskiFourier_schwartzTranslateN,
        cone_psi_tubeApproach_factor n hn v hv 1 one_pos x₀ p]
      change minkowskiFourier f p * (cone_psi n (tubeApproach n 0 v 1) p *
        vladimirov_kernel n (fun i k => (x₀ i k : ℂ)) p) = _
      have h_ker_eq : vladimirov_kernel n (fun i k => (x₀ i k : ℂ)) p =
          Complex.exp (-(Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (x₀ k) : ℝ) : ℂ))) := by
        dsimp [vladimirov_kernel]
        congr 1
        have h_sum : ∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (fun μ => (x₀ k μ : ℂ)) =
            ((∑ k : Fin n, minkowskiInner (p k) (x₀ k) : ℝ) : ℂ) := by
          have h_term : ∀ k : Fin n,
              minkowskiInnerC (fun μ => (p k μ : ℂ)) (fun μ => (x₀ k μ : ℂ)) =
                (minkowskiInner (p k) (x₀ k) : ℂ) := by
            intro k
            dsimp [minkowskiInnerC]
            rw [minkowskiInner_explicit]
            push_cast
            ring
          simp_rw [h_term]
          push_cast
          rfl
        rw [h_sum]
        ring
      rw [h_ker_eq]
      ring
    have hFL_val : F_L ((fun p => (u₀ p : ℂ)) + w₀) =
        T₀ (conv_schwartz n hn (schwartzTranslateN n x₀ f) v hv 1 one_pos) := by
      dsimp [F_L, T_f]
      rw [h_symm_w,
        cone_psi_schwartz_total_eq hn (tubeApproach_mem_forward_tube_n n x₀ v hv 1 one_pos),
        h_mf_eq]
    rw [hFL_val, clm_conv_schwartz_eq_integral n hn T₀ (schwartzTranslateN n x₀ f) v hv 1 one_pos]
    have h_shift := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume)
      (fun x : Fin n → Fin 4 → ℝ => schwartzTranslateN n x₀ f x *
        T₀ (cone_psi_schwartz n hn (tubeApproach n x v 1)
          (tubeApproach_mem_forward_tube_n n x v hv 1 one_pos))) x₀
    rw [← h_shift]
    dsimp [F_R]
    rw [← integral_comp_spacetimeFlatCLE n]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [schwartzTranslateN_apply, add_sub_cancel_right]
    have h_Hx : T₀ (cone_psi_schwartz n hn (tubeApproach n (x + x₀) v 1)
        (tubeApproach_mem_forward_tube_n n (x + x₀) v hv 1 one_pos)) =
        tubeForwardFlat E n α
          (fun p => (spacetimeFlatCLE n x p : ℂ) + (((fun q => (u₀ q : ℂ)) + w₀) p)) := by
      have h_arg : (spacetimeFlatCLE_C n).symm
          (fun p => (spacetimeFlatCLE n x p : ℂ) + (((fun q => (u₀ q : ℂ)) + w₀) p)) =
          tubeApproach n (x + x₀) v 1 := by
        ext i μ
        change ((spacetimeFlatCLE_C n).symm
            ((fun p => (spacetimeFlatCLE n x p : ℂ)) + ((fun q => (u₀ q : ℂ)) + w₀))) i μ = _
        rw [map_add, h_symm_w, spacetimeFlatCLE_C_symm_ofReal,
          ContinuousLinearEquiv.symm_apply_apply]
        dsimp [coeReal, tubeApproach]
        simp
        ring
      change _ = cone_H W n α ((spacetimeFlatCLE_C n).symm
        (fun p => (spacetimeFlatCLE n x p : ℂ) + (((fun q => (u₀ q : ℂ)) + w₀) p)))
      rw [h_arg]
      dsimp [cone_H, T₀]
      rw [dif_neg hn,
        cone_psi_schwartz_total_eq hn (tubeApproach_mem_forward_tube_n n (x + x₀) v hv 1 one_pos)]
      rfl
    rw [h_Hx]
    dsimp [f, ψ]
    ring
  have h_eq_all : ∀ w ∈ U_flat, F_L w = F_R w := by
    intro w hw
    have h0 := differentiableOn_eq_zero_of_convex_shifted_real hU_open hU_conv hw₀
      (hFL_diff.sub hFR_diff) (fun u₀ => sub_eq_zero.mpr (h_eq_shifted_real u₀)) w hw
    exact sub_eq_zero.mp h0
  have h_limit_W : T₀ (cone_limit_schwartz n f) = W n α f := by
    change W n α (invMinkowskiFourierCLM n (cone_limit_schwartz n f)) = W n α f
    refine W_eq_of_fourier_eq W hspec n α (invMinkowskiFourierCLM n (cone_limit_schwartz n f)) f
      (coneOpenNhd n) (isOpen_coneOpenNhd n) (spectralRegion_subset_coneOpenNhd n) fun p hp => ?_
    rw [minkowskiFourier_invMinkowskiFourierCLM_all, cone_limit_schwartz_apply,
      coneSpectralCutoff_eq_one_of_mem_coneOpenNhd n hp, Complex.ofReal_one, one_mul]
  rw [← h_limit_W]
  have h_ev_eq : ∀ᶠ y : Fin (n * 4) → ℝ in 𝓝[forwardTubeConeFlat n] 0,
      F_R (fun p => (y p : ℂ) * Complex.I) =
      if hy : y ∈ forwardTubeConeFlat n then
        T₀ (M_f (cone_psi_schwartz n hn
          ((spacetimeFlatCLE_C n).symm (fun p => (y p : ℂ) * Complex.I))
          (symm_mem_forward_tube_of_mem_tubeDomain n (by simpa [TubeDomain] using hy))))
      else 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [dif_pos hy]
    have hw_y : (fun p => (y p : ℂ) * Complex.I) ∈ U_flat := by simpa [U_flat, TubeDomain] using hy
    rw [← h_eq_all _ hw_y]
    dsimp [F_L, T_f]
    rw [cone_psi_schwartz_total_eq hn (symm_mem_forward_tube_of_mem_tubeDomain n hw_y)]
  have h_int_eq : Distribution.boundaryIntegral Ω (tubeForwardFlat E n α) φ =
      fun y => F_R (fun p => (y p : ℂ) * Complex.I) := rfl
  rw [h_int_eq, tendsto_congr' h_ev_eq, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, C_T, hCT_pos, hT_bound⟩ := schwartz_clm_bound n T₀
  have h_each : ∀ km ∈ s, ∀ᶠ y : Fin (n * 4) → ℝ in 𝓝[forwardTubeConeFlat n] 0,
      (if hy : y ∈ forwardTubeConeFlat n then
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
          (M_f (cone_psi_schwartz n hn
            ((spacetimeFlatCLE_C n).symm (fun p => (y p : ℂ) * Complex.I))
            (symm_mem_forward_tube_of_mem_tubeDomain n (by simpa [TubeDomain] using hy))) -
            cone_limit_schwartz n f)
      else 0) < ε / C_T := by
    intro km _
    exact (cone_psi_mul_fourier_seminorm_tendsto hn f km).eventually
      (Iio_mem_nhds (div_pos hε hCT_pos))
  filter_upwards [self_mem_nhdsWithin, (Filter.eventually_all_finset s).mpr h_each] with y hy h_km
  rw [dif_pos hy, dist_eq_norm, ← map_sub]
  let diff_s := M_f (cone_psi_schwartz n hn
    ((spacetimeFlatCLE_C n).symm (fun p => (y p : ℂ) * Complex.I))
    (symm_mem_forward_tube_of_mem_tubeDomain n (by simpa [TubeDomain] using hy))) -
    cone_limit_schwartz n f
  have h_sup_lt : (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)) diff_s < ε / C_T := by
    have h_sub : ∀ u : Finset (ℕ × ℕ), u ⊆ s →
        (u.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)) diff_s < ε / C_T := by
      intro u
      induction u using Finset.induction_on with
      | empty =>
        intro _
        rw [Finset.sup_empty, Seminorm.bot_eq_zero, _root_.zero_apply]
        exact div_pos hε hCT_pos
      | @insert a u _ha ih =>
        intro hu
        rw [Finset.sup_insert, Seminorm.sup_apply]
        have ha_lt := h_km a (hu (Finset.mem_insert_self a u))
        rw [dif_pos hy] at ha_lt
        exact max_lt ha_lt (ih fun km hkm => hu (Finset.mem_insert_of_mem hkm))
    exact h_sub s subset_rfl
  calc ‖T₀ diff_s‖
      ≤ C_T * (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)) diff_s := hT_bound _
    _ < C_T * (ε / C_T) := mul_lt_mul_of_pos_left h_sup_lt hCT_pos
    _ = ε := mul_div_cancel₀ ε hCT_pos.ne'

lemma measurePreserving_revFlatCLE (n : ℕ) :
    MeasureTheory.MeasurePreserving (revFlatCLE n)
      MeasureTheory.volume MeasureTheory.volume := by
  have h_comp : (revFlatCLE n).toLinearMap.comp (revFlatCLE n).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact revFlatCLE_involutive n
  have h_det := congr_arg LinearMap.det h_comp
  rw [LinearMap.det_comp, LinearMap.det_id] at h_det
  have h_abs : |LinearMap.det (revFlatCLE n).toLinearMap| = 1 := by
    rcases mul_self_eq_one_iff.mp h_det with h | h
    · rw [h, abs_one]
    · rw [h, abs_neg, abs_one]
  have h_det_ne : LinearMap.det (revFlatCLE n).toLinearMap ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at h_abs
    exact zero_ne_one h_abs
  have h_map := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    MeasureTheory.volume h_det_ne
  rw [abs_inv, h_abs, inv_one, ENNReal.ofReal_one, one_smul] at h_map
  exact ⟨(revFlatCLE n).continuous.measurable, h_map⟩

lemma integral_comp_revFlatCLE (n : ℕ) (g : (Fin (n * 4) → ℝ) → ℂ) :
    (∫ u : Fin (n * 4) → ℝ, g (revFlatCLE n u)) = ∫ u, g u :=
  (measurePreserving_revFlatCLE n).integral_comp
    (revFlatCLE n).toHomeomorph.isClosedEmbedding.measurableEmbedding g

theorem coneVladimirov_hasBoundaryValue_backward
    (η : ℂ) (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    {n : ℕ} (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (Ω : TopologicalSpace.Opens (Fin (n * 4) → ℝ)) :
    Distribution.HasBoundaryValue Ω
      (tubeBackwardRevFlat η (coneVladimirovTubeExtension R W hspec hP) n α)
      ((fun y => -y) '' forwardTubeConeFlat n)
      (Distribution.temperedToDistribution Ω (wightmanRevFlatTD η W n α)) := by
  let E := coneVladimirovTubeExtension R W hspec hP
  intro φ
  let topO : TopologicalSpace.Opens (Fin (n * 4) → ℝ) := ⊤
  let φ_rev : 𝓓(topO, ℝ) :=
    { toFun := fun u => φ (revFlatCLE n u)
      contDiff' := φ.contDiff'.comp (revFlatCLE n).contDiff
      hasCompactSupport' := φ.hasCompactSupport'.comp_homeomorph (revFlatCLE n).toHomeomorph
      tsupport_subset' := fun _ _ => trivial }
  have h_fwd := coneVladimirov_hasBoundaryValue_forward R W hspec hP hn (α ∘ Fin.rev) topO φ_rev
  have h_tend_rev : Tendsto (revFlatCLE n)
      (𝓝[(fun y => -y) '' forwardTubeConeFlat n] 0)
      (𝓝[forwardTubeConeFlat n] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : revFlatCLE n 0 = 0 := map_zero _
      exact h0 ▸ ((revFlatCLE n).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact revFlatCLE_mem_forwardTubeConeFlat_of_mem_neg n hy
  have h_comp := (h_fwd.comp h_tend_rev).const_mul (η ^ (n * (n - 1) / 2))
  have h_target : η ^ (n * (n - 1) / 2) *
      Distribution.temperedToDistribution topO (wightmanFlatTD W n (α ∘ Fin.rev)) φ_rev =
      Distribution.temperedToDistribution Ω (wightmanRevFlatTD η W n α) φ := by
    change η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev)
        (schwartzFlatCLM n (Distribution.testFunctionToSchwartzCLM topO φ_rev)) =
      η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev)
        (schwartzRevCLM n (schwartzFlatCLM n (Distribution.testFunctionToSchwartzCLM Ω φ)))
    congr 2
    ext x
    change (φ (revFlatCLE n (spacetimeFlatCLE n x)) : ℂ) =
      (φ (spacetimeFlatCLE n (x ∘ Fin.rev)) : ℂ)
    dsimp [revFlatCLE]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [h_target] at h_comp
  refine h_comp.congr fun y => ?_
  dsimp only [Function.comp_def, Distribution.boundaryIntegral]
  rw [← MeasureTheory.integral_const_mul, ← integral_comp_revFlatCLE n]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h_inv := revFlatCLE_involutive n u
  have h_val : tubeBackwardRevFlat η E n α (fun p => (u p : ℂ) + (y p : ℂ) * Complex.I) =
      η ^ (n * (n - 1) / 2) * tubeForwardFlat E n (α ∘ Fin.rev)
        (fun p => (revFlatCLE n u p : ℂ) + (revFlatCLE n y p : ℂ) * Complex.I) := by
    dsimp [tubeBackwardRevFlat, tubeForwardFlat]
    congr 2
    ext i μ
    dsimp [revFlatCLE, revCLE, revLinearEquiv]
    simp
  change η ^ (n * (n - 1) / 2) * (tubeForwardFlat E n (α ∘ Fin.rev)
      (fun p => (revFlatCLE n u p : ℂ) + (revFlatCLE n y p : ℂ) * Complex.I) *
      (φ (revFlatCLE n (revFlatCLE n u)) : ℂ)) =
    tubeBackwardRevFlat η E n α (fun p => (u p : ℂ) + (y p : ℂ) * Complex.I) * (φ u : ℂ)
  rw [h_inv, h_val, mul_assoc]

noncomputable def jostFlatOpens (n : ℕ) : TopologicalSpace.Opens (Fin (n * 4) → ℝ) :=
  ⟨(spacetimeFlatCLE n).symm ⁻¹' jost_points_n n,
    (isOpen_jost_points_n n).preimage (spacetimeFlatCLE n).symm.continuous⟩

omit [Fintype ι] [DecidableEq ι] in
theorem weakLocality_equalOn_jostFlat {η : ℂ} {W : WightmanFamily ι}
    (hloc : WeakLocality η W) (n : ℕ) (α : Fin n → ι) :
    Distribution.EqualOn (⊤ : TopologicalSpace.Opens (Fin (n * 4) → ℝ))
      (Distribution.temperedToDistribution ⊤ (wightmanFlatTD W n α))
      (Distribution.temperedToDistribution ⊤ (wightmanRevFlatTD η W n α))
      (jostFlatOpens n) (Set.subset_univ _) := by
  refine Distribution.equalOn_temperedToDistribution_of_schwartz_eq
    (Set.subset_univ _) (fun ψ hψ => ?_)
  rw [wightmanFlatTD_apply, wightmanRevFlatTD_apply]
  refine hloc n α (schwartzFlatCLM n ψ) (schwartzRevCLM n (schwartzFlatCLM n ψ)) ?_ ?_
  · intro x hx
    have hu : spacetimeFlatCLE n x ∈ jostFlatOpens n :=
      hψ (mem_tsupport_of_comp_continuous (spacetimeFlatCLE n).continuous hx)
    have h_symm : (spacetimeFlatCLE n).symm (spacetimeFlatCLE n x) ∈ jost_points_n n := hu
    rwa [ContinuousLinearEquiv.symm_apply_apply] at h_symm
  · intro x
    simp only [schwartzRevCLM_apply]
    congr 1
    ext i μ
    simp [Fin.rev_rev]

theorem coneVladimirov_jost_eow_extension
    {η : ℂ} (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) (n : ℕ) (α : Fin n → ι) :
    ∃ (W_jost : TopologicalSpace.Opens (Fin (n * 4) → ℂ))
      (F : (Fin (n * 4) → ℂ) → ℂ),
      (∀ u ∈ jostFlatOpens n, (fun p => (u p : ℂ)) ∈ W_jost) ∧
      DifferentiableOn ℂ F (W_jost : Set (Fin (n * 4) → ℂ)) ∧
      EqOn F (tubeForwardFlat (coneVladimirovTubeExtension R W hspec hP) n α)
        ((W_jost : Set (Fin (n * 4) → ℂ)) ∩ TubeDomain (forwardTubeConeFlat n)) ∧
      EqOn F (tubeBackwardRevFlat η (coneVladimirovTubeExtension R W hspec hP) n α)
        ((W_jost : Set (Fin (n * 4) → ℂ)) ∩
          TubeDomain ((fun y => -y) '' forwardTubeConeFlat n)) := by
  let E := coneVladimirovTubeExtension R W hspec hP
  by_cases hn : n ≤ 1
  · have h_univ_ft : forward_tube_n n = Set.univ := by
      ext z
      simp only [forward_tube_n, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro i hi
      omega
    have h_an_n : ∀ (β : Fin n → ι) (z : Fin n → Fin 4 → ℂ), AnalyticAt ℂ (E.H n β) z := by
      intro β z
      have h_on : AnalyticOn ℂ (E.H n β) Set.univ := h_univ_ft ▸ E.analytic n β
      exact h_on.analyticAt (isOpen_univ.mem_nhds (Set.mem_univ z))
    let revCLM : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun w => w ∘ Fin.rev
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
    let gCLM : (Fin (n * 4) → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
      revCLM.comp (spacetimeFlatCLE_C n).symm.toContinuousLinearMap
    have hf_plus_an : AnalyticOnNhd ℂ (tubeForwardFlat E n α) Set.univ := fun w _ =>
      (h_an_n α ((spacetimeFlatCLE_C n).symm w)).comp
        ((spacetimeFlatCLE_C n).symm.toContinuousLinearMap.analyticAt w)
    have hf_minus_an : AnalyticOnNhd ℂ (tubeBackwardRevFlat η E n α) Set.univ := fun w _ =>
      analyticAt_const.mul ((h_an_n (α ∘ Fin.rev) (gCLM w)).comp (gCLM.analyticAt w))
    have h_W_int : ∀ (β : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
        HasCompactSupport (fun x => f x) →
        W n β f = ∫ x : Fin n → Fin 4 → ℝ, E.H n β (coeReal n x) * f x := by
      intro β f hf_supp
      let v := unit_time_vector
      have hv : v ∈ forward_light_cone := unit_time_vector_mem_forward_light_cone
      let line : ℝ → (Fin n → Fin 4 → ℝ) → (Fin n → Fin 4 → ℂ) :=
        fun t x i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)
      have hH_cont : Continuous (E.H n β) :=
        continuous_iff_continuousAt.mpr (fun z => (h_an_n β z).continuousAt)
      have hline_cont : Continuous (fun p : ℝ × (Fin n → Fin 4 → ℝ) => line p.1 p.2) := by
        refine continuous_pi (fun i => continuous_pi (fun k => ?_))
        exact (Complex.continuous_ofReal.comp ((continuous_apply k).comp
          ((continuous_apply i).comp continuous_snd))).add
          (continuous_const.mul (Complex.continuous_ofReal.comp
            ((continuous_fst.mul continuous_const).mul continuous_const)))
      have h_norm_cont : Continuous
          (fun p : ℝ × (Fin n → Fin 4 → ℝ) => ‖E.H n β (line p.1 p.2)‖) :=
        continuous_norm.comp (hH_cont.comp hline_cont)
      let K : Set (Fin n → Fin 4 → ℝ) := tsupport (fun x => f x)
      rcases (isCompact_Icc.prod hf_supp : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ K)).bddAbove_image
        h_norm_cont.continuousOn with ⟨M₀, hM₀⟩
      let M : ℝ := max M₀ 0
      have h_dom : Tendsto
          (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, E.H n β (line t x) * f x)
          (𝓝[>] 0)
          (𝓝 (∫ x : Fin n → Fin 4 → ℝ, E.H n β (coeReal n x) * f x)) := by
        refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (fun x => M * ‖f x‖) ?_ ?_ (f.integrable.norm.const_mul M) ?_
        · refine Filter.Eventually.of_forall (fun t => ?_)
          have ht_cont : Continuous (fun x => line t x) :=
            hline_cont.comp (continuous_const.prodMk continuous_id)
          exact ((hH_cont.comp ht_cont).mul f.continuous).aestronglyMeasurable
        · filter_upwards [Filter.inter_mem
              (nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one))
              self_mem_nhdsWithin] with t ⟨ht_ball, ht_pos⟩
          have ht_lt : |t| < 1 := by simpa [Real.dist_eq] using ht_ball
          have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht_pos, le_of_lt (abs_lt.mp ht_lt).2⟩
          refine Filter.Eventually.of_forall (fun x => ?_)
          by_cases hx : x ∈ K
          · rw [norm_mul]
            exact mul_le_mul_of_nonneg_right
              ((hM₀ ⟨(t, x), ⟨ht_Icc, hx⟩, rfl⟩).trans (le_max_left M₀ 0)) (norm_nonneg (f x))
          · simp [image_eq_zero_of_notMem_tsupport hx]
        · refine Filter.Eventually.of_forall (fun x => ?_)
          have hx_cont : Continuous (fun t : ℝ => E.H n β (line t x) * f x) :=
            (hH_cont.comp (hline_cont.comp (continuous_id.prodMk continuous_const))).mul
              continuous_const
          have hx0 : E.H n β (line 0 x) * f x = E.H n β (coeReal n x) * f x := by
            congr 2; ext i k; simp [line, coeReal]
          rw [← hx0]
          exact (hx_cont.tendsto 0).mono_left nhdsWithin_le_nhds
      haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
      exact tendsto_nhds_unique (E.boundary n β f v hv) h_dom
    let g₁ : (Fin (n * 4) → ℝ) → ℂ := fun u => tubeForwardFlat E n α (fun p => (u p : ℂ))
    let g₂ : (Fin (n * 4) → ℝ) → ℂ := fun u => tubeBackwardRevFlat η E n α (fun p => (u p : ℂ))
    have h_emb : Continuous (fun u : Fin (n * 4) → ℝ => (fun p => (u p : ℂ))) :=
      continuous_pi fun p => Complex.continuous_ofReal.comp (continuous_apply p)
    have hg₁_cont : Continuous g₁ :=
      (continuous_iff_continuousAt.mpr fun w => (hf_plus_an w (Set.mem_univ w)).continuousAt).comp
        h_emb
    have hg₂_cont : Continuous g₂ :=
      (continuous_iff_continuousAt.mpr fun w => (hf_minus_an w (Set.mem_univ w)).continuousAt).comp
        h_emb
    have hg₁_loc : MeasureTheory.LocallyIntegrableOn g₁ (jostBallFlatOpens n)
        MeasureTheory.volume :=
      hg₁_cont.continuousOn.locallyIntegrableOn (jostBallFlatOpens n).isOpen.measurableSet
    have hg₂_loc : MeasureTheory.LocallyIntegrableOn g₂ (jostBallFlatOpens n)
        MeasureTheory.volume :=
      hg₂_cont.continuousOn.locallyIntegrableOn (jostBallFlatOpens n).isOpen.measurableSet
    have h_eq_dist : Distribution.EqualOn (jostBallFlatOpens n)
        (Distribution.ofLocallyIntegrableOn (jostBallFlatOpens n) g₁)
        (Distribution.ofLocallyIntegrableOn (jostBallFlatOpens n) g₂)
        (jostBallFlatOpens n) subset_rfl := by
      intro φ hφ
      rw [Distribution.ofLocallyIntegrableOn_apply hg₁_loc,
          Distribution.ofLocallyIntegrableOn_apply hg₂_loc]
      let ψ := Distribution.testFunctionToSchwartzCLM (jostBallFlatOpens n) φ
      have hψ_supp : HasCompactSupport (fun u => ψ u) :=
        φ.hasCompactSupport'.comp_left Complex.ofReal_zero
      have h1 : (∫ u, g₁ u * (φ u : ℂ)) =
          Distribution.temperedToDistribution (jostBallFlatOpens n) (wightmanFlatTD W n α) φ := by
        rw [Distribution.temperedToDistribution_apply, wightmanFlatTD_apply,
          h_W_int α (schwartzFlatCLM n ψ) (hasCompactSupport_schwartzFlatCLM n hψ_supp),
          ← integral_comp_spacetimeFlatCLE n]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have h_flat_coe : (fun p => ((spacetimeFlatCLE n x p) : ℂ)) =
            spacetimeFlatCLE_C n (coeReal n x) := by ext p; rfl
        change E.H n α ((spacetimeFlatCLE_C n).symm (fun p => ((spacetimeFlatCLE n x p) : ℂ))) *
            (φ (spacetimeFlatCLE n x) : ℂ) =
          E.H n α (coeReal n x) * (φ (spacetimeFlatCLE n x) : ℂ)
        rw [h_flat_coe, ContinuousLinearEquiv.symm_apply_apply]
      have h2 : (∫ u, g₂ u * (φ u : ℂ)) =
          Distribution.temperedToDistribution (jostBallFlatOpens n)
            (wightmanRevFlatTD η W n α) φ := by
        rw [Distribution.temperedToDistribution_apply, wightmanRevFlatTD_apply,
          h_W_int (α ∘ Fin.rev) (schwartzRevCLM n (schwartzFlatCLM n ψ))
            (hasCompactSupport_schwartzRevCLM n (hasCompactSupport_schwartzFlatCLM n hψ_supp)),
          ← integral_comp_rev n, ← MeasureTheory.integral_const_mul,
          ← integral_comp_spacetimeFlatCLE n]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have h_flat_coe : (fun p => ((spacetimeFlatCLE n x p) : ℂ)) =
            spacetimeFlatCLE_C n (coeReal n x) := by ext p; rfl
        change (η ^ (n * (n - 1) / 2) *
            E.H n (α ∘ Fin.rev)
              (((spacetimeFlatCLE_C n).symm (fun p => ((spacetimeFlatCLE n x p) : ℂ))) ∘
                Fin.rev)) *
            (φ (spacetimeFlatCLE n x) : ℂ) =
          η ^ (n * (n - 1) / 2) *
            (E.H n (α ∘ Fin.rev) (coeReal n (fun i => x (Fin.rev i))) *
              (φ (spacetimeFlatCLE n (fun i => x (Fin.rev (Fin.rev i)))) : ℂ))
        rw [h_flat_coe, ContinuousLinearEquiv.symm_apply_apply]
        have h_inv_x : (fun i : Fin n => x (Fin.rev (Fin.rev i))) = x := by
          ext i μ; simp [Fin.rev_rev]
        rw [h_inv_x, mul_assoc]
        rfl
      rw [h1, h2]
      exact weakLocality_equalOn_jostBallFlat hloc n α φ hφ
    have h_bdy_eq : EqOn g₁ g₂ (jostBallFlatOpens n) :=
      Distribution.eqOn_of_equalOn_continuousOn subset_rfl
        hg₁_loc hg₂_loc hg₁_cont.continuousOn hg₂_cont.continuousOn h_eq_dist
    have h_all : EqOn (tubeForwardFlat E n α) (tubeBackwardRevFlat η E n α) Set.univ :=
      Distribution.analyticOnNhd_eqOn_of_real_open isOpen_univ isPreconnected_univ
        hf_plus_an hf_minus_an (jostBallFlatOpens n).isOpen (jostBallFlatOpens_nonempty n)
        (fun _ _ => Set.mem_univ _) h_bdy_eq
    refine ⟨⊤, tubeForwardFlat E n α, fun _ _ => trivial,
      hf_plus_an.differentiableOn.mono (fun _ _ => Set.mem_univ _),
      fun _ _ => rfl, fun w _ => h_all (Set.mem_univ w)⟩
  · exact Distribution.local_eow_of_tempered_boundary
      (⊤ : TopologicalSpace.Opens (Fin (n * 4) → ℝ))
      (forwardTubeConeFlat n)
      ((fun y => -y) '' forwardTubeConeFlat n)
      (isOpen_forwardTubeConeFlat n)
      ((Homeomorph.neg (Fin (n * 4) → ℝ)).isOpenMap _ (isOpen_forwardTubeConeFlat n))
      rfl
      (convex_forwardTubeConeFlat n)
      ⟨tubeBaseImFlat n, tubeBaseImFlat_mem_forwardTubeConeFlat n⟩
      (zero_notMem_forwardTubeConeFlat hn)
      (fun v hv c hc => smul_mem_forwardTubeConeFlat n hc hv)
      (tubeForwardFlat E n α)
      (tubeBackwardRevFlat η E n α)
      (differentiableOn_tubeForwardFlat E n α)
      (differentiableOn_tubeBackwardRevFlat η E n α)
      (coneVladimirov_hasPolynomialTubeGrowth_forward R W hspec hP hn α)
      (coneVladimirov_hasPolynomialTubeGrowth_backward η R W hspec hP hn α)
      (jostFlatOpens n)
      (Set.subset_univ _)
      (Distribution.temperedToDistribution ⊤ (wightmanFlatTD W n α))
      (coneVladimirov_hasBoundaryValue_forward R W hspec hP hn α ⊤)
      (Distribution.temperedToDistribution ⊤ (wightmanRevFlatTD η W n α))
      (coneVladimirov_hasBoundaryValue_backward η R W hspec hP hn α ⊤)
      (weakLocality_equalOn_jostFlat hloc n α)

end GeneralDimensionJostEOW

end QFT
