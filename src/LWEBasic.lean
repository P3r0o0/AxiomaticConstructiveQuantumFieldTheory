import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace LWE

section Generic

variable (R : Type*) [CommRing R]

abbrev VectorR (len : ℕ) := Fin len → R

abbrev MatrixR (n m : ℕ) := Matrix (Fin m) (Fin n) R

open scoped BigOperators

def evaluate (n m : ℕ) (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m) : VectorR R m :=
  fun i => (∑ j, A i j * s j) + e i

structure Sample (n m : ℕ) where
  A : MatrixR R n m
  b : VectorR R m

def mkSample (n m : ℕ) (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m) : Sample R n m :=
  { A := A, b := evaluate R n m A s e }

def addSamples {n m : ℕ} (c1 c2 : Sample R n m) : Sample R n m :=
  { A := c1.A + c2.A,
    b := c1.b + c2.b }

theorem addSamples_correct {n m : ℕ} (s : VectorR R n) (A1 A2 : MatrixR R n m)
    (e1 e2 : VectorR R m) :
    addSamples R (mkSample R n m A1 s e1) (mkSample R n m A2 s e2) =
    mkSample R n m (A1 + A2) s (e1 + e2) := by
  dsimp [addSamples, mkSample]
  congr 1
  ext i
  simp [evaluate, add_mul, Finset.sum_add_distrib]
  ring

end Generic

section Zq

structure LWEParams where
  n : ℕ
  m : ℕ
  q : ℕ
  [q_pos : Fact (0 < q)]

variable (params : LWEParams)

abbrev Zq := ZMod params.q

def centeredLift (x : Zq params) : ℤ :=
  let val : ℤ := ZMod.val x
  let q_int : ℤ := params.q
  if val ≤ q_int / 2 then
    val
  else
    val - q_int

def norm (x : Zq params) : ℕ :=
  (centeredLift params x).natAbs

def normInf {len : ℕ} (v : VectorR (Zq params) len) : ℕ :=
  Finset.sup Finset.univ (fun i => norm params (v i))

lemma val_lt (x : Zq params) : (ZMod.val x : ℤ) < params.q := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h := ZMod.val_lt x
  exact_mod_cast h

lemma val_nonneg (x : Zq params) : 0 ≤ (ZMod.val x : ℤ) := by
  exact Int.natCast_nonneg (ZMod.val x)

lemma val_add_cases (x y : Zq params) :
    (ZMod.val (x + y) : ℤ) = (ZMod.val x : ℤ) + (ZMod.val y : ℤ) ∨
    (ZMod.val (x + y) : ℤ) = (ZMod.val x : ℤ) + (ZMod.val y : ℤ) - params.q := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h_add := ZMod.val_add x y
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  by_cases h : ZMod.val x + ZMod.val y < params.q
  · left
    rw [h_add, Nat.mod_eq_of_lt h]
    push_cast
    rfl
  · right
    have h_le : params.q ≤ ZMod.val x + ZMod.val y := by omega
    have h_mod := Nat.mod_eq_sub_mod h_le
    rw [h_add, h_mod]
    have h_lt : ZMod.val x + ZMod.val y - params.q < params.q := by omega
    rw [Nat.mod_eq_of_lt h_lt]
    rw [Nat.cast_sub h_le]
    push_cast
    rfl

theorem norm_add_le_elem (params : LWEParams) (x y : Zq params) :
    norm params (x + y) ≤ norm params x + norm params y := by
  have h_cases := val_add_cases params x y
  have hq_pos : 0 < (params.q : ℤ) := by exact_mod_cast params.q_pos.out
  have hx_lt := val_lt params x
  have hy_lt := val_lt params y
  have hxy_lt := val_lt params (x + y)
  have hx_ge := val_nonneg params x
  have hy_ge := val_nonneg params y
  have hxy_ge := val_nonneg params (x + y)
  generalize hcxy : centeredLift params (x + y) = cxy
  generalize hcx : centeredLift params x = cx
  generalize hcy : centeredLift params y = cy
  unfold norm
  rw [hcxy, hcx, hcy]
  unfold centeredLift at hcxy hcx hcy
  dsimp at hcxy hcx hcy
  rcases h_cases with h_add | h_add
  · rw [h_add] at hcxy
    split_ifs at hcxy hcx hcy <;> omega
  · rw [h_add] at hcxy
    split_ifs at hcxy hcx hcy <;> omega

theorem norm_add_le {len : ℕ} (e1 e2 : VectorR (Zq params) len) :
    normInf params (e1 + e2) ≤ normInf params e1 + normInf params e2 := by
  dsimp [normInf]
  apply Finset.sup_le
  intro i _
  have h_elem := norm_add_le_elem params (e1 i) (e2 i)
  have h_sup1 : norm params (e1 i) ≤ Finset.sup Finset.univ (fun j => norm params (e1 j)) :=
    Finset.le_sup (f := fun j => norm params (e1 j)) (Finset.mem_univ i)
  have h_sup2 : norm params (e2 i) ≤ Finset.sup Finset.univ (fun j => norm params (e2 j)) :=
    Finset.le_sup (f := fun j => norm params (e2 j)) (Finset.mem_univ i)
  omega

theorem norm_neg_elem (params : LWEParams) (x : Zq params) :
    norm params (-x) = norm params x := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h_cases := val_add_cases params x (-x)
  rw [add_neg_cancel, ZMod.val_zero, Nat.cast_zero] at h_cases
  have hq_pos : 0 < (params.q : ℤ) := by exact_mod_cast params.q_pos.out
  have hx_lt := val_lt params x
  have hnx_lt := val_lt params (-x)
  have hx_ge := val_nonneg params x
  have hnx_ge := val_nonneg params (-x)
  unfold norm centeredLift
  dsimp
  rcases h_cases with h_sum | h_sum
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem norm_sub_le_elem (params : LWEParams) (x y : Zq params) :
    norm params (x - y) ≤ norm params x + norm params y := by
  rw [sub_eq_add_neg, ← norm_neg_elem params y]
  exact norm_add_le_elem params x (-y)

theorem norm_neg {len : ℕ} (e : VectorR (Zq params) len) :
    normInf params (-e) = normInf params e := by
  dsimp [normInf]
  congr 1
  ext i
  exact norm_neg_elem params (e i)

theorem norm_sub_le {len : ℕ} (e1 e2 : VectorR (Zq params) len) :
    normInf params (e1 - e2) ≤ normInf params e1 + normInf params e2 := by
  rw [sub_eq_add_neg, ← norm_neg params e2]
  exact norm_add_le params e1 (-e2)

theorem norm_zero (params : LWEParams) : norm params 0 = 0 := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  unfold norm centeredLift
  dsimp
  rw [ZMod.val_zero, Nat.cast_zero]
  split_ifs <;> omega

theorem norm_finset_sum_le (params : LWEParams) {ι : Type*} (s : Finset ι) (f : ι → Zq params) :
    norm params (∑ i ∈ s, f i) ≤ ∑ i ∈ s, norm params (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [norm_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_add := norm_add_le_elem params (f a) (∑ i ∈ s, f i)
    omega

def IsTernaryElem {R : Type*} [Ring R] (x : R) : Prop :=
  x = 0 ∨ x = 1 ∨ x = -1

theorem norm_ternary_mul_le (params : LWEParams) (c x : Zq params) (hc : IsTernaryElem c) :
    norm params (c * x) ≤ norm params x := by
  rcases hc with rfl | rfl | rfl
  · rw [zero_mul, norm_zero]
    exact Nat.zero_le _
  · rw [one_mul]
  · rw [neg_one_mul, norm_neg_elem]

instance instNeZeroLWEParams (params : LWEParams) : NeZero params.q :=
  ⟨ne_of_gt params.q_pos.out⟩

lemma norm_le_div_two (params : LWEParams) (x : Zq params) :
    norm params x ≤ params.q / 2 := by
  have h_lt := ZMod.val_lt x
  unfold norm centeredLift
  dsimp only
  split_ifs <;> omega

lemma intCast_centeredLift (params : LWEParams) (x : Zq params) :
    ((centeredLift params x : ℤ) : Zq params) = x := by
  unfold centeredLift
  dsimp only
  split_ifs
  · rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, sub_zero]

lemma centeredLift_intCast_of_mem_Icc (params : LWEParams) {M : ℕ} (hM : 2 * M < params.q)
    {k : ℤ} (hk : k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
    centeredLift params (k : Zq params) = k := by
  rw [Finset.mem_Icc] at hk
  by_cases hk0 : 0 ≤ k
  · have h_eq : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg hk0).symm
    have hk_lt : k.toNat < params.q := by omega
    have hx : (k : Zq params) = ((k.toNat : ℕ) : Zq params) := by
      conv_lhs => rw [h_eq]
      rw [Int.cast_natCast]
    have h_val : ZMod.val (k : Zq params) = k.toNat := by
      rw [hx, ZMod.val_natCast_of_lt hk_lt]
    unfold centeredLift
    dsimp only
    rw [h_val, if_pos (by omega)]
    omega
  · have hneg : 0 ≤ -k := by omega
    set n : ℕ := (-k).toNat
    have hn_eq : (n : ℤ) = -k := Int.toNat_of_nonneg hneg
    have hn_pos : 0 < n := by omega
    have hn_lt : n < params.q := by omega
    have h_sub_lt : params.q - n < params.q := by omega
    have hx : (k : Zq params) = ((params.q - n : ℕ) : Zq params) := by
      have hk_neg : k = -(n : ℤ) := by omega
      rw [hk_neg, Int.cast_neg, Int.cast_natCast, neg_eq_iff_add_eq_zero, ← Nat.cast_add,
        Nat.add_sub_cancel' (le_of_lt hn_lt), ZMod.natCast_self]
    have h_val : ZMod.val (k : Zq params) = params.q - n := by
      rw [hx, ZMod.val_natCast_of_lt h_sub_lt]
    unfold centeredLift
    dsimp only
    rw [h_val, if_neg (by omega)]
    omega

lemma norm_intCast_of_mem_Icc (params : LWEParams) {M : ℕ} (hM : 2 * M < params.q)
    {k : ℤ} (hk : k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)) :
    norm params (k : Zq params) = k.natAbs := by
  unfold norm
  rw [centeredLift_intCast_of_mem_Icc params hM hk]

theorem norm_intCast_le_natAbs (params : LWEParams) (δ : ℤ) :
    norm params (δ : Zq params) ≤ δ.natAbs := by
  by_cases hM : 2 * δ.natAbs < params.q
  · have hk : δ ∈ Finset.Icc (-(δ.natAbs : ℤ)) (δ.natAbs : ℤ) := by
      rw [Finset.mem_Icc]
      omega
    rw [norm_intCast_of_mem_Icc params hM hk]
  · have h_le := norm_le_div_two params (δ : Zq params)
    omega

def boundedBall (params : LWEParams) (M : ℕ) : Finset (Zq params) :=
  Finset.univ.filter (fun x => norm params x ≤ M)

@[simp] lemma mem_boundedBall (params : LWEParams) (M : ℕ) (x : Zq params) :
    x ∈ boundedBall params M ↔ norm params x ≤ M := by
  simp [boundedBall]

theorem card_boundedBall (params : LWEParams) (M : ℕ) (hM : 2 * M < params.q) :
    (boundedBall params M).card = 2 * M + 1 := by
  have h_bij : (boundedBall params M).card = (Finset.Icc (-(M : ℤ)) (M : ℤ)).card := by
    refine Finset.card_bij (fun x _ => centeredLift params x) ?_ ?_ ?_
    · intro x hx
      rw [mem_boundedBall] at hx
      unfold norm at hx
      rw [Finset.mem_Icc]
      omega
    · intro x₁ _ x₂ _ h_eq
      have h_cast := congrArg (fun z : ℤ => (z : Zq params)) h_eq
      simpa [intCast_centeredLift] using h_cast
    · intro k hk
      refine ⟨(k : Zq params), ?_, centeredLift_intCast_of_mem_Icc params hM hk⟩
      rw [mem_boundedBall, norm_intCast_of_mem_Icc params hM hk]
      rw [Finset.mem_Icc] at hk
      omega
  rw [h_bij, Int.card_Icc]
  omega

def divRoundInt (a : ℤ) (q : ℕ) : ℤ :=
  (a + ((q / 2 : ℕ) : ℤ)) / (q : ℤ)

theorem divRoundInt_mul_sub_bounds {q : ℕ} (hq : 0 < q) (a : ℤ) :
    ((q : ℤ) * divRoundInt a q - a).natAbs ≤ q / 2 := by
  dsimp [divRoundInt]
  set z := (a + ((q / 2 : ℕ) : ℤ)) / (q : ℤ)
  set r := (a + ((q / 2 : ℕ) : ℤ)) % (q : ℤ)
  have hq_pos : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr hq
  have h_dm : r + (q : ℤ) * z = a + ((q / 2 : ℕ) : ℤ) := Int.emod_add_mul_ediv _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hq_pos)
  have hrq : r < (q : ℤ) := Int.emod_lt_of_pos _ hq_pos
  change ((q : ℤ) * z - a).natAbs ≤ q / 2
  omega

theorem divRoundInt_neg_of_odd {q : ℕ} (hq_odd : Odd q) (a : ℤ) :
    divRoundInt (-a) q = -divRoundInt a q := by
  have hq_mod : q % 2 = 1 := Nat.odd_iff.mp hq_odd
  have hq_pos : 0 < q := by omega
  have hq_z_pos : (0 : ℤ) < (q : ℤ) := Int.natCast_pos.mpr hq_pos
  dsimp [divRoundInt]
  set z := (a + ((q / 2 : ℕ) : ℤ)) / (q : ℤ)
  set r := (a + ((q / 2 : ℕ) : ℤ)) % (q : ℤ)
  set z' := (-a + ((q / 2 : ℕ) : ℤ)) / (q : ℤ)
  set r' := (-a + ((q / 2 : ℕ) : ℤ)) % (q : ℤ)
  have h_dm : r + (q : ℤ) * z = a + ((q / 2 : ℕ) : ℤ) := Int.emod_add_mul_ediv _ _
  have h_dm' : r' + (q : ℤ) * z' = -a + ((q / 2 : ℕ) : ℤ) := Int.emod_add_mul_ediv _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hq_z_pos)
  have hrq : r < (q : ℤ) := Int.emod_lt_of_pos _ hq_z_pos
  have hr0' : 0 ≤ r' := Int.emod_nonneg _ (ne_of_gt hq_z_pos)
  have hrq' : r' < (q : ℤ) := Int.emod_lt_of_pos _ hq_z_pos
  have h_sum_q : (q : ℤ) * (z + z') = (q : ℤ) - 1 - (r + r') := by
    rw [mul_add]
    omega
  have h_neg1_lt : -(q : ℤ) < (q : ℤ) * (z + z') := by omega
  have h_lt_q : (q : ℤ) * (z + z') < (q : ℤ) := by omega
  have h_not_ge1 : ¬ 1 ≤ z + z' := by
    intro h1
    have h_mul := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hq_z_pos)
    omega
  have h_not_le_neg1 : ¬ z + z' ≤ -1 := by
    intro h1
    have h_mul := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hq_z_pos)
    omega
  change z' = -z
  omega

theorem natAbs_le_div_of_mul_eq {q M : ℕ} (hq : 0 < q) {w r : ℤ}
    (h_eq : (q : ℤ) * w = r) (hr : r.natAbs ≤ M) : w.natAbs ≤ M / q := by
  have h_abs : q * w.natAbs = r.natAbs := by
    calc
      q * w.natAbs = (q : ℤ).natAbs * w.natAbs := by rw [Int.natAbs_natCast]
      _ = ((q : ℤ) * w).natAbs := (Int.natAbs_mul (q : ℤ) w).symm
      _ = r.natAbs := by rw [h_eq]
  have h_le : w.natAbs * q ≤ M := by rw [mul_comm, h_abs]; exact hr
  have h_div := Nat.div_le_div_right (c := q) h_le
  rwa [Nat.mul_div_cancel _ hq] at h_div

theorem ediv_natAbs_le {t B : ℕ} (ht : 0 < t) {x : ℤ}
    (hx : x.natAbs ≤ B) : (x / (t : ℤ)).natAbs ≤ (B + (t - 1)) / t := by
  have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
  have h_dm : x % (t : ℤ) + (t : ℤ) * (x / (t : ℤ)) = x := Int.emod_add_mul_ediv _ _
  have hr0 : 0 ≤ x % (t : ℤ) := Int.emod_nonneg _ (ne_of_gt ht_pos)
  have hrt : x % (t : ℤ) < (t : ℤ) := Int.emod_lt_of_pos _ ht_pos
  have h_eq : (t : ℤ) * (x / (t : ℤ)) = x - x % (t : ℤ) := by omega
  have hr_le : (x - x % (t : ℤ)).natAbs ≤ B + (t - 1) := by omega
  exact natAbs_le_div_of_mul_eq ht h_eq hr_le

end Zq

section RingLWE

variable {R : Type*} [CommRing R]

structure RingSample (R : Type*) [CommRing R] where
  a : R
  b : R

def mkRingSample (a s e : R) : RingSample R :=
  { a := a, b := a * s + e }

structure RingSample2 (R : Type*) [CommRing R] where
  d0 : R
  d1 : R
  d2 : R

def mulRingSamples (c1 c2 : RingSample R) : RingSample2 R :=
  { d0 := c1.b * c2.b,
    d1 := c1.a * c2.b + c2.a * c1.b,
    d2 := c1.a * c2.a }

theorem mulRingSamples_correct (s a1 a2 e1 e2 : R) :
    let c1 := mkRingSample a1 s e1
    let c2 := mkRingSample a2 s e2
    let c_mul := mulRingSamples c1 c2
    c_mul.d0 - c_mul.d1 * s + c_mul.d2 * (s * s) = e1 * e2 := by
  dsimp [mkRingSample, mulRingSamples]
  ring

structure RelinKey (R : Type*) [CommRing R] where
  a_rk : R
  b_rk : R

def mkRelinKey (a_rk s e_rk : R) : RelinKey R :=
  { a_rk := a_rk, b_rk := a_rk * s + e_rk + (s * s) }

def relinearize (c_mul : RingSample2 R) (rk : RelinKey R) : RingSample R :=
  { a := c_mul.d1 + c_mul.d2 * rk.a_rk,
    b := c_mul.d0 + c_mul.d2 * rk.b_rk }

theorem relinearize_correct (s a_rk e_rk d0 d1 d2 : R) :
    let rk := mkRelinKey a_rk s e_rk
    let c_mul : RingSample2 R := { d0 := d0, d1 := d1, d2 := d2 }
    let c_relin := relinearize c_mul rk
    c_relin.b - c_relin.a * s = (d0 - d1 * s + d2 * (s * s)) + d2 * e_rk := by
  dsimp [mkRelinKey, relinearize]
  ring

def IsValidDecomposition {l : ℕ} (G : VectorR R l) (decompose : R → VectorR R l) : Prop :=
  ∀ x : R, (∑ i : Fin l, decompose x i * G i) = x

structure GadgetRelinKey (R : Type*) [CommRing R] (l : ℕ) where
  a_rk : VectorR R l
  b_rk : VectorR R l

def mkGadgetRelinKey {l : ℕ} (a_rk e_rk : VectorR R l) (s : R) (G : VectorR R l) :
    GadgetRelinKey R l :=
  { a_rk := a_rk,
    b_rk := fun i => a_rk i * s + e_rk i + G i * (s * s) }

def gadgetRelinearize {l : ℕ} (c_mul : RingSample2 R) (decomp : R → VectorR R l)
    (rk : GadgetRelinKey R l) : RingSample R :=
  let d2_dec := decomp c_mul.d2
  { a := c_mul.d1 + (∑ i, d2_dec i * rk.a_rk i),
    b := c_mul.d0 + (∑ i, d2_dec i * rk.b_rk i) }

theorem gadgetRelinearize_correct {l : ℕ} (s d0 d1 d2 : R)
    (a_rk e_rk G : VectorR R l) (decomp : R → VectorR R l) (h_dec : IsValidDecomposition G decomp) :
    let rk := mkGadgetRelinKey a_rk e_rk s G
    let c_mul : RingSample2 R := { d0 := d0, d1 := d1, d2 := d2 }
    let c_relin := gadgetRelinearize c_mul decomp rk
    c_relin.b - c_relin.a * s = (d0 - d1 * s + d2 * (s * s)) + (∑ i, decomp d2 i * e_rk i) := by
  dsimp [mkGadgetRelinKey, gadgetRelinearize]
  simp only [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ i : Fin l, decomp d2 i * (a_rk i * s)) =
      (∑ i : Fin l, decomp d2 i * a_rk i) * s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  have h2 : (∑ i : Fin l, decomp d2 i * (G i * (s * s))) =
      (∑ i : Fin l, decomp d2 i * G i) * (s * s) := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  rw [h1, h2, h_dec d2]
  ring

end RingLWE

section ConcreteGadget

open scoped BigOperators

theorem nat_base_decomp_sum (B : ℕ) :
    ∀ (l v : ℕ), v < B ^ l →
      (∑ i : Fin l, ((v / B ^ (i : ℕ)) % B) * B ^ (i : ℕ)) = v
  | 0, v, hv => by
    simp only [pow_zero, Nat.lt_one_iff] at hv
    subst hv
    simp
  | l + 1, v, hv => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one, Fin.val_succ]
    have hB_pos : 0 < B := by
      by_contra h
      have h0 : B = 0 := by omega
      rw [h0, zero_pow (Nat.succ_ne_zero l)] at hv
      omega
    have hv_div : v / B < B ^ l := by
      apply Nat.div_lt_of_lt_mul
      simpa [pow_succ'] using hv
    have h_tail :
        (∑ i : Fin l, ((v / B ^ ((i : ℕ) + 1)) % B) * B ^ ((i : ℕ) + 1)) =
        (∑ i : Fin l, (((v / B) / B ^ (i : ℕ)) % B) * B ^ (i : ℕ)) * B := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ', ← Nat.div_div_eq_div_mul, mul_comm B (B ^ (i : ℕ)), ← mul_assoc]
    rw [h_tail, nat_base_decomp_sum B l (v / B) hv_div]
    have h_div := Nat.mod_add_div v B
    have h_comm : B * (v / B) = v / B * B := Nat.mul_comm B (v / B)
    omega

variable (params : LWEParams)

def baseGadget (B l : ℕ) : VectorR (Zq params) l :=
  fun i => ((B ^ (i : ℕ) : ℕ) : Zq params)

def baseDecomp (B l : ℕ) (x : Zq params) : VectorR (Zq params) l :=
  fun i => ((((ZMod.val x) / B ^ (i : ℕ)) % B : ℕ) : Zq params)

theorem baseDecomp_isValid (B l : ℕ) (hq : params.q ≤ B ^ l) :
    IsValidDecomposition (baseGadget params B l) (baseDecomp params B l) := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  intro x
  dsimp [baseGadget, baseDecomp]
  have h_lt : ZMod.val x < B ^ l := lt_of_lt_of_le (ZMod.val_lt x) hq
  have h_nat := nat_base_decomp_sum B l (ZMod.val x) h_lt
  have h_cast :
      (∑ i : Fin l, ((((ZMod.val x / B ^ (i : ℕ)) % B : ℕ) : Zq params) *
        ((B ^ (i : ℕ) : ℕ) : Zq params))) =
      (((∑ i : Fin l, ((ZMod.val x / B ^ (i : ℕ)) % B) * B ^ (i : ℕ)) : ℕ) : Zq params) := by
    push_cast
    rfl
  rw [h_cast, h_nat, ZMod.natCast_zmod_val]

theorem baseDecomp_norm_lt (B l : ℕ) (hB : 0 < B) (h2B : 2 * B ≤ params.q)
    (x : Zq params) (i : Fin l) :
    norm params (baseDecomp params B l x i) < B := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  dsimp [baseDecomp]
  set d : ℕ := (ZMod.val x / B ^ (i : ℕ)) % B
  have hd_lt_B : d < B := Nat.mod_lt _ hB
  have hd_lt_q : d < params.q := by omega
  have h_val : ZMod.val (d : Zq params) = d := ZMod.val_natCast_of_lt hd_lt_q
  unfold norm centeredLift
  dsimp
  rw [h_val]
  split_ifs <;> omega

def polyBaseGadget (N B l : ℕ) : VectorR (VectorR (Zq params) N) l :=
  fun j _ => baseGadget params B l j

def decomposePoly (N B l : ℕ) (p : VectorR (Zq params) N) : VectorR (VectorR (Zq params) N) l :=
  fun j k => baseDecomp params B l (p k) j

theorem decomposePoly_isValid (N B l : ℕ) (hq : params.q ≤ B ^ l) :
    IsValidDecomposition (polyBaseGadget params N B l) (decomposePoly params N B l) := by
  intro p
  ext k
  simp only [Finset.sum_apply, Pi.mul_apply, polyBaseGadget, decomposePoly]
  exact baseDecomp_isValid params B l hq (p k)

theorem decomposePoly_normInf_le (N B l : ℕ) (hB : 0 < B) (h2B : 2 * B ≤ params.q)
    (p : VectorR (Zq params) N) (j : Fin l) :
    normInf params (decomposePoly params N B l p j) ≤ B - 1 := by
  dsimp [normInf, decomposePoly]
  apply Finset.sup_le
  intro k _
  have h_lt := baseDecomp_norm_lt params B l hB h2B (p k) j
  omega

theorem concrete_gadgetRelinearize_correct (B l : ℕ) (hq : params.q ≤ B ^ l)
    (s d0 d1 d2 : Zq params) (a_rk e_rk : VectorR (Zq params) l) :
    let rk := mkGadgetRelinKey a_rk e_rk s (baseGadget params B l)
    let c_mul : RingSample2 (Zq params) := { d0 := d0, d1 := d1, d2 := d2 }
    let c_relin := gadgetRelinearize c_mul (baseDecomp params B l) rk
    c_relin.b - c_relin.a * s =
      (d0 - d1 * s + d2 * (s * s)) + (∑ i, baseDecomp params B l d2 i * e_rk i) :=
  gadgetRelinearize_correct s d0 d1 d2 a_rk e_rk (baseGadget params B l)
    (baseDecomp params B l) (baseDecomp_isValid params B l hq)

end ConcreteGadget

section NegacyclicPolyRing

open scoped BigOperators

@[ext]
structure NegacyclicPoly (R : Type*) (N : ℕ) where
  coeffs : Fin N → R

namespace NegacyclicPoly

def coeffsEquiv (R : Type*) (N : ℕ) : NegacyclicPoly R N ≃ (Fin N → R) where
  toFun := NegacyclicPoly.coeffs
  invFun := NegacyclicPoly.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (R : Type*) (N : ℕ) [DecidableEq R] : DecidableEq (NegacyclicPoly R N) :=
  fun p q => decidable_of_iff (p.coeffs = q.coeffs) (NegacyclicPoly.ext_iff.symm)

instance (R : Type*) (N : ℕ) [Fintype R] : Fintype (NegacyclicPoly R N) :=
  Fintype.ofEquiv (Fin N → R) (coeffsEquiv R N).symm

variable {R : Type*} [CommRing R] {N : ℕ}

instance : Zero (NegacyclicPoly R N) := ⟨⟨fun _ => 0⟩⟩
instance : Add (NegacyclicPoly R N) := ⟨fun p q => ⟨fun k => p.coeffs k + q.coeffs k⟩⟩
instance : Neg (NegacyclicPoly R N) := ⟨fun p => ⟨fun k => -p.coeffs k⟩⟩
instance : Sub (NegacyclicPoly R N) := ⟨fun p q => ⟨fun k => p.coeffs k - q.coeffs k⟩⟩
instance : SMul ℕ (NegacyclicPoly R N) := ⟨fun n p => ⟨fun k => n • p.coeffs k⟩⟩
instance : SMul ℤ (NegacyclicPoly R N) := ⟨fun z p => ⟨fun k => z • p.coeffs k⟩⟩

@[simp] lemma zero_coeffs (k : Fin N) : (0 : NegacyclicPoly R N).coeffs k = 0 := rfl
@[simp] lemma add_coeffs (p q : NegacyclicPoly R N) (k : Fin N) :
    (p + q).coeffs k = p.coeffs k + q.coeffs k := rfl
@[simp] lemma neg_coeffs (p : NegacyclicPoly R N) (k : Fin N) :
    (-p).coeffs k = -p.coeffs k := rfl
@[simp] lemma sub_coeffs (p q : NegacyclicPoly R N) (k : Fin N) :
    (p - q).coeffs k = p.coeffs k - q.coeffs k := rfl

instance : AddCommGroup (NegacyclicPoly R N) where
  add_assoc a b c := by ext k; exact add_assoc _ _ _
  zero_add a := by ext k; exact zero_add _
  add_zero a := by ext k; exact add_zero _
  nsmul n a := n • a
  nsmul_zero a := by ext k; exact zero_nsmul _
  nsmul_succ n a := by ext k; exact succ_nsmul _ _
  zsmul z a := z • a
  zsmul_zero' a := by ext k; exact zero_zsmul _
  zsmul_succ' n a := by ext k; exact SubNegMonoid.zsmul_succ' n (a.coeffs k)
  zsmul_neg' n a := by ext k; exact SubNegMonoid.zsmul_neg' n (a.coeffs k)
  neg_add_cancel a := by ext k; exact neg_add_cancel _
  add_comm a b := by ext k; exact add_comm _ _
  sub_eq_add_neg a b := by ext k; exact sub_eq_add_neg _ _

@[simp] lemma sum_coeffs {ι : Type*} (s : Finset ι) (f : ι → NegacyclicPoly R N) (k : Fin N) :
    (∑ x ∈ s, f x).coeffs k = ∑ x ∈ s, (f x).coeffs k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, add_coeffs, ih, Finset.sum_insert ha]

def negacyclicSign (N m : ℕ) : R :=
  (-1 : R) ^ (m / N)

def mulSchoolbook (p q : NegacyclicPoly R N) : NegacyclicPoly R N :=
  ⟨fun k =>
    ∑ i : Fin N, ∑ j : Fin N,
      if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
      else 0⟩

instance : Mul (NegacyclicPoly R N) := ⟨mulSchoolbook⟩
instance : One (NegacyclicPoly R N) := ⟨⟨fun k => if (k : ℕ) = 0 then 1 else 0⟩⟩
instance : NatCast (NegacyclicPoly R N) := ⟨fun n => ⟨fun k => if (k : ℕ) = 0 then (n : R) else 0⟩⟩
instance : IntCast (NegacyclicPoly R N) := ⟨fun z => ⟨fun k => if (k : ℕ) = 0 then (z : R) else 0⟩⟩

@[simp] lemma one_coeffs (k : Fin N) :
    (1 : NegacyclicPoly R N).coeffs k = if (k : ℕ) = 0 then 1 else 0 := rfl

@[simp] lemma mul_coeffs (p q : NegacyclicPoly R N) (k : Fin N) :
    (p * q).coeffs k =
      ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
        else 0 := rfl

theorem mul_coeffs_eq_schoolbook_branches (p q : NegacyclicPoly R N) (k : Fin N) :
    (p * q).coeffs k =
      ∑ i : Fin N, ∑ j : Fin N,
        if (i : ℕ) + (j : ℕ) < N then
          if (i : ℕ) + (j : ℕ) = (k : ℕ) then p.coeffs i * q.coeffs j else 0
        else
          if (i : ℕ) + (j : ℕ) - N = (k : ℕ) then -(p.coeffs i * q.coeffs j) else 0 := by
  rw [mul_coeffs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi := i.isLt
  have hj := j.isLt
  by_cases hlt : (i : ℕ) + (j : ℕ) < N
  · rw [if_pos hlt]
    have hmod : ((i : ℕ) + (j : ℕ)) % N = (i : ℕ) + (j : ℕ) := Nat.mod_eq_of_lt hlt
    have hdiv : ((i : ℕ) + (j : ℕ)) / N = 0 := Nat.div_eq_of_lt hlt
    simp [negacyclicSign, hmod, hdiv]
  · rw [if_neg hlt]
    have hge : N ≤ (i : ℕ) + (j : ℕ) := by omega
    have hsub_lt : (i : ℕ) + (j : ℕ) - N < N := by omega
    have hmod : ((i : ℕ) + (j : ℕ)) % N = (i : ℕ) + (j : ℕ) - N := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub_lt]
    have hdiv : ((i : ℕ) + (j : ℕ)) / N = 1 := by
      have h_eq : (i : ℕ) + (j : ℕ) = ((i : ℕ) + (j : ℕ) - N) + N * 1 := by omega
      have hN_pos : 0 < N := by omega
      rw [h_eq, Nat.add_mul_div_left _ _ hN_pos, Nat.div_eq_of_lt hsub_lt]
    simp [negacyclicSign, hmod, hdiv]

lemma div_add_mod_div (a b N : ℕ) (hN : 0 < N) :
    a / N + (a % N + b) / N = (a + b) / N := by
  have h1 : a + b = (a % N + b) + N * (a / N) := by
    have h_div := Nat.div_add_mod a N
    omega
  rw [h1, Nat.add_mul_div_left (a % N + b) (a / N) hN]
  omega

lemma negacyclicSign_mul_mod_left (a b N : ℕ) (hN : 0 < N) :
    (negacyclicSign N (a % N + b) : R) * negacyclicSign N a = negacyclicSign N (a + b) := by
  unfold negacyclicSign
  rw [← pow_add, add_comm ((a % N + b) / N) (a / N), div_add_mod_div a b N hN]

lemma negacyclicSign_mul_mod_right (a b N : ℕ) (hN : 0 < N) :
    (negacyclicSign N (a + b % N) : R) * negacyclicSign N b = negacyclicSign N (a + b) := by
  have h_comm1 : a + b % N = b % N + a := Nat.add_comm a (b % N)
  have h_comm2 : a + b = b + a := Nat.add_comm a b
  rw [h_comm1, h_comm2]
  exact negacyclicSign_mul_mod_left b a N hN

lemma mul_assoc_eq_triple_sum [hN : Fact (0 < N)]
    (p q r : NegacyclicPoly R N) (k : Fin N) :
    ((p * q) * r).coeffs k =
      ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin N,
        if ((i : ℕ) + (j : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ) + (l : ℕ)) * p.coeffs i * q.coeffs j * r.coeffs l
        else 0 := by
  simp only [mul_coeffs]
  have h_step1 :
      (∑ u : Fin N, ∑ l : Fin N,
        if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((u : ℕ) + (l : ℕ)) *
            (∑ i : Fin N, ∑ j : Fin N,
              if ((i : ℕ) + (j : ℕ)) % N = (u : ℕ) then
                negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
              else 0) * r.coeffs l
        else 0) =
      ∑ u : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N,
        if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          if ((i : ℕ) + (j : ℕ)) % N = (u : ℕ) then
            negacyclicSign N ((u : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hul : ((u : ℕ) + (l : ℕ)) % N = (k : ℕ)
    · simp only [if_pos hul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    · simp [if_neg hul]
  rw [h_step1]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_lhs =>
    arg 2; ext l
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    arg 2; ext i
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  let u0 : Fin N := ⟨((i : ℕ) + (j : ℕ)) % N, Nat.mod_lt _ hN.out⟩
  have h_inner :
      (∑ u : Fin N,
        if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          if ((i : ℕ) + (j : ℕ)) % N = (u : ℕ) then
            negacyclicSign N ((u : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0) =
      if ((u0 : ℕ) + (l : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((u0 : ℕ) + (l : ℕ)) *
          (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
      else 0 := by
    have h_eq : ∀ u : Fin N, (((i : ℕ) + (j : ℕ)) % N = (u : ℕ)) ↔ u = u0 := by
      intro u
      rw [Fin.ext_iff, eq_comm]
    simp_rw [h_eq]
    have h_ite : ∀ u : Fin N,
        (if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          if u = u0 then
            negacyclicSign N ((u : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0) =
        if u = u0 then
          if ((u0 : ℕ) + (l : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((u0 : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0 := by
      intro u
      by_cases hu : u = u0
      · subst hu; simp
      · simp [hu]
    simp_rw [h_ite]
    simp
  rw [h_inner]
  have hu0_mod : ((u0 : ℕ) + (l : ℕ)) % N = ((i : ℕ) + (j : ℕ) + (l : ℕ)) % N := by
    change (((i : ℕ) + (j : ℕ)) % N + (l : ℕ)) % N = ((i : ℕ) + (j : ℕ) + (l : ℕ)) % N
    exact Nat.mod_add_mod ((i : ℕ) + (j : ℕ)) N (l : ℕ)
  have hu0_sign :
      (negacyclicSign N ((u0 : ℕ) + (l : ℕ)) : R) * negacyclicSign N ((i : ℕ) + (j : ℕ)) =
      negacyclicSign N ((i : ℕ) + (j : ℕ) + (l : ℕ)) := by
    change (negacyclicSign N (((i : ℕ) + (j : ℕ)) % N + (l : ℕ)) : R) *
      negacyclicSign N ((i : ℕ) + (j : ℕ)) = _
    exact negacyclicSign_mul_mod_left ((i : ℕ) + (j : ℕ)) (l : ℕ) N hN.out
  rw [hu0_mod]
  split_ifs with hmod
  · calc
      negacyclicSign N ((u0 : ℕ) + (l : ℕ)) *
          (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
        = (negacyclicSign N ((u0 : ℕ) + (l : ℕ)) * negacyclicSign N ((i : ℕ) + (j : ℕ))) *
            p.coeffs i * q.coeffs j * r.coeffs l := by ring
      _ = negacyclicSign N ((i : ℕ) + (j : ℕ) + (l : ℕ)) *
            p.coeffs i * q.coeffs j * r.coeffs l := by
        rw [hu0_sign]
  · rfl

lemma mul_comm_poly (p q : NegacyclicPoly R N) : p * q = q * p := by
  ext k
  simp only [mul_coeffs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h_add : (i : ℕ) + (j : ℕ) = (j : ℕ) + (i : ℕ) := Nat.add_comm _ _
  rw [h_add]
  split_ifs <;> ring

lemma left_distrib_poly (p q r : NegacyclicPoly R N) : p * (q + r) = p * q + p * r := by
  ext k
  simp only [mul_coeffs, add_coeffs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma right_distrib_poly (p q r : NegacyclicPoly R N) : (p + q) * r = p * r + q * r := by
  rw [mul_comm_poly (p + q) r, left_distrib_poly, mul_comm_poly p r, mul_comm_poly q r]

lemma zero_mul_poly (p : NegacyclicPoly R N) : 0 * p = 0 := by
  ext k
  simp [mul_coeffs]

lemma mul_zero_poly (p : NegacyclicPoly R N) : p * 0 = 0 := by
  ext k
  simp [mul_coeffs]

lemma one_mul_poly [hN : Fact (0 < N)] (p : NegacyclicPoly R N) : 1 * p = p := by
  ext k
  simp only [mul_coeffs, one_coeffs]
  let z0 : Fin N := ⟨0, hN.out⟩
  have hz0 : ∀ i : Fin N, ((i : ℕ) = 0) ↔ i = z0 := by
    intro i
    rw [Fin.ext_iff]
  simp_rw [hz0]
  have h_outer :
      (∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then (1 : R) else 0) * p.coeffs j
        else 0) =
      ∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * 1 * p.coeffs j
        else 0 := by
    have h_ite : ∀ i : Fin N,
        (∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then (1 : R) else 0) * p.coeffs j
          else 0) =
        if i = z0 then
          ∑ j : Fin N,
            if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
              negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * 1 * p.coeffs j
            else 0
        else 0 := by
      intro i
      by_cases hi : i = z0
      · subst hi; simp
      · simp [hi]
    simp_rw [h_ite]
    simp
  rw [h_outer]
  have h_inner :
      (∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * 1 * p.coeffs j
        else 0) =
      ∑ j : Fin N, if j = k then p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj_mod : ((z0 : ℕ) + (j : ℕ)) % N = (j : ℕ) := by
      change (0 + (j : ℕ)) % N = (j : ℕ)
      rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt]
    have hj_sign : (negacyclicSign N ((z0 : ℕ) + (j : ℕ)) : R) = 1 := by
      unfold negacyclicSign
      change (-1 : R) ^ ((0 + (j : ℕ)) / N) = 1
      rw [Nat.zero_add, Nat.div_eq_of_lt j.isLt, pow_zero]
    rw [hj_mod, hj_sign]
    simp [Fin.ext_iff]
  rw [h_inner]
  simp

lemma mul_one_poly [Fact (0 < N)] (p : NegacyclicPoly R N) : p * 1 = p := by
  rw [mul_comm_poly, one_mul_poly]

lemma mul_assoc_poly [Fact (0 < N)] (p q r : NegacyclicPoly R N) :
    (p * q) * r = p * (q * r) := by
  ext k
  have h_lhs := mul_assoc_eq_triple_sum p q r k
  have h_rhs : (p * (q * r)).coeffs k = ((q * r) * p).coeffs k := by
    rw [mul_comm_poly p (q * r)]
  rw [h_lhs, h_rhs, mul_assoc_eq_triple_sum q r p k]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_rhs =>
    arg 2; ext l
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have h_add : (j : ℕ) + (i : ℕ) + (l : ℕ) = (i : ℕ) + (l : ℕ) + (j : ℕ) := by omega
  rw [h_add]
  split_ifs <;> ring

instance [Fact (0 < N)] : CommRing (NegacyclicPoly R N) where
  mul := (· * ·)
  mul_assoc := mul_assoc_poly
  one := 1
  one_mul := one_mul_poly
  mul_one := mul_one_poly
  zero_mul := zero_mul_poly
  mul_zero := mul_zero_poly
  left_distrib := left_distrib_poly
  right_distrib := right_distrib_poly
  mul_comm := mul_comm_poly
  natCast n := (n : NegacyclicPoly R N)
  natCast_zero := by
    ext k
    change (if (k : ℕ) = 0 then ((0 : ℕ) : R) else 0) = 0
    simp
  natCast_succ n := by
    ext k
    change (if (k : ℕ) = 0 then ((n + 1 : ℕ) : R) else 0) =
      (if (k : ℕ) = 0 then (n : R) else 0) + (if (k : ℕ) = 0 then 1 else 0)
    split_ifs <;> simp
  intCast z := (z : NegacyclicPoly R N)
  intCast_ofNat n := by
    ext k
    change (if (k : ℕ) = 0 then ((n : ℤ) : R) else 0) = if (k : ℕ) = 0 then (n : R) else 0
    split_ifs <;> simp
  intCast_negSucc n := by
    ext k
    change (if (k : ℕ) = 0 then (Int.negSucc n : R) else 0) =
      -(if (k : ℕ) = 0 then ((n + 1 : ℕ) : R) else 0)
    split_ifs <;> simp [Int.negSucc_eq]

def constPoly (c : R) : NegacyclicPoly R N :=
  ⟨fun k => if (k : ℕ) = 0 then c else 0⟩

theorem constPoly_mul_coeffs [hN : Fact (0 < N)] (c : R) (p : NegacyclicPoly R N) (k : Fin N) :
    (constPoly c * p).coeffs k = c * p.coeffs k := by
  simp only [mul_coeffs, constPoly]
  let z0 : Fin N := ⟨0, hN.out⟩
  have hz0 : ∀ i : Fin N, ((i : ℕ) = 0) ↔ i = z0 := by
    intro i; rw [Fin.ext_iff]
  simp_rw [hz0]
  have h_outer :
      (∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then c else 0) * p.coeffs j
        else 0) =
      ∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * c * p.coeffs j
        else 0 := by
    have h_ite : ∀ i : Fin N,
        (∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then c else 0) * p.coeffs j
          else 0) =
        if i = z0 then
          ∑ j : Fin N,
            if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
              negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * c * p.coeffs j
            else 0
        else 0 := by
      intro i
      by_cases hi : i = z0
      · subst hi; simp
      · simp [hi]
    simp_rw [h_ite]
    simp
  rw [h_outer]
  have h_inner :
      (∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * c * p.coeffs j
        else 0) =
      ∑ j : Fin N, if j = k then c * p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj_mod : ((z0 : ℕ) + (j : ℕ)) % N = (j : ℕ) := by
      change (0 + (j : ℕ)) % N = (j : ℕ)
      rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt]
    have hj_sign : (negacyclicSign N ((z0 : ℕ) + (j : ℕ)) : R) = 1 := by
      unfold negacyclicSign
      change (-1 : R) ^ ((0 + (j : ℕ)) / N) = 1
      rw [Nat.zero_add, Nat.div_eq_of_lt j.isLt, pow_zero]
    rw [hj_mod, hj_sign]
    simp [Fin.ext_iff]
  rw [h_inner]
  simp

def negacyclicGadget (params : LWEParams) (N B l : ℕ) :
    VectorR (NegacyclicPoly (Zq params) N) l :=
  fun i => constPoly (baseGadget params B l i)

def negacyclicDecomp (params : LWEParams) (N B l : ℕ)
    (p : NegacyclicPoly (Zq params) N) : VectorR (NegacyclicPoly (Zq params) N) l :=
  fun i => ⟨fun k => baseDecomp params B l (p.coeffs k) i⟩

theorem negacyclicDecomp_isValid (params : LWEParams) (N B l : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l) :
    IsValidDecomposition (negacyclicGadget params N B l) (negacyclicDecomp params N B l) := by
  intro p
  ext k
  rw [sum_coeffs]
  have h_comm : ∀ i : Fin l,
      (negacyclicDecomp params N B l p i * negacyclicGadget params N B l i).coeffs k =
      baseDecomp params B l (p.coeffs k) i * baseGadget params B l i := by
    intro i
    rw [mul_comm (negacyclicDecomp params N B l p i) (negacyclicGadget params N B l i)]
    change (constPoly (baseGadget params B l i) * negacyclicDecomp params N B l p i).coeffs k = _
    rw [constPoly_mul_coeffs, mul_comm]
    rfl
  simp_rw [h_comm]
  exact baseDecomp_isValid params B l hq (p.coeffs k)

theorem negacyclic_poly_mul_and_gadgetRelinearize_correct
    (params : LWEParams) (N B l : ℕ) [Fact (0 < N)] (hq : params.q ≤ B ^ l)
    (s a1 a2 e1 e2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l) :
    let c1 := mkRingSample a1 s e1
    let c2 := mkRingSample a2 s e2
    let c_mul := mulRingSamples c1 c2
    let rk := mkGadgetRelinKey a_rk e_rk s (negacyclicGadget params N B l)
    let c_relin := gadgetRelinearize c_mul (negacyclicDecomp params N B l) rk
    c_relin.b - c_relin.a * s =
      e1 * e2 + (∑ i : Fin l, negacyclicDecomp params N B l c_mul.d2 i * e_rk i) := by
  intro c1 c2 c_mul rk c_relin
  have h_relin := gadgetRelinearize_correct s c_mul.d0 c_mul.d1 c_mul.d2 a_rk e_rk
    (negacyclicGadget params N B l) (negacyclicDecomp params N B l)
    (negacyclicDecomp_isValid params N B l hq)
  have h_mul := mulRingSamples_correct s a1 a2 e1 e2
  dsimp at h_relin h_mul
  rw [h_relin, h_mul]

def IsTernaryPoly {R : Type*} [Ring R] {N : ℕ} (c : NegacyclicPoly R N) : Prop :=
  ∀ i : Fin N, IsTernaryElem (c.coeffs i)

lemma norm_neg_one_pow_mul (params : LWEParams) (x : Zq params) :
    ∀ d : ℕ, norm params ((-1 : Zq params) ^ d * x) = norm params x
  | 0 => by simp
  | d + 1 => by
    rw [pow_succ', neg_one_mul, neg_mul, norm_neg_elem, norm_neg_one_pow_mul params x d]

lemma norm_negacyclicSign_mul (params : LWEParams) (N m : ℕ) (x : Zq params) :
    norm params (negacyclicSign N m * x) = norm params x :=
  norm_neg_one_pow_mul params x (m / N)

lemma mod_add_eq_iff_fin [hN : Fact (0 < N)] (i k j : Fin N) :
    (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔
      j = ⟨((k : ℕ) + N - (i : ℕ)) % N, Nat.mod_lt _ hN.out⟩ := by
  have hi := i.isLt
  have hk := k.isLt
  have hj := j.isLt
  rw [Fin.ext_iff]
  dsimp
  by_cases hik : (i : ℕ) ≤ (k : ℕ)
  · have h_rhs : ((k : ℕ) + N - (i : ℕ)) % N = (k : ℕ) - (i : ℕ) := by
      have h_eq : (k : ℕ) + N - (i : ℕ) = ((k : ℕ) - (i : ℕ)) + N * 1 := by omega
      have h_lt : (k : ℕ) - (i : ℕ) < N := by omega
      rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_lt]
    rw [h_rhs]
    by_cases hlt : (i : ℕ) + (j : ℕ) < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hge : N ≤ (i : ℕ) + (j : ℕ) := by omega
      have hsub : (i : ℕ) + (j : ℕ) - N < N := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
      omega
  · have h_rhs : ((k : ℕ) + N - (i : ℕ)) % N = (k : ℕ) + N - (i : ℕ) := by
      have h_lt : (k : ℕ) + N - (i : ℕ) < N := by omega
      exact Nat.mod_eq_of_lt h_lt
    rw [h_rhs]
    by_cases hlt : (i : ℕ) + (j : ℕ) < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hge : N ≤ (i : ℕ) + (j : ℕ) := by omega
      have hsub : (i : ℕ) + (j : ℕ) - N < N := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
      omega

theorem normInf_ternary_mul_le (params : LWEParams) (N : ℕ) [hN : Fact (0 < N)]
    (c s : NegacyclicPoly (Zq params) N) (hc : IsTernaryPoly c) :
    normInf params (c * s).coeffs ≤ N * normInf params s.coeffs := by
  dsimp [normInf]
  apply Finset.sup_le
  intro k _
  have h_sum_le := norm_finset_sum_le params Finset.univ (fun i : Fin N =>
    ∑ j : Fin N,
      if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((i : ℕ) + (j : ℕ)) * c.coeffs i * s.coeffs j
      else 0)
  have h_term_le :
      (∑ i : Fin N, norm params (
        ∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * c.coeffs i * s.coeffs j
          else 0)) ≤
      ∑ _i : Fin N, Finset.univ.sup (fun j => norm params (s.coeffs j)) := by
    apply Finset.sum_le_sum
    intro i _
    let j0 : Fin N := ⟨((k : ℕ) + N - (i : ℕ)) % N, Nat.mod_lt _ hN.out⟩
    have hj0 : ∀ j : Fin N, (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔ j = j0 :=
      mod_add_eq_iff_fin i k
    simp_rw [hj0]
    have h_inner :
        (∑ j : Fin N,
          if j = j0 then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * c.coeffs i * s.coeffs j
          else 0) =
        negacyclicSign N ((i : ℕ) + (j0 : ℕ)) * (c.coeffs i * s.coeffs j0) := by
      simp [mul_assoc]
    rw [h_inner, norm_negacyclicSign_mul]
    have h1 := norm_ternary_mul_le params (c.coeffs i) (s.coeffs j0) (hc i)
    have h2 : norm params (s.coeffs j0) ≤ Finset.univ.sup (fun j => norm params (s.coeffs j)) :=
      Finset.le_sup (f := fun j => norm params (s.coeffs j)) (Finset.mem_univ j0)
    omega
  have h_const :
      (∑ _i : Fin N, Finset.univ.sup (fun j => norm params (s.coeffs j))) =
        N * Finset.univ.sup (fun j => norm params (s.coeffs j)) := by
    simp
  omega

def negacyclicEvalPow (g : ℕ) (p : NegacyclicPoly R N) : NegacyclicPoly R N :=
  ⟨fun k =>
    ∑ j : Fin N,
      if ((j : ℕ) * g) % N = (k : ℕ) then
        negacyclicSign N ((j : ℕ) * g) * p.coeffs j
      else 0⟩

lemma negacyclicEvalPow_coeffs (g : ℕ) (p : NegacyclicPoly R N) (k : Fin N) :
    (negacyclicEvalPow g p).coeffs k =
      ∑ j : Fin N,
        if ((j : ℕ) * g) % N = (k : ℕ) then
          negacyclicSign N ((j : ℕ) * g) * p.coeffs j
        else 0 := rfl

lemma negacyclicEvalPow_one (p : NegacyclicPoly R N) :
    negacyclicEvalPow 1 p = p := by
  ext k
  rw [negacyclicEvalPow_coeffs]
  have h_ite :
      (∑ j : Fin N,
        if ((j : ℕ) * 1) % N = (k : ℕ) then
          negacyclicSign N ((j : ℕ) * 1) * p.coeffs j
        else 0) =
      ∑ j : Fin N, if j = k then p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj_mod : ((j : ℕ) * 1) % N = (j : ℕ) := by
      rw [mul_one, Nat.mod_eq_of_lt j.isLt]
    have hj_sign : (negacyclicSign N ((j : ℕ) * 1) : R) = 1 := by
      unfold negacyclicSign
      rw [mul_one, Nat.div_eq_of_lt j.isLt, pow_zero]
    rw [hj_mod, hj_sign, one_mul]
    simp [Fin.ext_iff]
  rw [h_ite]
  simp

lemma negacyclicEvalPow_add_two_mul (g : ℕ) (p : NegacyclicPoly R N) :
    negacyclicEvalPow (g + 2 * N) p = negacyclicEvalPow g p := by
  ext k
  rw [negacyclicEvalPow_coeffs, negacyclicEvalPow_coeffs]
  apply Finset.sum_congr rfl
  intro j _
  have hN_pos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have h_eq : (j : ℕ) * (g + 2 * N) = (j : ℕ) * g + N * (2 * (j : ℕ)) := by ring
  have h_mod : ((j : ℕ) * (g + 2 * N)) % N = ((j : ℕ) * g) % N := by
    rw [h_eq, Nat.add_mul_mod_self_left]
  have h_div : ((j : ℕ) * (g + 2 * N)) / N = ((j : ℕ) * g) / N + 2 * (j : ℕ) := by
    rw [h_eq, Nat.add_mul_div_left _ _ hN_pos]
  have h_sign : (negacyclicSign N ((j : ℕ) * (g + 2 * N)) : R) =
      negacyclicSign N ((j : ℕ) * g) := by
    unfold negacyclicSign
    rw [h_div, pow_add, pow_mul]
    have h2 : (-1 : R) ^ 2 = 1 := by ring
    rw [h2, one_pow, mul_one]
  rw [h_mod, h_sign]

lemma negacyclicEvalPow_add_mul_two_mul (g q : ℕ) (p : NegacyclicPoly R N) :
    negacyclicEvalPow (g + q * (2 * N)) p = negacyclicEvalPow g p := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h_assoc : g + (q + 1) * (2 * N) = (g + q * (2 * N)) + 2 * N := by ring
    rw [h_assoc, negacyclicEvalPow_add_two_mul, ih]

lemma negacyclicEvalPow_mod_two_mul (g : ℕ) (p : NegacyclicPoly R N) :
    negacyclicEvalPow g p = negacyclicEvalPow (g % (2 * N)) p := by
  conv_lhs => rw [← Nat.mod_add_div g (2 * N), Nat.mul_comm (2 * N) (g / (2 * N))]
  exact negacyclicEvalPow_add_mul_two_mul (g % (2 * N)) (g / (2 * N)) p

lemma negacyclicSign_mul_odd (a g M : ℕ) (hM : 0 < M) (hg : Odd g) :
    (negacyclicSign M ((a % M) * g) : R) * negacyclicSign M a = negacyclicSign M (a * g) := by
  rcases hg with ⟨m, rfl⟩
  have h_a : a = a % M + M * (a / M) := (Nat.mod_add_div a M).symm
  have h_eq : a * (2 * m + 1) = (a % M) * (2 * m + 1) + M * ((a / M) * (2 * m + 1)) := by
    conv_lhs => rw [h_a]
    ring
  have h_div : (a * (2 * m + 1)) / M = ((a % M) * (2 * m + 1)) / M + (a / M) * (2 * m + 1) := by
    rw [h_eq, Nat.add_mul_div_left _ _ hM]
  unfold negacyclicSign
  rw [h_div, pow_add]
  have h_pow : (-1 : R) ^ ((a / M) * (2 * m + 1)) = (-1 : R) ^ (a / M) := by
    have h_split : (a / M) * (2 * m + 1) = 2 * ((a / M) * m) + (a / M) := by ring
    rw [h_split, pow_add, pow_mul]
    have h2 : (-1 : R) ^ 2 = 1 := by ring
    rw [h2, one_pow, one_mul]
  rw [h_pow]

theorem negacyclicEvalPow_comp_odd {g1 : ℕ} (hg1 : Odd g1) (g2 : ℕ)
    (p : NegacyclicPoly R N) :
    negacyclicEvalPow g1 (negacyclicEvalPow g2 p) = negacyclicEvalPow (g2 * g1) p := by
  ext k
  have hN_pos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  rw [negacyclicEvalPow_coeffs, negacyclicEvalPow_coeffs]
  simp_rw [negacyclicEvalPow_coeffs]
  have h_push :
      (∑ i : Fin N,
        if ((i : ℕ) * g1) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) * g1) *
            ∑ j : Fin N,
              if ((j : ℕ) * g2) % N = (i : ℕ) then
                negacyclicSign N ((j : ℕ) * g2) * p.coeffs j
              else 0
        else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) * g1) % N = (k : ℕ) ∧ ((j : ℕ) * g2) % N = (i : ℕ) then
          negacyclicSign N ((i : ℕ) * g1) * negacyclicSign N ((j : ℕ) * g2) * p.coeffs j
        else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ((i : ℕ) * g1) % N = (k : ℕ)
    · rw [if_pos hi, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : ((j : ℕ) * g2) % N = (i : ℕ)
      · rw [if_pos hj, if_pos ⟨hi, hj⟩, mul_assoc]
      · rw [if_neg hj, mul_zero, if_neg (fun h => hj h.2)]
    · rw [if_neg hi]
      symm
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hi h.1)]
  rw [h_push, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let i0 : Fin N := ⟨((j : ℕ) * g2) % N, Nat.mod_lt _ hN_pos⟩
  have h_eq_i0 :
      (∑ i : Fin N,
        if ((i : ℕ) * g1) % N = (k : ℕ) ∧ ((j : ℕ) * g2) % N = (i : ℕ) then
          negacyclicSign N ((i : ℕ) * g1) * negacyclicSign N ((j : ℕ) * g2) * p.coeffs j
        else 0) =
      if ((i0 : ℕ) * g1) % N = (k : ℕ) then
        negacyclicSign N ((i0 : ℕ) * g1) * negacyclicSign N ((j : ℕ) * g2) * p.coeffs j
      else 0 := by
    rw [Finset.sum_eq_single i0]
    · have hi0 : ((j : ℕ) * g2) % N = (i0 : ℕ) := rfl
      simp [hi0]
    · intro i _ hne
      have hneq : ((j : ℕ) * g2) % N ≠ (i : ℕ) := by
        intro h_eq
        apply hne
        exact Fin.ext h_eq.symm
      rw [if_neg (fun h => hneq h.2)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ i0))
  rw [h_eq_i0]
  have h_mod : ((i0 : ℕ) * g1) % N = ((j : ℕ) * (g2 * g1)) % N := by
    change ((((j : ℕ) * g2) % N) * g1) % N = ((j : ℕ) * (g2 * g1)) % N
    rw [Nat.mod_mul_mod, mul_assoc]
  have h_sign :
      (negacyclicSign N ((i0 : ℕ) * g1) : R) * negacyclicSign N ((j : ℕ) * g2) =
        negacyclicSign N ((j : ℕ) * (g2 * g1)) := by
    have h_s := negacyclicSign_mul_odd (R := R) ((j : ℕ) * g2) g1 N hN_pos hg1
    simpa [i0, mul_assoc] using h_s
  rw [h_mod, h_sign]

lemma negacyclicEvalPow_map_add (g : ℕ) (p q : NegacyclicPoly R N) :
    negacyclicEvalPow g (p + q) = negacyclicEvalPow g p + negacyclicEvalPow g q := by
  ext k
  rw [add_coeffs, negacyclicEvalPow_coeffs, negacyclicEvalPow_coeffs, negacyclicEvalPow_coeffs,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [add_coeffs]
  split_ifs <;> ring

lemma negacyclicEvalPow_map_one [hN : Fact (0 < N)] (g : ℕ) :
    negacyclicEvalPow g (1 : NegacyclicPoly R N) = 1 := by
  ext k
  rw [negacyclicEvalPow_coeffs, one_coeffs]
  let z0 : Fin N := ⟨0, hN.out⟩
  rw [Finset.sum_eq_single z0]
  · simp [z0, negacyclicSign]
    by_cases hk : (k : ℕ) = 0
    · simp [hk]
    · simp [hk, Ne.symm hk]
  · intro j _ hne
    have hj0 : (j : ℕ) ≠ 0 := by
      intro h0
      exact hne (Fin.ext h0)
    simp [hj0]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ z0))

theorem negacyclicEvalPow_map_mul [hN : Fact (0 < N)] {g : ℕ} (hg : Odd g)
    (p q : NegacyclicPoly R N) :
    negacyclicEvalPow g (p * q) = negacyclicEvalPow g p * negacyclicEvalPow g q := by
  ext k
  rw [negacyclicEvalPow_coeffs, mul_coeffs]
  have h_lhs :
      (∑ l : Fin N,
        if ((l : ℕ) * g) % N = (k : ℕ) then
          negacyclicSign N ((l : ℕ) * g) * (p * q).coeffs l
        else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) * g + (j : ℕ) * g) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) * g + (j : ℕ) * g) * p.coeffs i * q.coeffs j
        else 0 := by
    have h_push :
        (∑ l : Fin N,
          if ((l : ℕ) * g) % N = (k : ℕ) then
            negacyclicSign N ((l : ℕ) * g) *
              ∑ i : Fin N, ∑ j : Fin N,
                if ((i : ℕ) + (j : ℕ)) % N = (l : ℕ) then
                  negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
                else 0
          else 0) =
        ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N,
          if ((l : ℕ) * g) % N = (k : ℕ) ∧ ((i : ℕ) + (j : ℕ)) % N = (l : ℕ) then
            negacyclicSign N ((l : ℕ) * g) * negacyclicSign N ((i : ℕ) + (j : ℕ)) *
              p.coeffs i * q.coeffs j
          else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : ((l : ℕ) * g) % N = (k : ℕ)
      · rw [if_pos hl, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : ((i : ℕ) + (j : ℕ)) % N = (l : ℕ)
        · rw [if_pos hij, if_pos ⟨hl, hij⟩]
          ring
        · rw [if_neg hij, mul_zero, if_neg (fun h => hij h.2)]
      · rw [if_neg hl]
        symm
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (fun h => hl h.1)]
    have h_swap1 :
        (∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N,
          if ((l : ℕ) * g) % N = (k : ℕ) ∧ ((i : ℕ) + (j : ℕ)) % N = (l : ℕ) then
            negacyclicSign N ((l : ℕ) * g) * negacyclicSign N ((i : ℕ) + (j : ℕ)) *
              p.coeffs i * q.coeffs j
          else 0) =
        ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin N,
          if ((l : ℕ) * g) % N = (k : ℕ) ∧ ((i : ℕ) + (j : ℕ)) % N = (l : ℕ) then
            negacyclicSign N ((l : ℕ) * g) * negacyclicSign N ((i : ℕ) + (j : ℕ)) *
              p.coeffs i * q.coeffs j
          else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    change (∑ l : Fin N,
      if ((l : ℕ) * g) % N = (k : ℕ) then
        negacyclicSign N ((l : ℕ) * g) * (p * q).coeffs l
      else 0) = _
    simp_rw [mul_coeffs]
    rw [h_push, h_swap1]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    let l0 : Fin N := ⟨((i : ℕ) + (j : ℕ)) % N, Nat.mod_lt _ hN.out⟩
    rw [Finset.sum_eq_single l0]
    · have hl0 : ((i : ℕ) + (j : ℕ)) % N = (l0 : ℕ) := rfl
      have h_mod : ((l0 : ℕ) * g) % N = ((i : ℕ) * g + (j : ℕ) * g) % N := by
        change ((((i : ℕ) + (j : ℕ)) % N) * g) % N = ((i : ℕ) * g + (j : ℕ) * g) % N
        rw [Nat.mod_mul_mod, Nat.add_mul]
      have h_sign :
          (negacyclicSign N ((l0 : ℕ) * g) : R) * negacyclicSign N ((i : ℕ) + (j : ℕ)) =
            negacyclicSign N ((i : ℕ) * g + (j : ℕ) * g) := by
        have h_s :
            (negacyclicSign N ((((i : ℕ) + (j : ℕ)) % N) * g) : R) *
                negacyclicSign N ((i : ℕ) + (j : ℕ)) =
              negacyclicSign N (((i : ℕ) + (j : ℕ)) * g) :=
          negacyclicSign_mul_odd ((i : ℕ) + (j : ℕ)) g N hN.out hg
        simpa [l0, Nat.add_mul] using h_s
      simp only [hl0, and_true, h_mod]
      split_ifs <;> simp [h_sign]
    · intro l _ hne
      have hneq : ((i : ℕ) + (j : ℕ)) % N ≠ (l : ℕ) := by
        intro h_eq
        exact hne (Fin.ext h_eq.symm)
      rw [if_neg (fun h => hneq h.2)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ l0))
  have h_rhs :
      (∑ a : Fin N, ∑ b : Fin N,
        if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((a : ℕ) + (b : ℕ)) *
            (negacyclicEvalPow g p).coeffs a * (negacyclicEvalPow g q).coeffs b
        else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) * g + (j : ℕ) * g) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) * g + (j : ℕ) * g) * p.coeffs i * q.coeffs j
        else 0 := by
    simp_rw [negacyclicEvalPow_coeffs]
    have h_push :
        (∑ a : Fin N, ∑ b : Fin N,
          if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((a : ℕ) + (b : ℕ)) *
              (∑ i : Fin N,
                if ((i : ℕ) * g) % N = (a : ℕ) then
                  negacyclicSign N ((i : ℕ) * g) * p.coeffs i
                else 0) *
              (∑ j : Fin N,
                if ((j : ℕ) * g) % N = (b : ℕ) then
                  negacyclicSign N ((j : ℕ) * g) * q.coeffs j
                else 0)
          else 0) =
        ∑ a : Fin N, ∑ b : Fin N, ∑ i : Fin N, ∑ j : Fin N,
          if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) ∧
              ((i : ℕ) * g) % N = (a : ℕ) ∧ ((j : ℕ) * g) % N = (b : ℕ) then
            negacyclicSign N ((a : ℕ) + (b : ℕ)) *
              negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) *
              p.coeffs i * q.coeffs j
          else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hab : ((a : ℕ) + (b : ℕ)) % N = (k : ℕ)
      · rw [if_pos hab]
        conv_lhs =>
          arg 1
          rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hi : ((i : ℕ) * g) % N = (a : ℕ)
        · by_cases hj : ((j : ℕ) * g) % N = (b : ℕ)
          · rw [if_pos hi, if_pos hj, if_pos ⟨hab, hi, hj⟩]
            ring
          · rw [if_pos hi, if_neg hj, mul_zero, if_neg (fun h => hj h.2.2)]
        · rw [if_neg hi, mul_zero, zero_mul, if_neg (fun h => hi h.2.1)]
      · rw [if_neg hab]
        symm
        apply Finset.sum_eq_zero
        intro i _
        apply Finset.sum_eq_zero
        intro j _
        rw [if_neg (fun h => hab h.1)]
    rw [h_push]
    have h_swap_ab :
        (∑ a : Fin N, ∑ b : Fin N, ∑ i : Fin N, ∑ j : Fin N,
          if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) ∧
              ((i : ℕ) * g) % N = (a : ℕ) ∧ ((j : ℕ) * g) % N = (b : ℕ) then
            negacyclicSign N ((a : ℕ) + (b : ℕ)) *
              negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) *
              p.coeffs i * q.coeffs j
          else 0) =
        ∑ i : Fin N, ∑ j : Fin N, ∑ a : Fin N, ∑ b : Fin N,
          if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) ∧
              ((i : ℕ) * g) % N = (a : ℕ) ∧ ((j : ℕ) * g) % N = (b : ℕ) then
            negacyclicSign N ((a : ℕ) + (b : ℕ)) *
              negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) *
              p.coeffs i * q.coeffs j
          else 0 := by
      have h_inner_swap :
          ∀ a : Fin N,
            (∑ b : Fin N, ∑ i : Fin N, ∑ j : Fin N,
              if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) ∧
                  ((i : ℕ) * g) % N = (a : ℕ) ∧ ((j : ℕ) * g) % N = (b : ℕ) then
                negacyclicSign N ((a : ℕ) + (b : ℕ)) *
                  negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) *
                  p.coeffs i * q.coeffs j
              else 0) =
            ∑ i : Fin N, ∑ j : Fin N, ∑ b : Fin N,
              if ((a : ℕ) + (b : ℕ)) % N = (k : ℕ) ∧
                  ((i : ℕ) * g) % N = (a : ℕ) ∧ ((j : ℕ) * g) % N = (b : ℕ) then
                negacyclicSign N ((a : ℕ) + (b : ℕ)) *
                  negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) *
                  p.coeffs i * q.coeffs j
              else 0 := by
        intro a
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      simp_rw [h_inner_swap]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    rw [h_swap_ab]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    let a0 : Fin N := ⟨((i : ℕ) * g) % N, Nat.mod_lt _ hN.out⟩
    let b0 : Fin N := ⟨((j : ℕ) * g) % N, Nat.mod_lt _ hN.out⟩
    rw [Finset.sum_eq_single a0]
    · rw [Finset.sum_eq_single b0]
      · have ha0 : ((i : ℕ) * g) % N = (a0 : ℕ) := rfl
        have hb0 : ((j : ℕ) * g) % N = (b0 : ℕ) := rfl
        have h_mod : ((a0 : ℕ) + (b0 : ℕ)) % N = ((i : ℕ) * g + (j : ℕ) * g) % N := by
          change (((i : ℕ) * g) % N + ((j : ℕ) * g) % N) % N =
            ((i : ℕ) * g + (j : ℕ) * g) % N
          exact (Nat.add_mod _ _ _).symm
        have h_sign :
            (negacyclicSign N ((a0 : ℕ) + (b0 : ℕ)) : R) *
                negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) =
              negacyclicSign N ((i : ℕ) * g + (j : ℕ) * g) := by
          have h1 := negacyclicSign_mul_mod_left (R := R) ((i : ℕ) * g) (((j : ℕ) * g) % N) N
            hN.out
          have h2 := negacyclicSign_mul_mod_right (R := R) ((i : ℕ) * g) ((j : ℕ) * g) N hN.out
          change (negacyclicSign N (((i : ℕ) * g) % N + ((j : ℕ) * g) % N) : R) *
              negacyclicSign N ((i : ℕ) * g) * negacyclicSign N ((j : ℕ) * g) = _
          rw [h1, h2]
        simp only [ha0, hb0, and_self, and_true, h_mod]
        split_ifs <;> simp [h_sign]
      · intro b _ hne
        have hneq : ((j : ℕ) * g) % N ≠ (b : ℕ) := fun h_eq => hne (Fin.ext h_eq.symm)
        rw [if_neg (fun h => hneq h.2.2)]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ b0))
    · intro a _ hne
      apply Finset.sum_eq_zero
      intro b _
      have hneq : ((i : ℕ) * g) % N ≠ (a : ℕ) := fun h_eq => hne (Fin.ext h_eq.symm)
      rw [if_neg (fun h => hneq h.2.1)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ a0))
  exact h_lhs.trans h_rhs.symm

def negacyclicGaloisHom [Fact (0 < N)] (g : ℕ) (hg : Odd g) :
    NegacyclicPoly R N →+* NegacyclicPoly R N where
  toFun := negacyclicEvalPow g
  map_one' := negacyclicEvalPow_map_one g
  map_mul' := negacyclicEvalPow_map_mul hg
  map_zero' := by ext k; simp [negacyclicEvalPow_coeffs]
  map_add' := negacyclicEvalPow_map_add g

theorem negacyclicGaloisHom_comp [Fact (0 < N)] {g1 g2 : ℕ} (hg1 : Odd g1) (hg2 : Odd g2)
    (p : NegacyclicPoly R N) :
    negacyclicGaloisHom g1 hg1 (negacyclicGaloisHom g2 hg2 p) =
      negacyclicGaloisHom (g2 * g1) (hg2.mul hg1) p :=
  negacyclicEvalPow_comp_odd hg1 g2 p

lemma galois_inv_exists [hN : Fact (0 < N)] {g : ℕ} (hg : Odd g) (hcop : Nat.Coprime g N) :
    ∃ g_inv : ℕ, Odd g_inv ∧ Nat.Coprime g_inv N ∧ (g * g_inv) % (2 * N) = 1 := by
  have hN_pos : 0 < N := hN.out
  have hcop2 : Nat.Coprime g (2 * N) := (Nat.coprime_two_right.mpr hg).mul_right hcop
  haveI : NeZero (2 * N) := ⟨by omega⟩
  let u := ZMod.unitOfCoprime g hcop2
  let g_inv := ZMod.val ((u⁻¹ : (ZMod (2 * N))ˣ) : ZMod (2 * N))
  have h_mod : (g * g_inv) % (2 * N) = 1 := by
    have h_zm : ((g * g_inv : ℕ) : ZMod (2 * N)) = ((1 : ℕ) : ZMod (2 * N)) := by
      rw [Nat.cast_mul, ← ZMod.coe_unitOfCoprime g hcop2]
      have h_ui : (g_inv : ZMod (2 * N)) = ((u⁻¹ : (ZMod (2 * N))ˣ) : ZMod (2 * N)) :=
        ZMod.natCast_zmod_val _
      rw [h_ui, ← Units.val_mul, mul_inv_cancel, Units.val_one, Nat.cast_one]
    have h_val := congrArg ZMod.val h_zm
    rw [ZMod.val_natCast, ZMod.val_natCast_of_lt (by omega)] at h_val
    exact h_val
  have h_mul_eq : 1 + 2 * N * ((g * g_inv) / (2 * N)) = g * g_inv := by
    have h_dm := Nat.mod_add_div (g * g_inv) (2 * N)
    omega
  have h_odd : Odd g_inv := by
    rw [Nat.odd_iff]
    by_contra h_ne
    have h_even : g_inv % 2 = 0 := by omega
    have h_mul2 : g_inv = 2 * (g_inv / 2) := by omega
    set x := N * ((g * g_inv) / (2 * N))
    set y := g * (g_inv / 2)
    have hx : g * g_inv = 1 + 2 * x := by
      calc g * g_inv = 1 + 2 * N * ((g * g_inv) / (2 * N)) := h_mul_eq.symm
        _ = 1 + 2 * x := by dsimp [x]; ring
    have hy : g * g_inv = 2 * y := by
      calc g * g_inv = g * (2 * (g_inv / 2)) := by conv_lhs => rw [h_mul2]
        _ = 2 * y := by dsimp [y]; ring
    omega
  have h_cop_inv : Nat.Coprime g_inv N := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have h_d1 : Nat.gcd g_inv N ∣ g * g_inv :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left g_inv N) g
    have h_d2 : Nat.gcd g_inv N ∣ 2 * N * ((g * g_inv) / (2 * N)) :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Nat.gcd_dvd_right g_inv N) 2) _
    have h_d_one : Nat.gcd g_inv N ∣ 1 := (Nat.dvd_add_left h_d2).mp (h_mul_eq.symm ▸ h_d1)
    exact Nat.dvd_one.mp h_d_one
  exact ⟨g_inv, h_odd, h_cop_inv, h_mod⟩

noncomputable def negacyclicGaloisEquiv [hN : Fact (0 < N)] (g : ℕ) (hg : Odd g)
    (hcop : Nat.Coprime g N) :
    NegacyclicPoly R N ≃+* NegacyclicPoly R N := by
  let g_inv := Classical.choose (galois_inv_exists (N := N) hg hcop)
  have h_spec := Classical.choose_spec (galois_inv_exists (N := N) hg hcop)
  have hg_inv : Odd g_inv := h_spec.1
  have h_mod1 : (g * g_inv) % (2 * N) = 1 := h_spec.2.2
  have h_mod2 : (g_inv * g) % (2 * N) = 1 := by rw [mul_comm]; exact h_mod1
  exact
    { toFun := negacyclicGaloisHom g hg
      invFun := negacyclicGaloisHom g_inv hg_inv
      left_inv := fun p => by
        rw [negacyclicGaloisHom_comp]
        change negacyclicEvalPow (g * g_inv) p = p
        rw [negacyclicEvalPow_mod_two_mul, h_mod1, negacyclicEvalPow_one]
      right_inv := fun p => by
        rw [negacyclicGaloisHom_comp]
        change negacyclicEvalPow (g_inv * g) p = p
        rw [negacyclicEvalPow_mod_two_mul, h_mod2, negacyclicEvalPow_one]
      map_mul' := (negacyclicGaloisHom g hg).map_mul
      map_add' := (negacyclicGaloisHom g hg).map_add }

lemma negacyclicGaloisEquiv_spec [hN : Fact (0 < N)] {g : ℕ} (hg : Odd g)
    (hcop : Nat.Coprime g N) (p : NegacyclicPoly R N) :
    negacyclicGaloisEquiv g hg hcop p = negacyclicEvalPow g p := rfl

lemma negacyclicGaloisEquiv_symm_exists [hN : Fact (0 < N)] {g : ℕ} (hg : Odd g)
    (hcop : Nat.Coprime g N) :
    ∃ g_inv : ℕ, Odd g_inv ∧ Nat.Coprime g_inv N ∧
      ∀ p : NegacyclicPoly R N, (negacyclicGaloisEquiv g hg hcop).symm p =
        negacyclicEvalPow g_inv p := by
  let g_inv := Classical.choose (galois_inv_exists (N := N) hg hcop)
  have h_spec := Classical.choose_spec (galois_inv_exists (N := N) hg hcop)
  exact ⟨g_inv, h_spec.1, h_spec.2.1, fun _ => rfl⟩

lemma mul_coprime_inj_fin {g : ℕ} (hcop : Nat.Coprime g N)
    {j1 j2 : Fin N} (h_eq : ((j1 : ℕ) * g) % N = ((j2 : ℕ) * g) % N) : j1 = j2 := by
  haveI : NeZero N := ⟨ne_of_gt (Fin.pos j1)⟩
  let u := ZMod.unitOfCoprime g hcop
  have h_zm : ((j1 : ℕ) : ZMod N) * (g : ZMod N) = ((j2 : ℕ) : ZMod N) * (g : ZMod N) := by
    have h_cast : (((j1 : ℕ) * g : ℕ) : ZMod N) = (((j2 : ℕ) * g : ℕ) : ZMod N) := by
      have h_z1 : (((j1 : ℕ) * g : ℕ) : ZMod N) = ((((j1 : ℕ) * g) % N : ℕ) : ZMod N) := by
        rw [ZMod.natCast_mod]
      have h_z2 : (((j2 : ℕ) * g : ℕ) : ZMod N) = ((((j2 : ℕ) * g) % N : ℕ) : ZMod N) := by
        rw [ZMod.natCast_mod]
      rw [h_z1, h_z2, h_eq]
    simpa [Nat.cast_mul] using h_cast
  have h_unit : ((j1 : ℕ) : ZMod N) = ((j2 : ℕ) : ZMod N) := by
    rw [← ZMod.coe_unitOfCoprime g hcop] at h_zm
    have h_mul := congrArg (fun x : ZMod N => x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N)) h_zm
    change ((j1 : ℕ) : ZMod N) * (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) =
      ((j2 : ℕ) : ZMod N) * (u : ZMod N) * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) at h_mul
    rwa [mul_assoc ((j1 : ℕ) : ZMod N), mul_assoc ((j2 : ℕ) : ZMod N),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one, mul_one] at h_mul
  have h_val := congrArg ZMod.val h_unit
  rw [ZMod.val_natCast_of_lt j1.isLt, ZMod.val_natCast_of_lt j2.isLt] at h_val
  exact Fin.ext h_val

lemma normInf_negacyclicEvalPow_le (params : LWEParams) (N g : ℕ) [Fact (0 < N)]
    (hcop : Nat.Coprime g N) (p : NegacyclicPoly (Zq params) N) :
    normInf params (negacyclicEvalPow g p).coeffs ≤ normInf params p.coeffs := by
  dsimp [normInf]
  apply Finset.sup_le
  intro k _
  rw [negacyclicEvalPow_coeffs]
  by_cases hex : ∃ j0 : Fin N, ((j0 : ℕ) * g) % N = (k : ℕ)
  · rcases hex with ⟨j0, hj0⟩
    have h_single :
        (∑ j : Fin N,
          if ((j : ℕ) * g) % N = (k : ℕ) then
            negacyclicSign N ((j : ℕ) * g) * p.coeffs j
          else 0) =
        negacyclicSign N ((j0 : ℕ) * g) * p.coeffs j0 := by
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0]
      · intro j _ hne
        have h_ne_mod : ((j : ℕ) * g) % N ≠ (k : ℕ) := by
          intro h_eq
          exact hne (mul_coprime_inj_fin hcop (h_eq.trans hj0.symm))
        rw [if_neg h_ne_mod]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j0))
    rw [h_single, norm_negacyclicSign_mul]
    exact Finset.le_sup (f := fun j => norm params (p.coeffs j)) (Finset.mem_univ j0)
  · have h_zero :
        (∑ j : Fin N,
          if ((j : ℕ) * g) % N = (k : ℕ) then
            negacyclicSign N ((j : ℕ) * g) * p.coeffs j
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hex ⟨j, h⟩)]
    rw [h_zero, norm_zero]
    exact Nat.zero_le _

theorem normInf_negacyclicGaloisEquiv (params : LWEParams) (N g : ℕ) [Fact (0 < N)]
    (hg : Odd g) (hcop : Nat.Coprime g N) (p : NegacyclicPoly (Zq params) N) :
    normInf params (negacyclicGaloisEquiv g hg hcop p).coeffs = normInf params p.coeffs := by
  refine le_antisymm ?_ ?_
  · rw [negacyclicGaloisEquiv_spec]
    exact normInf_negacyclicEvalPow_le params N g hcop p
  · rcases negacyclicGaloisEquiv_symm_exists (R := Zq params) (N := N) hg hcop with
      ⟨g_inv, _, hcop_inv, h_symm⟩
    have h_back : (negacyclicGaloisEquiv g hg hcop).symm (negacyclicGaloisEquiv g hg hcop p) = p :=
      (negacyclicGaloisEquiv g hg hcop).symm_apply_apply p
    conv_lhs => rw [← h_back, h_symm]
    exact normInf_negacyclicEvalPow_le params N g_inv hcop_inv _

lemma intCast_finset_sum {S : Type*} [Ring S] {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ((∑ i ∈ s, f i : ℤ) : S) = ∑ i ∈ s, ((f i : ℤ) : S) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Int.cast_add, ih]

lemma int_natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_tri := Int.natAbs_add_le (f a) (∑ i ∈ s, f i)
    omega

lemma int_negacyclicSign_natAbs_mul (N m : ℕ) (z : ℤ) :
    (negacyclicSign N m * z).natAbs = z.natAbs := by
  unfold negacyclicSign
  rw [Int.natAbs_mul, Int.natAbs_pow]
  simp

def intCastPolyHom (params : LWEParams) (N : ℕ) [Fact (0 < N)] :
    NegacyclicPoly ℤ N →+* NegacyclicPoly (Zq params) N where
  toFun P := ⟨fun k => Int.cast (P.coeffs k)⟩
  map_one' := by
    ext k
    change Int.cast (if (k : ℕ) = 0 then (1 : ℤ) else 0) =
      if (k : ℕ) = 0 then (1 : Zq params) else 0
    split_ifs <;> simp
  map_mul' P Q := by
    ext k
    simp only [mul_coeffs]
    rw [intCast_finset_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [intCast_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [Int.cast_mul, Int.cast_mul]
      congr 2
      unfold negacyclicSign
      rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
    · rw [Int.cast_zero]
  map_zero' := by
    ext k
    exact Int.cast_zero
  map_add' P Q := by
    ext k
    exact Int.cast_add (P.coeffs k) (Q.coeffs k)

lemma intCastPolyHom_coeffs (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (P : NegacyclicPoly ℤ N) (k : Fin N) :
    (intCastPolyHom params N P).coeffs k = Int.cast (P.coeffs k) := rfl

def liftPolyCentered (params : LWEParams) (N : ℕ)
    (p : NegacyclicPoly (Zq params) N) : NegacyclicPoly ℤ N :=
  ⟨fun k => centeredLift params (p.coeffs k)⟩

lemma intCastPolyHom_liftPolyCentered (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (p : NegacyclicPoly (Zq params) N) :
    intCastPolyHom params N (liftPolyCentered params N p) = p := by
  ext k
  exact intCast_centeredLift params (p.coeffs k)

lemma intCastPolyHom_q_zero (params : LWEParams) (N : ℕ) [Fact (0 < N)] :
    intCastPolyHom params N (params.q : NegacyclicPoly ℤ N) = 0 := by
  ext k
  change ((if (k : ℕ) = 0 then (params.q : ℤ) else 0 : ℤ) : Zq params) = 0
  split_ifs
  · rw [Int.cast_natCast, ZMod.natCast_self]
  · exact Int.cast_zero

def intPolyNormInf {N : ℕ} (P : NegacyclicPoly ℤ N) : ℕ :=
  Finset.univ.sup (fun k => (P.coeffs k).natAbs)

lemma natAbs_coeffs_le_intPolyNormInf {N : ℕ} (P : NegacyclicPoly ℤ N) (k : Fin N) :
    (P.coeffs k).natAbs ≤ intPolyNormInf P :=
  Finset.le_sup (f := fun j => (P.coeffs j).natAbs) (Finset.mem_univ k)

lemma intPolyNormInf_liftPolyCentered (params : LWEParams) (N : ℕ)
    (p : NegacyclicPoly (Zq params) N) :
    intPolyNormInf (liftPolyCentered params N p) = normInf params p.coeffs := rfl

theorem normInf_intCastPolyHom_le (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (P : NegacyclicPoly ℤ N) :
    normInf params (intCastPolyHom params N P).coeffs ≤ intPolyNormInf P := by
  dsimp [normInf, intPolyNormInf, intCastPolyHom]
  apply Finset.sup_le
  intro k _
  exact le_trans (norm_intCast_le_natAbs params (P.coeffs k))
    (Finset.le_sup (f := fun j => (P.coeffs j).natAbs) (Finset.mem_univ k))

theorem intPolyNormInf_add_le {N : ℕ} (P Q : NegacyclicPoly ℤ N) :
    intPolyNormInf (P + Q) ≤ intPolyNormInf P + intPolyNormInf Q := by
  change Finset.univ.sup (fun k => ((P + Q).coeffs k).natAbs) ≤ _
  apply Finset.sup_le
  intro k _
  exact le_trans (Int.natAbs_add_le (P.coeffs k) (Q.coeffs k))
    (Nat.add_le_add (natAbs_coeffs_le_intPolyNormInf P k)
      (natAbs_coeffs_le_intPolyNormInf Q k))

theorem intPolyNormInf_neg {N : ℕ} (P : NegacyclicPoly ℤ N) :
    intPolyNormInf (-P) = intPolyNormInf P := by
  dsimp [intPolyNormInf]
  congr 1
  ext k
  exact Int.natAbs_neg (P.coeffs k)

theorem intPolyNormInf_sub_le {N : ℕ} (P Q : NegacyclicPoly ℤ N) :
    intPolyNormInf (P - Q) ≤ intPolyNormInf P + intPolyNormInf Q := by
  rw [sub_eq_add_neg, ← intPolyNormInf_neg Q]
  exact intPolyNormInf_add_le P (-Q)

theorem intPolyNormInf_constPoly_mul_le {N : ℕ} [Fact (0 < N)]
    (c : ℤ) (P : NegacyclicPoly ℤ N) :
    intPolyNormInf (constPoly c * P) ≤ c.natAbs * intPolyNormInf P := by
  change Finset.univ.sup (fun k => ((constPoly c * P).coeffs k).natAbs) ≤ _
  apply Finset.sup_le
  intro k _
  rw [constPoly_mul_coeffs, Int.natAbs_mul]
  exact Nat.mul_le_mul_left c.natAbs (natAbs_coeffs_le_intPolyNormInf P k)

theorem intPolyNormInf_intCast_mul_le {N : ℕ} [Fact (0 < N)]
    (c : ℤ) (P : NegacyclicPoly ℤ N) :
    intPolyNormInf ((c : NegacyclicPoly ℤ N) * P) ≤ c.natAbs * intPolyNormInf P :=
  intPolyNormInf_constPoly_mul_le c P

theorem intPolyNormInf_mul_le {N : ℕ} [hN : Fact (0 < N)] (P Q : NegacyclicPoly ℤ N) :
    intPolyNormInf (P * Q) ≤ N * intPolyNormInf P * intPolyNormInf Q := by
  change Finset.univ.sup (fun k => ((P * Q).coeffs k).natAbs) ≤ _
  apply Finset.sup_le
  intro k _
  rw [mul_coeffs]
  have h_sum_le := int_natAbs_sum_le Finset.univ (fun i : Fin N =>
    ∑ j : Fin N,
      if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((i : ℕ) + (j : ℕ)) * P.coeffs i * Q.coeffs j
      else 0)
  have h_term_le :
      (∑ i : Fin N, (∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * P.coeffs i * Q.coeffs j
        else 0).natAbs) ≤
      ∑ _i : Fin N, intPolyNormInf P * intPolyNormInf Q := by
    apply Finset.sum_le_sum
    intro i _
    let j0 : Fin N := ⟨((k : ℕ) + N - (i : ℕ)) % N, Nat.mod_lt _ hN.out⟩
    have hj0 : ∀ j : Fin N, (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔ j = j0 :=
      mod_add_eq_iff_fin i k
    simp_rw [hj0]
    have h_inner :
        (∑ j : Fin N,
          if j = j0 then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * P.coeffs i * Q.coeffs j
          else 0) =
        negacyclicSign N ((i : ℕ) + (j0 : ℕ)) * (P.coeffs i * Q.coeffs j0) := by
      simp [mul_assoc]
    rw [h_inner, int_negacyclicSign_natAbs_mul, Int.natAbs_mul]
    exact Nat.mul_le_mul
      (natAbs_coeffs_le_intPolyNormInf P i) (natAbs_coeffs_le_intPolyNormInf Q j0)
  have h_const :
      (∑ _i : Fin N, intPolyNormInf P * intPolyNormInf Q) =
        N * (intPolyNormInf P * intPolyNormInf Q) := by
    simp
  have h_assoc : N * (intPolyNormInf P * intPolyNormInf Q) =
      N * intPolyNormInf P * intPolyNormInf Q := by ring
  rw [h_const, h_assoc] at h_term_le
  exact le_trans h_sum_le h_term_le

theorem intPolyNormInf_negacyclicEvalPow_le {N g : ℕ} (hcop : Nat.Coprime g N)
    (P : NegacyclicPoly ℤ N) :
    intPolyNormInf (negacyclicEvalPow g P) ≤ intPolyNormInf P := by
  change Finset.univ.sup (fun k => ((negacyclicEvalPow g P).coeffs k).natAbs) ≤ _
  apply Finset.sup_le
  intro k _
  rw [negacyclicEvalPow_coeffs]
  by_cases hex : ∃ j0 : Fin N, ((j0 : ℕ) * g) % N = (k : ℕ)
  · rcases hex with ⟨j0, hj0⟩
    have h_single :
        (∑ j : Fin N,
          if ((j : ℕ) * g) % N = (k : ℕ) then
            negacyclicSign N ((j : ℕ) * g) * P.coeffs j
          else 0) =
        negacyclicSign N ((j0 : ℕ) * g) * P.coeffs j0 := by
      rw [Finset.sum_eq_single j0]
      · rw [if_pos hj0]
      · intro j _ hne
        have h_ne_mod : ((j : ℕ) * g) % N ≠ (k : ℕ) := by
          intro h_eq
          exact hne (mul_coprime_inj_fin hcop (h_eq.trans hj0.symm))
        rw [if_neg h_ne_mod]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j0))
    rw [h_single, int_negacyclicSign_natAbs_mul]
    exact natAbs_coeffs_le_intPolyNormInf P j0
  · have h_zero :
        (∑ j : Fin N,
          if ((j : ℕ) * g) % N = (k : ℕ) then
            negacyclicSign N ((j : ℕ) * g) * P.coeffs j
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg (fun h => hex ⟨j, h⟩)]
    rw [h_zero, Int.natAbs_zero]
    exact Nat.zero_le _

theorem normInf_mul_le (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (p q : NegacyclicPoly (Zq params) N) :
    normInf params (p * q).coeffs ≤ N * normInf params p.coeffs * normInf params q.coeffs := by
  have h_eq :
      p * q = intCastPolyHom params N
        (liftPolyCentered params N p * liftPolyCentered params N q) := by
    rw [map_mul, intCastPolyHom_liftPolyCentered, intCastPolyHom_liftPolyCentered]
  rw [h_eq]
  exact le_trans (normInf_intCastPolyHom_le params N _)
    (intPolyNormInf_mul_le (liftPolyCentered params N p) (liftPolyCentered params N q))

theorem normInf_le_one_of_isTernaryPoly (params : LWEParams) (N : ℕ)
    (s : NegacyclicPoly (Zq params) N) (hs : IsTernaryPoly s) :
    normInf params s.coeffs ≤ 1 := by
  dsimp [normInf]
  apply Finset.sup_le
  intro k _
  rcases hs k with h0 | h1 | hn1
  · rw [h0, norm_zero]
    exact Nat.zero_le 1
  · rw [h1, ← Int.cast_one]
    exact norm_intCast_le_natAbs params 1
  · rw [hn1, norm_neg_elem, ← Int.cast_one]
    exact norm_intCast_le_natAbs params 1

theorem normInf_negacyclicDecomp_le (params : LWEParams) (N B l : ℕ)
    (hB : 0 < B) (h2B : 2 * B ≤ params.q)
    (p : NegacyclicPoly (Zq params) N) (i : Fin l) :
    normInf params (negacyclicDecomp params N B l p i).coeffs ≤ B - 1 := by
  dsimp [normInf, negacyclicDecomp]
  apply Finset.sup_le
  intro k _
  have h_lt := baseDecomp_norm_lt params B l hB h2B (p.coeffs k) i
  omega

end NegacyclicPoly

lemma normInf_finset_sum_poly_le {ι : Type*}
    (params : LWEParams) (N : ℕ) (s : Finset ι)
    (f : ι → NegacyclicPoly (Zq params) N) :
    normInf params (∑ i ∈ s, f i).coeffs ≤ ∑ i ∈ s, normInf params (f i).coeffs := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold normInf
    rw [Finset.sup_le_iff]
    intro j _
    change norm params 0 ≤ 0
    unfold norm centeredLift
    rw [ZMod.val_zero]
    dsimp
    split_ifs <;> omega
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_add := norm_add_le params (f a).coeffs (∑ i ∈ s, f i).coeffs
    change normInf params ((f a).coeffs + (∑ i ∈ s, f i).coeffs) ≤ _
    omega

theorem NegacyclicPoly.normInf_gadgetRelin_noise_le (params : LWEParams) (N B l B_rk : ℕ)
    [Fact (0 < N)]
    (hB : 0 < B) (h2B : 2 * B ≤ params.q)
    (p : NegacyclicPoly (Zq params) N)
    (e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (herk : ∀ i : Fin l, normInf params (e_rk i).coeffs ≤ B_rk) :
    normInf params
        (∑ i : Fin l, NegacyclicPoly.negacyclicDecomp params N B l p i * e_rk i).coeffs ≤
      l * (N * (B - 1) * B_rk) := by
  have h_sum := normInf_finset_sum_poly_le params N Finset.univ
    (fun i : Fin l => NegacyclicPoly.negacyclicDecomp params N B l p i * e_rk i)
  have h_each : ∀ i ∈ (Finset.univ : Finset (Fin l)),
      normInf params (NegacyclicPoly.negacyclicDecomp params N B l p i * e_rk i).coeffs ≤
        N * (B - 1) * B_rk := by
    intro i _
    have h_mul := NegacyclicPoly.normInf_mul_le params N
      (NegacyclicPoly.negacyclicDecomp params N B l p i) (e_rk i)
    have h_dec := NegacyclicPoly.normInf_negacyclicDecomp_le params N B l hB h2B p i
    have h_rk := herk i
    have h1 : N * normInf params (NegacyclicPoly.negacyclicDecomp params N B l p i).coeffs ≤
        N * (B - 1) :=
      Nat.mul_le_mul_left N h_dec
    have h2 : N * normInf params (NegacyclicPoly.negacyclicDecomp params N B l p i).coeffs *
        normInf params (e_rk i).coeffs ≤ N * (B - 1) * B_rk :=
      Nat.mul_le_mul h1 h_rk
    exact le_trans h_mul h2
  have h_le := Finset.sum_le_sum h_each
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_le
  exact le_trans h_sum h_le

end NegacyclicPolyRing

section NTT

variable (PolyR : Type*) [CommRing PolyR]
variable (ScalarR : Type*) [CommRing ScalarR]
variable (N : ℕ)

structure NTTHom (PolyR : Type*) [CommRing PolyR] (N : ℕ) (ScalarR : Type*) [CommRing ScalarR] where
  toFun : PolyR → (Fin N → ScalarR)
  map_add : ∀ x y : PolyR, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y : PolyR, toFun (x * y) = toFun x * toFun y
  map_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → PolyR), toFun (∑ x ∈ s, f x) = ∑ x ∈ s, toFun (f x)

structure NTTSample where
  a_ntt : Fin N → ScalarR
  b_ntt : Fin N → ScalarR

def toNTT (c : RingSample PolyR) (ntt : NTTHom PolyR N ScalarR) : NTTSample ScalarR N :=
  { a_ntt := ntt.toFun c.a,
    b_ntt := ntt.toFun c.b }

structure NTTSample2 where
  d0_ntt : Fin N → ScalarR
  d1_ntt : Fin N → ScalarR
  d2_ntt : Fin N → ScalarR

def nttMultiply (x y : NTTSample ScalarR N) : NTTSample2 ScalarR N :=
  { d0_ntt := x.b_ntt * y.b_ntt,
    d1_ntt := x.a_ntt * y.b_ntt + x.b_ntt * y.a_ntt,
    d2_ntt := x.a_ntt * y.a_ntt }

theorem ntt_multiply_correct (c1 c2 : RingSample PolyR) (ntt : NTTHom PolyR N ScalarR) :
    let c_mul := mulRingSamples c1 c2
    let ntt_c_mul : NTTSample2 ScalarR N :=
      { d0_ntt := ntt.toFun c_mul.d0, d1_ntt := ntt.toFun c_mul.d1, d2_ntt := ntt.toFun c_mul.d2 }
    let ntt1 := toNTT PolyR ScalarR N c1 ntt
    let ntt2 := toNTT PolyR ScalarR N c2 ntt
    nttMultiply ScalarR N ntt1 ntt2 = ntt_c_mul := by
  dsimp [mulRingSamples, toNTT, nttMultiply]
  congr
  · exact (ntt.map_mul c1.b c2.b).symm
  · rw [ntt.map_add, ntt.map_mul, ntt.map_mul]
    ring
  · exact (ntt.map_mul c1.a c2.a).symm

end NTT

section ConcreteNTT

open scoped BigOperators

variable {R : Type*} [CommRing R] {N : ℕ}

def oddRoot (ψ : R) (m : Fin N) : R :=
  ψ ^ (2 * (m : ℕ) + 1)

def concreteNTT (ψ : R) (p : NegacyclicPoly R N) : Fin N → R :=
  fun m => ∑ j : Fin N, p.coeffs j * (oddRoot ψ m) ^ (j : ℕ)

def concreteInvNTT (ψ_inv n_inv : R) (evals : Fin N → R) : NegacyclicPoly R N :=
  ⟨fun i => n_inv * ∑ m : Fin N, evals m * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))⟩

lemma oddRoot_pow_N (ψ : R) (hpsi : ψ ^ N = -1) (m : Fin N) :
    (oddRoot ψ m) ^ N = -1 := by
  unfold oddRoot
  rw [← pow_mul, mul_comm (2 * (m : ℕ) + 1) N, pow_mul, hpsi]
  rw [pow_add, pow_mul, pow_one]
  have h2 : (-1 : R) ^ 2 = 1 := by ring
  rw [h2, one_pow, one_mul]

lemma oddRoot_pow_eq_negacyclicSign (ψ : R) (hpsi : ψ ^ N = -1) (m : Fin N) (a : ℕ) :
    (oddRoot ψ m) ^ a = NegacyclicPoly.negacyclicSign N a * (oddRoot ψ m) ^ (a % N) := by
  have h_div : a = N * (a / N) + a % N := (Nat.div_add_mod a N).symm
  conv_lhs => rw [h_div]
  rw [pow_add, pow_mul, oddRoot_pow_N ψ hpsi m]
  rfl

theorem concreteNTT_map_add (ψ : R) (p q : NegacyclicPoly R N) :
    concreteNTT ψ (p + q) = concreteNTT ψ p + concreteNTT ψ q := by
  ext m
  simp only [concreteNTT, Pi.add_apply, NegacyclicPoly.add_coeffs, add_mul, Finset.sum_add_distrib]

theorem concreteNTT_map_sum (ψ : R) {ι : Type} (s : Finset ι) (f : ι → NegacyclicPoly R N) :
    concreteNTT ψ (∑ x ∈ s, f x) = ∑ x ∈ s, concreteNTT ψ (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext m
    simp [concreteNTT]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, concreteNTT_map_add, ih, Finset.sum_insert ha]

theorem concreteNTT_map_mul [hN : Fact (0 < N)] (ψ : R) (hpsi : ψ ^ N = -1)
    (p q : NegacyclicPoly R N) :
    concreteNTT ψ (p * q) = concreteNTT ψ p * concreteNTT ψ q := by
  ext m
  simp only [concreteNTT, Pi.mul_apply, NegacyclicPoly.mul_coeffs]
  have h_push :
      (∑ k : Fin N,
        (∑ i : Fin N, ∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
          else 0) * (oddRoot ψ m) ^ (k : ℕ)) =
      ∑ k : Fin N, ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
            (oddRoot ψ m) ^ (k : ℕ)
        else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [h_push]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  have h_collapse :
      (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
            (oddRoot ψ m) ^ (k : ℕ)
        else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        (p.coeffs i * (oddRoot ψ m) ^ (i : ℕ)) * (q.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    let k0 : Fin N := ⟨((i : ℕ) + (j : ℕ)) % N, Nat.mod_lt _ hN.out⟩
    have hk0 : ∀ k : Fin N, (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔ k = k0 := by
      intro k
      rw [Fin.ext_iff, eq_comm]
    simp_rw [hk0]
    have h_sum_k :
        (∑ k : Fin N,
          if k = k0 then
            NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
              (oddRoot ψ m) ^ (k : ℕ)
          else 0) =
        NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
          (oddRoot ψ m) ^ (((i : ℕ) + (j : ℕ)) % N) := by
      simp [k0]
    rw [h_sum_k]
    have h_pow := oddRoot_pow_eq_negacyclicSign ψ hpsi m ((i : ℕ) + (j : ℕ))
    calc
      NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
          (oddRoot ψ m) ^ (((i : ℕ) + (j : ℕ)) % N)
        = p.coeffs i * q.coeffs j *
            (NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) *
              (oddRoot ψ m) ^ (((i : ℕ) + (j : ℕ)) % N)) := by ring
      _ = p.coeffs i * q.coeffs j * (oddRoot ψ m) ^ ((i : ℕ) + (j : ℕ)) := by rw [← h_pow]
      _ = (p.coeffs i * (oddRoot ψ m) ^ (i : ℕ)) * (q.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) := by
        rw [pow_add]
        ring
  rw [h_collapse, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]

def concreteNTTHom [Fact (0 < N)] (ψ : R) (hpsi : ψ ^ N = -1) :
    NTTHom (NegacyclicPoly R N) N R where
  toFun := concreteNTT ψ
  map_add := concreteNTT_map_add ψ
  map_mul := concreteNTT_map_mul ψ hpsi
  map_sum := concreteNTT_map_sum ψ

def IsValidNTTInverse (N : ℕ) (ψ ψ_inv n_inv : R) : Prop :=
  ∀ j i : Fin N,
    n_inv * (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
      if j = i then 1 else 0

lemma oddRoot_mul_inv_diag (ψ ψ_inv : R) (h_inv : ψ * ψ_inv = 1) (m : Fin N) (i : ℕ) :
    (oddRoot ψ m) ^ i * ψ_inv ^ ((2 * (m : ℕ) + 1) * i) = 1 := by
  unfold oddRoot
  rw [← pow_mul, ← mul_pow, h_inv, one_pow]

lemma oddRoot_mul_inv_term (ψ ψ_inv : R) (m : Fin N) (j i : ℕ) :
    (oddRoot ψ m) ^ j * ψ_inv ^ ((2 * (m : ℕ) + 1) * i) =
      (ψ ^ j * ψ_inv ^ i) * (ψ ^ (2 * j) * ψ_inv ^ (2 * i)) ^ (m : ℕ) := by
  unfold oddRoot
  have h1 : (2 * (m : ℕ) + 1) * j = j + (2 * j) * (m : ℕ) := by ring
  have h2 : (2 * (m : ℕ) + 1) * i = i + (2 * i) * (m : ℕ) := by ring
  rw [← pow_mul, h1, h2, pow_add, pow_add, pow_mul, pow_mul, mul_pow]
  ring

lemma finset_geom_sum_mul (r : R) :
    ∀ n : ℕ, (∑ m ∈ Finset.range n, r ^ m) * (r - 1) = r ^ n - 1
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, add_mul, finset_geom_sum_mul r n, pow_succ]
    ring

lemma oddRoot_ratio_pow_N_eq_one (ψ ψ_inv : R) (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1)
    (j i : ℕ) :
    (ψ ^ (2 * j) * ψ_inv ^ (2 * i)) ^ N = 1 := by
  have h_psi2N : (ψ ^ N) ^ 2 = 1 := by
    rw [hpsi]
    ring
  have h_invN : (ψ_inv ^ N) ^ 2 = 1 := by
    have h_prod : (ψ ^ N) ^ 2 * (ψ_inv ^ N) ^ 2 = 1 := by
      rw [← mul_pow, ← mul_pow, h_inv, one_pow, one_pow]
    rw [h_psi2N, one_mul] at h_prod
    exact h_prod
  have hj : (ψ ^ (2 * j)) ^ N = ((ψ ^ N) ^ 2) ^ j := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hi : (ψ_inv ^ (2 * i)) ^ N = ((ψ_inv ^ N) ^ 2) ^ i := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [mul_pow, hj, hi, h_psi2N, h_invN, one_pow, one_pow, mul_one]

theorem isValidNTTInverse_of_primitive [NoZeroDivisors R] (ψ ψ_inv n_inv : R)
    (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1) :
    IsValidNTTInverse N ψ ψ_inv n_inv := by
  intro j i
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    have h_diag : (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (j : ℕ))) =
        (N : R) := by
      simp_rw [oddRoot_mul_inv_diag ψ ψ_inv h_inv _ (j : ℕ)]
      simp
    rw [h_diag, hn]
  · rw [if_neg hji]
    set r : R := ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ))
    have h_factor :
        (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
          (ψ ^ (j : ℕ) * ψ_inv ^ (i : ℕ)) * (∑ m : Fin N, r ^ (m : ℕ)) := by
      simp_rw [oddRoot_mul_inv_term ψ ψ_inv _ (j : ℕ) (i : ℕ)]
      rw [← Finset.mul_sum]
    have h_fin_sum : (∑ m : Fin N, r ^ (m : ℕ)) = ∑ m ∈ Finset.range N, r ^ m := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => r ^ m) N]
    have h_geom : (∑ m ∈ Finset.range N, r ^ m) * (r - 1) = 0 := by
      rw [finset_geom_sum_mul r N,
        oddRoot_ratio_pow_N_eq_one ψ ψ_inv hpsi h_inv (j : ℕ) (i : ℕ), sub_self]
    have hr_ne : r - 1 ≠ 0 := sub_ne_zero.mpr (h_prim j i hji)
    have h_sum_zero : (∑ m ∈ Finset.range N, r ^ m) = 0 := by
      rcases mul_eq_zero.mp h_geom with h0 | h1
      · exact h0
      · exact False.elim (hr_ne h1)
    rw [h_factor, h_fin_sum, h_sum_zero, mul_zero, mul_zero]

theorem concreteInvNTT_concreteNTT (ψ ψ_inv n_inv : R)
    (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv) (p : NegacyclicPoly R N) :
    concreteInvNTT ψ_inv n_inv (concreteNTT ψ p) = p := by
  ext i
  dsimp [concreteInvNTT, concreteNTT]
  have h_expand :
      (∑ m : Fin N,
        (∑ j : Fin N, p.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) *
          ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
      ∑ j : Fin N, p.coeffs j *
        (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) := by
    have h1 :
        (∑ m : Fin N,
          (∑ j : Fin N, p.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) *
            ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
        ∑ m : Fin N, ∑ j : Fin N,
          p.coeffs j * ((oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
  rw [h_expand, Finset.mul_sum]
  have h_orth_apply :
      (∑ j : Fin N,
        n_inv * (p.coeffs j *
          (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))))) =
      ∑ j : Fin N, if j = i then p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have h_j :
        n_inv * (p.coeffs j *
          (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ)))) =
        p.coeffs j *
          (n_inv * (∑ m : Fin N,
            (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ)))) := by
      ring
    rw [h_j, h_orth j i]
    split_ifs <;> ring
  rw [h_orth_apply]
  simp

theorem concrete_ntt_mul_eq_mulSchoolbook [Fact (0 < N)] (ψ ψ_inv n_inv : R)
    (hpsi : ψ ^ N = -1) (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (p q : NegacyclicPoly R N) :
    concreteInvNTT ψ_inv n_inv (concreteNTT ψ p * concreteNTT ψ q) = p * q := by
  rw [← concreteNTT_map_mul ψ hpsi p q]
  exact concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth (p * q)

theorem concrete_ntt_mul_eq_mulSchoolbook_of_primitive [Fact (0 < N)] [NoZeroDivisors R]
    (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1)
    (p q : NegacyclicPoly R N) :
    concreteInvNTT ψ_inv n_inv (concreteNTT ψ p * concreteNTT ψ q) = p * q :=
  concrete_ntt_mul_eq_mulSchoolbook ψ ψ_inv n_inv hpsi
    (isValidNTTInverse_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim) p q

def IsValidNTTSlotInverse (N : ℕ) (ψ ψ_inv n_inv : R) : Prop :=
  ∀ m1 m2 : Fin N,
    n_inv * (∑ j : Fin N, ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ)) * (oddRoot ψ m2) ^ (j : ℕ)) =
      if m1 = m2 then 1 else 0

lemma inv_odd_mul_oddRoot (ψ ψ_inv : R) (h_inv : ψ * ψ_inv = 1) (m1 m2 j : ℕ) :
    ψ_inv ^ ((2 * m1 + 1) * j) * (ψ ^ (2 * m2 + 1)) ^ j =
      (ψ ^ (2 * m2) * ψ_inv ^ (2 * m1)) ^ j := by
  have h_base : ψ_inv ^ (2 * m1 + 1) * ψ ^ (2 * m2 + 1) = ψ ^ (2 * m2) * ψ_inv ^ (2 * m1) := by
    rw [pow_succ, pow_succ]
    calc (ψ_inv ^ (2 * m1) * ψ_inv) * (ψ ^ (2 * m2) * ψ)
        = (ψ ^ (2 * m2) * ψ_inv ^ (2 * m1)) * (ψ * ψ_inv) := by ring
      _ = ψ ^ (2 * m2) * ψ_inv ^ (2 * m1) := by rw [h_inv, mul_one]
  calc ψ_inv ^ ((2 * m1 + 1) * j) * (ψ ^ (2 * m2 + 1)) ^ j
      = (ψ_inv ^ (2 * m1 + 1)) ^ j * (ψ ^ (2 * m2 + 1)) ^ j := by rw [pow_mul]
    _ = (ψ_inv ^ (2 * m1 + 1) * ψ ^ (2 * m2 + 1)) ^ j := by rw [← mul_pow]
    _ = (ψ ^ (2 * m2) * ψ_inv ^ (2 * m1)) ^ j := by rw [h_base]

theorem isValidNTTSlotInverse_of_primitive [NoZeroDivisors R] (ψ ψ_inv n_inv : R)
    (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1) :
    IsValidNTTSlotInverse N ψ ψ_inv n_inv := by
  intro m1 m2
  have h_term : ∀ j : Fin N,
      ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ)) * (oddRoot ψ m2) ^ (j : ℕ) =
        (ψ ^ (2 * (m2 : ℕ)) * ψ_inv ^ (2 * (m1 : ℕ))) ^ (j : ℕ) := by
    intro j
    exact inv_odd_mul_oddRoot ψ ψ_inv h_inv m1 m2 j
  simp_rw [h_term]
  by_cases hm : m1 = m2
  · subst hm
    rw [if_pos rfl]
    have h_one : ψ ^ (2 * (m1 : ℕ)) * ψ_inv ^ (2 * (m1 : ℕ)) = 1 := by
      rw [← mul_pow, h_inv, one_pow]
    simp [h_one, hn]
  · rw [if_neg hm]
    set r : R := ψ ^ (2 * (m2 : ℕ)) * ψ_inv ^ (2 * (m1 : ℕ))
    have h_fin_sum : (∑ j : Fin N, r ^ (j : ℕ)) = ∑ j ∈ Finset.range N, r ^ j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => r ^ j) N]
    have h_geom : (∑ j ∈ Finset.range N, r ^ j) * (r - 1) = 0 := by
      rw [finset_geom_sum_mul r N,
        oddRoot_ratio_pow_N_eq_one ψ ψ_inv hpsi h_inv (m2 : ℕ) (m1 : ℕ), sub_self]
    have hr_ne : r - 1 ≠ 0 := sub_ne_zero.mpr (h_prim m2 m1 (Ne.symm hm))
    have h_sum_zero : (∑ j ∈ Finset.range N, r ^ j) = 0 := by
      rcases mul_eq_zero.mp h_geom with h0 | h1
      · exact h0
      · exact False.elim (hr_ne h1)
    rw [h_fin_sum, h_sum_zero, mul_zero]

theorem concreteNTT_concreteInvNTT (ψ ψ_inv n_inv : R)
    (h_slot : IsValidNTTSlotInverse N ψ ψ_inv n_inv) (evals : Fin N → R) :
    concreteNTT ψ (concreteInvNTT ψ_inv n_inv evals) = evals := by
  ext m2
  dsimp [concreteNTT, concreteInvNTT]
  have h_push :
      (∑ j : Fin N,
        (n_inv * ∑ m1 : Fin N, evals m1 * ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ))) *
          (oddRoot ψ m2) ^ (j : ℕ)) =
      ∑ m1 : Fin N, evals m1 *
        (n_inv * ∑ j : Fin N,
          ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ)) * (oddRoot ψ m2) ^ (j : ℕ)) := by
    have h1 :
        (∑ j : Fin N,
          (n_inv * ∑ m1 : Fin N, evals m1 * ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ))) *
            (oddRoot ψ m2) ^ (j : ℕ)) =
        ∑ j : Fin N, ∑ m1 : Fin N,
          evals m1 *
            (n_inv * (ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ)) * (oddRoot ψ m2) ^ (j : ℕ))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m1 _
      ring
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m1 _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [h_push]
  have h_slot_apply :
      (∑ m1 : Fin N, evals m1 *
        (n_inv * ∑ j : Fin N,
          ψ_inv ^ ((2 * (m1 : ℕ) + 1) * (j : ℕ)) * (oddRoot ψ m2) ^ (j : ℕ))) =
      ∑ m1 : Fin N, if m1 = m2 then evals m1 else 0 := by
    apply Finset.sum_congr rfl
    intro m1 _
    rw [h_slot m1 m2]
    split_ifs <;> ring
  rw [h_slot_apply]
  simp

theorem concreteNTT_concreteInvNTT_of_primitive [NoZeroDivisors R] (ψ ψ_inv n_inv : R)
    (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1)
    (evals : Fin N → R) :
    concreteNTT ψ (concreteInvNTT ψ_inv n_inv evals) = evals :=
  concreteNTT_concreteInvNTT ψ ψ_inv n_inv
    (isValidNTTSlotInverse_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim) evals

lemma concreteNTT_one [hN : Fact (0 < N)] (ψ : R) :
    concreteNTT ψ (1 : NegacyclicPoly R N) = 1 := by
  ext m
  simp only [concreteNTT, NegacyclicPoly.one_coeffs, Pi.one_apply]
  let z0 : Fin N := ⟨0, hN.out⟩
  rw [Finset.sum_eq_single z0]
  · simp [z0]
  · intro j _ hne
    have hj0 : (j : ℕ) ≠ 0 := fun h0 => hne (Fin.ext h0)
    simp [hj0]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ z0))

def concreteNTTRingEquiv [Fact (0 < N)] (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1)
    (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (h_slot : IsValidNTTSlotInverse N ψ ψ_inv n_inv) :
    NegacyclicPoly R N ≃+* (Fin N → R) where
  toFun := concreteNTT ψ
  invFun := concreteInvNTT ψ_inv n_inv
  left_inv := concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth
  right_inv := concreteNTT_concreteInvNTT ψ ψ_inv n_inv h_slot
  map_mul' := concreteNTT_map_mul ψ hpsi
  map_add' := concreteNTT_map_add ψ

lemma pow_two_mul_ne_one_of_pow_two_pow_eq_neg_one :
    ∀ (k : ℕ) (ψ : R), (-1 : R) ≠ 1 → ψ ^ (2 ^ k) = -1 →
      ∀ d : ℕ, 0 < d → d < 2 ^ k → ψ ^ (2 * d) ≠ 1
  | 0, _, _, _, d, hd_pos, hd_lt => by
    exfalso
    have h1 : (2 : ℕ) ^ 0 = 1 := rfl
    omega
  | k + 1, ψ, hneg, hpsi, d, hd_pos, hd_lt => by
    intro h_eq
    by_cases heven : d % 2 = 0
    · set d' : ℕ := d / 2
      have hd_eq : d = 2 * d' := by omega
      have hd'_pos : 0 < d' := by omega
      have h_p2k : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have hd'_lt : d' < 2 ^ k := by omega
      have h_psi2_pow : (ψ ^ 2) ^ (2 ^ k) = -1 := by
        rw [← pow_mul, ← h_p2k, hpsi]
      have h_psi2_d : (ψ ^ 2) ^ (2 * d') = 1 := by
        rw [← pow_mul]
        have h_exp : 2 * (2 * d') = 2 * d := by rw [hd_eq]
        rw [h_exp, h_eq]
      exact pow_two_mul_ne_one_of_pow_two_pow_eq_neg_one k (ψ ^ 2) hneg h_psi2_pow d'
        hd'_pos hd'_lt h_psi2_d
    · have h_pow1 : (ψ ^ (2 * d)) ^ (2 ^ k) = 1 := by rw [h_eq, one_pow]
      have h_pow2 : (ψ ^ (2 * d)) ^ (2 ^ k) = (-1 : R) ^ d := by
        rw [← pow_mul]
        have h_exp : 2 * d * 2 ^ k = 2 ^ (k + 1) * d := by ring
        rw [h_exp, pow_mul, hpsi]
      have h_odd : (-1 : R) ^ d = -1 := by
        have hd_split : d = 2 * (d / 2) + 1 := by omega
        conv_lhs => rw [hd_split]
        rw [pow_add, pow_mul]
        have h2 : (-1 : R) ^ 2 = 1 := by ring
        rw [h2, one_pow, one_mul, pow_one]
      rw [h_pow2, h_odd] at h_pow1
      exact hneg h_pow1

lemma neg_pow_pred_mul_self_of_pow_eq_neg_one {M : ℕ} (hM : 0 < M) (ψ : R)
    (hpsi : ψ ^ M = -1) :
    ψ * (-ψ ^ (M - 1)) = 1 := by
  rw [mul_neg, ← pow_succ', Nat.sub_add_cancel hM, hpsi, neg_neg]

theorem pow_two_prim_of_pow_eq_neg_one {k : ℕ} {ψ ψ_inv : R}
    (hneg : (-1 : R) ≠ 1) (hpsi : ψ ^ (2 ^ k) = -1) (h_inv : ψ * ψ_inv = 1) :
    ∀ j i : Fin (2 ^ k), j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1 := by
  intro j i hne h_eq
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · set d : ℕ := (i : ℕ) - (j : ℕ)
    have hd_pos : 0 < d := by omega
    have hi_lt := i.isLt
    have hd_lt : d < 2 ^ k := by omega
    have hi_eq : 2 * (i : ℕ) = 2 * (j : ℕ) + 2 * d := by omega
    rw [hi_eq, pow_add] at h_eq
    have h_canc : ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (j : ℕ)) = 1 := by
      rw [← mul_pow, h_inv, one_pow]
    have h_inv_d : ψ_inv ^ (2 * d) = 1 := by
      calc ψ_inv ^ (2 * d)
          = (ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (j : ℕ))) * ψ_inv ^ (2 * d) := by
            rw [h_canc, one_mul]
        _ = ψ ^ (2 * (j : ℕ)) * (ψ_inv ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * d)) := by ring
        _ = 1 := h_eq
    have h_psi_d : ψ ^ (2 * d) = 1 := by
      calc ψ ^ (2 * d)
          = ψ ^ (2 * d) * ψ_inv ^ (2 * d) := by rw [h_inv_d, mul_one]
        _ = (ψ * ψ_inv) ^ (2 * d) := (mul_pow ψ ψ_inv (2 * d)).symm
        _ = 1 := by rw [h_inv, one_pow]
    exact pow_two_mul_ne_one_of_pow_two_pow_eq_neg_one k ψ hneg hpsi d hd_pos hd_lt h_psi_d
  · set d : ℕ := (j : ℕ) - (i : ℕ)
    have hd_pos : 0 < d := by omega
    have hj_lt := j.isLt
    have hd_lt : d < 2 ^ k := by omega
    have hj_eq : 2 * (j : ℕ) = 2 * (i : ℕ) + 2 * d := by omega
    rw [hj_eq, pow_add] at h_eq
    have h_canc : ψ ^ (2 * (i : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) = 1 := by
      rw [← mul_pow, h_inv, one_pow]
    have h_psi_d : ψ ^ (2 * d) = 1 := by
      calc ψ ^ (2 * d)
          = (ψ ^ (2 * (i : ℕ)) * ψ_inv ^ (2 * (i : ℕ))) * ψ ^ (2 * d) := by
            rw [h_canc, one_mul]
        _ = ψ ^ (2 * (i : ℕ)) * ψ ^ (2 * d) * ψ_inv ^ (2 * (i : ℕ)) := by ring
        _ = 1 := h_eq
    exact pow_two_mul_ne_one_of_pow_two_pow_eq_neg_one k ψ hneg hpsi d hd_pos hd_lt h_psi_d

def concreteNTTRingEquivPowTwo [NoZeroDivisors R] (k : ℕ) (ψ n_inv : R)
    (hneg : (-1 : R) ≠ 1) (hpsi : ψ ^ (2 ^ k) = -1)
    (hn : n_inv * ((2 ^ k : ℕ) : R) = 1) :
    NegacyclicPoly R (2 ^ k) ≃+* (Fin (2 ^ k) → R) := by
  have h_pos : 0 < 2 ^ k := Nat.pow_pos (by decide)
  haveI : Fact (0 < 2 ^ k) := ⟨h_pos⟩
  let ψ_inv : R := -ψ ^ (2 ^ k - 1)
  have h_inv : ψ * ψ_inv = 1 := neg_pow_pred_mul_self_of_pow_eq_neg_one h_pos ψ hpsi
  have h_prim := pow_two_prim_of_pow_eq_neg_one hneg hpsi h_inv
  exact concreteNTTRingEquiv ψ ψ_inv n_inv hpsi
    (isValidNTTInverse_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim)
    (isValidNTTSlotInverse_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim)

end ConcreteNTT

section ZKP

variable (R : Type*) [CommRing R]

structure ZKPPublicInfo where
  a : R
  t : R

structure ZKPSecretWitness where
  s : R
  e : R

def mkZKPPublicInfo (a : R) (wit : ZKPSecretWitness R) : ZKPPublicInfo R :=
  { a := a, t := a * wit.s + wit.e }

def zkpCommit (a y_s y_e : R) : R :=
  a * y_s + y_e

structure ZKPResponse where
  z_s : R
  z_e : R

def zkpRespond (y_s y_e c : R) (wit : ZKPSecretWitness R) : ZKPResponse R :=
  { z_s := y_s + c * wit.s,
    z_e := y_e + c * wit.e }

def zkpVerifyAlgebraic (pub : ZKPPublicInfo R) (c w : R) (resp : ZKPResponse R) : Prop :=
  pub.a * resp.z_s + resp.z_e - c * pub.t = w

theorem zkp_completeness (a y_s y_e c : R) (wit : ZKPSecretWitness R) :
    let pub := mkZKPPublicInfo R a wit
    let w := zkpCommit R a y_s y_e
    let resp := zkpRespond R y_s y_e c wit
    zkpVerifyAlgebraic R pub c w resp := by
  dsimp [mkZKPPublicInfo, zkpCommit, zkpRespond, zkpVerifyAlgebraic]
  ring

theorem zkp_special_soundness (pub : ZKPPublicInfo R) (c1 c2 w : R)
    (resp1 resp2 : ZKPResponse R)
    (h1 : zkpVerifyAlgebraic R pub c1 w resp1)
    (h2 : zkpVerifyAlgebraic R pub c2 w resp2) :
    pub.a * (resp1.z_s - resp2.z_s) + (resp1.z_e - resp2.z_e) = (c1 - c2) * pub.t := by
  dsimp [zkpVerifyAlgebraic] at h1 h2
  calc
    pub.a * (resp1.z_s - resp2.z_s) + (resp1.z_e - resp2.z_e)
      = (pub.a * resp1.z_s + resp1.z_e - c1 * pub.t) -
        (pub.a * resp2.z_s + resp2.z_e - c2 * pub.t) + (c1 - c2) * pub.t := by ring
    _ = w - w + (c1 - c2) * pub.t := by rw [h1, h2]
    _ = (c1 - c2) * pub.t := by ring

class HasInfinityNorm (R : Type*) [AddGroup R] where
  normInf : R → ℕ
  normInf_add_le : ∀ x y : R, normInf (x + y) ≤ normInf x + normInf y
  normInf_neg : ∀ x : R, normInf (-x) = normInf x

instance instHasInfinityNormZq (params : LWEParams) : HasInfinityNorm (Zq params) where
  normInf := norm params
  normInf_add_le := norm_add_le_elem params
  normInf_neg := norm_neg_elem params

instance instHasInfinityNormVectorZq (params : LWEParams) (len : ℕ) :
    HasInfinityNorm (VectorR (Zq params) len) where
  normInf := normInf params
  normInf_add_le := norm_add_le params
  normInf_neg := norm_neg params

instance instHasInfinityNormNegacyclicPolyZq (params : LWEParams) (N : ℕ) :
    HasInfinityNorm (NegacyclicPoly (Zq params) N) where
  normInf p := normInf params p.coeffs
  normInf_add_le p q := norm_add_le params p.coeffs q.coeffs
  normInf_neg p := norm_neg params p.coeffs

variable [HasInfinityNorm R]

lemma normInf_sub_le (x y : R) :
    HasInfinityNorm.normInf (x - y) ≤ HasInfinityNorm.normInf x + HasInfinityNorm.normInf y := by
  rw [sub_eq_add_neg, ← HasInfinityNorm.normInf_neg y]
  exact HasInfinityNorm.normInf_add_le x (-y)

def zkpVerifyBound (resp : ZKPResponse R) (bound : ℕ) : Bool :=
  HasInfinityNorm.normInf resp.z_s ≤ bound ∧ HasInfinityNorm.normInf resp.z_e ≤ bound

theorem zkp_respond_passes_verify_of_mask_bound
    (y_s y_e c : R) (wit : ZKPSecretWitness R) (safe_bound beta : ℕ)
    (hys : HasInfinityNorm.normInf y_s + beta ≤ safe_bound)
    (hye : HasInfinityNorm.normInf y_e + beta ≤ safe_bound)
    (hcs : HasInfinityNorm.normInf (c * wit.s) ≤ beta)
    (hce : HasInfinityNorm.normInf (c * wit.e) ≤ beta) :
    zkpVerifyBound R (zkpRespond R y_s y_e c wit) safe_bound = true := by
  dsimp [zkpVerifyBound, zkpRespond]
  rw [decide_eq_true_iff]
  have hzs := HasInfinityNorm.normInf_add_le y_s (c * wit.s)
  have hze := HasInfinityNorm.normInf_add_le y_e (c * wit.e)
  constructor <;> omega

theorem zkp_extracted_norm_bound
    (resp1 resp2 : ZKPResponse R) (safe_bound : ℕ)
    (hb1 : zkpVerifyBound R resp1 safe_bound = true)
    (hb2 : zkpVerifyBound R resp2 safe_bound = true) :
    HasInfinityNorm.normInf (resp1.z_s - resp2.z_s) ≤ 2 * safe_bound ∧
    HasInfinityNorm.normInf (resp1.z_e - resp2.z_e) ≤ 2 * safe_bound := by
  dsimp [zkpVerifyBound] at hb1 hb2
  rw [decide_eq_true_iff] at hb1 hb2
  have h_sub_s := normInf_sub_le R resp1.z_s resp2.z_s
  have h_sub_e := normInf_sub_le R resp1.z_e resp2.z_e
  constructor <;> omega

theorem concrete_zkp_respond_passes_verify
    (params : LWEParams) (N safe_bound beta B_w : ℕ) [Fact (0 < N)]
    (y_s y_e c : NegacyclicPoly (Zq params) N)
    (wit : ZKPSecretWitness (NegacyclicPoly (Zq params) N))
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : normInf params wit.s.coeffs ≤ B_w)
    (he : normInf params wit.e.coeffs ≤ B_w)
    (hbeta : N * B_w ≤ beta)
    (hys : normInf params y_s.coeffs + beta ≤ safe_bound)
    (hye : normInf params y_e.coeffs + beta ≤ safe_bound) :
    zkpVerifyBound (NegacyclicPoly (Zq params) N)
      (zkpRespond (NegacyclicPoly (Zq params) N) y_s y_e c wit) safe_bound = true := by
  apply zkp_respond_passes_verify_of_mask_bound (NegacyclicPoly (Zq params) N)
    y_s y_e c wit safe_bound beta hys hye
  · have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c wit.s hc
    have h_le : N * normInf params wit.s.coeffs ≤ N * B_w := Nat.mul_le_mul_left N hs
    change normInf params (c * wit.s).coeffs ≤ beta
    omega
  · have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c wit.e hc
    have h_le : N * normInf params wit.e.coeffs ≤ N * B_w := Nat.mul_le_mul_left N he
    change normInf params (c * wit.e).coeffs ≤ beta
    omega

theorem zkp_special_soundness_nonvacuous
    (params : LWEParams) (N safe_bound : ℕ) [Fact (0 < N)]
    (h_bound : 4 * safe_bound + 1 < params.q)
    (pub : ZKPPublicInfo (NegacyclicPoly (Zq params) N))
    (c1 c2 w : NegacyclicPoly (Zq params) N)
    (resp1 resp2 : ZKPResponse (NegacyclicPoly (Zq params) N))
    (hc_ne : c1 ≠ c2)
    (ha1 : zkpVerifyAlgebraic (NegacyclicPoly (Zq params) N) pub c1 w resp1)
    (ha2 : zkpVerifyAlgebraic (NegacyclicPoly (Zq params) N) pub c2 w resp2)
    (hb1 : zkpVerifyBound (NegacyclicPoly (Zq params) N) resp1 safe_bound = true)
    (hb2 : zkpVerifyBound (NegacyclicPoly (Zq params) N) resp2 safe_bound = true) :
    c1 - c2 ≠ 0 ∧
    pub.a * (resp1.z_s - resp2.z_s) + (resp1.z_e - resp2.z_e) = (c1 - c2) * pub.t ∧
    normInf params (resp1.z_s - resp2.z_s).coeffs ≤ 2 * safe_bound ∧
    normInf params (resp1.z_e - resp2.z_e).coeffs ≤ 2 * safe_bound ∧
    2 * safe_bound < params.q / 2 := by
  have h_alg := zkp_special_soundness (NegacyclicPoly (Zq params) N) pub c1 c2 w resp1 resp2
    ha1 ha2
  have h_bnd := zkp_extracted_norm_bound (NegacyclicPoly (Zq params) N) resp1 resp2 safe_bound
    hb1 hb2
  exact ⟨sub_ne_zero.mpr hc_ne, h_alg, h_bnd.1, h_bnd.2, by omega⟩

def zkpAcceptedCoordMasks (params : LWEParams) (B beta : ℕ) (δ : Zq params) :
    Finset (Zq params) :=
  (boundedBall params B).filter (fun y => norm params (y + δ) ≤ B - beta)

@[simp] lemma mem_zkpAcceptedCoordMasks (params : LWEParams) (B beta : ℕ) (δ y : Zq params) :
    y ∈ zkpAcceptedCoordMasks params B beta δ ↔
      norm params y ≤ B ∧ norm params (y + δ) ≤ B - beta := by
  simp [zkpAcceptedCoordMasks]

theorem existsUnique_coordMask_of_mem_boundedBall
    (params : LWEParams) {B beta : ℕ} (hbeta : beta ≤ B)
    {δ z : Zq params} (hδ : norm params δ ≤ beta) (hz : z ∈ boundedBall params (B - beta)) :
    ∃! y : Zq params, y ∈ zkpAcceptedCoordMasks params B beta δ ∧ y + δ = z := by
  refine ⟨z - δ, ?_, ?_⟩
  · refine ⟨?_, sub_add_cancel z δ⟩
    rw [mem_boundedBall] at hz
    rw [mem_zkpAcceptedCoordMasks]
    have h_tri := norm_sub_le_elem params z δ
    refine ⟨by omega, ?_⟩
    rw [sub_add_cancel]
    exact hz
  · rintro y ⟨_, rfl⟩
    exact (add_sub_cancel_right y δ).symm

theorem card_zkpAcceptedCoordMasks
    (params : LWEParams) {B beta : ℕ} (hB : 2 * B < params.q) (hbeta : beta ≤ B)
    {δ : Zq params} (hδ : norm params δ ≤ beta) :
    (zkpAcceptedCoordMasks params B beta δ).card = 2 * (B - beta) + 1 := by
  have h_bij : (zkpAcceptedCoordMasks params B beta δ).card =
      (boundedBall params (B - beta)).card := by
    refine Finset.card_bij (fun y _ => y + δ) ?_ ?_ ?_
    · intro y hy
      rw [mem_zkpAcceptedCoordMasks] at hy
      rw [mem_boundedBall]
      exact hy.2
    · intro y₁ _ y₂ _ h_eq
      exact add_right_cancel h_eq
    · intro z hz
      refine ⟨z - δ, ?_, sub_add_cancel z δ⟩
      rw [mem_boundedBall] at hz
      rw [mem_zkpAcceptedCoordMasks]
      have h_tri := norm_sub_le_elem params z δ
      refine ⟨by omega, ?_⟩
      rw [sub_add_cancel]
      exact hz
  rw [h_bij, card_boundedBall params (B - beta) (by omega)]

theorem zkp_no_rejection_leaks_witness (params : LWEParams) (B beta : ℕ)
    (hbeta_pos : 0 < beta) (hq : 2 * (B + beta) < params.q) :
    ∃ (δ z_star : Zq params),
      norm params δ ≤ beta ∧ norm params z_star ≤ B + beta ∧
      (∃ y ∈ boundedBall params B, y + δ = z_star) ∧
      (∀ y ∈ boundedBall params B, y + 0 ≠ z_star) := by
  refine ⟨(((beta : ℕ) : ℤ) : Zq params), (((B + beta : ℕ) : ℤ) : Zq params), ?_, ?_, ?_, ?_⟩
  · have hk : ((beta : ℕ) : ℤ) ∈ Finset.Icc (-((B + beta : ℕ) : ℤ)) ((B + beta : ℕ) : ℤ) := by
      rw [Finset.mem_Icc]
      omega
    rw [norm_intCast_of_mem_Icc params hq hk]
    omega
  · have hk : ((B + beta : ℕ) : ℤ) ∈ Finset.Icc (-((B + beta : ℕ) : ℤ)) ((B + beta : ℕ) : ℤ) := by
      rw [Finset.mem_Icc]
      omega
    rw [norm_intCast_of_mem_Icc params hq hk]
    omega
  · refine ⟨(((B : ℕ) : ℤ) : Zq params), ?_, ?_⟩
    · rw [mem_boundedBall]
      have hk : ((B : ℕ) : ℤ) ∈ Finset.Icc (-((B + beta : ℕ) : ℤ)) ((B + beta : ℕ) : ℤ) := by
        rw [Finset.mem_Icc]
        omega
      rw [norm_intCast_of_mem_Icc params hq hk]
      omega
    · push_cast
      ring
  · intro y hy h_eq
    rw [mem_boundedBall] at hy
    rw [add_zero] at h_eq
    have h_norm := congrArg (norm params) h_eq
    have hk : ((B + beta : ℕ) : ℤ) ∈ Finset.Icc (-((B + beta : ℕ) : ℤ)) ((B + beta : ℕ) : ℤ) := by
      rw [Finset.mem_Icc]
      omega
    rw [norm_intCast_of_mem_Icc params hq hk] at h_norm
    omega

def polyBoundedBall (params : LWEParams) (N M : ℕ) : Finset (NegacyclicPoly (Zq params) N) :=
  (Fintype.piFinset (fun _ : Fin N => boundedBall params M)).map
    (NegacyclicPoly.coeffsEquiv (Zq params) N).symm.toEmbedding

@[simp] lemma mem_polyBoundedBall_iff (params : LWEParams) (N M : ℕ)
    (p : NegacyclicPoly (Zq params) N) :
    p ∈ polyBoundedBall params N M ↔ normInf params p.coeffs ≤ M := by
  unfold polyBoundedBall
  rw [Finset.mem_map]
  constructor
  · rintro ⟨f, hf, h_eq⟩
    rw [Fintype.mem_piFinset] at hf
    have hc : p.coeffs = f := by
      rw [← h_eq]
      rfl
    dsimp [normInf]
    apply Finset.sup_le
    intro k _
    rw [hc]
    exact (mem_boundedBall params M (f k)).mp (hf k)
  · intro h
    refine ⟨p.coeffs, ?_, rfl⟩
    rw [Fintype.mem_piFinset]
    intro k
    rw [mem_boundedBall]
    exact le_trans (Finset.le_sup (f := fun j => norm params (p.coeffs j)) (Finset.mem_univ k)) h

theorem card_polyBoundedBall (params : LWEParams) (N M : ℕ) (hM : 2 * M < params.q) :
    (polyBoundedBall params N M).card = (2 * M + 1) ^ N := by
  unfold polyBoundedBall
  rw [Finset.card_map, Fintype.card_piFinset]
  simp [card_boundedBall params M hM]

def zkpAcceptedMaskPairs (params : LWEParams) (N B beta : ℕ) [Fact (0 < N)]
    (c : NegacyclicPoly (Zq params) N)
    (wit : ZKPSecretWitness (NegacyclicPoly (Zq params) N)) :
    Finset (NegacyclicPoly (Zq params) N × NegacyclicPoly (Zq params) N) :=
  (polyBoundedBall params N B ×ˢ polyBoundedBall params N B).filter
    (fun y =>
      zkpVerifyBound (NegacyclicPoly (Zq params) N)
        (zkpRespond (NegacyclicPoly (Zq params) N) y.1 y.2 c wit) (B - beta) = true)

theorem existsUnique_zkpMaskPair_of_verifyBound
    (params : LWEParams) (N B beta B_w : ℕ) [Fact (0 < N)]
    (hbeta : beta ≤ B)
    (c : NegacyclicPoly (Zq params) N)
    (wit : ZKPSecretWitness (NegacyclicPoly (Zq params) N))
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : normInf params wit.s.coeffs ≤ B_w)
    (he : normInf params wit.e.coeffs ≤ B_w)
    (hbeta_w : N * B_w ≤ beta)
    {z_s z_e : NegacyclicPoly (Zq params) N}
    (hz : zkpVerifyBound (NegacyclicPoly (Zq params) N) ⟨z_s, z_e⟩ (B - beta) = true) :
    ∃! y ∈ zkpAcceptedMaskPairs params N B beta c wit,
      zkpRespond (NegacyclicPoly (Zq params) N) y.1 y.2 c wit = ⟨z_s, z_e⟩ := by
  dsimp [zkpVerifyBound] at hz
  rw [decide_eq_true_iff] at hz
  have hcs : normInf params (c * wit.s).coeffs ≤ beta := by
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N c wit.s hc
    have h2 : N * normInf params wit.s.coeffs ≤ N * B_w := Nat.mul_le_mul_left N hs
    omega
  have hce : normInf params (c * wit.e).coeffs ≤ beta := by
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N c wit.e hc
    have h2 : N * normInf params wit.e.coeffs ≤ N * B_w := Nat.mul_le_mul_left N he
    omega
  refine ⟨(z_s - c * wit.s, z_e - c * wit.e), ?_, ?_⟩
  · constructor
    · rw [zkpAcceptedMaskPairs, Finset.mem_filter, Finset.mem_product, mem_polyBoundedBall_iff,
        mem_polyBoundedBall_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hs_sub := norm_sub_le params z_s.coeffs (c * wit.s).coeffs
        have hz1 : normInf params z_s.coeffs ≤ B - beta := hz.1
        change normInf params (z_s.coeffs - (c * wit.s).coeffs) ≤ B
        omega
      · have he_sub := norm_sub_le params z_e.coeffs (c * wit.e).coeffs
        have hz2 : normInf params z_e.coeffs ≤ B - beta := hz.2
        change normInf params (z_e.coeffs - (c * wit.e).coeffs) ≤ B
        omega
      · dsimp [zkpVerifyBound, zkpRespond]
        rw [decide_eq_true_iff, sub_add_cancel, sub_add_cancel]
        exact hz
    · dsimp [zkpRespond]
      rw [sub_add_cancel, sub_add_cancel]
  · rintro ⟨y_s, y_e⟩ ⟨_, h_eq⟩
    have h1 : y_s + c * wit.s = z_s := congrArg ZKPResponse.z_s h_eq
    have h2 : y_e + c * wit.e = z_e := congrArg ZKPResponse.z_e h_eq
    exact Prod.ext (eq_sub_of_add_eq h1) (eq_sub_of_add_eq h2)

theorem card_zkpAcceptedMaskPairs_eq
    (params : LWEParams) (N B beta B_w : ℕ) [Fact (0 < N)]
    (hB : 2 * B < params.q) (hbeta : beta ≤ B)
    (c : NegacyclicPoly (Zq params) N)
    (wit : ZKPSecretWitness (NegacyclicPoly (Zq params) N))
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : normInf params wit.s.coeffs ≤ B_w)
    (he : normInf params wit.e.coeffs ≤ B_w)
    (hbeta_w : N * B_w ≤ beta) :
    (zkpAcceptedMaskPairs params N B beta c wit).card = (2 * (B - beta) + 1) ^ (2 * N) ∧
    0 < (zkpAcceptedMaskPairs params N B beta c wit).card := by
  have h_bij : (zkpAcceptedMaskPairs params N B beta c wit).card =
      (polyBoundedBall params N (B - beta) ×ˢ polyBoundedBall params N (B - beta)).card := by
    refine Finset.card_bij (fun y _ => (y.1 + c * wit.s, y.2 + c * wit.e)) ?_ ?_ ?_
    · intro y hy
      simp only [zkpAcceptedMaskPairs, Finset.mem_filter, zkpVerifyBound, zkpRespond,
        decide_eq_true_iff] at hy
      simp only [Finset.mem_product, mem_polyBoundedBall_iff]
      exact hy.2
    · intro y₁ _ y₂ _ h_eq
      have h1 : y₁.1 + c * wit.s = y₂.1 + c * wit.s := congrArg Prod.fst h_eq
      have h2 : y₁.2 + c * wit.e = y₂.2 + c * wit.e := congrArg Prod.snd h_eq
      exact Prod.ext (add_right_cancel h1) (add_right_cancel h2)
    · rintro ⟨z_s, z_e⟩ hz
      simp only [Finset.mem_product, mem_polyBoundedBall_iff] at hz
      have hz_bnd : zkpVerifyBound (NegacyclicPoly (Zq params) N) ⟨z_s, z_e⟩ (B - beta) = true := by
        dsimp [zkpVerifyBound]
        rw [decide_eq_true_iff]
        exact hz
      rcases existsUnique_zkpMaskPair_of_verifyBound params N B beta B_w hbeta c wit hc hs he
        hbeta_w hz_bnd with ⟨⟨y_s, y_e⟩, ⟨hy_mem, hy_eq⟩, _⟩
      refine ⟨(y_s, y_e), hy_mem, ?_⟩
      exact Prod.ext (congrArg ZKPResponse.z_s hy_eq) (congrArg ZKPResponse.z_e hy_eq)
  have h_card : (zkpAcceptedMaskPairs params N B beta c wit).card =
      (2 * (B - beta) + 1) ^ (2 * N) := by
    rw [h_bij, Finset.card_product, card_polyBoundedBall params N (B - beta) (by omega),
      ← pow_add, ← two_mul N]
  refine ⟨h_card, ?_⟩
  rw [h_card]
  exact Nat.pow_pos (by omega)

end ZKP

section ModuleZKP

variable (R : Type*) [CommRing R]
variable (n m : ℕ)

open scoped BigOperators

structure ModZKPPublicInfo where
  A : MatrixR R n m
  t : VectorR R m

structure ModZKPSecretWitness where
  s : VectorR R n
  e : VectorR R m

def mkModZKPPublicInfo (A : MatrixR R n m) (wit : ModZKPSecretWitness R n m) :
    ModZKPPublicInfo R n m :=
  { A := A, t := evaluate R n m A wit.s wit.e }

def modZkpCommit (A : MatrixR R n m) (y_s : VectorR R n) (y_e : VectorR R m) : VectorR R m :=
  evaluate R n m A y_s y_e

structure ModZKPResponse where
  z_s : VectorR R n
  z_e : VectorR R m

def modZkpRespond (y_s : VectorR R n) (y_e : VectorR R m) (c : R)
    (wit : ModZKPSecretWitness R n m) : ModZKPResponse R n m :=
  { z_s := fun i => y_s i + c * wit.s i,
    z_e := fun i => y_e i + c * wit.e i }

def modZkpVerifyAlgebraic (pub : ModZKPPublicInfo R n m) (c : R) (w : VectorR R m)
    (resp : ModZKPResponse R n m) : Prop :=
  (fun i => (∑ j, pub.A i j * resp.z_s j) + resp.z_e i - c * pub.t i) = w

theorem mod_zkp_completeness (A : MatrixR R n m) (y_s : VectorR R n) (y_e : VectorR R m) (c : R)
    (wit : ModZKPSecretWitness R n m) :
    let pub := mkModZKPPublicInfo R n m A wit
    let w := modZkpCommit R n m A y_s y_e
    let resp := modZkpRespond R n m y_s y_e c wit
    modZkpVerifyAlgebraic R n m pub c w resp := by
  dsimp [mkModZKPPublicInfo, modZkpCommit, modZkpRespond, modZkpVerifyAlgebraic]
  ext i
  simp only [evaluate, mul_add, Finset.sum_add_distrib, sub_eq_add_neg]
  have h_inner : ∀ x, A i x * (c * wit.s x) = c * (A i x * wit.s x) := by intro x; ring
  simp_rw [h_inner, ← Finset.mul_sum]
  ring

theorem mod_zkp_special_soundness (pub : ModZKPPublicInfo R n m) (c1 c2 : R) (w : VectorR R m)
    (resp1 resp2 : ModZKPResponse R n m)
    (h1 : modZkpVerifyAlgebraic R n m pub c1 w resp1)
    (h2 : modZkpVerifyAlgebraic R n m pub c2 w resp2) :
    evaluate R n m pub.A (resp1.z_s - resp2.z_s) (resp1.z_e - resp2.z_e) =
      fun i => (c1 - c2) * pub.t i := by
  ext i
  have h1_i := congrFun h1 i
  have h2_i := congrFun h2 i
  dsimp [evaluate]
  simp only [mul_sub, Finset.sum_sub_distrib]
  calc
    (∑ x, pub.A i x * resp1.z_s x - ∑ x, pub.A i x * resp2.z_s x) + (resp1.z_e i - resp2.z_e i)
      = ((∑ x, pub.A i x * resp1.z_s x) + resp1.z_e i - c1 * pub.t i) -
        ((∑ x, pub.A i x * resp2.z_s x) + resp2.z_e i - c2 * pub.t i) +
        (c1 - c2) * pub.t i := by ring
    _ = w i - w i + (c1 - c2) * pub.t i := by rw [h1_i, h2_i]
    _ = (c1 - c2) * pub.t i := by ring

variable [HasInfinityNorm R]

def modZkpVerifyBound (resp : ModZKPResponse R n m) (bound : ℕ) : Prop :=
  (∀ j : Fin n, HasInfinityNorm.normInf (resp.z_s j) ≤ bound) ∧
  (∀ i : Fin m, HasInfinityNorm.normInf (resp.z_e i) ≤ bound)

theorem mod_zkp_respond_passes_verify_of_mask_bound
    (y_s : VectorR R n) (y_e : VectorR R m) (c : R)
    (wit : ModZKPSecretWitness R n m) (safe_bound beta : ℕ)
    (hys : ∀ j : Fin n, HasInfinityNorm.normInf (y_s j) + beta ≤ safe_bound)
    (hye : ∀ i : Fin m, HasInfinityNorm.normInf (y_e i) + beta ≤ safe_bound)
    (hcs : ∀ j : Fin n, HasInfinityNorm.normInf (c * wit.s j) ≤ beta)
    (hce : ∀ i : Fin m, HasInfinityNorm.normInf (c * wit.e i) ≤ beta) :
    modZkpVerifyBound R n m (modZkpRespond R n m y_s y_e c wit) safe_bound := by
  constructor
  · intro j
    change HasInfinityNorm.normInf (y_s j + c * wit.s j) ≤ safe_bound
    have h_tri := HasInfinityNorm.normInf_add_le (y_s j) (c * wit.s j)
    have h1 := hys j
    have h2 := hcs j
    omega
  · intro i
    change HasInfinityNorm.normInf (y_e i + c * wit.e i) ≤ safe_bound
    have h_tri := HasInfinityNorm.normInf_add_le (y_e i) (c * wit.e i)
    have h1 := hye i
    have h2 := hce i
    omega

theorem mod_zkp_extracted_norm_bound
    (resp1 resp2 : ModZKPResponse R n m) (safe_bound : ℕ)
    (hb1 : modZkpVerifyBound R n m resp1 safe_bound)
    (hb2 : modZkpVerifyBound R n m resp2 safe_bound) :
    (∀ j : Fin n, HasInfinityNorm.normInf ((resp1.z_s - resp2.z_s) j) ≤ 2 * safe_bound) ∧
    (∀ i : Fin m, HasInfinityNorm.normInf ((resp1.z_e - resp2.z_e) i) ≤ 2 * safe_bound) := by
  rcases hb1 with ⟨hs1, he1⟩
  rcases hb2 with ⟨hs2, he2⟩
  constructor
  · intro j
    simp only [Pi.sub_apply]
    have h_sub := normInf_sub_le R (resp1.z_s j) (resp2.z_s j)
    have h1 := hs1 j
    have h2 := hs2 j
    omega
  · intro i
    simp only [Pi.sub_apply]
    have h_sub := normInf_sub_le R (resp1.z_e i) (resp2.z_e i)
    have h1 := he1 i
    have h2 := he2 i
    omega

theorem concrete_mod_zkp_respond_passes_verify
    (params : LWEParams) (N safe_bound beta B_w : ℕ) [Fact (0 < N)]
    (y_s : VectorR (NegacyclicPoly (Zq params) N) n)
    (y_e : VectorR (NegacyclicPoly (Zq params) N) m)
    (c : NegacyclicPoly (Zq params) N)
    (wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) n m)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : ∀ j : Fin n, normInf params (wit.s j).coeffs ≤ B_w)
    (he : ∀ i : Fin m, normInf params (wit.e i).coeffs ≤ B_w)
    (hbeta : N * B_w ≤ beta)
    (hys : ∀ j : Fin n, normInf params (y_s j).coeffs + beta ≤ safe_bound)
    (hye : ∀ i : Fin m, normInf params (y_e i).coeffs + beta ≤ safe_bound) :
    modZkpVerifyBound (NegacyclicPoly (Zq params) N) n m
      (modZkpRespond (NegacyclicPoly (Zq params) N) n m y_s y_e c wit) safe_bound := by
  apply mod_zkp_respond_passes_verify_of_mask_bound (NegacyclicPoly (Zq params) N) n m
    y_s y_e c wit safe_bound beta hys hye
  · intro j
    have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c (wit.s j) hc
    have h_le : N * normInf params (wit.s j).coeffs ≤ N * B_w := Nat.mul_le_mul_left N (hs j)
    change normInf params (c * wit.s j).coeffs ≤ beta
    omega
  · intro i
    have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c (wit.e i) hc
    have h_le : N * normInf params (wit.e i).coeffs ≤ N * B_w := Nat.mul_le_mul_left N (he i)
    change normInf params (c * wit.e i).coeffs ≤ beta
    omega

theorem mod_zkp_special_soundness_nonvacuous
    (params : LWEParams) (N safe_bound : ℕ) [Fact (0 < N)]
    (h_bound : 4 * safe_bound + 1 < params.q)
    (pub : ModZKPPublicInfo (NegacyclicPoly (Zq params) N) n m)
    (c1 c2 : NegacyclicPoly (Zq params) N)
    (w : VectorR (NegacyclicPoly (Zq params) N) m)
    (resp1 resp2 : ModZKPResponse (NegacyclicPoly (Zq params) N) n m)
    (hc_ne : c1 ≠ c2)
    (ha1 : modZkpVerifyAlgebraic (NegacyclicPoly (Zq params) N) n m pub c1 w resp1)
    (ha2 : modZkpVerifyAlgebraic (NegacyclicPoly (Zq params) N) n m pub c2 w resp2)
    (hb1 : modZkpVerifyBound (NegacyclicPoly (Zq params) N) n m resp1 safe_bound)
    (hb2 : modZkpVerifyBound (NegacyclicPoly (Zq params) N) n m resp2 safe_bound) :
    c1 - c2 ≠ 0 ∧
    evaluate (NegacyclicPoly (Zq params) N) n m pub.A (resp1.z_s - resp2.z_s)
      (resp1.z_e - resp2.z_e) = (fun i => (c1 - c2) * pub.t i) ∧
    (∀ j : Fin n, normInf params ((resp1.z_s - resp2.z_s) j).coeffs ≤ 2 * safe_bound) ∧
    (∀ i : Fin m, normInf params ((resp1.z_e - resp2.z_e) i).coeffs ≤ 2 * safe_bound) ∧
    2 * safe_bound < params.q / 2 := by
  have h_alg := mod_zkp_special_soundness (NegacyclicPoly (Zq params) N) n m pub c1 c2 w
    resp1 resp2 ha1 ha2
  have h_bnd := mod_zkp_extracted_norm_bound (NegacyclicPoly (Zq params) N) n m resp1 resp2
    safe_bound hb1 hb2
  exact ⟨sub_ne_zero.mpr hc_ne, h_alg, h_bnd.1, h_bnd.2, by omega⟩

def modZkpMaskBall (params : LWEParams) (n m N M : ℕ) :
    Finset
      (VectorR (NegacyclicPoly (Zq params) N) n ×
        VectorR (NegacyclicPoly (Zq params) N) m) :=
  Fintype.piFinset (fun _ : Fin n => polyBoundedBall params N M) ×ˢ
    Fintype.piFinset (fun _ : Fin m => polyBoundedBall params N M)

@[simp] lemma mem_modZkpMaskBall_iff (params : LWEParams) (n m N M : ℕ)
    (y : VectorR (NegacyclicPoly (Zq params) N) n ×
      VectorR (NegacyclicPoly (Zq params) N) m) :
    y ∈ modZkpMaskBall params n m N M ↔
      (∀ j : Fin n, normInf params (y.1 j).coeffs ≤ M) ∧
      (∀ i : Fin m, normInf params (y.2 i).coeffs ≤ M) := by
  simp [modZkpMaskBall]

theorem card_modZkpMaskBall (params : LWEParams) (n m N M : ℕ) (hM : 2 * M < params.q) :
    (modZkpMaskBall params n m N M).card = (2 * M + 1) ^ ((n + m) * N) := by
  unfold modZkpMaskBall
  rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [card_polyBoundedBall params N M hM, ← pow_mul, ← pow_mul, ← pow_add, add_mul,
    mul_comm N n, mul_comm N m]

instance instDecidableModZkpVerifyBound (resp : ModZKPResponse R n m) (bound : ℕ) :
    Decidable (modZkpVerifyBound R n m resp bound) := by
  unfold modZkpVerifyBound
  exact inferInstance

def modZkpAcceptedMasks (params : LWEParams) (N B beta : ℕ) [Fact (0 < N)]
    (c : NegacyclicPoly (Zq params) N)
    (wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) n m) :
    Finset
      (VectorR (NegacyclicPoly (Zq params) N) n ×
        VectorR (NegacyclicPoly (Zq params) N) m) :=
  (modZkpMaskBall params n m N B).filter
    (fun y =>
      modZkpVerifyBound (NegacyclicPoly (Zq params) N) n m
        (modZkpRespond (NegacyclicPoly (Zq params) N) n m y.1 y.2 c wit) (B - beta))

theorem existsUnique_modZkpMask_of_verifyBound
    (params : LWEParams) (N B beta B_w : ℕ) [Fact (0 < N)]
    (hbeta : beta ≤ B)
    (c : NegacyclicPoly (Zq params) N)
    (wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) n m)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : ∀ j : Fin n, normInf params (wit.s j).coeffs ≤ B_w)
    (he : ∀ i : Fin m, normInf params (wit.e i).coeffs ≤ B_w)
    (hbeta_w : N * B_w ≤ beta)
    {z_s : VectorR (NegacyclicPoly (Zq params) N) n}
    {z_e : VectorR (NegacyclicPoly (Zq params) N) m}
    (hz : modZkpVerifyBound (NegacyclicPoly (Zq params) N) n m ⟨z_s, z_e⟩ (B - beta)) :
    ∃! y ∈ modZkpAcceptedMasks n m params N B beta c wit,
      modZkpRespond (NegacyclicPoly (Zq params) N) n m y.1 y.2 c wit = ⟨z_s, z_e⟩ := by
  have hcs : ∀ j : Fin n, normInf params (c * wit.s j).coeffs ≤ beta := by
    intro j
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N c (wit.s j) hc
    have h2 : N * normInf params (wit.s j).coeffs ≤ N * B_w := Nat.mul_le_mul_left N (hs j)
    omega
  have hce : ∀ i : Fin m, normInf params (c * wit.e i).coeffs ≤ beta := by
    intro i
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N c (wit.e i) hc
    have h2 : N * normInf params (wit.e i).coeffs ≤ N * B_w := Nat.mul_le_mul_left N (he i)
    omega
  refine ⟨(fun j => z_s j - c * wit.s j, fun i => z_e i - c * wit.e i), ?_, ?_⟩
  · constructor
    · rw [modZkpAcceptedMasks, Finset.mem_filter, mem_modZkpMaskBall_iff]
      refine ⟨⟨fun j => ?_, fun i => ?_⟩, ?_⟩
      · have hs_sub := norm_sub_le params (z_s j).coeffs (c * wit.s j).coeffs
        have hj : normInf params (z_s j).coeffs ≤ B - beta := hz.1 j
        have hcj := hcs j
        change normInf params ((z_s j).coeffs - (c * wit.s j).coeffs) ≤ B
        omega
      · have he_sub := norm_sub_le params (z_e i).coeffs (c * wit.e i).coeffs
        have hi : normInf params (z_e i).coeffs ≤ B - beta := hz.2 i
        have hci := hce i
        change normInf params ((z_e i).coeffs - (c * wit.e i).coeffs) ≤ B
        omega
      · dsimp [modZkpVerifyBound, modZkpRespond]
        refine ⟨fun j => ?_, fun i => ?_⟩
        · rw [sub_add_cancel]
          exact hz.1 j
        · rw [sub_add_cancel]
          exact hz.2 i
    · dsimp [modZkpRespond]
      refine congrArg₂ ModZKPResponse.mk ?_ ?_
      · funext j
        exact sub_add_cancel (z_s j) (c * wit.s j)
      · funext i
        exact sub_add_cancel (z_e i) (c * wit.e i)
  · rintro ⟨y_s, y_e⟩ ⟨_, h_eq⟩
    have h1 : (fun j => y_s j + c * wit.s j) = z_s := congrArg ModZKPResponse.z_s h_eq
    have h2 : (fun i => y_e i + c * wit.e i) = z_e := congrArg ModZKPResponse.z_e h_eq
    refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
    · exact eq_sub_of_add_eq (congrFun h1 j)
    · exact eq_sub_of_add_eq (congrFun h2 i)

theorem card_modZkpAcceptedMasks_eq
    (params : LWEParams) (N B beta B_w : ℕ) [Fact (0 < N)]
    (hB : 2 * B < params.q) (hbeta : beta ≤ B)
    (c : NegacyclicPoly (Zq params) N)
    (wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) n m)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : ∀ j : Fin n, normInf params (wit.s j).coeffs ≤ B_w)
    (he : ∀ i : Fin m, normInf params (wit.e i).coeffs ≤ B_w)
    (hbeta_w : N * B_w ≤ beta) :
    (modZkpAcceptedMasks n m params N B beta c wit).card = (2 * (B - beta) + 1) ^ ((n + m) * N) ∧
    0 < (modZkpAcceptedMasks n m params N B beta c wit).card := by
  have h_bij : (modZkpAcceptedMasks n m params N B beta c wit).card =
      (modZkpMaskBall params n m N (B - beta)).card := by
    refine Finset.card_bij
        (fun y _ => (fun j => y.1 j + c * wit.s j, fun i => y.2 i + c * wit.e i)) ?_ ?_ ?_
    · intro y hy
      rw [modZkpAcceptedMasks, Finset.mem_filter] at hy
      dsimp [modZkpVerifyBound, modZkpRespond] at hy
      rw [mem_modZkpMaskBall_iff]
      exact hy.2
    · intro y₁ _ y₂ _ h_eq
      have h1 := congrArg Prod.fst h_eq
      have h2 := congrArg Prod.snd h_eq
      refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
      · exact add_right_cancel (congrFun h1 j)
      · exact add_right_cancel (congrFun h2 i)
    · rintro ⟨z_s, z_e⟩ hz
      rw [mem_modZkpMaskBall_iff] at hz
      rcases existsUnique_modZkpMask_of_verifyBound n m params N B beta B_w hbeta c wit hc hs he
        hbeta_w hz with ⟨⟨y_s, y_e⟩, ⟨hy_mem, hy_eq⟩, _⟩
      refine ⟨(y_s, y_e), hy_mem, ?_⟩
      exact Prod.ext (congrArg ModZKPResponse.z_s hy_eq) (congrArg ModZKPResponse.z_e hy_eq)
  have h_card : (modZkpAcceptedMasks n m params N B beta c wit).card =
      (2 * (B - beta) + 1) ^ ((n + m) * N) := by
    rw [h_bij, card_modZkpMaskBall params n m N (B - beta) (by omega)]
  refine ⟨h_card, ?_⟩
  rw [h_card]
  exact Nat.pow_pos (by omega)

end ModuleZKP

section ModuleNTT

variable (PolyR : Type*) [CommRing PolyR]
variable (ScalarR : Type*) [CommRing ScalarR]
variable (N : ℕ)
variable (ntt : NTTHom PolyR N ScalarR)
variable {n m : ℕ}

def vectorNTT (v : VectorR PolyR n) : VectorR (Fin N → ScalarR) n :=
  fun i => ntt.toFun (v i)

def matrixNTT (A : MatrixR PolyR n m) : MatrixR (Fin N → ScalarR) n m :=
  fun i j => ntt.toFun (A i j)

theorem module_ntt_correct (A : MatrixR PolyR n m) (s : VectorR PolyR n) (e : VectorR PolyR m) :
    vectorNTT PolyR ScalarR N ntt (evaluate PolyR n m A s e) =
    evaluate (Fin N → ScalarR) n m (matrixNTT PolyR ScalarR N ntt A)
                                   (vectorNTT PolyR ScalarR N ntt s)
                                   (vectorNTT PolyR ScalarR N ntt e) := by
  ext i k
  dsimp [vectorNTT, matrixNTT, evaluate]
  have h_add := congrFun (ntt.map_add (∑ j, A i j * s j) (e i)) k
  have h_sum := congrFun (ntt.map_sum Finset.univ (fun j => A i j * s j)) k
  rw [h_add, Pi.add_apply, h_sum, Finset.sum_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.mul_apply]
  exact congrFun (ntt.map_mul (A i j) (s j)) k

def vectorInvNTT {R : Type*} [CommRing R] {N m : ℕ}
    (ψ_inv n_inv : R) (v : VectorR (Fin N → R) m) : VectorR (NegacyclicPoly R N) m :=
  fun i => concreteInvNTT ψ_inv n_inv (v i)

theorem concrete_module_ntt_eval_eq {R : Type*} [CommRing R] {N n m : ℕ} [Fact (0 < N)]
    (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1) (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (A : MatrixR (NegacyclicPoly R N) n m)
    (s : VectorR (NegacyclicPoly R N) n)
    (e : VectorR (NegacyclicPoly R N) m) :
    let ntt := concreteNTTHom ψ hpsi
    vectorInvNTT ψ_inv n_inv
      (evaluate (Fin N → R) n m
        (matrixNTT (NegacyclicPoly R N) R N ntt A)
        (vectorNTT (NegacyclicPoly R N) R N ntt s)
        (vectorNTT (NegacyclicPoly R N) R N ntt e)) =
    evaluate (NegacyclicPoly R N) n m A s e := by
  intro ntt
  rw [← module_ntt_correct (NegacyclicPoly R N) R N ntt A s e]
  ext i k
  dsimp [vectorInvNTT, vectorNTT, concreteNTTHom]
  exact congrFun (congrArg NegacyclicPoly.coeffs
    (concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth (evaluate (NegacyclicPoly R N) n m A s e i))) k

end ModuleNTT

section BFVFHE

open scoped BigOperators

section AlgebraicBFV

variable (R : Type*) [CommRing R]

structure BFVPublicKey where
  a : R
  b : R

structure BFVCiphertext where
  c0 : R
  c1 : R

def bfvKeygen (a s e : R) : BFVPublicKey R :=
  { a := a, b := -(a * s + e) }

def bfvEncrypt (pk : BFVPublicKey R) (u e0 e1 delta_m : R) : BFVCiphertext R :=
  { c0 := pk.b * u + e0 + delta_m,
    c1 := pk.a * u + e1 }

def bfvPhase (ct : BFVCiphertext R) (s : R) : R :=
  ct.c0 + ct.c1 * s

theorem bfvEncrypt_phase (a s e u e0 e1 delta_m : R) :
    bfvPhase R (bfvEncrypt R (bfvKeygen R a s e) u e0 e1 delta_m) s =
      delta_m + (e0 + e1 * s - e * u) := by
  dsimp [bfvPhase, bfvEncrypt, bfvKeygen]
  ring

def bfvAdd (ct1 ct2 : BFVCiphertext R) : BFVCiphertext R :=
  { c0 := ct1.c0 + ct2.c0,
    c1 := ct1.c1 + ct2.c1 }

theorem bfvAdd_phase (ct1 ct2 : BFVCiphertext R) (s : R) :
    bfvPhase R (bfvAdd R ct1 ct2) s = bfvPhase R ct1 s + bfvPhase R ct2 s := by
  dsimp [bfvPhase, bfvAdd]
  ring

def bfvSub (ct1 ct2 : BFVCiphertext R) : BFVCiphertext R :=
  { c0 := ct1.c0 - ct2.c0,
    c1 := ct1.c1 - ct2.c1 }

theorem bfvSub_phase (ct1 ct2 : BFVCiphertext R) (s : R) :
    bfvPhase R (bfvSub R ct1 ct2) s = bfvPhase R ct1 s - bfvPhase R ct2 s := by
  dsimp [bfvPhase, bfvSub]
  ring

def bfvAddPlain (ct : BFVCiphertext R) (delta_m : R) : BFVCiphertext R :=
  { c0 := ct.c0 + delta_m,
    c1 := ct.c1 }

theorem bfvAddPlain_phase (ct : BFVCiphertext R) (delta_m s : R) :
    bfvPhase R (bfvAddPlain R ct delta_m) s = bfvPhase R ct s + delta_m := by
  dsimp [bfvPhase, bfvAddPlain]
  ring

def bfvSubPlain (ct : BFVCiphertext R) (delta_m : R) : BFVCiphertext R :=
  { c0 := ct.c0 - delta_m,
    c1 := ct.c1 }

theorem bfvSubPlain_phase (ct : BFVCiphertext R) (delta_m s : R) :
    bfvPhase R (bfvSubPlain R ct delta_m) s = bfvPhase R ct s - delta_m := by
  dsimp [bfvPhase, bfvSubPlain]
  ring

def bfvMulPlain (ct : BFVCiphertext R) (pt : R) : BFVCiphertext R :=
  { c0 := ct.c0 * pt,
    c1 := ct.c1 * pt }

theorem bfvMulPlain_phase (ct : BFVCiphertext R) (pt s : R) :
    bfvPhase R (bfvMulPlain R ct pt) s = bfvPhase R ct s * pt := by
  dsimp [bfvPhase, bfvMulPlain]
  ring

def mkBFVGadgetRelinKey {l : ℕ} (a_rk e_rk : VectorR R l) (s : R) (G : VectorR R l) :
    GadgetRelinKey R l :=
  { a_rk := a_rk,
    b_rk := fun i => -(a_rk i * s + e_rk i) + G i * (s * s) }

def bfvGadgetRelinearize {l : ℕ} (d0 d1 d2 : R) (decomp : R → VectorR R l)
    (rk : GadgetRelinKey R l) : BFVCiphertext R :=
  let d2_dec := decomp d2
  { c0 := d0 + (∑ i, d2_dec i * rk.b_rk i),
    c1 := d1 + (∑ i, d2_dec i * rk.a_rk i) }

theorem bfvGadgetRelinearize_phase {l : ℕ} (s d0 d1 d2 : R)
    (a_rk e_rk G : VectorR R l) (decomp : R → VectorR R l)
    (h_dec : IsValidDecomposition G decomp) :
    let rk := mkBFVGadgetRelinKey R a_rk e_rk s G
    let ct_relin := bfvGadgetRelinearize R d0 d1 d2 decomp rk
    bfvPhase R ct_relin s =
      (d0 + d1 * s + d2 * (s * s)) - (∑ i, decomp d2 i * e_rk i) := by
  dsimp [mkBFVGadgetRelinKey, bfvGadgetRelinearize, bfvPhase]
  simp only [sub_eq_add_neg, neg_add, mul_add, add_mul, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have h1 : (∑ i : Fin l, decomp d2 i * (a_rk i * s)) =
      (∑ i : Fin l, decomp d2 i * a_rk i) * s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  have h2 : (∑ i : Fin l, decomp d2 i * (G i * (s * s))) =
      (∑ i : Fin l, decomp d2 i * G i) * (s * s) := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  rw [h1, h2, h_dec d2]
  ring

end AlgebraicBFV

section ConcreteBFVDecryption

variable (params : LWEParams)

def bfvEncodeElem (Δ m : ℕ) : Zq params :=
  ((Δ * m : ℕ) : Zq params)

def bfvDecodeElem (Δ : ℕ) (y : Zq params) : ℕ :=
  ZMod.val (y + ((Δ / 2 : ℕ) : Zq params)) / Δ

lemma decode_of_natCast_eq (Δ t m r : ℕ) (y : Zq params)
    (ht_le : Δ * t ≤ params.q) (hm : m < t) (hr : r < Δ)
    (hy : y + ((Δ / 2 : ℕ) : Zq params) = ((Δ * m + r : ℕ) : Zq params)) :
    bfvDecodeElem params Δ y = m := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have hΔ_pos : 0 < Δ := by omega
  have h_mul_le : Δ * (m + 1) ≤ Δ * t := Nat.mul_le_mul_left Δ hm
  have h_mul_succ : Δ * (m + 1) = Δ * m + Δ := Nat.mul_succ Δ m
  have h_lt_q : Δ * m + r < params.q := by omega
  unfold bfvDecodeElem
  rw [hy, ZMod.val_natCast_of_lt h_lt_q]
  have h_comm : Δ * m + r = r + Δ * m := Nat.add_comm _ _
  rw [h_comm, Nat.add_mul_div_left r m hΔ_pos, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem bfvDecodeElem_correct (Δ t m : ℕ) (e : Zq params)
    (ht_le : Δ * t ≤ params.q) (hm : m < t) (he : 2 * norm params e < Δ) :
    bfvDecodeElem params Δ (bfvEncodeElem params Δ m + e) = m := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have he_lt_q : ZMod.val e < params.q := ZMod.val_lt e
  have h_norm : norm params e =
      if (ZMod.val e : ℤ) ≤ (params.q : ℤ) / 2 then ZMod.val e else params.q - ZMod.val e := by
    unfold norm centeredLift
    dsimp
    split_ifs <;> omega
  by_cases h_half : (ZMod.val e : ℤ) ≤ (params.q : ℤ) / 2
  · rw [if_pos h_half] at h_norm
    let r : ℕ := ZMod.val e + Δ / 2
    have hr : r < Δ := by omega
    apply decode_of_natCast_eq params Δ t m r (bfvEncodeElem params Δ m + e) ht_le hm hr
    dsimp [bfvEncodeElem, r]
    push_cast
    rw [ZMod.natCast_zmod_val e]
    ring
  · rw [if_neg h_half] at h_norm
    let r : ℕ := Δ / 2 - (params.q - ZMod.val e)
    have hr : r < Δ := by omega
    have hr_add_q : r + params.q = ZMod.val e + Δ / 2 := by omega
    apply decode_of_natCast_eq params Δ t m r (bfvEncodeElem params Δ m + e) ht_le hm hr
    dsimp [bfvEncodeElem]
    have h_mod_q : ((Δ * m + r : ℕ) : Zq params) =
        (((Δ * m + (r + params.q) : ℕ) : Zq params)) := by
      push_cast
      rw [ZMod.natCast_self, add_zero]
    rw [h_mod_q, hr_add_q]
    push_cast
    rw [ZMod.natCast_zmod_val e]
    ring

def bfvEncodePoly (N Δ : ℕ) (m : Fin N → ℕ) : NegacyclicPoly (Zq params) N :=
  ⟨fun k => bfvEncodeElem params Δ (m k)⟩

def bfvDecodePoly (N Δ : ℕ) (p : NegacyclicPoly (Zq params) N) : Fin N → ℕ :=
  fun k => bfvDecodeElem params Δ (p.coeffs k)

def bfvDecryptPoly (N Δ : ℕ) [Fact (0 < N)]
    (s : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N)) : Fin N → ℕ :=
  bfvDecodePoly params N Δ (bfvPhase (NegacyclicPoly (Zq params) N) ct s)

theorem bfvDecryptPoly_of_phase_eq (N Δ t : ℕ) [Fact (0 < N)]
    (s E : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (h_noise : 2 * normInf params E.coeffs < Δ) :
    bfvDecryptPoly params N Δ s ct = m := by
  ext k
  unfold bfvDecryptPoly bfvDecodePoly
  rw [h_phase, NegacyclicPoly.add_coeffs]
  dsimp [bfvEncodePoly]
  have hk_le : norm params (E.coeffs k) ≤ normInf params E.coeffs :=
    Finset.le_sup (f := fun j => norm params (E.coeffs j)) (Finset.mem_univ k)
  have hk_noise : 2 * norm params (E.coeffs k) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (m k) (E.coeffs k) ht_le (hm k) hk_noise

theorem bfvDecryptPoly_encrypt_correct (N Δ t : ℕ) [Fact (0 < N)]
    (a s e u e0 e1 : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m k < t)
    (h_noise : 2 * normInf params (e0 + e1 * s - e * u).coeffs < Δ) :
    let pk := bfvKeygen (NegacyclicPoly (Zq params) N) a s e
    let ct := bfvEncrypt (NegacyclicPoly (Zq params) N) pk u e0 e1 (bfvEncodePoly params N Δ m)
    bfvDecryptPoly params N Δ s ct = m := by
  intro pk ct
  apply bfvDecryptPoly_of_phase_eq params N Δ t s (e0 + e1 * s - e * u) ct m ht_le hm
  · exact bfvEncrypt_phase (NegacyclicPoly (Zq params) N) a s e u e0 e1 (bfvEncodePoly params N Δ m)
  · exact h_noise

theorem bfvDecryptPoly_add_correct (N Δ t : ℕ) [Fact (0 < N)]
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m1 k + m2 k < t)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2)
    (h_noise : 2 * (normInf params E1.coeffs + normInf params E2.coeffs) < Δ) :
    bfvDecryptPoly params N Δ s (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) =
      fun k => m1 k + m2 k := by
  have h_encode_add :
      bfvEncodePoly params N Δ m1 + bfvEncodePoly params N Δ m2 =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) := by
    ext k
    simp only [NegacyclicPoly.add_coeffs, bfvEncodePoly, bfvEncodeElem, Nat.mul_add, Nat.cast_add]
  have h_phase_sum :
      bfvPhase (NegacyclicPoly (Zq params) N) (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) s =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) + (E1 + E2) := by
    rw [bfvAdd_phase, h_phase1, h_phase2, ← h_encode_add]
    ring
  have h_tri := norm_add_le params E1.coeffs E2.coeffs
  have h_noise_sum : 2 * normInf params (E1 + E2).coeffs < Δ := by
    change 2 * normInf params (E1.coeffs + E2.coeffs) < Δ
    omega
  exact bfvDecryptPoly_of_phase_eq params N Δ t s (E1 + E2)
    (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) (fun k => m1 k + m2 k)
    ht_le hm h_phase_sum h_noise_sum

theorem concrete_bfvGadgetRelinearize_phase {N B l : ℕ} [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (s d0 d1 d2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    let ct_relin := bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
      (NegacyclicPoly.negacyclicDecomp params N B l) rk
    bfvPhase (NegacyclicPoly (Zq params) N) ct_relin s =
      (d0 + d1 * s + d2 * (s * s)) -
        (∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i) :=
  bfvGadgetRelinearize_phase (NegacyclicPoly (Zq params) N) s d0 d1 d2 a_rk e_rk
    (NegacyclicPoly.negacyclicGadget params N B l)
    (NegacyclicPoly.negacyclicDecomp params N B l)
    (NegacyclicPoly.negacyclicDecomp_isValid params N B l hq)

theorem bfvDecryptPoly_mul_correct (N Δ t B l : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (s d0 d1 d2 E_scale : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m_prod : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m_prod k < t)
    (h_scale_phase : d0 + d1 * s + d2 * (s * s) = bfvEncodePoly params N Δ m_prod + E_scale)
    (h_noise : 2 * normInf params
      (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i).coeffs < Δ) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    let ct_mul := bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
      (NegacyclicPoly.negacyclicDecomp params N B l) rk
    bfvDecryptPoly params N Δ s ct_mul = m_prod := by
  intro rk ct_mul
  have h_relin := concrete_bfvGadgetRelinearize_phase params hq s d0 d1 d2 a_rk e_rk
  dsimp only at h_relin
  have h_phase :
      bfvPhase (NegacyclicPoly (Zq params) N) ct_mul s =
        bfvEncodePoly params N Δ m_prod +
          (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i) := by
    change bfvPhase (NegacyclicPoly (Zq params) N)
      (bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
        (NegacyclicPoly.negacyclicDecomp params N B l) rk) s = _
    rw [h_relin, h_scale_phase]
    ring
  exact bfvDecryptPoly_of_phase_eq params N Δ t s
    (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i)
    ct_mul m_prod ht_le hm h_phase h_noise

theorem bfvDecryptPoly_addPlain_correct (N Δ t : ℕ) [Fact (0 < N)]
    (s E : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m1 k + m2 k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m1 + E)
    (h_noise : 2 * normInf params E.coeffs < Δ) :
    bfvDecryptPoly params N Δ s
      (bfvAddPlain (NegacyclicPoly (Zq params) N) ct (bfvEncodePoly params N Δ m2)) =
      fun k => m1 k + m2 k := by
  have h_encode_add :
      bfvEncodePoly params N Δ m1 + bfvEncodePoly params N Δ m2 =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) := by
    ext k
    simp only [NegacyclicPoly.add_coeffs, bfvEncodePoly, bfvEncodeElem, Nat.mul_add, Nat.cast_add]
  have h_phase_add :
      bfvPhase (NegacyclicPoly (Zq params) N)
        (bfvAddPlain (NegacyclicPoly (Zq params) N) ct (bfvEncodePoly params N Δ m2)) s =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) + E := by
    rw [bfvAddPlain_phase, h_phase, ← h_encode_add]
    ring
  exact bfvDecryptPoly_of_phase_eq params N Δ t s E
    (bfvAddPlain (NegacyclicPoly (Zq params) N) ct (bfvEncodePoly params N Δ m2))
    (fun k => m1 k + m2 k) ht_le hm h_phase_add h_noise

theorem bfvDecryptPoly_mulPlain_correct (N Δ t : ℕ) [Fact (0 < N)]
    (s E pt : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m_prod : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m_prod k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m1 + E)
    (h_encode_mul : bfvEncodePoly params N Δ m1 * pt = bfvEncodePoly params N Δ m_prod)
    (h_noise : 2 * normInf params (E * pt).coeffs < Δ) :
    bfvDecryptPoly params N Δ s (bfvMulPlain (NegacyclicPoly (Zq params) N) ct pt) = m_prod := by
  have h_phase_mul :
      bfvPhase (NegacyclicPoly (Zq params) N)
        (bfvMulPlain (NegacyclicPoly (Zq params) N) ct pt) s =
        bfvEncodePoly params N Δ m_prod + E * pt := by
    rw [bfvMulPlain_phase, h_phase, add_mul, h_encode_mul]
  exact bfvDecryptPoly_of_phase_eq params N Δ t s (E * pt)
    (bfvMulPlain (NegacyclicPoly (Zq params) N) ct pt) m_prod ht_le hm h_phase_mul h_noise

def bfvPhaseNTT {R : Type*} [CommRing R] {N : ℕ}
    (ψ ψ_inv n_inv : R) (ct : BFVCiphertext (NegacyclicPoly R N)) (s : NegacyclicPoly R N) :
    NegacyclicPoly R N :=
  ct.c0 + concreteInvNTT ψ_inv n_inv (concreteNTT ψ ct.c1 * concreteNTT ψ s)

theorem bfvPhaseNTT_eq_bfvPhase {R : Type*} [CommRing R] [NoZeroDivisors R] {N : ℕ} [Fact (0 < N)]
    (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1)
    (ct : BFVCiphertext (NegacyclicPoly R N)) (s : NegacyclicPoly R N) :
    bfvPhaseNTT ψ ψ_inv n_inv ct s = bfvPhase (NegacyclicPoly R N) ct s := by
  unfold bfvPhaseNTT bfvPhase
  rw [concrete_ntt_mul_eq_mulSchoolbook_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim ct.c1 s]

def bfvPlainPoly (params : LWEParams) (N : ℕ) (m : Fin N → ℕ) : NegacyclicPoly (Zq params) N :=
  ⟨fun k => ((m k : ℕ) : Zq params)⟩

def bfvPlainMulMod (N t : ℕ) (m1 m2 : Fin N → ℕ) : Fin N → ℕ :=
  fun k =>
    (((⟨fun i => (m1 i : ℤ)⟩ : NegacyclicPoly ℤ N) *
      ⟨fun i => (m2 i : ℤ)⟩).coeffs k % (t : ℤ)).toNat

theorem bfvPlainMulMod_lt {N t : ℕ} (ht : 0 < t) (m1 m2 : Fin N → ℕ) (k : Fin N) :
    bfvPlainMulMod N t m1 m2 k < t := by
  dsimp only [bfvPlainMulMod]
  have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
  have h0 : 0 ≤ ((⟨fun i => (m1 i : ℤ)⟩ : NegacyclicPoly ℤ N) *
      ⟨fun i => (m2 i : ℤ)⟩).coeffs k % (t : ℤ) := Int.emod_nonneg _ (ne_of_gt ht_pos)
  have hlt := Int.emod_lt_of_pos
    (((⟨fun i => (m1 i : ℤ)⟩ : NegacyclicPoly ℤ N) * ⟨fun i => (m2 i : ℤ)⟩).coeffs k) ht_pos
  omega

theorem bfvPlainMulMod_cast_zmod (N t : ℕ) [ht : Fact (0 < t)] (m1 m2 : Fin N → ℕ) (k : Fin N) :
    ((bfvPlainMulMod N t m1 m2 k : ℕ) : ZMod t) =
      ((⟨fun i => (m1 i : ZMod t)⟩ : NegacyclicPoly (ZMod t) N) *
        ⟨fun i => (m2 i : ZMod t)⟩).coeffs k := by
  dsimp only [bfvPlainMulMod]
  set z := ((⟨fun i => (m1 i : ℤ)⟩ : NegacyclicPoly ℤ N) *
    ⟨fun i => (m2 i : ℤ)⟩).coeffs k
  have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht.out
  have hr0 : 0 ≤ z % (t : ℤ) := Int.emod_nonneg _ (ne_of_gt ht_pos)
  have h_toNat : (((z % (t : ℤ)).toNat : ℕ) : ℤ) = z % (t : ℤ) := Int.toNat_of_nonneg hr0
  have h_dm : z % (t : ℤ) + (t : ℤ) * (z / (t : ℤ)) = z := Int.emod_add_mul_ediv z (t : ℤ)
  have h_zmod : (((z % (t : ℤ)).toNat : ℕ) : ZMod t) = (z : ZMod t) := by
    rw [← Int.cast_natCast, h_toNat]
    have h_eq : (z : ZMod t) = Int.cast (z % (t : ℤ) + (t : ℤ) * (z / (t : ℤ))) := by
      rw [h_dm]
    rw [h_eq, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]
  rw [h_zmod]
  dsimp only [z]
  simp only [NegacyclicPoly.mul_coeffs]
  rw [NegacyclicPoly.intCast_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [NegacyclicPoly.intCast_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    congr 2
    unfold NegacyclicPoly.negacyclicSign
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  · rw [Int.cast_zero]

lemma intCastPolyHom_const_nat (params : LWEParams) (N Δ : ℕ) [Fact (0 < N)] (m : Fin N → ℕ) :
    NegacyclicPoly.intCastPolyHom params N
        ((Δ : NegacyclicPoly ℤ N) * ⟨fun k => (m k : ℤ)⟩) =
      bfvEncodePoly params N Δ m := by
  ext k
  rw [NegacyclicPoly.intCastPolyHom_coeffs]
  change Int.cast ((NegacyclicPoly.constPoly (Δ : ℤ) * ⟨fun i => (m i : ℤ)⟩).coeffs k) =
    ((Δ * m k : ℕ) : Zq params)
  rw [NegacyclicPoly.constPoly_mul_coeffs, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    Nat.cast_mul]

theorem bfvDecryptPoly_add_mod_t_correct (N Δ t : ℕ) [Fact (0 < N)] (ht : 0 < t)
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2)
    (h_noise :
      2 * (normInf params E1.coeffs + normInf params E2.coeffs + (params.q - Δ * t)) < Δ) :
    bfvDecryptPoly params N Δ s (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) =
      fun k => (m1 k + m2 k) % t := by
  let r_q : ℕ := params.q - Δ * t
  let D : NegacyclicPoly (Zq params) N :=
    ⟨fun k => -(((r_q * ((m1 k + m2 k) / t) : ℕ) : Zq params))⟩
  have h_dt_eq : ((Δ * t : ℕ) : Zq params) = -((r_q : ℕ) : Zq params) := by
    have hq_sum : Δ * t + r_q = params.q := by omega
    have hz : ((Δ * t + r_q : ℕ) : Zq params) = 0 := by rw [hq_sum, ZMod.natCast_self]
    rw [Nat.cast_add, add_eq_zero_iff_eq_neg] at hz
    exact hz
  have h_enc_eq :
      bfvEncodePoly params N Δ m1 + bfvEncodePoly params N Δ m2 =
        bfvEncodePoly params N Δ (fun k => (m1 k + m2 k) % t) + D := by
    ext k
    simp only [NegacyclicPoly.add_coeffs, bfvEncodePoly, bfvEncodeElem]
    have h_div_le : (m1 k + m2 k) / t ≤ 1 := by
      have hk1 := hm1 k
      have hk2 := hm2 k
      exact Nat.div_lt_of_lt_mul (by omega) |> Nat.le_of_lt_succ
    have h_split : m1 k + m2 k = (m1 k + m2 k) % t + t * ((m1 k + m2 k) / t) :=
      (Nat.mod_add_div (m1 k + m2 k) t).symm
    calc
      ((Δ * m1 k : ℕ) : Zq params) + ((Δ * m2 k : ℕ) : Zq params)
        = ((Δ * (m1 k + m2 k) : ℕ) : Zq params) := by rw [Nat.mul_add, Nat.cast_add]
      _ = ((Δ * ((m1 k + m2 k) % t) : ℕ) : Zq params) +
            ((Δ * t : ℕ) : Zq params) * (((m1 k + m2 k) / t : ℕ) : Zq params) := by
          conv_lhs =>
            rw [h_split, Nat.mul_add, Nat.cast_add, ← mul_assoc, Nat.cast_mul (Δ * t)]
      _ = ((Δ * ((m1 k + m2 k) % t) : ℕ) : Zq params) + D.coeffs k := by
          dsimp only [D]
          rw [h_dt_eq, neg_mul, ← Nat.cast_mul r_q]
  have hD_norm : normInf params D.coeffs ≤ r_q := by
    dsimp [normInf]
    apply Finset.sup_le
    intro k _
    dsimp [D]
    rw [norm_neg_elem, ← Int.cast_natCast]
    have h_le_z := norm_intCast_le_natAbs params ((r_q * ((m1 k + m2 k) / t) : ℕ) : ℤ)
    have h_div_le : (m1 k + m2 k) / t ≤ 1 := by
      have hk1 := hm1 k
      have hk2 := hm2 k
      exact Nat.div_lt_of_lt_mul (by omega) |> Nat.le_of_lt_succ
    have h_prod_le := Nat.mul_le_mul_left r_q h_div_le
    omega
  have h_phase_sum :
      bfvPhase (NegacyclicPoly (Zq params) N) (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) s =
        bfvEncodePoly params N Δ (fun k => (m1 k + m2 k) % t) + (E1 + E2 + D) := by
    rw [bfvAdd_phase, h_phase1, h_phase2]
    calc
      bfvEncodePoly params N Δ m1 + E1 + (bfvEncodePoly params N Δ m2 + E2)
        = (bfvEncodePoly params N Δ m1 + bfvEncodePoly params N Δ m2) + (E1 + E2) := by ring
      _ = bfvEncodePoly params N Δ (fun k => (m1 k + m2 k) % t) + (E1 + E2 + D) := by
          rw [h_enc_eq]; ring
  have h_tri1 := norm_add_le params (E1 + E2).coeffs D.coeffs
  have h_tri2 := norm_add_le params E1.coeffs E2.coeffs
  change normInf params (E1 + E2 + D).coeffs ≤
    normInf params (E1 + E2).coeffs + normInf params D.coeffs at h_tri1
  change normInf params (E1 + E2).coeffs ≤
    normInf params E1.coeffs + normInf params E2.coeffs at h_tri2
  dsimp only [r_q] at hD_norm
  have h_noise_sum : 2 * normInf params (E1 + E2 + D).coeffs < Δ :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (le_trans h_tri1 (Nat.add_le_add h_tri2 hD_norm))) h_noise
  exact bfvDecryptPoly_of_phase_eq params N Δ t s (E1 + E2 + D)
    (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) (fun k => (m1 k + m2 k) % t)
    ht_le (fun k => Nat.mod_lt _ ht) h_phase_sum h_noise_sum

theorem bfvDecryptPoly_mulPlain_mod_t_correct (N Δ t : ℕ) [Fact (0 < N)] (ht : 0 < t)
    (s E : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m1 + E)
    (h_noise :
      2 * (N * normInf params E.coeffs * (t - 1) +
        (params.q - Δ * t) * ((N * (t - 1) * (t - 1) + (t - 1)) / t)) < Δ) :
    bfvDecryptPoly params N Δ s
        (bfvMulPlain (NegacyclicPoly (Zq params) N) ct (bfvPlainPoly params N m2)) =
      bfvPlainMulMod N t m1 m2 := by
  let r_q : ℕ := params.q - Δ * t
  let M1 : NegacyclicPoly ℤ N := ⟨fun k => (m1 k : ℤ)⟩
  let M2 : NegacyclicPoly ℤ N := ⟨fun k => (m2 k : ℤ)⟩
  let Q_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k / (t : ℤ)⟩
  let P_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k % (t : ℤ)⟩
  have hM1_norm : NegacyclicPoly.intPolyNormInf M1 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M1]
    apply Finset.sup_le
    intro k _
    have hk := hm1 k
    omega
  have hM2_norm : NegacyclicPoly.intPolyNormInf M2 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M2]
    apply Finset.sup_le
    intro k _
    have hk := hm2 k
    omega
  have hM12_norm : NegacyclicPoly.intPolyNormInf (M1 * M2) ≤ N * (t - 1) * (t - 1) := by
    have h_mul := NegacyclicPoly.intPolyNormInf_mul_le M1 M2
    have h1 : N * NegacyclicPoly.intPolyNormInf M1 ≤ N * (t - 1) :=
      Nat.mul_le_mul_left N hM1_norm
    exact le_trans h_mul (Nat.mul_le_mul h1 hM2_norm)
  have hQM_norm :
      NegacyclicPoly.intPolyNormInf Q_M ≤ (N * (t - 1) * (t - 1) + (t - 1)) / t := by
    dsimp [NegacyclicPoly.intPolyNormInf, Q_M]
    apply Finset.sup_le
    intro k _
    have hk_le := le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf (M1 * M2) k) hM12_norm
    exact ediv_natAbs_le ht hk_le
  have h_split : M1 * M2 = (t : NegacyclicPoly ℤ N) * Q_M + P_M := by
    ext k
    rw [NegacyclicPoly.add_coeffs]
    change (M1 * M2).coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * Q_M).coeffs k + P_M.coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    dsimp [Q_M, P_M]
    rw [add_comm]
    exact (Int.emod_add_mul_ediv ((M1 * M2).coeffs k) (t : ℤ)).symm
  have h_dt : (Δ : NegacyclicPoly ℤ N) * (t : NegacyclicPoly ℤ N) =
      (params.q : NegacyclicPoly ℤ N) - (r_q : NegacyclicPoly ℤ N) := by
    have hq_nat : Δ * t + r_q = params.q := by omega
    have h_cast := congrArg (fun n : ℕ => (n : NegacyclicPoly ℤ N)) hq_nat
    push_cast at h_cast
    exact eq_sub_of_add_eq h_cast
  have hP_eq :
      NegacyclicPoly.intCastPolyHom params N ((Δ : NegacyclicPoly ℤ N) * P_M) =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) := by
    have hP_coeffs : P_M = ⟨fun k => (bfvPlainMulMod N t m1 m2 k : ℤ)⟩ := by
      ext k
      dsimp [P_M, bfvPlainMulMod]
      have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
      exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt ht_pos))).symm
    rw [hP_coeffs]
    exact intCastPolyHom_const_nat params N Δ (bfvPlainMulMod N t m1 m2)
  have h_enc_id :
      (Δ : NegacyclicPoly ℤ N) * (M1 * M2) =
        (params.q : NegacyclicPoly ℤ N) * Q_M +
          (Δ : NegacyclicPoly ℤ N) * P_M - (r_q : NegacyclicPoly ℤ N) * Q_M := by
    calc
      (Δ : NegacyclicPoly ℤ N) * (M1 * M2)
        = (Δ : NegacyclicPoly ℤ N) * ((t : NegacyclicPoly ℤ N) * Q_M + P_M) := by
          rw [h_split]
      _ = ((Δ : NegacyclicPoly ℤ N) * (t : NegacyclicPoly ℤ N)) * Q_M +
            (Δ : NegacyclicPoly ℤ N) * P_M := by ring
      _ = ((params.q : NegacyclicPoly ℤ N) - (r_q : NegacyclicPoly ℤ N)) * Q_M +
            (Δ : NegacyclicPoly ℤ N) * P_M := by rw [h_dt]
      _ = (params.q : NegacyclicPoly ℤ N) * Q_M +
            (Δ : NegacyclicPoly ℤ N) * P_M - (r_q : NegacyclicPoly ℤ N) * Q_M := by ring
  let D : NegacyclicPoly (Zq params) N :=
    -(NegacyclicPoly.intCastPolyHom params N ((r_q : NegacyclicPoly ℤ N) * Q_M))
  have hM1 : NegacyclicPoly.intCastPolyHom params N ((Δ : NegacyclicPoly ℤ N) * M1) =
      bfvEncodePoly params N Δ m1 := intCastPolyHom_const_nat params N Δ m1
  have hM2 : NegacyclicPoly.intCastPolyHom params N M2 = bfvPlainPoly params N m2 := by
    ext k
    exact Int.cast_natCast (m2 k)
  have h_encode_mul :
      bfvEncodePoly params N Δ m1 * bfvPlainPoly params N m2 =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) + D := by
    calc
      bfvEncodePoly params N Δ m1 * bfvPlainPoly params N m2
        = NegacyclicPoly.intCastPolyHom params N ((Δ : NegacyclicPoly ℤ N) * (M1 * M2)) := by
          rw [← hM1, ← hM2, ← map_mul, mul_assoc]
      _ = NegacyclicPoly.intCastPolyHom params N ((params.q : NegacyclicPoly ℤ N) * Q_M +
            (Δ : NegacyclicPoly ℤ N) * P_M - (r_q : NegacyclicPoly ℤ N) * Q_M) := by
          rw [h_enc_id]
      _ = bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) + D := by
          rw [map_sub, map_add, map_mul, NegacyclicPoly.intCastPolyHom_q_zero, zero_mul,
            zero_add, hP_eq, sub_eq_add_neg]
  have h_phase_mul :
      bfvPhase (NegacyclicPoly (Zq params) N)
          (bfvMulPlain (NegacyclicPoly (Zq params) N) ct (bfvPlainPoly params N m2)) s =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) +
          (E * bfvPlainPoly params N m2 + D) := by
    rw [bfvMulPlain_phase, h_phase, add_mul, h_encode_mul]
    ring
  have hM2_zq : normInf params (bfvPlainPoly params N m2).coeffs ≤ t - 1 := by
    dsimp [normInf, bfvPlainPoly]
    apply Finset.sup_le
    intro k _
    rw [← Int.cast_natCast]
    have h_le := norm_intCast_le_natAbs params (m2 k : ℤ)
    have hk := hm2 k
    omega
  have hE_mul : normInf params (E * bfvPlainPoly params N m2).coeffs ≤
      N * normInf params E.coeffs * (t - 1) := by
    have h_mul := NegacyclicPoly.normInf_mul_le params N E (bfvPlainPoly params N m2)
    have h_le : N * normInf params E.coeffs * normInf params (bfvPlainPoly params N m2).coeffs ≤
        N * normInf params E.coeffs * (t - 1) := Nat.mul_le_mul_left _ hM2_zq
    exact le_trans h_mul h_le
  have hD_norm : normInf params D.coeffs ≤ r_q * ((N * (t - 1) * (t - 1) + (t - 1)) / t) := by
    change normInf params
      (-((NegacyclicPoly.intCastPolyHom params N ((r_q : NegacyclicPoly ℤ N) * Q_M)).coeffs)) ≤
      r_q * ((N * (t - 1) * (t - 1) + (t - 1)) / t)
    rw [norm_neg]
    have h_le1 := NegacyclicPoly.normInf_intCastPolyHom_le params N
      ((r_q : NegacyclicPoly ℤ N) * Q_M)
    have h_rq_mul : (r_q : NegacyclicPoly ℤ N) * Q_M =
        NegacyclicPoly.constPoly (r_q : ℤ) * Q_M := rfl
    have h_le2 : NegacyclicPoly.intPolyNormInf ((r_q : NegacyclicPoly ℤ N) * Q_M) ≤
        r_q * NegacyclicPoly.intPolyNormInf Q_M := by
      rw [h_rq_mul]
      have h_cm := NegacyclicPoly.intPolyNormInf_constPoly_mul_le (N := N) (r_q : ℤ) Q_M
      rwa [Int.natAbs_natCast] at h_cm
    have h_le3 : r_q * NegacyclicPoly.intPolyNormInf Q_M ≤
        r_q * ((N * (t - 1) * (t - 1) + (t - 1)) / t) := Nat.mul_le_mul_left r_q hQM_norm
    exact le_trans h_le1 (le_trans h_le2 h_le3)
  have h_tri := norm_add_le params (E * bfvPlainPoly params N m2).coeffs D.coeffs
  change normInf params (E * bfvPlainPoly params N m2 + D).coeffs ≤
    normInf params (E * bfvPlainPoly params N m2).coeffs + normInf params D.coeffs at h_tri
  dsimp only [r_q] at hD_norm
  have h_tot : 2 * normInf params (E * bfvPlainPoly params N m2 + D).coeffs < Δ :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (le_trans h_tri (Nat.add_le_add hE_mul hD_norm))) h_noise
  exact bfvDecryptPoly_of_phase_eq params N Δ t s (E * bfvPlainPoly params N m2 + D)
    (bfvMulPlain (NegacyclicPoly (Zq params) N) ct (bfvPlainPoly params N m2))
    (bfvPlainMulMod N t m1 m2) ht_le (bfvPlainMulMod_lt ht m1 m2) h_phase_mul h_tot

def bfvTensorD0 (params : LWEParams) (N : ℕ)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N)) : NegacyclicPoly ℤ N :=
  NegacyclicPoly.liftPolyCentered params N ct1.c0 *
    NegacyclicPoly.liftPolyCentered params N ct2.c0

def bfvTensorD1 (params : LWEParams) (N : ℕ)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N)) : NegacyclicPoly ℤ N :=
  NegacyclicPoly.liftPolyCentered params N ct1.c0 *
      NegacyclicPoly.liftPolyCentered params N ct2.c1 +
    NegacyclicPoly.liftPolyCentered params N ct1.c1 *
      NegacyclicPoly.liftPolyCentered params N ct2.c0

def bfvTensorD2 (params : LWEParams) (N : ℕ)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N)) : NegacyclicPoly ℤ N :=
  NegacyclicPoly.liftPolyCentered params N ct1.c1 *
    NegacyclicPoly.liftPolyCentered params N ct2.c1

def bfvTensorScalePoly (params : LWEParams) (N t : ℕ) (D : NegacyclicPoly ℤ N) :
    NegacyclicPoly (Zq params) N :=
  ⟨fun k => Int.cast (divRoundInt ((t : ℤ) * D.coeffs k) params.q)⟩

def bfvMul (params : LWEParams) (N t B l : ℕ) [Fact (0 < N)]
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (rk : GadgetRelinKey (NegacyclicPoly (Zq params) N) l) :
    BFVCiphertext (NegacyclicPoly (Zq params) N) :=
  bfvGadgetRelinearize (NegacyclicPoly (Zq params) N)
    (bfvTensorScalePoly params N t (bfvTensorD0 params N ct1 ct2))
    (bfvTensorScalePoly params N t (bfvTensorD1 params N ct1 ct2))
    (bfvTensorScalePoly params N t (bfvTensorD2 params N ct1 ct2))
    (NegacyclicPoly.negacyclicDecomp params N B l) rk

def bfvPhaseWrapBound (q N t B_s B_e : ℕ) : ℕ :=
  ((N * B_s + 1) * (q / 2) + (q / t) * (t - 1) + B_e) / q

def bfvPlainCarryBound (N t : ℕ) : ℕ :=
  (N * (t - 1) * (t - 1) + (t - 1)) / t

def bfvMulScaleNoiseBound (q N t B_s B_1 B_2 : ℕ) : ℕ :=
  let Δ := q / t
  let r_q := q % t
  let K1 := bfvPhaseWrapBound q N t B_s B_1
  let K2 := bfvPhaseWrapBound q N t B_s B_2
  let Q_b := bfvPlainCarryBound N t
  let quotBound :=
    N * (t - 1) * B_2 + N * B_1 * (t - 1) + 2 * r_q * Q_b +
      N * K1 * (t * B_2 + r_q * (t - 1)) + N * (t * B_1 + r_q * (t - 1)) * K2
  let remBound :=
    t * (N * B_1 * B_2) + r_q * r_q * Q_b + r_q * Δ * (t - 1) +
      r_q * (N * (t - 1) * B_2 + N * B_1 * (t - 1)) +
      (q / 2 + N * (q / 2) * B_s + N * (q / 2) * (N * B_s * B_s))
  quotBound + remBound / q

def bfvMulTotalNoiseBound (q N t B_s B_1 B_2 B l B_rk : ℕ) : ℕ :=
  bfvMulScaleNoiseBound q N t B_s B_1 B_2 + l * (N * (B - 1) * B_rk)

lemma bfv_phase_wrap_decomp (N Δ t B_s B_e : ℕ) [Fact (0 < N)]
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : normInf params s.coeffs ≤ B_s)
    (hE : normInf params E.coeffs ≤ B_e)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E) :
    ∃ K : NegacyclicPoly ℤ N,
      NegacyclicPoly.liftPolyCentered params N ct.c0 +
        NegacyclicPoly.liftPolyCentered params N ct.c1 *
          NegacyclicPoly.liftPolyCentered params N s =
        (Δ : NegacyclicPoly ℤ N) * ⟨fun k => (m k : ℤ)⟩ +
          NegacyclicPoly.liftPolyCentered params N E +
          (params.q : NegacyclicPoly ℤ N) * K ∧
      NegacyclicPoly.intPolyNormInf K ≤
        ((N * B_s + 1) * (params.q / 2) + Δ * (t - 1) + B_e) / params.q := by
  let C0 := NegacyclicPoly.liftPolyCentered params N ct.c0
  let C1 := NegacyclicPoly.liftPolyCentered params N ct.c1
  let S := NegacyclicPoly.liftPolyCentered params N s
  let E_hat := NegacyclicPoly.liftPolyCentered params N E
  let M : NegacyclicPoly ℤ N := ⟨fun k => (m k : ℤ)⟩
  let diff := (C0 + C1 * S) - ((Δ : NegacyclicPoly ℤ N) * M + E_hat)
  have h_hom_zero : NegacyclicPoly.intCastPolyHom params N diff = 0 := by
    dsimp [diff]
    rw [map_sub, map_add, map_add, map_mul,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      intCastPolyHom_const_nat]
    change bfvPhase (NegacyclicPoly (Zq params) N) ct s -
      (bfvEncodePoly params N Δ m + E) = 0
    rw [h_phase, sub_self]
  have hk_dvd : ∀ k : Fin N, ∃ kz : ℤ, diff.coeffs k = (params.q : ℤ) * kz := by
    intro k
    have hk0 : ((diff.coeffs k : ℤ) : Zq params) = 0 := by
      have hk := congrArg (fun p => p.coeffs k) h_hom_zero
      exact hk
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (diff.coeffs k) params.q).mp hk0
  let K : NegacyclicPoly ℤ N := ⟨fun k => Classical.choose (hk_dvd k)⟩
  refine ⟨K, ?_, ?_⟩
  · have h_sub_eq : diff = (params.q : NegacyclicPoly ℤ N) * K := by
      ext k
      have h_mul : ((params.q : NegacyclicPoly ℤ N) * K).coeffs k =
          (params.q : ℤ) * K.coeffs k :=
        NegacyclicPoly.constPoly_mul_coeffs (R := ℤ) (params.q : ℤ) K k
      rw [h_mul]
      exact Classical.choose_spec (hk_dvd k)
    dsimp [diff] at h_sub_eq
    exact (sub_eq_iff_eq_add.mp h_sub_eq).trans (add_comm _ _)
  · have hC0 : NegacyclicPoly.intPolyNormInf C0 ≤ params.q / 2 := by
      dsimp [NegacyclicPoly.intPolyNormInf, C0, NegacyclicPoly.liftPolyCentered]
      apply Finset.sup_le
      intro k _
      exact norm_le_div_two params (ct.c0.coeffs k)
    have hC1 : NegacyclicPoly.intPolyNormInf C1 ≤ params.q / 2 := by
      dsimp [NegacyclicPoly.intPolyNormInf, C1, NegacyclicPoly.liftPolyCentered]
      apply Finset.sup_le
      intro k _
      exact norm_le_div_two params (ct.c1.coeffs k)
    have hS : NegacyclicPoly.intPolyNormInf S ≤ B_s := hs
    have hC1S : NegacyclicPoly.intPolyNormInf (C1 * S) ≤ N * (params.q / 2) * B_s := by
      have h_mul := NegacyclicPoly.intPolyNormInf_mul_le C1 S
      have h1 : N * NegacyclicPoly.intPolyNormInf C1 ≤ N * (params.q / 2) :=
        Nat.mul_le_mul_left N hC1
      exact le_trans h_mul (Nat.mul_le_mul h1 hS)
    have hM_norm : NegacyclicPoly.intPolyNormInf M ≤ t - 1 := by
      dsimp [NegacyclicPoly.intPolyNormInf, M]
      apply Finset.sup_le
      intro k _
      have hk := hm k
      omega
    have hΔM : NegacyclicPoly.intPolyNormInf ((Δ : NegacyclicPoly ℤ N) * M) ≤ Δ * (t - 1) := by
      have h_eq : (Δ : NegacyclicPoly ℤ N) * M = NegacyclicPoly.constPoly (Δ : ℤ) * M := rfl
      rw [h_eq]
      have h_cm := NegacyclicPoly.intPolyNormInf_constPoly_mul_le (N := N) (Δ : ℤ) M
      rw [Int.natAbs_natCast] at h_cm
      exact le_trans h_cm (Nat.mul_le_mul_left Δ hM_norm)
    have hE_norm : NegacyclicPoly.intPolyNormInf E_hat ≤ B_e := hE
    dsimp [NegacyclicPoly.intPolyNormInf]
    apply Finset.sup_le
    intro k _
    have h_eq_k : (params.q : ℤ) * K.coeffs k = diff.coeffs k :=
      (Classical.choose_spec (hk_dvd k)).symm
    have h_diff_norm : (diff.coeffs k).natAbs ≤
        (N * B_s + 1) * (params.q / 2) + Δ * (t - 1) + B_e := by
      have h1 := NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf C0 k
      have h2 := NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf (C1 * S) k
      have h3 := NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf ((Δ : NegacyclicPoly ℤ N) * M) k
      have h4 := NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf E_hat k
      have h_coeff : diff.coeffs k = C0.coeffs k + (C1 * S).coeffs k -
          (((Δ : NegacyclicPoly ℤ N) * M).coeffs k + E_hat.coeffs k) := rfl
      have h_mul_eq : N * (params.q / 2) * B_s + params.q / 2 = (N * B_s + 1) * (params.q / 2) := by
        ring
      omega
    exact natAbs_le_div_of_mul_eq params.q_pos.out h_eq_k h_diff_norm

theorem bfvTensorScale_phase_bound (N Δ t B_s B_1 B_2 : ℕ) [Fact (0 < N)]
    (ht : 0 < t)
    (hΔ : Δ = params.q / t)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hs : normInf params s.coeffs ≤ B_s)
    (hE1 : normInf params E1.coeffs ≤ B_1)
    (hE2 : normInf params E2.coeffs ≤ B_2)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2) :
    let d0 := bfvTensorScalePoly params N t (bfvTensorD0 params N ct1 ct2)
    let d1 := bfvTensorScalePoly params N t (bfvTensorD1 params N ct1 ct2)
    let d2 := bfvTensorScalePoly params N t (bfvTensorD2 params N ct1 ct2)
    ∃ E_scale : NegacyclicPoly (Zq params) N,
      d0 + d1 * s + d2 * (s * s) =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) + E_scale ∧
      normInf params E_scale.coeffs ≤ bfvMulScaleNoiseBound params.q N t B_s B_1 B_2 := by
  intro d0 d1 d2
  let q : ℕ := params.q
  let r_q : ℕ := q % t
  have hq_pos : 0 < q := params.q_pos.out
  have hq_split : q = Δ * t + r_q := by
    dsimp [q, r_q]
    rw [hΔ]
    exact (Nat.div_add_mod params.q t).symm.trans (by rw [mul_comm])
  have hq_z : (q : NegacyclicPoly ℤ N) =
      (Δ : NegacyclicPoly ℤ N) * (t : NegacyclicPoly ℤ N) + (r_q : NegacyclicPoly ℤ N) := by
    have h_cast := congrArg (fun n : ℕ => (n : NegacyclicPoly ℤ N)) hq_split
    push_cast at h_cast
    exact h_cast
  let C10 := NegacyclicPoly.liftPolyCentered params N ct1.c0
  let C11 := NegacyclicPoly.liftPolyCentered params N ct1.c1
  let C20 := NegacyclicPoly.liftPolyCentered params N ct2.c0
  let C21 := NegacyclicPoly.liftPolyCentered params N ct2.c1
  let S := NegacyclicPoly.liftPolyCentered params N s
  let E1_hat := NegacyclicPoly.liftPolyCentered params N E1
  let E2_hat := NegacyclicPoly.liftPolyCentered params N E2
  let M1 : NegacyclicPoly ℤ N := ⟨fun k => (m1 k : ℤ)⟩
  let M2 : NegacyclicPoly ℤ N := ⟨fun k => (m2 k : ℤ)⟩
  rcases bfv_phase_wrap_decomp params N Δ t B_s B_1 ct1 s E1 m1 hm1 hs hE1 h_phase1 with
    ⟨K1, hK1_eq, hK1_norm⟩
  rcases bfv_phase_wrap_decomp params N Δ t B_s B_2 ct2 s E2 m2 hm2 hs hE2 h_phase2 with
    ⟨K2, hK2_eq, hK2_norm⟩
  rw [hΔ] at hK1_norm hK2_norm
  let Q_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k / (t : ℤ)⟩
  let P_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k % (t : ℤ)⟩
  have h_m12_split : M1 * M2 = (t : NegacyclicPoly ℤ N) * Q_M + P_M := by
    ext k
    rw [NegacyclicPoly.add_coeffs]
    change (M1 * M2).coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * Q_M).coeffs k + P_M.coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    dsimp [Q_M, P_M]
    rw [add_comm]
    exact (Int.emod_add_mul_ediv ((M1 * M2).coeffs k) (t : ℤ)).symm
  have hP_eq :
      NegacyclicPoly.intCastPolyHom params N ((Δ : NegacyclicPoly ℤ N) * P_M) =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) := by
    have hP_coeffs : P_M = ⟨fun k => (bfvPlainMulMod N t m1 m2 k : ℤ)⟩ := by
      ext k
      dsimp [P_M, bfvPlainMulMod]
      have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
      exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt ht_pos))).symm
    rw [hP_coeffs]
    exact intCastPolyHom_const_nat params N Δ (bfvPlainMulMod N t m1 m2)
  let D0 := bfvTensorD0 params N ct1 ct2
  let D1 := bfvTensorD1 params N ct1 ct2
  let D2 := bfvTensorD2 params N ct1 ct2
  let Z0 : NegacyclicPoly ℤ N := ⟨fun k => divRoundInt ((t : ℤ) * D0.coeffs k) params.q⟩
  let Z1 : NegacyclicPoly ℤ N := ⟨fun k => divRoundInt ((t : ℤ) * D1.coeffs k) params.q⟩
  let Z2 : NegacyclicPoly ℤ N := ⟨fun k => divRoundInt ((t : ℤ) * D2.coeffs k) params.q⟩
  let ρ0 : NegacyclicPoly ℤ N := (q : NegacyclicPoly ℤ N) * Z0 - (t : NegacyclicPoly ℤ N) * D0
  let ρ1 : NegacyclicPoly ℤ N := (q : NegacyclicPoly ℤ N) * Z1 - (t : NegacyclicPoly ℤ N) * D1
  let ρ2 : NegacyclicPoly ℤ N := (q : NegacyclicPoly ℤ N) * Z2 - (t : NegacyclicPoly ℤ N) * D2
  have h_round_le : ∀ (D_p Z_p ρ_p : NegacyclicPoly ℤ N),
      Z_p = ⟨fun k => divRoundInt ((t : ℤ) * D_p.coeffs k) params.q⟩ →
      ρ_p = (q : NegacyclicPoly ℤ N) * Z_p - (t : NegacyclicPoly ℤ N) * D_p →
      NegacyclicPoly.intPolyNormInf ρ_p ≤ q / 2 := by
    intro D_p Z_p ρ_p hZp hρp
    subst hZp hρp
    change Finset.univ.sup (fun k =>
      (((q : NegacyclicPoly ℤ N) * ⟨fun j => divRoundInt ((t : ℤ) * D_p.coeffs j) params.q⟩ -
        (t : NegacyclicPoly ℤ N) * D_p).coeffs k).natAbs) ≤ q / 2
    apply Finset.sup_le
    intro k _
    rw [NegacyclicPoly.sub_coeffs]
    change ((NegacyclicPoly.constPoly (q : ℤ) * _).coeffs k -
        (NegacyclicPoly.constPoly (t : ℤ) * D_p).coeffs k).natAbs ≤ q / 2
    rw [NegacyclicPoly.constPoly_mul_coeffs, NegacyclicPoly.constPoly_mul_coeffs]
    exact divRoundInt_mul_sub_bounds hq_pos ((t : ℤ) * D_p.coeffs k)
  have hρ0 : NegacyclicPoly.intPolyNormInf ρ0 ≤ q / 2 := h_round_le D0 Z0 ρ0 rfl rfl
  have hρ1 : NegacyclicPoly.intPolyNormInf ρ1 ≤ q / 2 := h_round_le D1 Z1 ρ1 rfl rfl
  have hρ2 : NegacyclicPoly.intPolyNormInf ρ2 ≤ q / 2 := h_round_le D2 Z2 ρ2 rfl rfl
  let H_quad : NegacyclicPoly ℤ N := Q_M + K1 * (M2 + (t : NegacyclicPoly ℤ N) * K2) + M1 * K2
  let E_quot : NegacyclicPoly ℤ N :=
    -((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M +
      (M1 * E2_hat + E1_hat * M2) +
      K1 * ((t : NegacyclicPoly ℤ N) * E2_hat - (r_q : NegacyclicPoly ℤ N) * M2) +
      ((t : NegacyclicPoly ℤ N) * E1_hat - (r_q : NegacyclicPoly ℤ N) * M1) * K2
  let E_rem : NegacyclicPoly ℤ N :=
    (t : NegacyclicPoly ℤ N) * (E1_hat * E2_hat) +
      ((r_q * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M -
      ((r_q * Δ : ℕ) : NegacyclicPoly ℤ N) * P_M -
      (r_q : NegacyclicPoly ℤ N) * (M1 * E2_hat + E1_hat * M2) +
      (ρ0 + ρ1 * S + ρ2 * (S * S))
  let W : NegacyclicPoly ℤ N :=
    (Z0 + Z1 * S + Z2 * (S * S)) -
      ((q : NegacyclicPoly ℤ N) * H_quad + (Δ : NegacyclicPoly ℤ N) * P_M + E_quot)
  have hD_tensor : D0 + D1 * S + D2 * (S * S) = (C10 + C11 * S) * (C20 + C21 * S) := by
    dsimp [D0, D1, D2, bfvTensorD0, bfvTensorD1, bfvTensorD2]
    ring
  have hZ_rel :
      (q : NegacyclicPoly ℤ N) * (Z0 + Z1 * S + Z2 * (S * S)) =
        (t : NegacyclicPoly ℤ N) * (D0 + D1 * S + D2 * (S * S)) +
          (ρ0 + ρ1 * S + ρ2 * (S * S)) := by
    have h0 : (q : NegacyclicPoly ℤ N) * Z0 = (t : NegacyclicPoly ℤ N) * D0 + ρ0 := by
      dsimp [ρ0]; ring
    have h1 : (q : NegacyclicPoly ℤ N) * Z1 = (t : NegacyclicPoly ℤ N) * D1 + ρ1 := by
      dsimp [ρ1]; ring
    have h2 : (q : NegacyclicPoly ℤ N) * Z2 = (t : NegacyclicPoly ℤ N) * D2 + ρ2 := by
      dsimp [ρ2]; ring
    calc
      (q : NegacyclicPoly ℤ N) * (Z0 + Z1 * S + Z2 * (S * S))
        = ((q : NegacyclicPoly ℤ N) * Z0) + ((q : NegacyclicPoly ℤ N) * Z1) * S +
            ((q : NegacyclicPoly ℤ N) * Z2) * (S * S) := by ring
      _ = ((t : NegacyclicPoly ℤ N) * D0 + ρ0) +
            ((t : NegacyclicPoly ℤ N) * D1 + ρ1) * S +
            ((t : NegacyclicPoly ℤ N) * D2 + ρ2) * (S * S) := by rw [h0, h1, h2]
      _ = (t : NegacyclicPoly ℤ N) * (D0 + D1 * S + D2 * (S * S)) +
            (ρ0 + ρ1 * S + ρ2 * (S * S)) := by ring
  have hΦ_expand :
      ((Δ : NegacyclicPoly ℤ N) * M1 + E1_hat + (q : NegacyclicPoly ℤ N) * K1) *
          ((Δ : NegacyclicPoly ℤ N) * M2 + E2_hat + (q : NegacyclicPoly ℤ N) * K2) =
        (Δ : NegacyclicPoly ℤ N) ^ 2 * (M1 * M2) +
          (Δ : NegacyclicPoly ℤ N) * (M1 * E2_hat + E1_hat * M2) + E1_hat * E2_hat +
          (q : NegacyclicPoly ℤ N) * K1 *
            ((Δ : NegacyclicPoly ℤ N) * M2 + E2_hat + (q : NegacyclicPoly ℤ N) * K2) +
          ((Δ : NegacyclicPoly ℤ N) * M1 + E1_hat) * ((q : NegacyclicPoly ℤ N) * K2) := by
    ring
  have h_qW : (q : NegacyclicPoly ℤ N) * W = E_rem := by
    have h_alg :
        (q : NegacyclicPoly ℤ N) * (Z0 + Z1 * S + Z2 * (S * S)) =
          (q : NegacyclicPoly ℤ N) *
            ((q : NegacyclicPoly ℤ N) * H_quad + (Δ : NegacyclicPoly ℤ N) * P_M + E_quot) +
            E_rem := by
      rw [hZ_rel, hD_tensor]
      rw [hK1_eq, hK2_eq, hΦ_expand, h_m12_split, hq_z]
      dsimp [H_quad, E_quot, E_rem]
      push_cast
      ring
    dsimp [W]
    rw [mul_sub, h_alg]
    ring
  have hM1_norm : NegacyclicPoly.intPolyNormInf M1 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M1]
    apply Finset.sup_le
    intro k _
    have hk := hm1 k
    omega
  have hM2_norm : NegacyclicPoly.intPolyNormInf M2 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M2]
    apply Finset.sup_le
    intro k _
    have hk := hm2 k
    omega
  have hS_norm : NegacyclicPoly.intPolyNormInf S ≤ B_s := hs
  have hE1_norm : NegacyclicPoly.intPolyNormInf E1_hat ≤ B_1 := hE1
  have hE2_norm : NegacyclicPoly.intPolyNormInf E2_hat ≤ B_2 := hE2
  have hM12_norm : NegacyclicPoly.intPolyNormInf (M1 * M2) ≤ N * (t - 1) * (t - 1) := by
    have h_mul := NegacyclicPoly.intPolyNormInf_mul_le M1 M2
    have h1 : N * NegacyclicPoly.intPolyNormInf M1 ≤ N * (t - 1) :=
      Nat.mul_le_mul_left N hM1_norm
    exact le_trans h_mul (Nat.mul_le_mul h1 hM2_norm)
  have hQM_norm : NegacyclicPoly.intPolyNormInf Q_M ≤ bfvPlainCarryBound N t := by
    dsimp [NegacyclicPoly.intPolyNormInf, Q_M, bfvPlainCarryBound]
    apply Finset.sup_le
    intro k _
    exact ediv_natAbs_le ht
      (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf (M1 * M2) k) hM12_norm)
  have hPM_norm : NegacyclicPoly.intPolyNormInf P_M ≤ t - 1 := by
    dsimp only [NegacyclicPoly.intPolyNormInf, P_M]
    apply Finset.sup_le
    intro k _
    have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
    have h0 := Int.emod_nonneg ((M1 * M2).coeffs k) (ne_of_gt ht_pos)
    have hlt := Int.emod_lt_of_pos ((M1 * M2).coeffs k) ht_pos
    omega
  have hM1E2 : NegacyclicPoly.intPolyNormInf (M1 * E2_hat) ≤ N * (t - 1) * B_2 :=
    le_trans (NegacyclicPoly.intPolyNormInf_mul_le M1 E2_hat)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hM1_norm) hE2_norm)
  have hE1M2 : NegacyclicPoly.intPolyNormInf (E1_hat * M2) ≤ N * B_1 * (t - 1) :=
    le_trans (NegacyclicPoly.intPolyNormInf_mul_le E1_hat M2)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hE1_norm) hM2_norm)
  have hME_sum : NegacyclicPoly.intPolyNormInf (M1 * E2_hat + E1_hat * M2) ≤
      N * (t - 1) * B_2 + N * B_1 * (t - 1) :=
    le_trans (NegacyclicPoly.intPolyNormInf_add_le _ _) (Nat.add_le_add hM1E2 hE1M2)
  have h_nat_mul_norm : ∀ (c : ℕ) (P : NegacyclicPoly ℤ N),
      NegacyclicPoly.intPolyNormInf ((c : NegacyclicPoly ℤ N) * P) ≤
        c * NegacyclicPoly.intPolyNormInf P := by
    intro c P
    have h_eq : (c : NegacyclicPoly ℤ N) * P = NegacyclicPoly.constPoly (c : ℤ) * P := rfl
    rw [h_eq]
    have h_cm := NegacyclicPoly.intPolyNormInf_constPoly_mul_le (N := N) (c : ℤ) P
    rwa [Int.natAbs_natCast] at h_cm
  have h_quot_bound : NegacyclicPoly.intPolyNormInf E_quot ≤
      N * (t - 1) * B_2 + N * B_1 * (t - 1) + 2 * r_q * bfvPlainCarryBound N t +
        N * bfvPhaseWrapBound q N t B_s B_1 * (t * B_2 + r_q * (t - 1)) +
        N * (t * B_1 + r_q * (t - 1)) * bfvPhaseWrapBound q N t B_s B_2 := by
    have h_2rq_Q : NegacyclicPoly.intPolyNormInf (-((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M) ≤
        2 * r_q * bfvPlainCarryBound N t := by
      have h_neg : -((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M =
          -(((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M) := by ring
      rw [h_neg, NegacyclicPoly.intPolyNormInf_neg]
      exact le_trans (h_nat_mul_norm (2 * r_q) Q_M) (Nat.mul_le_mul_left (2 * r_q) hQM_norm)
    have h_tE2_rM2 : NegacyclicPoly.intPolyNormInf
        ((t : NegacyclicPoly ℤ N) * E2_hat - (r_q : NegacyclicPoly ℤ N) * M2) ≤
        t * B_2 + r_q * (t - 1) := by
      refine le_trans (NegacyclicPoly.intPolyNormInf_sub_le _ _) (Nat.add_le_add ?_ ?_)
      · exact le_trans (h_nat_mul_norm t E2_hat) (Nat.mul_le_mul_left t hE2_norm)
      · exact le_trans (h_nat_mul_norm r_q M2) (Nat.mul_le_mul_left r_q hM2_norm)
    have h_tE1_rM1 : NegacyclicPoly.intPolyNormInf
        ((t : NegacyclicPoly ℤ N) * E1_hat - (r_q : NegacyclicPoly ℤ N) * M1) ≤
        t * B_1 + r_q * (t - 1) := by
      refine le_trans (NegacyclicPoly.intPolyNormInf_sub_le _ _) (Nat.add_le_add ?_ ?_)
      · exact le_trans (h_nat_mul_norm t E1_hat) (Nat.mul_le_mul_left t hE1_norm)
      · exact le_trans (h_nat_mul_norm r_q M1) (Nat.mul_le_mul_left r_q hM1_norm)
    have h_K1_term : NegacyclicPoly.intPolyNormInf
        (K1 * ((t : NegacyclicPoly ℤ N) * E2_hat - (r_q : NegacyclicPoly ℤ N) * M2)) ≤
        N * bfvPhaseWrapBound q N t B_s B_1 * (t * B_2 + r_q * (t - 1)) :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le _ _)
        (Nat.mul_le_mul (Nat.mul_le_mul_left N hK1_norm) h_tE2_rM2)
    have h_K2_term : NegacyclicPoly.intPolyNormInf
        (((t : NegacyclicPoly ℤ N) * E1_hat - (r_q : NegacyclicPoly ℤ N) * M1) * K2) ≤
        N * (t * B_1 + r_q * (t - 1)) * bfvPhaseWrapBound q N t B_s B_2 :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le _ _)
        (Nat.mul_le_mul (Nat.mul_le_mul_left N h_tE1_rM1) hK2_norm)
    dsimp [E_quot]
    have h_a1 := NegacyclicPoly.intPolyNormInf_add_le
      (-((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M + (M1 * E2_hat + E1_hat * M2) +
        K1 * ((t : NegacyclicPoly ℤ N) * E2_hat - (r_q : NegacyclicPoly ℤ N) * M2))
      (((t : NegacyclicPoly ℤ N) * E1_hat - (r_q : NegacyclicPoly ℤ N) * M1) * K2)
    have h_a2 := NegacyclicPoly.intPolyNormInf_add_le
      (-((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M + (M1 * E2_hat + E1_hat * M2))
      (K1 * ((t : NegacyclicPoly ℤ N) * E2_hat - (r_q : NegacyclicPoly ℤ N) * M2))
    have h_a3 := NegacyclicPoly.intPolyNormInf_add_le
      (-((2 * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M) (M1 * E2_hat + E1_hat * M2)
    omega
  have h_rem_bound : NegacyclicPoly.intPolyNormInf E_rem ≤
      t * (N * B_1 * B_2) + r_q * r_q * bfvPlainCarryBound N t + r_q * Δ * (t - 1) +
        r_q * (N * (t - 1) * B_2 + N * B_1 * (t - 1)) +
        (q / 2 + N * (q / 2) * B_s + N * (q / 2) * (N * B_s * B_s)) := by
    have hE12 : NegacyclicPoly.intPolyNormInf (E1_hat * E2_hat) ≤ N * B_1 * B_2 :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le E1_hat E2_hat)
        (Nat.mul_le_mul (Nat.mul_le_mul_left N hE1_norm) hE2_norm)
    have h_tE12 : NegacyclicPoly.intPolyNormInf ((t : NegacyclicPoly ℤ N) * (E1_hat * E2_hat)) ≤
        t * (N * B_1 * B_2) :=
      le_trans (h_nat_mul_norm t (E1_hat * E2_hat)) (Nat.mul_le_mul_left t hE12)
    have h_rq2Q : NegacyclicPoly.intPolyNormInf (((r_q * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M) ≤
        r_q * r_q * bfvPlainCarryBound N t :=
      le_trans (h_nat_mul_norm (r_q * r_q) Q_M) (Nat.mul_le_mul_left (r_q * r_q) hQM_norm)
    have h_rqΔP : NegacyclicPoly.intPolyNormInf (((r_q * Δ : ℕ) : NegacyclicPoly ℤ N) * P_M) ≤
        r_q * Δ * (t - 1) :=
      le_trans (h_nat_mul_norm (r_q * Δ) P_M) (Nat.mul_le_mul_left (r_q * Δ) hPM_norm)
    have h_rqME : NegacyclicPoly.intPolyNormInf
        ((r_q : NegacyclicPoly ℤ N) * (M1 * E2_hat + E1_hat * M2)) ≤
        r_q * (N * (t - 1) * B_2 + N * B_1 * (t - 1)) :=
      le_trans (h_nat_mul_norm r_q _) (Nat.mul_le_mul_left r_q hME_sum)
    have h_S2 : NegacyclicPoly.intPolyNormInf (S * S) ≤ N * B_s * B_s :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le S S)
        (Nat.mul_le_mul (Nat.mul_le_mul_left N hS_norm) hS_norm)
    have h_ρ1S : NegacyclicPoly.intPolyNormInf (ρ1 * S) ≤ N * (q / 2) * B_s :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le ρ1 S)
        (Nat.mul_le_mul (Nat.mul_le_mul_left N hρ1) hS_norm)
    have h_ρ2S2 : NegacyclicPoly.intPolyNormInf (ρ2 * (S * S)) ≤
        N * (q / 2) * (N * B_s * B_s) :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le ρ2 (S * S))
        (Nat.mul_le_mul (Nat.mul_le_mul_left N hρ2) h_S2)
    have h_ρsum : NegacyclicPoly.intPolyNormInf (ρ0 + ρ1 * S + ρ2 * (S * S)) ≤
        q / 2 + N * (q / 2) * B_s + N * (q / 2) * (N * B_s * B_s) := by
      have h1 := NegacyclicPoly.intPolyNormInf_add_le (ρ0 + ρ1 * S) (ρ2 * (S * S))
      have h2 := NegacyclicPoly.intPolyNormInf_add_le ρ0 (ρ1 * S)
      omega
    dsimp [E_rem]
    have h1 := NegacyclicPoly.intPolyNormInf_add_le
      ((t : NegacyclicPoly ℤ N) * (E1_hat * E2_hat) +
        ((r_q * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M -
        ((r_q * Δ : ℕ) : NegacyclicPoly ℤ N) * P_M -
        (r_q : NegacyclicPoly ℤ N) * (M1 * E2_hat + E1_hat * M2))
      (ρ0 + ρ1 * S + ρ2 * (S * S))
    have h2 := NegacyclicPoly.intPolyNormInf_sub_le
      ((t : NegacyclicPoly ℤ N) * (E1_hat * E2_hat) +
        ((r_q * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M -
        ((r_q * Δ : ℕ) : NegacyclicPoly ℤ N) * P_M)
      ((r_q : NegacyclicPoly ℤ N) * (M1 * E2_hat + E1_hat * M2))
    have h3 := NegacyclicPoly.intPolyNormInf_sub_le
      ((t : NegacyclicPoly ℤ N) * (E1_hat * E2_hat) +
        ((r_q * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M)
      (((r_q * Δ : ℕ) : NegacyclicPoly ℤ N) * P_M)
    have h4 := NegacyclicPoly.intPolyNormInf_add_le
      ((t : NegacyclicPoly ℤ N) * (E1_hat * E2_hat))
      (((r_q * r_q : ℕ) : NegacyclicPoly ℤ N) * Q_M)
    omega
  have hW_norm : NegacyclicPoly.intPolyNormInf W ≤
      (t * (N * B_1 * B_2) + r_q * r_q * bfvPlainCarryBound N t + r_q * Δ * (t - 1) +
        r_q * (N * (t - 1) * B_2 + N * B_1 * (t - 1)) +
        (q / 2 + N * (q / 2) * B_s + N * (q / 2) * (N * B_s * B_s))) / q := by
    dsimp [NegacyclicPoly.intPolyNormInf]
    apply Finset.sup_le
    intro k _
    have h_eq_k : (q : ℤ) * W.coeffs k = E_rem.coeffs k := by
      have hk := congrArg (fun p => p.coeffs k) h_qW
      have h_cm : ((q : NegacyclicPoly ℤ N) * W).coeffs k = (q : ℤ) * W.coeffs k :=
        NegacyclicPoly.constPoly_mul_coeffs (R := ℤ) (q : ℤ) W k
      rwa [h_cm] at hk
    exact natAbs_le_div_of_mul_eq hq_pos h_eq_k
      (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf E_rem k) h_rem_bound)
  let E_scale : NegacyclicPoly (Zq params) N :=
    NegacyclicPoly.intCastPolyHom params N (E_quot + W)
  refine ⟨E_scale, ?_, ?_⟩
  · have h_z_recombine :
        Z0 + Z1 * S + Z2 * (S * S) =
          (q : NegacyclicPoly ℤ N) * H_quad + (Δ : NegacyclicPoly ℤ N) * P_M + (E_quot + W) := by
      dsimp [W]
      ring
    have hd0_hom : d0 = NegacyclicPoly.intCastPolyHom params N Z0 := rfl
    have hd1_hom : d1 = NegacyclicPoly.intCastPolyHom params N Z1 := rfl
    have hd2_hom : d2 = NegacyclicPoly.intCastPolyHom params N Z2 := rfl
    have hs_hom : s = NegacyclicPoly.intCastPolyHom params N S :=
      (NegacyclicPoly.intCastPolyHom_liftPolyCentered params N s).symm
    calc
      d0 + d1 * s + d2 * (s * s)
        = NegacyclicPoly.intCastPolyHom params N (Z0 + Z1 * S + Z2 * (S * S)) := by
          rw [hd0_hom, hd1_hom, hd2_hom, hs_hom, map_add, map_add, map_mul, map_mul, map_mul]
      _ = NegacyclicPoly.intCastPolyHom params N
            ((q : NegacyclicPoly ℤ N) * H_quad + (Δ : NegacyclicPoly ℤ N) * P_M +
              (E_quot + W)) := by rw [h_z_recombine]
      _ = bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) + E_scale := by
          rw [map_add, map_add, map_mul, NegacyclicPoly.intCastPolyHom_q_zero, zero_mul,
            zero_add, hP_eq]
  · have h_le1 := NegacyclicPoly.normInf_intCastPolyHom_le params N (E_quot + W)
    have h_le2 := NegacyclicPoly.intPolyNormInf_add_le E_quot W
    rw [hΔ] at hW_norm
    exact le_trans h_le1 (le_trans h_le2 (Nat.add_le_add h_quot_bound hW_norm))

theorem bfvDecryptPoly_bfvMul_correct (N Δ t B_s B_1 B_2 B l B_rk : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (hB : 0 < B)
    (h2B : 2 * B ≤ params.q)
    (ht : 0 < t)
    (hΔ : Δ = params.q / t)
    (ht_le : Δ * t ≤ params.q)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hs : normInf params s.coeffs ≤ B_s)
    (hE1 : normInf params E1.coeffs ≤ B_1)
    (hE2 : normInf params E2.coeffs ≤ B_2)
    (herk : ∀ i : Fin l, normInf params (e_rk i).coeffs ≤ B_rk)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2)
    (h_noise : 2 * bfvMulTotalNoiseBound params.q N t B_s B_1 B_2 B l B_rk < Δ) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    bfvDecryptPoly params N Δ s (bfvMul params N t B l ct1 ct2 rk) =
      bfvPlainMulMod N t m1 m2 := by
  intro rk
  rcases bfvTensorScale_phase_bound params N Δ t B_s B_1 B_2 ht hΔ ct1 ct2 s E1 E2 m1 m2
    hm1 hm2 hs hE1 hE2 h_phase1 h_phase2 with ⟨E_scale, h_scale_phase, h_scale_norm⟩
  let d0 := bfvTensorScalePoly params N t (bfvTensorD0 params N ct1 ct2)
  let d1 := bfvTensorScalePoly params N t (bfvTensorD1 params N ct1 ct2)
  let d2 := bfvTensorScalePoly params N t (bfvTensorD2 params N ct1 ct2)
  have h_relin_norm := NegacyclicPoly.normInf_gadgetRelin_noise_le params N B l B_rk hB h2B
    d2 e_rk herk
  have h_sub := norm_sub_le params E_scale.coeffs
    (∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i).coeffs
  change normInf params
      (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i).coeffs ≤
    normInf params E_scale.coeffs +
      normInf params
        (∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i).coeffs at h_sub
  dsimp only [bfvMulTotalNoiseBound] at h_noise
  have h_tot_noise : 2 * normInf params
      (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i).coeffs < Δ :=
    lt_of_le_of_lt
      (Nat.mul_le_mul_left 2 (le_trans h_sub (Nat.add_le_add h_scale_norm h_relin_norm)))
      h_noise
  exact bfvDecryptPoly_mul_correct params N Δ t B l hq s d0 d1 d2 E_scale a_rk e_rk
    (bfvPlainMulMod N t m1 m2) ht_le (bfvPlainMulMod_lt ht m1 m2) h_scale_phase h_tot_noise

theorem bfvDecryptPoly_bfvMul_ternary_correct (N Δ t B_1 B_2 B l B_rk : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (hB : 0 < B)
    (h2B : 2 * B ≤ params.q)
    (ht : 0 < t)
    (hΔ : Δ = params.q / t)
    (ht_le : Δ * t ≤ params.q)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hE1 : normInf params E1.coeffs ≤ B_1)
    (hE2 : normInf params E2.coeffs ≤ B_2)
    (herk : ∀ i : Fin l, normInf params (e_rk i).coeffs ≤ B_rk)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2)
    (h_noise : 2 * bfvMulTotalNoiseBound params.q N t 1 B_1 B_2 B l B_rk < Δ) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    bfvDecryptPoly params N Δ s (bfvMul params N t B l ct1 ct2 rk) =
      bfvPlainMulMod N t m1 m2 :=
  bfvDecryptPoly_bfvMul_correct params N Δ t 1 B_1 B_2 B l B_rk hq hB h2B ht hΔ ht_le
    ct1 ct2 s E1 E2 a_rk e_rk m1 m2 hm1 hm2
    (NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N s hs)
    hE1 hE2 herk h_phase1 h_phase2 h_noise

end ConcreteBFVDecryption

end BFVFHE

section ModulePKE

open scoped BigOperators

variable (R : Type*) [CommRing R]
variable (k : ℕ)

def transposeMatrix {n m : ℕ} (A : MatrixR R n m) : MatrixR R m n :=
  fun i j => A j i

def dotProductR (u v : VectorR R k) : R :=
  ∑ i : Fin k, u i * v i

theorem dotProduct_mulVec_transpose (A : MatrixR R k k) (s r : VectorR R k) :
    dotProductR R k (fun i => ∑ j : Fin k, A i j * s j) r =
      dotProductR R k s (fun j => ∑ i : Fin k, transposeMatrix R A j i * r i) := by
  dsimp [dotProductR, transposeMatrix]
  have h_lhs :
      (∑ i : Fin k, (∑ j : Fin k, A i j * s j) * r i) =
        ∑ i : Fin k, ∑ j : Fin k, A i j * s j * r i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  have h_rhs :
      (∑ j : Fin k, s j * ∑ i : Fin k, A i j * r i) =
        ∑ j : Fin k, ∑ i : Fin k, s j * (A i j * r i) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  rw [h_lhs, h_rhs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

structure ModPKEPublicKey where
  A : MatrixR R k k
  t : VectorR R k

structure ModPKECiphertext where
  u : VectorR R k
  v : R

def modPKEKeygen (A : MatrixR R k k) (s e : VectorR R k) : ModPKEPublicKey R k :=
  { A := A, t := evaluate R k k A s e }

def modPKEEncrypt (pk : ModPKEPublicKey R k) (r e1 : VectorR R k) (e2 delta_m : R) :
    ModPKECiphertext R k :=
  { u := evaluate R k k (transposeMatrix R pk.A) r e1,
    v := dotProductR R k pk.t r + e2 + delta_m }

def modPKEPhase (ct : ModPKECiphertext R k) (s : VectorR R k) : R :=
  ct.v - dotProductR R k s ct.u

theorem modPKE_phase_eq (A : MatrixR R k k) (s e r e1 : VectorR R k) (e2 delta_m : R) :
    modPKEPhase R k (modPKEEncrypt R k (modPKEKeygen R k A s e) r e1 e2 delta_m) s =
      delta_m + (dotProductR R k e r + e2 - dotProductR R k s e1) := by
  dsimp [modPKEPhase, modPKEEncrypt, modPKEKeygen]
  have h_tr :
      dotProductR R k (evaluate R k k A s e) r =
        dotProductR R k (fun i => ∑ j : Fin k, A i j * s j) r + dotProductR R k e r := by
    dsimp [dotProductR, evaluate]
    simp only [add_mul, Finset.sum_add_distrib]
  have h_su :
      dotProductR R k s (evaluate R k k (transposeMatrix R A) r e1) =
        dotProductR R k s (fun i => ∑ j : Fin k, transposeMatrix R A i j * r j) +
          dotProductR R k s e1 := by
    dsimp [dotProductR, evaluate]
    simp only [mul_add, Finset.sum_add_distrib]
  rw [h_tr, h_su, dotProduct_mulVec_transpose R k A s r]
  ring

theorem modPKE_decrypt_correct (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise : 2 * normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 (bfvEncodePoly params N Δ m)
    bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s) = m := by
  intro pk ct
  have h_phase := modPKE_phase_eq (NegacyclicPoly (Zq params) N) k A s e r e1 e2
    (bfvEncodePoly params N Δ m)
  change bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s) = m
  rw [h_phase]
  ext idx
  unfold bfvDecodePoly
  rw [NegacyclicPoly.add_coeffs]
  dsimp [bfvEncodePoly]
  set E := dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
    dotProductR (NegacyclicPoly (Zq params) N) k s e1
  have h_le : norm params (E.coeffs idx) ≤ normInf params E.coeffs :=
    Finset.le_sup (f := fun j => norm params (E.coeffs j)) (Finset.mem_univ idx)
  have h_idx_noise : 2 * norm params (E.coeffs idx) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (m idx) (E.coeffs idx) ht_le (hm idx) h_idx_noise

def bfvNoise (ct : BFVCiphertext R) (s delta_m : R) : R :=
  bfvPhase R ct s - delta_m

theorem bfvNoise_encrypt (a s e u e0 e1 delta_m : R) :
    bfvNoise R (bfvEncrypt R (bfvKeygen R a s e) u e0 e1 delta_m) s delta_m =
      e0 + e1 * s - e * u := by
  dsimp [bfvNoise]
  rw [bfvEncrypt_phase]
  ring

theorem bfvNoise_add (ct1 ct2 : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvAdd R ct1 ct2) s (dm1 + dm2) =
      bfvNoise R ct1 s dm1 + bfvNoise R ct2 s dm2 := by
  dsimp [bfvNoise]
  rw [bfvAdd_phase]
  ring

theorem bfvNoise_sub (ct1 ct2 : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvSub R ct1 ct2) s (dm1 - dm2) =
      bfvNoise R ct1 s dm1 - bfvNoise R ct2 s dm2 := by
  dsimp [bfvNoise]
  rw [bfvSub_phase]
  ring

theorem bfvNoise_addPlain (ct : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvAddPlain R ct dm2) s (dm1 + dm2) =
      bfvNoise R ct s dm1 := by
  dsimp [bfvNoise]
  rw [bfvAddPlain_phase]
  ring

theorem bfvNoise_subPlain (ct : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvSubPlain R ct dm2) s (dm1 - dm2) =
      bfvNoise R ct s dm1 := by
  dsimp [bfvNoise]
  rw [bfvSubPlain_phase]
  ring

theorem bfvNoise_mulPlain (ct : BFVCiphertext R) (s dm pt : R) :
    bfvNoise R (bfvMulPlain R ct pt) s (dm * pt) =
      bfvNoise R ct s dm * pt := by
  dsimp [bfvNoise]
  rw [bfvMulPlain_phase]
  ring

theorem bfvAdd_noise_bound (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s dm1 dm2 : NegacyclicPoly (Zq params) N) (B1 B2 : ℕ)
    (h1 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs ≤ B1)
    (h2 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs ≤ B2) :
    normInf params
      (bfvNoise (NegacyclicPoly (Zq params) N)
        (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) s (dm1 + dm2)).coeffs ≤ B1 + B2 := by
  rw [bfvNoise_add]
  have h_tri := norm_add_le params
    (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs
    (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs
  change normInf params
    ((bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs +
      (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs) ≤ B1 + B2
  omega

theorem bfvSub_noise_bound (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s dm1 dm2 : NegacyclicPoly (Zq params) N) (B1 B2 : ℕ)
    (h1 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs ≤ B1)
    (h2 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs ≤ B2) :
    normInf params
      (bfvNoise (NegacyclicPoly (Zq params) N)
        (bfvSub (NegacyclicPoly (Zq params) N) ct1 ct2) s (dm1 - dm2)).coeffs ≤ B1 + B2 := by
  rw [bfvNoise_sub]
  have h_tri := norm_sub_le params
    (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs
    (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs
  change normInf params
    ((bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs -
      (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs) ≤ B1 + B2
  omega

def modKEMEncaps {Key Coins : Type*} (params : LWEParams) (k N Δ : ℕ) [Fact (0 < N)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (m : Fin N → ℕ) : ModPKECiphertext (NegacyclicPoly (Zq params) N) k × Key :=
  let kc := G pk m
  let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
    (expandR kc.2) (expandE1 kc.2) (expandE2 kc.2) (bfvEncodePoly params N Δ m)
  (ct, kc.1)

def modKEMDecaps {Key Coins Seed : Type*} (params : LWEParams) (k N Δ : ℕ) [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) : Key :=
  let m' := bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s)
  let kc' := G pk m'
  let ct' := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
    (expandR kc'.2) (expandE1 kc'.2) (expandE2 kc'.2) (bfvEncodePoly params N Δ m')
  if ct = ct' then kc'.1 else J z ct

theorem modKEM_correctness {Key Coins Seed : Type*} (params : LWEParams) (k N Δ t : ℕ)
    [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise :
      let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
      let coins := (G pk m).2
      2 * normInf params
        (dotProductR (NegacyclicPoly (Zq params) N) k e (expandR coins) + expandE2 coins -
          dotProductR (NegacyclicPoly (Zq params) N) k s (expandE1 coins)).coeffs < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let enc := modKEMEncaps params k N Δ G expandR expandE1 expandE2 pk m
    modKEMDecaps params k N Δ G expandR expandE1 expandE2 J pk s z enc.1 = enc.2 := by
  intro pk enc
  have h_dec :
      bfvDecodePoly params N Δ
        (modPKEPhase (NegacyclicPoly (Zq params) N) k enc.1 s) = m :=
    modPKE_decrypt_correct params k N Δ t A s e
      (expandR (G pk m).2) (expandE1 (G pk m).2) (expandE2 (G pk m).2) m ht_le hm h_noise
  change (let m' := bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k enc.1 s)
    let kc' := G pk m'
    let ct' := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
      (expandR kc'.2) (expandE1 kc'.2) (expandE2 kc'.2) (bfvEncodePoly params N Δ m')
    if enc.1 = ct' then kc'.1 else J z enc.1) = (G pk m).1
  rw [h_dec]
  exact if_pos rfl

theorem modKEM_implicit_rejection {Key Coins Seed : Type*} (params : LWEParams) (k N Δ : ℕ)
    [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k)
    (h_invalid :
      let m' := bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s)
      let kc' := G pk m'
      ct ≠ modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
        (expandR kc'.2) (expandE1 kc'.2) (expandE2 kc'.2) (bfvEncodePoly params N Δ m')) :
    modKEMDecaps params k N Δ G expandR expandE1 expandE2 J pk s z ct = J z ct := by
  dsimp [modKEMDecaps]
  exact if_neg h_invalid

def modPKEEncryptionMatrix (pk : ModPKEPublicKey R k) : MatrixR R k (k + 1) :=
  Fin.snoc (α := fun _ => VectorR R k) (transposeMatrix R pk.A) pk.t

def modPKEExtendError (e1 : VectorR R k) (e2 : R) : VectorR R (k + 1) :=
  Fin.snoc (α := fun _ => R) e1 e2

def modPKECiphertextTarget (ct : ModPKECiphertext R k) (delta_m : R) : VectorR R (k + 1) :=
  Fin.snoc (α := fun _ => R) ct.u (ct.v - delta_m)

theorem modPKE_ciphertext_relation_correct (pk : ModPKEPublicKey R k)
    (r e1 : VectorR R k) (e2 delta_m : R) :
    evaluate R k (k + 1) (modPKEEncryptionMatrix R k pk) r (modPKEExtendError R k e1 e2) =
      modPKECiphertextTarget R k (modPKEEncrypt R k pk r e1 e2 delta_m) delta_m := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · dsimp [evaluate, modPKEEncryptionMatrix, modPKEExtendError, modPKECiphertextTarget,
      modPKEEncrypt, dotProductR]
    simp only [Fin.snoc_last]
    ring
  · intro j
    dsimp [evaluate, modPKEEncryptionMatrix, modPKEExtendError, modPKECiphertextTarget,
      modPKEEncrypt]
    simp only [Fin.snoc_castSucc]
    rfl

theorem verifiable_encrypt_completeness (params : LWEParams) (k N safe_bound beta : ℕ)
    [Fact (0 < N)]
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 delta_m : NegacyclicPoly (Zq params) N)
    (y_r : VectorR (NegacyclicPoly (Zq params) N) k)
    (y_e : VectorR (NegacyclicPoly (Zq params) N) (k + 1))
    (c : NegacyclicPoly (Zq params) N)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hr : ∀ j : Fin k, normInf params (r j).coeffs ≤ 1)
    (he1 : ∀ i : Fin k, normInf params (e1 i).coeffs ≤ 1)
    (he2 : normInf params e2.coeffs ≤ 1)
    (hbeta : N * 1 ≤ beta)
    (h_yr : ∀ j : Fin k, normInf params (y_r j).coeffs + beta ≤ safe_bound)
    (h_ye : ∀ i : Fin (k + 1), normInf params (y_e i).coeffs + beta ≤ safe_bound) :
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 delta_m
    let M_enc := modPKEEncryptionMatrix (NegacyclicPoly (Zq params) N) k pk
    let e_ext := modPKEExtendError (NegacyclicPoly (Zq params) N) k e1 e2
    let wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) k (k + 1) := { s := r, e := e_ext }
    let pub : ModZKPPublicInfo (NegacyclicPoly (Zq params) N) k (k + 1) :=
      { A := M_enc, t := modPKECiphertextTarget (NegacyclicPoly (Zq params) N) k ct delta_m }
    let w := modZkpCommit (NegacyclicPoly (Zq params) N) k (k + 1) M_enc y_r y_e
    let resp := modZkpRespond (NegacyclicPoly (Zq params) N) k (k + 1) y_r y_e c wit
    modZkpVerifyAlgebraic (NegacyclicPoly (Zq params) N) k (k + 1) pub c w resp ∧
    modZkpVerifyBound (NegacyclicPoly (Zq params) N) k (k + 1) resp safe_bound := by
  intro ct M_enc e_ext wit pub w resp
  constructor
  · have h_pub_eq :
        pub = mkModZKPPublicInfo (NegacyclicPoly (Zq params) N) k (k + 1) M_enc wit := by
      dsimp [pub, mkModZKPPublicInfo, wit, M_enc, e_ext, ct]
      rw [modPKE_ciphertext_relation_correct (NegacyclicPoly (Zq params) N) k pk r e1 e2 delta_m]
    rw [h_pub_eq]
    exact mod_zkp_completeness (NegacyclicPoly (Zq params) N) k (k + 1) M_enc y_r y_e c wit
  · have he_ext : ∀ i : Fin (k + 1), normInf params (e_ext i).coeffs ≤ 1 := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · dsimp [e_ext, modPKEExtendError]
        rw [Fin.snoc_last]
        exact he2
      · intro j
        dsimp [e_ext, modPKEExtendError]
        rw [Fin.snoc_castSucc]
        exact he1 j
    exact concrete_mod_zkp_respond_passes_verify k (k + 1) params N safe_bound beta 1
      y_r y_e c wit hc hr he_ext hbeta h_yr h_ye

theorem dotProductR_ternary_norm_le (params : LWEParams) (k N : ℕ) [Fact (0 < N)]
    (u v : VectorR (NegacyclicPoly (Zq params) N) k)
    (hu : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (u i))
    (hv : ∀ i : Fin k, normInf params (v i).coeffs ≤ 1) :
    normInf params (dotProductR (NegacyclicPoly (Zq params) N) k u v).coeffs ≤ k * N := by
  dsimp [dotProductR]
  have h_sum := normInf_finset_sum_poly_le params N Finset.univ (fun i : Fin k => u i * v i)
  have h_each : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      normInf params (u i * v i).coeffs ≤ N := by
    intro i _
    have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N (u i) (v i) (hu i)
    have h_v := hv i
    have h_le : N * normInf params (v i).coeffs ≤ N * 1 := Nat.mul_le_mul_left N h_v
    omega
  have h_bound := Finset.sum_le_sum h_each
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_bound
  omega

theorem modPKE_ternary_noise_bound (params : LWEParams) (k N : ℕ) [Fact (0 < N)]
    (s e r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 : NegacyclicPoly (Zq params) N)
    (hr_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (r i))
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (he1_norm : ∀ i : Fin k, normInf params (e1 i).coeffs ≤ 1)
    (he2_norm : normInf params e2.coeffs ≤ 1) :
    normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs ≤ 2 * k * N + 1 := by
  have h_comm :
      dotProductR (NegacyclicPoly (Zq params) N) k e r =
        dotProductR (NegacyclicPoly (Zq params) N) k r e := by
    dsimp [dotProductR]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [h_comm]
  have h_re := dotProductR_ternary_norm_le params k N r e hr_tern he_norm
  have h_se1 := dotProductR_ternary_norm_le params k N s e1 hs_tern he1_norm
  have h_sub :
      normInf params
        (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2 -
          dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs ≤
      normInf params (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2).coeffs +
        normInf params (dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs :=
    norm_sub_le params
      (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2).coeffs
      (dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs
  have h_add :
      normInf params (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2).coeffs ≤
        normInf params (dotProductR (NegacyclicPoly (Zq params) N) k r e).coeffs +
          normInf params e2.coeffs :=
    norm_add_le params
      (dotProductR (NegacyclicPoly (Zq params) N) k r e).coeffs
      e2.coeffs
  have h_2kn : 2 * k * N = k * N + k * N := by ring
  omega

theorem modKEM_zero_failure_correctness {Key Coins Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin k, normInf params (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf params (expandE2 c).coeffs ≤ 1)
    (h_zero_fail : 2 * (2 * k * N + 1) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let enc := modKEMEncaps params k N Δ G expandR expandE1 expandE2 pk m
    modKEMDecaps params k N Δ G expandR expandE1 expandE2 J pk s z enc.1 = enc.2 := by
  intro pk enc
  apply modKEM_correctness params k N Δ t G expandR expandE1 expandE2 J A s e z m ht_le hm
  dsimp
  set coins := (G (modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e) m).2
  have h_bound := modPKE_ternary_noise_bound params k N s e
    (expandR coins) (expandE1 coins) (expandE2 coins)
    (hr_tern coins) hs_tern he_norm (he1_norm coins) (he2_norm coins)
  omega

end ModulePKE

section BFVModSwitchAndGalois

open scoped BigOperators

def bfvModSwitchCoeff (q q_new c : ℕ) : ℕ :=
  (q_new * c + q / 2) / q

def bfvModSwitchRem (q q_new c : ℕ) : ℕ :=
  (q_new * c + q / 2) % q

theorem bfvModSwitchCoeff_eq (q q_new c : ℕ) :
    q * bfvModSwitchCoeff q q_new c + bfvModSwitchRem q q_new c = q_new * c + q / 2 := by
  dsimp [bfvModSwitchCoeff, bfvModSwitchRem]
  exact Nat.div_add_mod (q_new * c + q / 2) q

theorem bfvModSwitchRem_lt (q q_new c : ℕ) (hq : 0 < q) :
    bfvModSwitchRem q q_new c < q := by
  dsimp [bfvModSwitchRem]
  exact Nat.mod_lt (q_new * c + q / 2) hq

theorem bfvModSwitch_error_bound (q q_new c : ℕ) (hq : 0 < q) :
    -((q - 1 - q / 2 : ℕ) : ℤ) ≤
      (q : ℤ) * (bfvModSwitchCoeff q q_new c : ℤ) - (q_new : ℤ) * (c : ℤ) ∧
    (q : ℤ) * (bfvModSwitchCoeff q q_new c : ℤ) - (q_new : ℤ) * (c : ℤ) ≤
      ((q / 2 : ℕ) : ℤ) := by
  have h_eq := bfvModSwitchCoeff_eq q q_new c
  have h_lt := bfvModSwitchRem_lt q q_new c hq
  omega

structure GaloisKey (R : Type*) (l : ℕ) where
  a_gk : VectorR R l
  b_gk : VectorR R l

def mkBFVGaloisKey (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (a_gk e_gk : VectorR R l) (s : R) (G : VectorR R l) : GaloisKey R l :=
  { a_gk := a_gk,
    b_gk := fun i => -(a_gk i * s + e_gk i) + G i * σ s }

def bfvApplyGalois (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (ct : BFVCiphertext R) (decomp : R → VectorR R l)
    (gk : GaloisKey R l) : BFVCiphertext R :=
  let c1_dec := decomp (σ ct.c1)
  { c0 := σ ct.c0 + (∑ i, c1_dec i * gk.b_gk i),
    c1 := ∑ i, c1_dec i * gk.a_gk i }

theorem bfvApplyGalois_phase (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (ct : BFVCiphertext R) (s : R)
    (a_gk e_gk G : VectorR R l) (decomp : R → VectorR R l)
    (h_dec : IsValidDecomposition G decomp) :
    let gk := mkBFVGaloisKey R σ a_gk e_gk s G
    bfvPhase R (bfvApplyGalois R σ ct decomp gk) s =
      σ (bfvPhase R ct s) - (∑ i, decomp (σ ct.c1) i * e_gk i) := by
  dsimp [mkBFVGaloisKey, bfvApplyGalois, bfvPhase]
  rw [map_add, map_mul]
  simp only [sub_eq_add_neg, neg_add, mul_add, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have h1 : (∑ i : Fin l, decomp (σ ct.c1) i * (a_gk i * s)) =
      (∑ i : Fin l, decomp (σ ct.c1) i * a_gk i) * s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  have h2 : (∑ i : Fin l, decomp (σ ct.c1) i * (G i * σ s)) =
      (∑ i : Fin l, decomp (σ ct.c1) i * G i) * σ s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  rw [h1, h2, h_dec (σ ct.c1)]
  ring

theorem bfvNoise_applyGalois (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (ct : BFVCiphertext R) (s dm : R)
    (a_gk e_gk G : VectorR R l) (decomp : R → VectorR R l)
    (h_dec : IsValidDecomposition G decomp) :
    let gk := mkBFVGaloisKey R σ a_gk e_gk s G
    bfvNoise R (bfvApplyGalois R σ ct decomp gk) s (σ dm) =
      σ (bfvNoise R ct s dm) - (∑ i, decomp (σ ct.c1) i * e_gk i) := by
  dsimp [bfvNoise]
  rw [bfvApplyGalois_phase R σ ct s a_gk e_gk G decomp h_dec, map_sub]
  ring

theorem bfvDecryptPoly_applyGalois_correct (params : LWEParams) (N Δ t : ℕ) {l : ℕ} [Fact (0 < N)]
    (σ : NegacyclicPoly (Zq params) N →+* NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (a_gk e_gk G : VectorR (NegacyclicPoly (Zq params) N) l)
    (decomp : NegacyclicPoly (Zq params) N → VectorR (NegacyclicPoly (Zq params) N) l)
    (m m_gal : Fin N → ℕ)
    (h_dec : IsValidDecomposition G decomp)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m_gal k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (h_encode_gal : σ (bfvEncodePoly params N Δ m) = bfvEncodePoly params N Δ m_gal)
    (h_noise : 2 * normInf params
      (σ E - (∑ i, decomp (σ ct.c1) i * e_gk i)).coeffs < Δ) :
    let gk := mkBFVGaloisKey (NegacyclicPoly (Zq params) N) σ a_gk e_gk s G
    bfvDecryptPoly params N Δ s
      (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct decomp gk) = m_gal := by
  intro gk
  have h_phase_gal :
      bfvPhase (NegacyclicPoly (Zq params) N)
        (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct decomp gk) s =
        bfvEncodePoly params N Δ m_gal +
          (σ E - (∑ i, decomp (σ ct.c1) i * e_gk i)) := by
    rw [bfvApplyGalois_phase (NegacyclicPoly (Zq params) N) σ ct s a_gk e_gk G decomp h_dec,
      h_phase, map_add, h_encode_gal]
    ring
  exact bfvDecryptPoly_of_phase_eq params N Δ t s
    (σ E - (∑ i, decomp (σ ct.c1) i * e_gk i))
    (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct decomp gk)
    m_gal ht_le hm h_phase_gal h_noise

def bfvPlainGaloisMod (N t g : ℕ) (m : Fin N → ℕ) : Fin N → ℕ :=
  fun k =>
    ((NegacyclicPoly.negacyclicEvalPow g
      (⟨fun i => (m i : ℤ)⟩ : NegacyclicPoly ℤ N)).coeffs k % (t : ℤ)).toNat

theorem bfvPlainGaloisMod_lt {N t g : ℕ} (ht : 0 < t) (m : Fin N → ℕ) (k : Fin N) :
    bfvPlainGaloisMod N t g m k < t := by
  dsimp [bfvPlainGaloisMod]
  have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
  have h0 := Int.emod_nonneg
    ((NegacyclicPoly.negacyclicEvalPow g
      (⟨fun i => (m i : ℤ)⟩ : NegacyclicPoly ℤ N)).coeffs k) (ne_of_gt ht_pos)
  have hlt := Int.emod_lt_of_pos
    ((NegacyclicPoly.negacyclicEvalPow g
      (⟨fun i => (m i : ℤ)⟩ : NegacyclicPoly ℤ N)).coeffs k) ht_pos
  omega

lemma intCastPolyHom_negacyclicEvalPow (params : LWEParams) (N g : ℕ) [Fact (0 < N)]
    (P : NegacyclicPoly ℤ N) :
    NegacyclicPoly.intCastPolyHom params N (NegacyclicPoly.negacyclicEvalPow g P) =
      NegacyclicPoly.negacyclicEvalPow g (NegacyclicPoly.intCastPolyHom params N P) := by
  ext k
  rw [NegacyclicPoly.intCastPolyHom_coeffs, NegacyclicPoly.negacyclicEvalPow_coeffs,
    NegacyclicPoly.negacyclicEvalPow_coeffs, NegacyclicPoly.intCast_finset_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · rw [Int.cast_mul]
    congr 1
    unfold NegacyclicPoly.negacyclicSign
    rw [Int.cast_pow, Int.cast_neg, Int.cast_one]
  · rw [Int.cast_zero]

theorem bfvDecryptPoly_applyGalois_mod_t_correct (params : LWEParams) (N Δ t g B l B_gk : ℕ)
    [Fact (0 < N)]
    (hg : Odd g)
    (hcop : Nat.Coprime g N)
    (hq : params.q ≤ B ^ l)
    (hB : 0 < B)
    (h2B : 2 * B ≤ params.q)
    (ht : 0 < t)
    (ht_le : Δ * t ≤ params.q)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (a_gk e_gk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (hegk : ∀ i : Fin l, normInf params (e_gk i).coeffs ≤ B_gk)
    (h_noise : 2 * (normInf params E.coeffs + (params.q - Δ * t) + l * (N * (B - 1) * B_gk)) < Δ) :
    let σ := NegacyclicPoly.negacyclicGaloisHom (R := Zq params) (N := N) g hg
    let gk := mkBFVGaloisKey (NegacyclicPoly (Zq params) N) σ a_gk e_gk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    bfvDecryptPoly params N Δ s
        (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct
          (NegacyclicPoly.negacyclicDecomp params N B l) gk) =
      bfvPlainGaloisMod N t g m := by
  intro σ gk
  let r_q : ℕ := params.q - Δ * t
  let M : NegacyclicPoly ℤ N := ⟨fun i => (m i : ℤ)⟩
  let M_gal : NegacyclicPoly ℤ N := NegacyclicPoly.negacyclicEvalPow g M
  let Q_gal : NegacyclicPoly ℤ N := ⟨fun k => M_gal.coeffs k / (t : ℤ)⟩
  let P_gal : NegacyclicPoly ℤ N := ⟨fun k => M_gal.coeffs k % (t : ℤ)⟩
  have hM_norm : NegacyclicPoly.intPolyNormInf M ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M]
    apply Finset.sup_le
    intro k _
    have hk := hm k
    omega
  have hM_gal_norm : NegacyclicPoly.intPolyNormInf M_gal ≤ t - 1 :=
    le_trans (NegacyclicPoly.intPolyNormInf_negacyclicEvalPow_le hcop M) hM_norm
  have hQ_gal_norm : NegacyclicPoly.intPolyNormInf Q_gal ≤ 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, Q_gal]
    apply Finset.sup_le
    intro k _
    have hk_le := le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf M_gal k) hM_gal_norm
    have h_div := ediv_natAbs_le ht hk_le
    have h_lt2 : (t - 1) + (t - 1) < t * 2 := by omega
    have h_le1 : ((t - 1) + (t - 1)) / t ≤ 1 :=
      Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul h_lt2)
    omega
  have h_split : M_gal = (t : NegacyclicPoly ℤ N) * Q_gal + P_gal := by
    ext k
    rw [NegacyclicPoly.add_coeffs]
    change M_gal.coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * Q_gal).coeffs k + P_gal.coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    dsimp [Q_gal, P_gal]
    rw [add_comm]
    exact (Int.emod_add_mul_ediv (M_gal.coeffs k) (t : ℤ)).symm
  have h_dt : (Δ : NegacyclicPoly ℤ N) * (t : NegacyclicPoly ℤ N) =
      (params.q : NegacyclicPoly ℤ N) - (r_q : NegacyclicPoly ℤ N) := by
    have hq_nat : Δ * t + r_q = params.q := by omega
    have h_cast := congrArg (fun n : ℕ => (n : NegacyclicPoly ℤ N)) hq_nat
    push_cast at h_cast
    exact eq_sub_of_add_eq h_cast
  have hP_eq :
      NegacyclicPoly.intCastPolyHom params N ((Δ : NegacyclicPoly ℤ N) * P_gal) =
        bfvEncodePoly params N Δ (bfvPlainGaloisMod N t g m) := by
    have hP_coeffs : P_gal = ⟨fun k => (bfvPlainGaloisMod N t g m k : ℤ)⟩ := by
      ext k
      dsimp [P_gal, bfvPlainGaloisMod, M_gal, M]
      have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
      exact (Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt ht_pos))).symm
    rw [hP_coeffs]
    exact intCastPolyHom_const_nat params N Δ (bfvPlainGaloisMod N t g m)
  let D_gal : NegacyclicPoly (Zq params) N :=
    -(NegacyclicPoly.intCastPolyHom params N ((r_q : NegacyclicPoly ℤ N) * Q_gal))
  have h_encode_gal :
      σ (bfvEncodePoly params N Δ m) =
        bfvEncodePoly params N Δ (bfvPlainGaloisMod N t g m) + D_gal := by
    have h_sigma_eq : σ (bfvEncodePoly params N Δ m) =
        NegacyclicPoly.intCastPolyHom params N
          (NegacyclicPoly.negacyclicGaloisHom (R := ℤ) (N := N) g hg
            ((Δ : NegacyclicPoly ℤ N) * M)) := by
      rw [← intCastPolyHom_const_nat params N Δ m]
      change NegacyclicPoly.negacyclicEvalPow g _ = _
      rw [← intCastPolyHom_negacyclicEvalPow]
      rfl
    have h_gal_mul :
        NegacyclicPoly.negacyclicGaloisHom (R := ℤ) (N := N) g hg
            ((Δ : NegacyclicPoly ℤ N) * M) =
          (Δ : NegacyclicPoly ℤ N) * M_gal := by
      rw [map_mul, map_natCast]
      rfl
    have h_id : (Δ : NegacyclicPoly ℤ N) * M_gal =
        (params.q : NegacyclicPoly ℤ N) * Q_gal + (Δ : NegacyclicPoly ℤ N) * P_gal -
          (r_q : NegacyclicPoly ℤ N) * Q_gal := by
      calc
        (Δ : NegacyclicPoly ℤ N) * M_gal
          = (Δ : NegacyclicPoly ℤ N) * ((t : NegacyclicPoly ℤ N) * Q_gal + P_gal) := by
            rw [h_split]
        _ = ((Δ : NegacyclicPoly ℤ N) * (t : NegacyclicPoly ℤ N)) * Q_gal +
              (Δ : NegacyclicPoly ℤ N) * P_gal := by ring
        _ = ((params.q : NegacyclicPoly ℤ N) - (r_q : NegacyclicPoly ℤ N)) * Q_gal +
              (Δ : NegacyclicPoly ℤ N) * P_gal := by rw [h_dt]
        _ = (params.q : NegacyclicPoly ℤ N) * Q_gal + (Δ : NegacyclicPoly ℤ N) * P_gal -
              (r_q : NegacyclicPoly ℤ N) * Q_gal := by ring
    rw [h_sigma_eq, h_gal_mul, h_id, map_sub, map_add, map_mul,
      NegacyclicPoly.intCastPolyHom_q_zero, zero_mul, zero_add, hP_eq, sub_eq_add_neg]
  have hD_norm : normInf params D_gal.coeffs ≤ r_q := by
    change normInf params
      (-((NegacyclicPoly.intCastPolyHom params N ((r_q : NegacyclicPoly ℤ N) * Q_gal)).coeffs)) ≤
      r_q
    rw [norm_neg]
    have h1 := NegacyclicPoly.normInf_intCastPolyHom_le params N
      ((r_q : NegacyclicPoly ℤ N) * Q_gal)
    have h_rq_mul : (r_q : NegacyclicPoly ℤ N) * Q_gal =
        NegacyclicPoly.constPoly (r_q : ℤ) * Q_gal := rfl
    have h2 : NegacyclicPoly.intPolyNormInf ((r_q : NegacyclicPoly ℤ N) * Q_gal) ≤
        r_q * NegacyclicPoly.intPolyNormInf Q_gal := by
      rw [h_rq_mul]
      have h_cm := NegacyclicPoly.intPolyNormInf_constPoly_mul_le (N := N) (r_q : ℤ) Q_gal
      rwa [Int.natAbs_natCast] at h_cm
    have h3 : r_q * NegacyclicPoly.intPolyNormInf Q_gal ≤ r_q * 1 :=
      Nat.mul_le_mul_left r_q hQ_gal_norm
    omega
  have h_sig_E : normInf params (σ E).coeffs = normInf params E.coeffs := by
    change normInf params (NegacyclicPoly.negacyclicGaloisEquiv g hg hcop E).coeffs =
      normInf params E.coeffs
    exact NegacyclicPoly.normInf_negacyclicGaloisEquiv params N g hg hcop E
  have h_gk_noise := NegacyclicPoly.normInf_gadgetRelin_noise_le params N B l B_gk hB h2B
    (σ ct.c1) e_gk hegk
  have h_phase_gal :
      bfvPhase (NegacyclicPoly (Zq params) N)
          (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct
            (NegacyclicPoly.negacyclicDecomp params N B l) gk) s =
        bfvEncodePoly params N Δ (bfvPlainGaloisMod N t g m) +
          (σ E + D_gal -
            ∑ i, NegacyclicPoly.negacyclicDecomp params N B l (σ ct.c1) i * e_gk i) := by
    have h_ap := bfvApplyGalois_phase (NegacyclicPoly (Zq params) N) σ ct s a_gk e_gk
      (NegacyclicPoly.negacyclicGadget params N B l)
      (NegacyclicPoly.negacyclicDecomp params N B l)
      (NegacyclicPoly.negacyclicDecomp_isValid params N B l hq)
    dsimp only at h_ap
    change bfvPhase (NegacyclicPoly (Zq params) N)
      (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct
        (NegacyclicPoly.negacyclicDecomp params N B l) gk) s = _ at h_ap
    rw [h_ap, h_phase, map_add, h_encode_gal]
    ring
  have h_tri1 := norm_sub_le params (σ E + D_gal).coeffs
    (∑ i, NegacyclicPoly.negacyclicDecomp params N B l (σ ct.c1) i * e_gk i).coeffs
  have h_tri2 := norm_add_le params (σ E).coeffs D_gal.coeffs
  change normInf params
      (σ E + D_gal -
        ∑ i, NegacyclicPoly.negacyclicDecomp params N B l (σ ct.c1) i * e_gk i).coeffs ≤
    normInf params (σ E + D_gal).coeffs +
      normInf params
        (∑ i, NegacyclicPoly.negacyclicDecomp params N B l (σ ct.c1) i * e_gk i).coeffs
      at h_tri1
  change normInf params (σ E + D_gal).coeffs ≤
    normInf params (σ E).coeffs + normInf params D_gal.coeffs at h_tri2
  rw [h_sig_E] at h_tri2
  dsimp only [r_q] at hD_norm
  have h_tot_noise : 2 * normInf params
      (σ E + D_gal -
        ∑ i, NegacyclicPoly.negacyclicDecomp params N B l (σ ct.c1) i * e_gk i).coeffs < Δ :=
    lt_of_le_of_lt
      (Nat.mul_le_mul_left 2
        (le_trans h_tri1
          (Nat.add_le_add (le_trans h_tri2 (Nat.add_le_add_left hD_norm _)) h_gk_noise)))
      h_noise
  exact bfvDecryptPoly_of_phase_eq params N Δ t s
    (σ E + D_gal - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l (σ ct.c1) i * e_gk i)
    (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct
      (NegacyclicPoly.negacyclicDecomp params N B l) gk)
    (bfvPlainGaloisMod N t g m) ht_le (bfvPlainGaloisMod_lt ht m) h_phase_gal h_tot_noise

def bfvModSwitchElemCentered (params params_new : LWEParams) (x : Zq params) : Zq params_new :=
  Int.cast (divRoundInt ((params_new.q : ℤ) * centeredLift params x) params.q)

def bfvModSwitchPolyCentered (params params_new : LWEParams) (N : ℕ)
    (p : NegacyclicPoly (Zq params) N) : NegacyclicPoly (Zq params_new) N :=
  ⟨fun k => bfvModSwitchElemCentered params params_new (p.coeffs k)⟩

def bfvModSwitchCiphertext (params params_new : LWEParams) (N : ℕ)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N)) :
    BFVCiphertext (NegacyclicPoly (Zq params_new) N) :=
  { c0 := bfvModSwitchPolyCentered params params_new N ct.c0,
    c1 := bfvModSwitchPolyCentered params params_new N ct.c1 }

def liftPolyToModulus (params params_new : LWEParams) (N : ℕ)
    (s : NegacyclicPoly (Zq params) N) : NegacyclicPoly (Zq params_new) N :=
  ⟨fun k => Int.cast (centeredLift params (s.coeffs k))⟩

def bfvModSwitchNoiseBound (q q_new N Δ Δ_new t B_s B_e : ℕ) : ℕ :=
  ((((q_new : ℤ) - (Δ_new : ℤ) * (t : ℤ)) * (Δ : ℤ) -
      ((q : ℤ) - (Δ : ℤ) * (t : ℤ)) * (Δ_new : ℤ)).natAbs * (t - 1) +
    q_new * B_e + (N * B_s + 1) * (q / 2)) / q

theorem bfvModSwitch_phase_bound (params params_new : LWEParams) (N Δ Δ_new t B_s B_e : ℕ)
    [Fact (0 < N)]
    (ht_le : Δ * t ≤ params.q)
    (ht_new_le : Δ_new * t ≤ params_new.q)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : normInf params s.coeffs ≤ B_s)
    (hE : normInf params E.coeffs ≤ B_e)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E) :
    ∃ E_sw : NegacyclicPoly (Zq params_new) N,
      bfvPhase (NegacyclicPoly (Zq params_new) N)
          (bfvModSwitchCiphertext params params_new N ct)
          (liftPolyToModulus params params_new N s) =
        bfvEncodePoly params_new N Δ_new m + E_sw ∧
      normInf params_new E_sw.coeffs ≤
        bfvModSwitchNoiseBound params.q params_new.q N Δ Δ_new t B_s B_e := by
  let q : ℕ := params.q
  let q_new : ℕ := params_new.q
  let r_q : ℕ := q - Δ * t
  let r_new : ℕ := q_new - Δ_new * t
  have hq_pos : 0 < q := params.q_pos.out
  let C0 := NegacyclicPoly.liftPolyCentered params N ct.c0
  let C1 := NegacyclicPoly.liftPolyCentered params N ct.c1
  let S := NegacyclicPoly.liftPolyCentered params N s
  let E_hat := NegacyclicPoly.liftPolyCentered params N E
  let M : NegacyclicPoly ℤ N := ⟨fun k => (m k : ℤ)⟩
  rcases bfv_phase_wrap_decomp params N Δ t B_s B_e ct s E m hm hs hE h_phase with
    ⟨K, hK_eq, _⟩
  let C0' : NegacyclicPoly ℤ N :=
    ⟨fun k => divRoundInt ((q_new : ℤ) * C0.coeffs k) q⟩
  let C1' : NegacyclicPoly ℤ N :=
    ⟨fun k => divRoundInt ((q_new : ℤ) * C1.coeffs k) q⟩
  let τ0 : NegacyclicPoly ℤ N :=
    (q : NegacyclicPoly ℤ N) * C0' - (q_new : NegacyclicPoly ℤ N) * C0
  let τ1 : NegacyclicPoly ℤ N :=
    (q : NegacyclicPoly ℤ N) * C1' - (q_new : NegacyclicPoly ℤ N) * C1
  have h_tau_le : ∀ (C_p C_p' τ_p : NegacyclicPoly ℤ N),
      C_p' = ⟨fun k => divRoundInt ((q_new : ℤ) * C_p.coeffs k) q⟩ →
      τ_p = (q : NegacyclicPoly ℤ N) * C_p' - (q_new : NegacyclicPoly ℤ N) * C_p →
      NegacyclicPoly.intPolyNormInf τ_p ≤ q / 2 := by
    intro C_p C_p' τ_p hCp' hτp
    subst hCp' hτp
    change Finset.univ.sup (fun k =>
      (((q : NegacyclicPoly ℤ N) * ⟨fun j => divRoundInt ((q_new : ℤ) * C_p.coeffs j) q⟩ -
        (q_new : NegacyclicPoly ℤ N) * C_p).coeffs k).natAbs) ≤ q / 2
    apply Finset.sup_le
    intro k _
    rw [NegacyclicPoly.sub_coeffs]
    change ((NegacyclicPoly.constPoly (q : ℤ) * _).coeffs k -
        (NegacyclicPoly.constPoly (q_new : ℤ) * C_p).coeffs k).natAbs ≤ q / 2
    rw [NegacyclicPoly.constPoly_mul_coeffs, NegacyclicPoly.constPoly_mul_coeffs]
    exact divRoundInt_mul_sub_bounds hq_pos ((q_new : ℤ) * C_p.coeffs k)
  have hτ0 : NegacyclicPoly.intPolyNormInf τ0 ≤ q / 2 := h_tau_le C0 C0' τ0 rfl rfl
  have hτ1 : NegacyclicPoly.intPolyNormInf τ1 ≤ q / 2 := h_tau_le C1 C1' τ1 rfl rfl
  let δ_scale : ℤ := (r_new : ℤ) * (Δ : ℤ) - (r_q : ℤ) * (Δ_new : ℤ)
  have h_q_scale : (q_new : NegacyclicPoly ℤ N) * (Δ : NegacyclicPoly ℤ N) =
      (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) +
        (δ_scale : NegacyclicPoly ℤ N) := by
    have h_z : (q_new : ℤ) * (Δ : ℤ) = (q : ℤ) * (Δ_new : ℤ) + δ_scale := by
      have h1 : (q : ℤ) = (Δ : ℤ) * (t : ℤ) + (r_q : ℤ) := by omega
      have h2 : (q_new : ℤ) = (Δ_new : ℤ) * (t : ℤ) + (r_new : ℤ) := by omega
      rw [h1, h2]
      dsimp [δ_scale]
      ring
    have h_c := congrArg (fun z : ℤ => (z : NegacyclicPoly ℤ N)) h_z
    push_cast at h_c
    exact h_c
  let E_sw_z : NegacyclicPoly ℤ N :=
    (C0' + C1' * S) - ((Δ_new : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * K)
  have h_qE_sw : (q : NegacyclicPoly ℤ N) * E_sw_z =
      (δ_scale : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * E_hat +
        (τ0 + τ1 * S) := by
    have h0 : (q : NegacyclicPoly ℤ N) * C0' = (q_new : NegacyclicPoly ℤ N) * C0 + τ0 := by
      dsimp [τ0]; ring
    have h1 : (q : NegacyclicPoly ℤ N) * C1' = (q_new : NegacyclicPoly ℤ N) * C1 + τ1 := by
      dsimp [τ1]; ring
    calc
      (q : NegacyclicPoly ℤ N) * E_sw_z
        = (q : NegacyclicPoly ℤ N) * C0' + ((q : NegacyclicPoly ℤ N) * C1') * S -
            (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) * M -
            (q : NegacyclicPoly ℤ N) * (q_new : NegacyclicPoly ℤ N) * K := by
          dsimp [E_sw_z]; ring
      _ = ((q_new : NegacyclicPoly ℤ N) * C0 + τ0) +
            ((q_new : NegacyclicPoly ℤ N) * C1 + τ1) * S -
            (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) * M -
            (q : NegacyclicPoly ℤ N) * (q_new : NegacyclicPoly ℤ N) * K := by rw [h0, h1]
      _ = (q_new : NegacyclicPoly ℤ N) * (C0 + C1 * S) + (τ0 + τ1 * S) -
            (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) * M -
            (q : NegacyclicPoly ℤ N) * (q_new : NegacyclicPoly ℤ N) * K := by ring
      _ = (q_new : NegacyclicPoly ℤ N) *
              ((Δ : NegacyclicPoly ℤ N) * M + E_hat + (q : NegacyclicPoly ℤ N) * K) +
            (τ0 + τ1 * S) -
            (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) * M -
            (q : NegacyclicPoly ℤ N) * (q_new : NegacyclicPoly ℤ N) * K := by rw [hK_eq]
      _ = ((q_new : NegacyclicPoly ℤ N) * (Δ : NegacyclicPoly ℤ N)) * M +
            (q_new : NegacyclicPoly ℤ N) * E_hat + (τ0 + τ1 * S) -
            (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) * M := by ring
      _ = ((q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) +
              (δ_scale : NegacyclicPoly ℤ N)) * M +
            (q_new : NegacyclicPoly ℤ N) * E_hat + (τ0 + τ1 * S) -
            (q : NegacyclicPoly ℤ N) * (Δ_new : NegacyclicPoly ℤ N) * M := by rw [h_q_scale]
      _ = (δ_scale : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * E_hat +
            (τ0 + τ1 * S) := by ring
  have hM_norm : NegacyclicPoly.intPolyNormInf M ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M]
    apply Finset.sup_le
    intro k _
    have hk := hm k
    omega
  have hS_norm : NegacyclicPoly.intPolyNormInf S ≤ B_s := hs
  have hE_norm : NegacyclicPoly.intPolyNormInf E_hat ≤ B_e := hE
  have hδM : NegacyclicPoly.intPolyNormInf ((δ_scale : NegacyclicPoly ℤ N) * M) ≤
      δ_scale.natAbs * (t - 1) :=
    le_trans (NegacyclicPoly.intPolyNormInf_intCast_mul_le δ_scale M)
      (Nat.mul_le_mul_left δ_scale.natAbs hM_norm)
  have hqE :
      NegacyclicPoly.intPolyNormInf ((q_new : NegacyclicPoly ℤ N) * E_hat) ≤ q_new * B_e := by
    have h_eq : (q_new : NegacyclicPoly ℤ N) * E_hat =
        NegacyclicPoly.constPoly (q_new : ℤ) * E_hat := rfl
    rw [h_eq]
    have h_cm := NegacyclicPoly.intPolyNormInf_constPoly_mul_le (N := N) (q_new : ℤ) E_hat
    rw [Int.natAbs_natCast] at h_cm
    exact le_trans h_cm (Nat.mul_le_mul_left q_new hE_norm)
  have hτ1S : NegacyclicPoly.intPolyNormInf (τ1 * S) ≤ N * (q / 2) * B_s :=
    le_trans (NegacyclicPoly.intPolyNormInf_mul_le τ1 S)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hτ1) hS_norm)
  have hτ_sum : NegacyclicPoly.intPolyNormInf (τ0 + τ1 * S) ≤ (N * B_s + 1) * (q / 2) := by
    have h_add := NegacyclicPoly.intPolyNormInf_add_le τ0 (τ1 * S)
    have h_mul_eq : N * (q / 2) * B_s + q / 2 = (N * B_s + 1) * (q / 2) := by ring
    omega
  have h_rhs_norm :
      NegacyclicPoly.intPolyNormInf
          ((δ_scale : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * E_hat +
            (τ0 + τ1 * S)) ≤
        δ_scale.natAbs * (t - 1) + q_new * B_e + (N * B_s + 1) * (q / 2) := by
    have h1 := NegacyclicPoly.intPolyNormInf_add_le
      ((δ_scale : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * E_hat) (τ0 + τ1 * S)
    have h2 := NegacyclicPoly.intPolyNormInf_add_le
      ((δ_scale : NegacyclicPoly ℤ N) * M) ((q_new : NegacyclicPoly ℤ N) * E_hat)
    omega
  have hE_sw_norm : NegacyclicPoly.intPolyNormInf E_sw_z ≤
      (δ_scale.natAbs * (t - 1) + q_new * B_e + (N * B_s + 1) * (q / 2)) / q := by
    dsimp [NegacyclicPoly.intPolyNormInf]
    apply Finset.sup_le
    intro k _
    have hk := congrArg (fun p => p.coeffs k) h_qE_sw
    have h_cm : ((q : NegacyclicPoly ℤ N) * E_sw_z).coeffs k = (q : ℤ) * E_sw_z.coeffs k :=
      NegacyclicPoly.constPoly_mul_coeffs (R := ℤ) (q : ℤ) E_sw_z k
    rw [h_cm] at hk
    exact natAbs_le_div_of_mul_eq hq_pos hk
      (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf _ k) h_rhs_norm)
  let E_sw : NegacyclicPoly (Zq params_new) N :=
    NegacyclicPoly.intCastPolyHom params_new N E_sw_z
  refine ⟨E_sw, ?_, ?_⟩
  · have h_recombine : C0' + C1' * S =
        (Δ_new : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * K + E_sw_z := by
      dsimp [E_sw_z]
      ring
    have hc0_hom : bfvModSwitchPolyCentered params params_new N ct.c0 =
        NegacyclicPoly.intCastPolyHom params_new N C0' := rfl
    have hc1_hom : bfvModSwitchPolyCentered params params_new N ct.c1 =
        NegacyclicPoly.intCastPolyHom params_new N C1' := rfl
    have hs_hom : liftPolyToModulus params params_new N s =
        NegacyclicPoly.intCastPolyHom params_new N S := rfl
    calc
      bfvPhase (NegacyclicPoly (Zq params_new) N)
          (bfvModSwitchCiphertext params params_new N ct)
          (liftPolyToModulus params params_new N s)
        = NegacyclicPoly.intCastPolyHom params_new N (C0' + C1' * S) := by
          dsimp [bfvPhase, bfvModSwitchCiphertext]
          rw [hc0_hom, hc1_hom, hs_hom, map_add, map_mul]
      _ = NegacyclicPoly.intCastPolyHom params_new N
            ((Δ_new : NegacyclicPoly ℤ N) * M + (q_new : NegacyclicPoly ℤ N) * K + E_sw_z) := by
          rw [h_recombine]
      _ = bfvEncodePoly params_new N Δ_new m + E_sw := by
          rw [map_add, map_add, intCastPolyHom_const_nat, map_mul,
            NegacyclicPoly.intCastPolyHom_q_zero, zero_mul, add_zero]
  · have h_le := NegacyclicPoly.normInf_intCastPolyHom_le params_new N E_sw_z
    have hr_new_z : (r_new : ℤ) = (q_new : ℤ) - (Δ_new : ℤ) * (t : ℤ) := by
      dsimp [r_new]
      rw [Nat.cast_sub ht_new_le, Nat.cast_mul]
    have hr_q_z : (r_q : ℤ) = (q : ℤ) - (Δ : ℤ) * (t : ℤ) := by
      dsimp [r_q]
      rw [Nat.cast_sub ht_le, Nat.cast_mul]
    have hδ_eq :
        δ_scale = ((q_new : ℤ) - (Δ_new : ℤ) * (t : ℤ)) * (Δ : ℤ) -
          ((q : ℤ) - (Δ : ℤ) * (t : ℤ)) * (Δ_new : ℤ) := by
      dsimp [δ_scale]
      rw [hr_new_z, hr_q_z]
    dsimp only [q, q_new] at hδ_eq
    dsimp [bfvModSwitchNoiseBound, E_sw]
    rw [← hδ_eq]
    exact le_trans h_le hE_sw_norm

theorem bfvDecryptPoly_modSwitch_correct (params params_new : LWEParams) (N Δ Δ_new t B_s B_e : ℕ)
    [Fact (0 < N)]
    (ht_le : Δ * t ≤ params.q)
    (ht_new_le : Δ_new * t ≤ params_new.q)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : normInf params s.coeffs ≤ B_s)
    (hE : normInf params E.coeffs ≤ B_e)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (h_noise :
      2 * bfvModSwitchNoiseBound params.q params_new.q N Δ Δ_new t B_s B_e < Δ_new) :
    bfvDecryptPoly params_new N Δ_new (liftPolyToModulus params params_new N s)
      (bfvModSwitchCiphertext params params_new N ct) = m := by
  rcases bfvModSwitch_phase_bound params params_new N Δ Δ_new t B_s B_e ht_le ht_new_le
    ct s E m hm hs hE h_phase with ⟨E_sw, h_sw_phase, h_sw_norm⟩
  have h_tot : 2 * normInf params_new E_sw.coeffs < Δ_new := by omega
  exact bfvDecryptPoly_of_phase_eq params_new N Δ_new t
    (liftPolyToModulus params params_new N s) E_sw
    (bfvModSwitchCiphertext params params_new N ct) m ht_new_le hm h_sw_phase h_tot

theorem bfvDecryptPoly_modSwitch_ternary_correct
    (params params_new : LWEParams) (N Δ Δ_new t B_e : ℕ) [Fact (0 < N)]
    (ht_le : Δ * t ≤ params.q)
    (ht_new_le : Δ_new * t ≤ params_new.q)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hE : normInf params E.coeffs ≤ B_e)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (h_noise :
      2 * bfvModSwitchNoiseBound params.q params_new.q N Δ Δ_new t 1 B_e < Δ_new) :
    bfvDecryptPoly params_new N Δ_new (liftPolyToModulus params params_new N s)
      (bfvModSwitchCiphertext params params_new N ct) = m :=
  bfvDecryptPoly_modSwitch_correct params params_new N Δ Δ_new t 1 B_e ht_le ht_new_le
    ct s E m hm (NegacyclicPoly.normInf_le_one_of_isTernaryPoly params N s hs) hE h_phase h_noise

end BFVModSwitchAndGalois

section StandardLWERegev

open scoped BigOperators

def samplePhase (R : Type*) [CommRing R] {n m : ℕ}
    (c : Sample R n m) (s : VectorR R n) : VectorR R m :=
  fun i => c.b i - ∑ j : Fin n, c.A i j * s j

def regevEncrypt (params : LWEParams) (Δ : ℕ)
    (base : Sample (Zq params) params.n params.m) (msg : Fin params.m → ℕ) :
    Sample (Zq params) params.n params.m :=
  { A := base.A,
    b := fun i => base.b i + bfvEncodeElem params Δ (msg i) }

def regevDecrypt (params : LWEParams) (Δ : ℕ)
    (s : VectorR (Zq params) params.n)
    (ct : Sample (Zq params) params.n params.m) : Fin params.m → ℕ :=
  fun i => bfvDecodeElem params Δ (samplePhase (Zq params) ct s i)

theorem regevPhase_eq (params : LWEParams) (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (s : VectorR (Zq params) params.n)
    (e : VectorR (Zq params) params.m)
    (msg : Fin params.m → ℕ) (i : Fin params.m) :
    samplePhase (Zq params)
      (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A s e) msg) s i =
      bfvEncodeElem params Δ (msg i) + e i := by
  dsimp [samplePhase, regevEncrypt, mkSample, evaluate]
  ring

theorem regevDecrypt_correct (params : LWEParams) (Δ t : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (s : VectorR (Zq params) params.n)
    (e : VectorR (Zq params) params.m)
    (msg : Fin params.m → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ i : Fin params.m, msg i < t)
    (h_noise : 2 * normInf params e < Δ) :
    regevDecrypt params Δ s
      (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A s e) msg) = msg := by
  ext i
  unfold regevDecrypt
  rw [regevPhase_eq]
  have hi_le : norm params (e i) ≤ normInf params e :=
    Finset.le_sup (f := fun j => norm params (e j)) (Finset.mem_univ i)
  have hi_noise : 2 * norm params (e i) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (msg i) (e i) ht_le (hm i) hi_noise

theorem regevDecrypt_add_correct (params : LWEParams) (Δ t : ℕ)
    (A1 A2 : MatrixR (Zq params) params.n params.m)
    (s : VectorR (Zq params) params.n)
    (e1 e2 : VectorR (Zq params) params.m)
    (msg1 msg2 : Fin params.m → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ i : Fin params.m, msg1 i + msg2 i < t)
    (h_noise : 2 * (normInf params e1 + normInf params e2) < Δ) :
    let ct1 := regevEncrypt params Δ (mkSample (Zq params) params.n params.m A1 s e1) msg1
    let ct2 := regevEncrypt params Δ (mkSample (Zq params) params.n params.m A2 s e2) msg2
    regevDecrypt params Δ s (addSamples (Zq params) ct1 ct2) =
      fun i => msg1 i + msg2 i := by
  intro ct1 ct2
  ext i
  unfold regevDecrypt
  have h_phase_sum :
      samplePhase (Zq params) (addSamples (Zq params) ct1 ct2) s i =
        bfvEncodeElem params Δ (msg1 i + msg2 i) + (e1 + e2) i := by
    dsimp [samplePhase, addSamples, ct1, ct2, regevEncrypt, mkSample, evaluate, bfvEncodeElem]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  rw [h_phase_sum]
  have h_tri := norm_add_le params e1 e2
  have hi_le : norm params ((e1 + e2) i) ≤ normInf params (e1 + e2) :=
    Finset.le_sup (f := fun j => norm params ((e1 + e2) j)) (Finset.mem_univ i)
  have hi_noise : 2 * norm params ((e1 + e2) i) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (msg1 i + msg2 i) ((e1 + e2) i) ht_le (hm i) hi_noise

end StandardLWERegev

section BFVBatchSIMD

open scoped BigOperators

def bfvBatchEncode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ_inv n_inv : Rt) (slots : Fin N → Rt) : NegacyclicPoly Rt N :=
  concreteInvNTT ψ_inv n_inv slots

def bfvBatchDecode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ : Rt) (pt : NegacyclicPoly Rt N) : Fin N → Rt :=
  concreteNTT ψ pt

theorem bfvBatchEncode_decode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ ψ_inv n_inv : Rt) (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (pt : NegacyclicPoly Rt N) :
    bfvBatchEncode ψ_inv n_inv (bfvBatchDecode ψ pt) = pt :=
  concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth pt

theorem bfvBatchDecode_add {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ : Rt) (p1 p2 : NegacyclicPoly Rt N) :
    bfvBatchDecode ψ (p1 + p2) = bfvBatchDecode ψ p1 + bfvBatchDecode ψ p2 :=
  concreteNTT_map_add ψ p1 p2

theorem bfvBatchDecode_mul {Rt : Type*} [CommRing Rt] {N : ℕ} [Fact (0 < N)]
    (ψ : Rt) (hpsi : ψ ^ N = -1) (p1 p2 : NegacyclicPoly Rt N) :
    bfvBatchDecode ψ (p1 * p2) = bfvBatchDecode ψ p1 * bfvBatchDecode ψ p2 :=
  concreteNTT_map_mul ψ hpsi p1 p2

theorem bfvBatchDecode_encode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ ψ_inv n_inv : Rt) (h_slot : IsValidNTTSlotInverse N ψ ψ_inv n_inv)
    (slots : Fin N → Rt) :
    bfvBatchDecode ψ (bfvBatchEncode ψ_inv n_inv slots) = slots :=
  concreteNTT_concreteInvNTT ψ ψ_inv n_inv h_slot slots

end BFVBatchSIMD

section CompressedModPKE

open scoped BigOperators

structure ModPKECompressedPublicKey (Seed R : Type*) (k : ℕ) where
  rho : Seed
  t : VectorR R k

def modPKEKeygenCompressed {Seed : Type*} (R : Type*) [CommRing R] (k : ℕ)
    (expandA : Seed → MatrixR R k k) (rho : Seed) (s e : VectorR R k) :
    ModPKECompressedPublicKey Seed R k :=
  { rho := rho,
    t := evaluate R k k (expandA rho) s e }

def modPKEDecompressPublicKey {Seed : Type*} (R : Type*) (k : ℕ)
    (expandA : Seed → MatrixR R k k) (cpk : ModPKECompressedPublicKey Seed R k) :
    ModPKEPublicKey R k :=
  { A := expandA cpk.rho,
    t := cpk.t }

theorem modPKEDecompress_keygenCompressed_eq {Seed : Type*} (R : Type*) [CommRing R] (k : ℕ)
    (expandA : Seed → MatrixR R k k) (rho : Seed) (s e : VectorR R k) :
    modPKEDecompressPublicKey R k expandA (modPKEKeygenCompressed R k expandA rho s e) =
      modPKEKeygen R k (expandA rho) s e :=
  rfl

def lweCompressCoeff (q d x : ℕ) : ℕ :=
  ((x * 2 ^ d + q / 2) / q) % 2 ^ d

def lweDecompressCoeff (q d y : ℕ) : ℕ :=
  (2 * y * q + 2 ^ d) / 2 ^ (d + 1)

theorem lweDecompressCoeff_eq_of_pos (q d y : ℕ) (hd : 0 < d) :
    lweDecompressCoeff q d y = (y * q + 2 ^ (d - 1)) / 2 ^ d := by
  dsimp [lweDecompressCoeff]
  have hd_eq : d = (d - 1) + 1 := (Nat.sub_add_cancel hd).symm
  conv_lhs => rw [hd_eq]
  have h1 : 2 * y * q + 2 ^ (d - 1 + 1) = 2 * (y * q + 2 ^ (d - 1)) := by
    rw [pow_succ']
    ring
  have h2 : 2 ^ (d - 1 + 1 + 1) = 2 * 2 ^ (d - 1 + 1) := by rw [pow_succ']
  rw [h1, h2, Nat.mul_div_mul_left _ _ zero_lt_two, ← hd_eq]

theorem lweCompressCoeff_lt (q d x : ℕ) :
    lweCompressCoeff q d x < 2 ^ d := by
  dsimp [lweCompressCoeff]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

def lweCompressElem (params : LWEParams) (d : ℕ) (x : Zq params) : ℕ :=
  lweCompressCoeff params.q d (ZMod.val x)

def lweDecompressElem (params : LWEParams) (d y : ℕ) : Zq params :=
  (lweDecompressCoeff params.q d y : Zq params)

def lweCompressPoly (params : LWEParams) (N d : ℕ) (p : NegacyclicPoly (Zq params) N) :
    Fin N → ℕ :=
  fun k => lweCompressElem params d (p.coeffs k)

def lweDecompressPoly (params : LWEParams) (N d : ℕ) (c : Fin N → ℕ) :
    NegacyclicPoly (Zq params) N :=
  ⟨fun k => lweDecompressElem params d (c k)⟩

structure ModPKEQuantizedCiphertext (N k : ℕ) where
  u_comp : Fin k → Fin N → ℕ
  v_comp : Fin N → ℕ

def modPKECompressCiphertext (params : LWEParams) (N k d_u d_v : ℕ)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) :
    ModPKEQuantizedCiphertext N k :=
  { u_comp := fun i => lweCompressPoly params N d_u (ct.u i),
    v_comp := lweCompressPoly params N d_v ct.v }

def modPKEDecompressCiphertext (params : LWEParams) (N k d_u d_v : ℕ)
    (qct : ModPKEQuantizedCiphertext N k) :
    ModPKECiphertext (NegacyclicPoly (Zq params) N) k :=
  { u := fun i => lweDecompressPoly params N d_u (qct.u_comp i),
    v := lweDecompressPoly params N d_v qct.v_comp }

lemma int_natAbs_le_of_mul_bounds {D : ℕ} (hD : 0 < D) {q : ℕ} {diff : ℤ}
    (h_lo : -((q : ℤ) + (D : ℤ)) ≤ (2 * (D : ℤ)) * diff)
    (h_hi : (2 * (D : ℤ)) * diff ≤ (q : ℤ) + (D : ℤ)) :
    diff.natAbs ≤ (q + D) / (2 * D) := by
  set B : ℕ := (q + D) / (2 * D)
  by_contra h_gt
  have hB1 : B + 1 ≤ diff.natAbs := by omega
  have h_mod_lt : (q + D) % (2 * D) < 2 * D := Nat.mod_lt (q + D) (by omega)
  have h_dm : (2 * D) * B + (q + D) % (2 * D) = q + D := Nat.div_add_mod (q + D) (2 * D)
  have h_mul_succ : (2 * D) * (B + 1) = (2 * D) * B + 2 * D := Nat.mul_succ (2 * D) B
  have h_gt_qD : (q : ℤ) + (D : ℤ) < (2 * (D : ℤ)) * ((B : ℤ) + 1) := by
    have h_nat : q + D < (2 * D) * (B + 1) := by omega
    exact_mod_cast h_nat
  have hD_nn : (0 : ℤ) ≤ 2 * (D : ℤ) := by omega
  by_cases h0 : 0 ≤ diff
  · have h_abs : ((B : ℤ) + 1) ≤ diff := by omega
    have h_mul := Int.mul_le_mul_of_nonneg_left h_abs hD_nn
    omega
  · have h_abs : ((B : ℤ) + 1) ≤ -diff := by omega
    have h_mul := Int.mul_le_mul_of_nonneg_left h_abs hD_nn
    have h_neg : (2 * (D : ℤ)) * (-diff) = -((2 * (D : ℤ)) * diff) := by ring
    omega

theorem norm_lweDecompress_lweCompress_sub_le (params : LWEParams) (d : ℕ) (x : Zq params) :
    norm params (lweDecompressElem params d (lweCompressElem params d x) - x) ≤
      (params.q + 2 ^ d) / 2 ^ (d + 1) := by
  set q : ℕ := params.q
  have hq : 0 < q := params.q_pos.out
  set v : ℕ := ZMod.val x
  have hv_lt : v < q := ZMod.val_lt x
  set D : ℕ := 2 ^ d
  have hD : 0 < D := Nat.pow_pos (by decide)
  have h_pow_succ : 2 ^ (d + 1) = 2 * D := by dsimp [D]; rw [pow_succ']
  rw [h_pow_succ]
  set u : ℕ := (v * D + q / 2) / q
  set r_u : ℕ := (v * D + q / 2) % q
  have h_u_eq : q * u + r_u = v * D + q / 2 := Nat.div_add_mod (v * D + q / 2) q
  have h_ru_lt : r_u < q := Nat.mod_lt (v * D + q / 2) hq
  have hu_le : u ≤ D := by
    have hv1 : v + 1 ≤ q := hv_lt
    have h_mul : (v + 1) * D ≤ q * D := Nat.mul_le_mul_right D hv1
    have h_s1 : (v + 1) * D = v * D + D := Nat.succ_mul v D
    have h_s2 : q * (D + 1) = q * D + q := Nat.mul_succ q D
    have h_num_lt : v * D + q / 2 < q * (D + 1) := by omega
    have h_div_lt : u < D + 1 := Nat.div_lt_of_lt_mul h_num_lt
    omega
  have hq_half : 2 * (q / 2) ≤ q ∧ q ≤ 2 * (q / 2) + 1 := by omega
  by_cases hu_lt : u < D
  · have h_comp : lweCompressElem params d x = u := by
      dsimp [lweCompressElem, lweCompressCoeff]
      exact Nat.mod_eq_of_lt hu_lt
    set z : ℕ := lweDecompressCoeff q d u
    set r_z : ℕ := (2 * u * q + D) % (2 ^ (d + 1))
    have h_z_eq : 2 ^ (d + 1) * z + r_z = 2 * u * q + D := Nat.div_add_mod _ _
    have h_rz_lt : r_z < 2 * D := by
      rw [← h_pow_succ]
      exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    have h_u_z : (q : ℤ) * (u : ℤ) + (r_u : ℤ) = (v : ℤ) * (D : ℤ) + ((q / 2 : ℕ) : ℤ) := by
      exact_mod_cast h_u_eq
    have h_z_z : (2 * (D : ℤ)) * (z : ℤ) + (r_z : ℤ) = 2 * ((q : ℤ) * (u : ℤ)) + (D : ℤ) := by
      rw [h_pow_succ] at h_z_eq
      have h_mul : 2 * u * q = 2 * (q * u) := by ring
      rw [h_mul] at h_z_eq
      exact_mod_cast h_z_eq
    have h_lin : (2 * (D : ℤ)) * ((z : ℤ) - (v : ℤ)) =
        2 * ((q / 2 : ℕ) : ℤ) - 2 * (r_u : ℤ) + (D : ℤ) - (r_z : ℤ) := by
      calc
        (2 * (D : ℤ)) * ((z : ℤ) - (v : ℤ))
          = ((2 * (D : ℤ)) * (z : ℤ) + (r_z : ℤ)) + 2 * ((q / 2 : ℕ) : ℤ) -
              2 * ((v : ℤ) * (D : ℤ) + ((q / 2 : ℕ) : ℤ)) - (r_z : ℤ) := by ring
        _ = (2 * ((q : ℤ) * (u : ℤ)) + (D : ℤ)) + 2 * ((q / 2 : ℕ) : ℤ) -
              2 * ((q : ℤ) * (u : ℤ) + (r_u : ℤ)) - (r_z : ℤ) := by
            rw [h_z_z, ← h_u_z]
        _ = 2 * ((q / 2 : ℕ) : ℤ) - 2 * (r_u : ℤ) + (D : ℤ) - (r_z : ℤ) := by ring
    have h_lo : -((q : ℤ) + (D : ℤ)) ≤ (2 * (D : ℤ)) * ((z : ℤ) - (v : ℤ)) := by omega
    have h_hi : (2 * (D : ℤ)) * ((z : ℤ) - (v : ℤ)) ≤ (q : ℤ) + (D : ℤ) := by omega
    have h_abs := int_natAbs_le_of_mul_bounds hD h_lo h_hi
    have h_cast : lweDecompressElem params d (lweCompressElem params d x) - x =
        Int.cast ((z : ℤ) - (v : ℤ)) := by
      rw [h_comp]
      dsimp [lweDecompressElem]
      have hx_eq : x = ((v : ℕ) : Zq params) := (ZMod.natCast_zmod_val x).symm
      rw [hx_eq, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    rw [h_cast]
    exact le_trans (norm_intCast_le_natAbs params ((z : ℤ) - (v : ℤ))) h_abs
  · have hu_eq : u = D := by omega
    have h_comp : lweCompressElem params d x = 0 := by
      dsimp [lweCompressElem, lweCompressCoeff]
      change u % D = 0
      rw [hu_eq, Nat.mod_self]
    have h_decomp0 : lweDecompressCoeff q d 0 = 0 := by
      dsimp [lweDecompressCoeff]
      rw [zero_mul, zero_add, h_pow_succ]
      change D / (2 * D) = 0
      exact Nat.div_eq_of_lt (by omega)
    have h_u_z : (q : ℤ) * (D : ℤ) + (r_u : ℤ) = (v : ℤ) * (D : ℤ) + ((q / 2 : ℕ) : ℤ) := by
      have h_eq' : q * D + r_u = v * D + q / 2 := hu_eq ▸ h_u_eq
      exact_mod_cast h_eq'
    have h_lin : (D : ℤ) * ((q : ℤ) - (v : ℤ)) = ((q / 2 : ℕ) : ℤ) - (r_u : ℤ) := by
      calc
        (D : ℤ) * ((q : ℤ) - (v : ℤ))
          = ((q : ℤ) * (D : ℤ) + (r_u : ℤ)) - (v : ℤ) * (D : ℤ) - (r_u : ℤ) := by ring
        _ = ((v : ℤ) * (D : ℤ) + ((q / 2 : ℕ) : ℤ)) - (v : ℤ) * (D : ℤ) - (r_u : ℤ) := by
            rw [h_u_z]
        _ = ((q / 2 : ℕ) : ℤ) - (r_u : ℤ) := by ring
    have h_lin2 : (2 * (D : ℤ)) * ((q : ℤ) - (v : ℤ)) =
        2 * ((q / 2 : ℕ) : ℤ) - 2 * (r_u : ℤ) := by
      calc
        (2 * (D : ℤ)) * ((q : ℤ) - (v : ℤ))
          = 2 * ((D : ℤ) * ((q : ℤ) - (v : ℤ))) := by ring
        _ = 2 * (((q / 2 : ℕ) : ℤ) - (r_u : ℤ)) := by rw [h_lin]
        _ = 2 * ((q / 2 : ℕ) : ℤ) - 2 * (r_u : ℤ) := by ring
    have h_lo : -((q : ℤ) + (D : ℤ)) ≤ (2 * (D : ℤ)) * ((q : ℤ) - (v : ℤ)) := by omega
    have h_hi : (2 * (D : ℤ)) * ((q : ℤ) - (v : ℤ)) ≤ (q : ℤ) + (D : ℤ) := by omega
    have h_abs := int_natAbs_le_of_mul_bounds hD h_lo h_hi
    have h_cast : lweDecompressElem params d (lweCompressElem params d x) - x =
        Int.cast ((q : ℤ) - (v : ℤ)) := by
      rw [h_comp]
      dsimp [lweDecompressElem]
      rw [h_decomp0, Nat.cast_zero, zero_sub]
      have hx_eq : x = ((v : ℕ) : Zq params) := (ZMod.natCast_zmod_val x).symm
      rw [hx_eq, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
      have hq0 : ((q : ℕ) : Zq params) = 0 := ZMod.natCast_self params.q
      rw [hq0, zero_sub]
    rw [h_cast]
    exact le_trans (norm_intCast_le_natAbs params ((q : ℤ) - (v : ℤ))) h_abs

theorem normInf_lweDecompressPoly_lweCompressPoly_sub_le
    (params : LWEParams) (N d : ℕ) (p : NegacyclicPoly (Zq params) N) :
    normInf params (lweDecompressPoly params N d (lweCompressPoly params N d p) - p).coeffs ≤
      (params.q + 2 ^ d) / 2 ^ (d + 1) := by
  dsimp [normInf]
  apply Finset.sup_le
  intro k _
  exact norm_lweDecompress_lweCompress_sub_le params d (p.coeffs k)

theorem modPKE_compressed_phase_eq (R : Type*) [CommRing R] (k : ℕ)
    (A : MatrixR R k k) (s e r e1 e_u : VectorR R k) (e2 e_v delta_m : R) :
    let pk := modPKEKeygen R k A s e
    let ct := modPKEEncrypt R k pk r e1 e2 delta_m
    let ct_comp : ModPKECiphertext R k := { u := ct.u + e_u, v := ct.v + e_v }
    modPKEPhase R k ct_comp s =
      delta_m +
        ((dotProductR R k e r + e2 - dotProductR R k s e1) +
          (e_v - dotProductR R k s e_u)) := by
  intro pk ct ct_comp
  have h_base := modPKE_phase_eq R k A s e r e1 e2 delta_m
  have h_su :
      dotProductR R k s (ct.u + e_u) =
        dotProductR R k s ct.u + dotProductR R k s e_u := by
    dsimp [dotProductR]
    simp only [mul_add, Finset.sum_add_distrib]
  change (ct.v + e_v) - dotProductR R k s (ct.u + e_u) = _
  rw [h_su]
  have h_expand :
      (ct.v + e_v) - (dotProductR R k s ct.u + dotProductR R k s e_u) =
        modPKEPhase R k ct s + (e_v - dotProductR R k s e_u) := by
    dsimp [modPKEPhase]
    ring
  rw [h_expand, h_base]
  ring

theorem modPKE_compressed_decrypt_correct (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e r e1 e_u : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 e_v : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise : 2 * (normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs +
      normInf params
        (e_v - dotProductR (NegacyclicPoly (Zq params) N) k s e_u).coeffs) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 (bfvEncodePoly params N Δ m)
    let ct_comp : ModPKECiphertext (NegacyclicPoly (Zq params) N) k :=
      { u := ct.u + e_u, v := ct.v + e_v }
    bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct_comp s) = m := by
  intro pk ct ct_comp
  have h_phase := modPKE_compressed_phase_eq (NegacyclicPoly (Zq params) N) k A s e r e1 e_u e2 e_v
    (bfvEncodePoly params N Δ m)
  change bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct_comp s) = m
  rw [h_phase]
  ext idx
  unfold bfvDecodePoly
  rw [NegacyclicPoly.add_coeffs]
  dsimp [bfvEncodePoly]
  set E_pke := dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
    dotProductR (NegacyclicPoly (Zq params) N) k s e1
  set E_comp := e_v - dotProductR (NegacyclicPoly (Zq params) N) k s e_u
  have h_tri := norm_add_le params E_pke.coeffs E_comp.coeffs
  have h_le : norm params ((E_pke + E_comp).coeffs idx) ≤ normInf params (E_pke + E_comp).coeffs :=
    Finset.le_sup (f := fun j => norm params ((E_pke + E_comp).coeffs j)) (Finset.mem_univ idx)
  have h_eq_add : normInf params (E_pke + E_comp).coeffs ≤
      normInf params E_pke.coeffs + normInf params E_comp.coeffs := h_tri
  have h_idx_noise : 2 * norm params ((E_pke + E_comp).coeffs idx) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (m idx) ((E_pke + E_comp).coeffs idx)
    ht_le (hm idx) h_idx_noise

theorem modPKE_actual_compress_decrypt_correct
    (params : LWEParams) (k N Δ t d_u d_v : ℕ) [Fact (0 < N)]
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise : 2 * (normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs +
      ((params.q + 2 ^ d_v) / 2 ^ (d_v + 1) +
        k * N * ((params.q + 2 ^ d_u) / 2 ^ (d_u + 1)))) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 (bfvEncodePoly params N Δ m)
    let qct := modPKECompressCiphertext params N k d_u d_v ct
    let ct_dec := modPKEDecompressCiphertext params N k d_u d_v qct
    bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct_dec s) = m := by
  intro pk ct qct ct_dec
  let B_u : ℕ := (params.q + 2 ^ d_u) / 2 ^ (d_u + 1)
  let B_v : ℕ := (params.q + 2 ^ d_v) / 2 ^ (d_v + 1)
  let e_u : VectorR (NegacyclicPoly (Zq params) N) k :=
    fun i => lweDecompressPoly params N d_u (lweCompressPoly params N d_u (ct.u i)) - ct.u i
  let e_v : NegacyclicPoly (Zq params) N :=
    lweDecompressPoly params N d_v (lweCompressPoly params N d_v ct.v) - ct.v
  have h_ct_eq : ct_dec = { u := ct.u + e_u, v := ct.v + e_v } := by
    dsimp [ct_dec, qct, modPKEDecompressCiphertext, modPKECompressCiphertext]
    congr 1
    · ext i idx
      change (lweDecompressPoly params N d_u (lweCompressPoly params N d_u (ct.u i))).coeffs idx =
        (ct.u i + e_u i).coeffs idx
      rw [NegacyclicPoly.add_coeffs, NegacyclicPoly.sub_coeffs, add_sub_cancel]
    · rw [add_sub_cancel]
  have h_ev : normInf params e_v.coeffs ≤ B_v :=
    normInf_lweDecompressPoly_lweCompressPoly_sub_le params N d_v ct.v
  have h_su :
      normInf params (dotProductR (NegacyclicPoly (Zq params) N) k s e_u).coeffs ≤
        k * N * B_u := by
    dsimp [dotProductR]
    have h_sum := normInf_finset_sum_poly_le params N Finset.univ (fun i : Fin k => s i * e_u i)
    have h_each : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        normInf params (s i * e_u i).coeffs ≤ N * B_u := by
      intro i _
      have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N (s i) (e_u i) (hs_tern i)
      have h_eu := normInf_lweDecompressPoly_lweCompressPoly_sub_le params N d_u (ct.u i)
      have h_le : N * normInf params (e_u i).coeffs ≤ N * B_u := Nat.mul_le_mul_left N h_eu
      omega
    have h_sum_le := Finset.sum_le_sum h_each
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_sum_le
    have h_assoc : k * (N * B_u) = k * N * B_u := by ring
    omega
  have h_comp_bound : normInf params
      (e_v - dotProductR (NegacyclicPoly (Zq params) N) k s e_u).coeffs ≤
      B_v + k * N * B_u := by
    have h_sub := norm_sub_le params e_v.coeffs
      (dotProductR (NegacyclicPoly (Zq params) N) k s e_u).coeffs
    exact le_trans h_sub (Nat.add_le_add h_ev h_su)
  have h_tot_noise : 2 * (normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs +
      normInf params
        (e_v - dotProductR (NegacyclicPoly (Zq params) N) k s e_u).coeffs) < Δ := by
    dsimp only [B_u, B_v] at h_comp_bound
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.add_le_add_left h_comp_bound _)) h_noise
  rw [h_ct_eq]
  exact modPKE_compressed_decrypt_correct params k N Δ t A s e r e1 e_u e2 e_v m ht_le hm
    h_tot_noise

end CompressedModPKE

section RegevINDCPASecurity

open scoped BigOperators

def regevEncodeVec (params : LWEParams) (Δ : ℕ) (msg : Fin params.m → ℕ) :
    VectorR (Zq params) params.m :=
  fun i => bfvEncodeElem params Δ (msg i)

def regevEncryptPad (params : LWEParams) (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (pad : VectorR (Zq params) params.m)
    (msg : Fin params.m → ℕ) : Sample (Zq params) params.n params.m :=
  { A := A, b := pad + regevEncodeVec params Δ msg }

theorem regevEncrypt_eq_regevEncryptPad (params : LWEParams) (Δ : ℕ)
    (sample : Sample (Zq params) params.n params.m) (msg : Fin params.m → ℕ) :
    regevEncrypt params Δ sample msg = regevEncryptPad params Δ sample.A sample.b msg := by
  cases sample
  rfl

def regevPadEquiv (params : LWEParams) (Δ : ℕ) (msg : Fin params.m → ℕ) :
    VectorR (Zq params) params.m ≃ VectorR (Zq params) params.m :=
  Equiv.addRight (regevEncodeVec params Δ msg)

theorem regevPad_bijective (params : LWEParams) (Δ : ℕ) (msg : Fin params.m → ℕ) :
    Function.Bijective
      (fun pad : VectorR (Zq params) params.m => pad + regevEncodeVec params Δ msg) :=
  (regevPadEquiv params Δ msg).bijective

theorem regevUniformSum_eq (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    {M : Type*} [AddCommMonoid M]
    (D : Sample (Zq params) params.n params.m → M)
    (A : MatrixR (Zq params) params.n params.m)
    (msg : Fin params.m → ℕ) :
    (∑ u : VectorR (Zq params) params.m, D (regevEncryptPad params Δ A u msg)) =
      ∑ v : VectorR (Zq params) params.m, D { A := A, b := v } := by
  exact Equiv.sum_comp (regevPadEquiv params Δ msg) (fun v => D { A := A, b := v })

theorem regevUniformSum_indep (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    {M : Type*} [AddCommMonoid M]
    (D : Sample (Zq params) params.n params.m → M)
    (A : MatrixR (Zq params) params.n params.m)
    (msg0 msg1 : Fin params.m → ℕ) :
    (∑ u : VectorR (Zq params) params.m, D (regevEncryptPad params Δ A u msg0)) =
      (∑ u : VectorR (Zq params) params.m, D (regevEncryptPad params Δ A u msg1)) := by
  rw [regevUniformSum_eq params Δ D A msg0, regevUniformSum_eq params Δ D A msg1]

theorem regev_ind_cpa_reduction (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (D : Sample (Zq params) params.n params.m → ℤ)
    (A : MatrixR (Zq params) params.n params.m)
    (E_LWE : (VectorR (Zq params) params.m → ℤ) → ℤ)
    (msg0 msg1 : Fin params.m → ℕ) :
    let f0 := fun pad => D (regevEncryptPad params Δ A pad msg0)
    let f1 := fun pad => D (regevEncryptPad params Δ A pad msg1)
    let u0 := ∑ u : VectorR (Zq params) params.m, f0 u
    let u1 := ∑ u : VectorR (Zq params) params.m, f1 u
    (E_LWE f0 - E_LWE f1).natAbs ≤ (E_LWE f0 - u0).natAbs + (E_LWE f1 - u1).natAbs := by
  intro f0 f1 u0 u1
  have h_unif : u0 = u1 := regevUniformSum_indep params Δ D A msg0 msg1
  omega

def bitToInt (b : Bool) : ℤ :=
  if b then 1 else 0

structure FinDist (α : Type*) [Fintype α] where
  weight : α → ℕ

def FinDist.totalMass {α : Type*} [Fintype α] (dist : FinDist α) : ℕ :=
  ∑ x : α, dist.weight x

def uniformFinDist (α : Type*) [Fintype α] : FinDist α :=
  { weight := fun _ => 1 }

def FinDist.acceptWeight {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) : ℤ :=
  ∑ x : α, (dist.weight x : ℤ) * bitToInt (P x)

def FinDist.eventMass {α : Type*} [Fintype α]
    (dist : FinDist α) (E : α → Prop) [DecidablePred E] : ℕ :=
  ∑ x : α, if E x then dist.weight x else 0

theorem FinDist.difference_lemma {α : Type*} [Fintype α]
    (dist : FinDist α) (P1 P2 : α → Bool) (E : α → Prop) [DecidablePred E]
    (h_agree : ∀ x : α, ¬ E x → P1 x = P2 x) :
    (dist.acceptWeight P1 - dist.acceptWeight P2).natAbs ≤ dist.eventMass E := by
  dsimp [FinDist.acceptWeight, FinDist.eventMass]
  rw [← Finset.sum_sub_distrib]
  have h_term : ∀ x : α,
      ((dist.weight x : ℤ) * bitToInt (P1 x) - (dist.weight x : ℤ) * bitToInt (P2 x)).natAbs ≤
        if E x then dist.weight x else 0 := by
    intro x
    by_cases hx : E x
    · rw [if_pos hx]
      dsimp [bitToInt]
      cases P1 x <;> cases P2 x <;> simp
    · rw [if_neg hx, h_agree x hx, sub_self]
      simp
  have h_sum_le :
      (∑ x : α,
        ((dist.weight x : ℤ) * bitToInt (P1 x) -
          (dist.weight x : ℤ) * bitToInt (P2 x))).natAbs ≤
        ∑ x : α,
          ((dist.weight x : ℤ) * bitToInt (P1 x) -
            (dist.weight x : ℤ) * bitToInt (P2 x)).natAbs := by
    induction (Finset.univ : Finset α) using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      have h_tri := Int.natAbs_add_le
        ((dist.weight a : ℤ) * bitToInt (P1 a) - (dist.weight a : ℤ) * bitToInt (P2 a))
        (∑ x ∈ s, ((dist.weight x : ℤ) * bitToInt (P1 x) - (dist.weight x : ℤ) * bitToInt (P2 x)))
      omega
  have h_bound :
      (∑ x : α,
        ((dist.weight x : ℤ) * bitToInt (P1 x) -
          (dist.weight x : ℤ) * bitToInt (P2 x)).natAbs) ≤
        ∑ x : α, if E x then dist.weight x else 0 :=
    Finset.sum_le_sum (fun x _ => h_term x)
  omega

def regevShiftedDistinguisher (params : LWEParams) (Δ : ℕ)
    (msg : Fin params.m → ℕ) (D : Sample (Zq params) params.n params.m → Bool) :
    Sample (Zq params) params.n params.m → Bool :=
  fun sample => D (regevEncrypt params Δ sample msg)

def DLWEAdvantage (params : LWEParams) [NeZero params.q]
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (D_dlwe : Sample (Zq params) params.n params.m → Bool) : ℕ :=
  let cardU : ℤ := Fintype.card (VectorR (Zq params) params.m)
  let realW : ℤ := seDist.acceptWeight
    (fun se => D_dlwe (mkSample (Zq params) params.n params.m A se.1 se.2))
  let unifW : ℤ := ∑ u : VectorR (Zq params) params.m, bitToInt (D_dlwe { A := A, b := u })
  (cardU * realW - (seDist.totalMass : ℤ) * unifW).natAbs

def INDCPAAdvantage (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (msg0 msg1 : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) : ℕ :=
  let cardU : ℤ := Fintype.card (VectorR (Zq params) params.m)
  let real0 : ℤ := seDist.acceptWeight
    (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2) msg0))
  let real1 : ℤ := seDist.acceptWeight
    (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2) msg1))
  (cardU * real0 - cardU * real1).natAbs

theorem regevShifted_uniform_sum_eq (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (msg : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) :
    (∑ u : VectorR (Zq params) params.m,
        bitToInt (regevShiftedDistinguisher params Δ msg D { A := A, b := u })) =
      ∑ v : VectorR (Zq params) params.m, bitToInt (D { A := A, b := v }) := by
  dsimp [regevShiftedDistinguisher]
  have h_pad : ∀ u : VectorR (Zq params) params.m,
      regevEncrypt params Δ { A := A, b := u } msg = regevEncryptPad params Δ A u msg :=
    fun u => regevEncrypt_eq_regevEncryptPad params Δ { A := A, b := u } msg
  simp_rw [h_pad]
  exact regevUniformSum_eq params Δ (fun s => bitToInt (D s)) A msg

theorem regev_ind_cpa_to_dlwe_reduction (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (msg0 msg1 : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) :
    INDCPAAdvantage params Δ A seDist msg0 msg1 D ≤
      DLWEAdvantage params A seDist (regevShiftedDistinguisher params Δ msg0 D) +
        DLWEAdvantage params A seDist (regevShiftedDistinguisher params Δ msg1 D) := by
  dsimp [INDCPAAdvantage, DLWEAdvantage]
  have h0 := regevShifted_uniform_sum_eq params Δ A msg0 D
  have h1 := regevShifted_uniform_sum_eq params Δ A msg1 D
  rw [h0, h1]
  dsimp [regevShiftedDistinguisher]
  omega

end RegevINDCPASecurity

section FujisakiOkamotoINDCCA2Reduction

open scoped BigOperators

def foEncDet {PK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (m : Msg) : CT :=
  encPKE pk m (G pk m).2

def IsCorrectFOPKE {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK) : Prop :=
  ∀ m : Msg, decPKE sk (foEncDet encPKE G pk m) = m

theorem foEncDet_injective_of_correct {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK)
    (h_corr : IsCorrectFOPKE encPKE decPKE G pk sk) :
    Function.Injective (foEncDet encPKE G pk) := by
  intro m1 m2 h_eq
  have h1 := h_corr m1
  have h2 := h_corr m2
  rw [h_eq] at h1
  exact h1.symm.trans h2

theorem foDecPKE_eq_of_foEncDet_eq {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK)
    (h_corr : IsCorrectFOPKE encPKE decPKE G pk sk)
    {m : Msg} {ct : CT}
    (h_enc : foEncDet encPKE G pk m = ct) :
    decPKE sk ct = m := by
  rw [← h_enc]
  exact h_corr m

def foDecapsReal {PK SK Msg Coins Key Seed CT : Type*} [DecidableEq CT]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT) : Key :=
  let m' := decPKE sk ct
  if foEncDet encPKE G pk m' = ct then
    (G pk m').1
  else
    J z ct

def foDecapsSim {PK SK Msg Coins Key Seed CT : Type*} [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT) : Key :=
  let m' := decPKE sk ct
  if m' ∈ Q_G ∧ foEncDet encPKE G pk m' = ct then
    (G pk m').1
  else
    J z ct

theorem foDecapsSim_accept_iff_mem_image {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK)
    (h_corr : IsCorrectFOPKE encPKE decPKE G pk sk)
    (ct : CT) :
    (decPKE sk ct ∈ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct) ↔
      ∃ m ∈ Q_G, foEncDet encPKE G pk m = ct := by
  constructor
  · rintro ⟨hm_in, h_enc⟩
    exact ⟨decPKE sk ct, hm_in, h_enc⟩
  · rintro ⟨m, hm_in, h_enc⟩
    have hm_eq := foDecPKE_eq_of_foEncDet_eq encPKE decPKE G pk sk h_corr h_enc
    rw [hm_eq]
    exact ⟨hm_in, h_enc⟩

def foBadDecapsEvent {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (ct : CT) : Prop :=
  decPKE sk ct ∉ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct

instance {PK SK Msg Coins Key CT : Type*} [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) :
    DecidablePred (foBadDecapsEvent encPKE decPKE G Q_G pk sk) := by
  intro ct
  unfold foBadDecapsEvent
  infer_instance

theorem foDecapsReal_eq_foDecapsSim_of_not_bad {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT)
    (h_not_bad : ¬ foBadDecapsEvent encPKE decPKE G Q_G pk sk ct) :
    foDecapsReal encPKE decPKE G J pk sk z ct =
      foDecapsSim encPKE decPKE G J Q_G pk sk z ct := by
  dsimp [foDecapsReal, foDecapsSim]
  by_cases h_enc : foEncDet encPKE G pk (decPKE sk ct) = ct
  · have hm_in : decPKE sk ct ∈ Q_G := by
      by_contra h_notin
      exact h_not_bad ⟨h_notin, h_enc⟩
    rw [if_pos h_enc, if_pos ⟨hm_in, h_enc⟩]
  · have h_not_both : ¬ (decPKE sk ct ∈ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct) :=
      fun h => h_enc h.2
    rw [if_neg h_enc, if_neg h_not_both]

theorem foDecapsTranscript_eq_of_no_bad {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg] {q_D : ℕ}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (z : Seed)
    (ct_queries : Fin q_D → CT)
    (h_no_bad : ∀ i : Fin q_D, ¬ foBadDecapsEvent encPKE decPKE G Q_G pk sk (ct_queries i)) :
    (fun i => foDecapsReal encPKE decPKE G J pk sk z (ct_queries i)) =
      (fun i => foDecapsSim encPKE decPKE G J Q_G pk sk z (ct_queries i)) := by
  ext i
  exact foDecapsReal_eq_foDecapsSim_of_not_bad encPKE decPKE G J Q_G pk sk z
    (ct_queries i) (h_no_bad i)

theorem fo_ind_cca2_security_reduction {Ω : Type*} [Fintype Ω]
    (dist : FinDist Ω)
    (RealGame0 RealGame1 SimGame0 SimGame1 IdealGame0 IdealGame1 : Ω → Bool)
    (BadDecaps QueryChallenge : Ω → Prop)
    [DecidablePred BadDecaps] [DecidablePred QueryChallenge]
    (h_hop1_b0 : ∀ ω : Ω, ¬ BadDecaps ω → RealGame0 ω = SimGame0 ω)
    (h_hop1_b1 : ∀ ω : Ω, ¬ BadDecaps ω → RealGame1 ω = SimGame1 ω)
    (h_hop2_b0 : ∀ ω : Ω, ¬ QueryChallenge ω → SimGame0 ω = IdealGame0 ω)
    (h_hop2_b1 : ∀ ω : Ω, ¬ QueryChallenge ω → SimGame1 ω = IdealGame1 ω)
    (h_ideal_eq : dist.acceptWeight IdealGame0 = dist.acceptWeight IdealGame1) :
    (dist.acceptWeight RealGame0 - dist.acceptWeight RealGame1).natAbs ≤
      2 * dist.eventMass BadDecaps + 2 * dist.eventMass QueryChallenge := by
  have h_diff_b0 := FinDist.difference_lemma dist RealGame0 SimGame0 BadDecaps h_hop1_b0
  have h_diff_b1 := FinDist.difference_lemma dist RealGame1 SimGame1 BadDecaps h_hop1_b1
  have h_diff_q0 := FinDist.difference_lemma dist SimGame0 IdealGame0 QueryChallenge h_hop2_b0
  have h_diff_q1 := FinDist.difference_lemma dist SimGame1 IdealGame1 QueryChallenge h_hop2_b1
  omega

def foReprogramKey {PK Msg Coins Key : Type*} [DecidableEq Msg]
    (G : PK → Msg → Key × Coins) (m_star : Msg) (k_new : Key) : PK → Msg → Key × Coins :=
  fun pk m => if m = m_star then (k_new, (G pk m).2) else G pk m

theorem foEncDet_reprogramKey_eq {PK Msg Coins Key CT : Type*} [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (G : PK → Msg → Key × Coins) (m_star : Msg) (k_new : Key) (pk : PK) (m : Msg) :
    foEncDet encPKE (foReprogramKey G m_star k_new) pk m = foEncDet encPKE G pk m := by
  dsimp [foEncDet, foReprogramKey]
  split_ifs <;> rfl

theorem foDecapsSim_reprogramKey_eq_of_not_mem {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (m_star : Msg) (k_new : Key)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT)
    (h_not_mem : m_star ∉ Q_G) :
    foDecapsSim encPKE decPKE (foReprogramKey G m_star k_new) J Q_G pk sk z ct =
      foDecapsSim encPKE decPKE G J Q_G pk sk z ct := by
  dsimp [foDecapsSim]
  rw [foEncDet_reprogramKey_eq]
  by_cases h_cond : decPKE sk ct ∈ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct
  · rw [if_pos h_cond, if_pos h_cond]
    have h_ne : decPKE sk ct ≠ m_star := by
      intro h_eq
      rw [h_eq] at h_cond
      exact h_not_mem h_cond.1
    dsimp [foReprogramKey]
    rw [if_neg h_ne]
  · rw [if_neg h_cond, if_neg h_cond]

theorem fo_concrete_ind_cca2_reduction
    {PK SK Msg Coins Key Seed CT : Type*}
    [Fintype Msg] [Fintype Key] [DecidableEq CT] [DecidableEq Msg] {q_D : ℕ}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (pk : PK) (sk : SK) (z : Seed)
    (Q_G : Msg → Finset Msg)
    (ct_queries : Msg → Fin q_D → CT)
    (adv : CT → Key → (Fin q_D → Key) → Bool) :
    let Ω := Msg × (Key × Key)
    let dist : FinDist Ω := uniformFinDist Ω
    let Real0 : Ω → Bool := fun ω =>
      let m_star := ω.1
      let k0 := ω.2.1
      let G' := foReprogramKey G m_star k0
      let ct_star := foEncDet encPKE G' pk m_star
      adv ct_star k0 (fun i => foDecapsReal encPKE decPKE G' J pk sk z (ct_queries m_star i))
    let Real1 : Ω → Bool := fun ω =>
      let m_star := ω.1
      let k0 := ω.2.1
      let k1 := ω.2.2
      let G' := foReprogramKey G m_star k0
      let ct_star := foEncDet encPKE G' pk m_star
      adv ct_star k1 (fun i => foDecapsReal encPKE decPKE G' J pk sk z (ct_queries m_star i))
    let BadDecaps : Ω → Prop := fun ω =>
      ∃ i : Fin q_D,
        foBadDecapsEvent encPKE decPKE (foReprogramKey G ω.1 ω.2.1) (Q_G ω.1) pk sk
          (ct_queries ω.1 i)
    let QueryChallenge : Ω → Prop := fun ω => ω.1 ∈ Q_G ω.1
    (dist.acceptWeight Real0 - dist.acceptWeight Real1).natAbs ≤
      2 * dist.eventMass BadDecaps + 2 * dist.eventMass QueryChallenge := by
  intro Ω dist Real0 Real1 BadDecaps QueryChallenge
  let Sim0 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k0 := ω.2.1
    let G' := foReprogramKey G m_star k0
    let ct_star := foEncDet encPKE G' pk m_star
    adv ct_star k0
      (fun i => foDecapsSim encPKE decPKE G' J (Q_G m_star) pk sk z (ct_queries m_star i))
  let Sim1 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k0 := ω.2.1
    let k1 := ω.2.2
    let G' := foReprogramKey G m_star k0
    let ct_star := foEncDet encPKE G' pk m_star
    adv ct_star k1
      (fun i => foDecapsSim encPKE decPKE G' J (Q_G m_star) pk sk z (ct_queries m_star i))
  let Ideal0 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k0 := ω.2.1
    let ct_star := foEncDet encPKE G pk m_star
    adv ct_star k0
      (fun i => foDecapsSim encPKE decPKE G J (Q_G m_star) pk sk z (ct_queries m_star i))
  let Ideal1 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k1 := ω.2.2
    let ct_star := foEncDet encPKE G pk m_star
    adv ct_star k1
      (fun i => foDecapsSim encPKE decPKE G J (Q_G m_star) pk sk z (ct_queries m_star i))
  apply fo_ind_cca2_security_reduction dist Real0 Real1 Sim0 Sim1 Ideal0 Ideal1
    BadDecaps QueryChallenge
  · intro ω h_nb
    dsimp [Real0, Sim0]
    have h_tr := foDecapsTranscript_eq_of_no_bad encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J
      (Q_G ω.1) pk sk z (ct_queries ω.1) (fun i hi => h_nb ⟨i, hi⟩)
    rw [h_tr]
  · intro ω h_nb
    dsimp [Real1, Sim1]
    have h_tr := foDecapsTranscript_eq_of_no_bad encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J
      (Q_G ω.1) pk sk z (ct_queries ω.1) (fun i hi => h_nb ⟨i, hi⟩)
    rw [h_tr]
  · intro ω h_nq
    dsimp [Sim0, Ideal0]
    rw [foEncDet_reprogramKey_eq]
    have h_sim_eq :
        (fun i => foDecapsSim encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J (Q_G ω.1) pk sk z
          (ct_queries ω.1 i)) =
        (fun i => foDecapsSim encPKE decPKE G J (Q_G ω.1) pk sk z (ct_queries ω.1 i)) := by
      ext i
      exact foDecapsSim_reprogramKey_eq_of_not_mem encPKE decPKE G J (Q_G ω.1) ω.1 ω.2.1 pk sk z
        (ct_queries ω.1 i) h_nq
    rw [h_sim_eq]
  · intro ω h_nq
    dsimp [Sim1, Ideal1]
    rw [foEncDet_reprogramKey_eq]
    have h_sim_eq :
        (fun i => foDecapsSim encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J (Q_G ω.1) pk sk z
          (ct_queries ω.1 i)) =
        (fun i => foDecapsSim encPKE decPKE G J (Q_G ω.1) pk sk z (ct_queries ω.1 i)) := by
      ext i
      exact foDecapsSim_reprogramKey_eq_of_not_mem encPKE decPKE G J (Q_G ω.1) ω.1 ω.2.1 pk sk z
        (ct_queries ω.1 i) h_nq
    rw [h_sim_eq]
  · dsimp [FinDist.acceptWeight, dist, uniformFinDist, Ideal0, Ideal1]
    let e : Ω ≃ Ω := Equiv.prodCongr (Equiv.refl Msg) (Equiv.prodComm Key Key)
    exact Equiv.sum_comp e (fun ω : Ω =>
      (1 : ℤ) * bitToInt (adv (foEncDet encPKE G pk ω.1) ω.2.2
        (fun i => foDecapsSim encPKE decPKE G J (Q_G ω.1) pk sk z (ct_queries ω.1 i))))

theorem modPKE_isCorrectFOPKE (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    {Coins Key : Type*}
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (ht_le : Δ * t ≤ params.q)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin k, normInf params (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf params (expandE2 c).coeffs ≤ 1)
    (h_zero_fail : 2 * (2 * k * N + 1) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let encPKE := fun pk' (m : { m : Fin N → ℕ // ∀ idx, m idx < t }) (c : Coins) =>
      modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk' (expandR c) (expandE1 c) (expandE2 c)
        (bfvEncodePoly params N Δ m.1)
    let decPKE := fun s' (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) =>
      (bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s'))
    ∀ m : { m : Fin N → ℕ // ∀ idx, m idx < t },
      decPKE s (foEncDet encPKE (fun pk' m' => G pk' m'.1) pk m) = m.1 := by
  intro pk encPKE decPKE m
  dsimp [foEncDet, encPKE, decPKE]
  set c := (G pk m.1).2
  have h_bound := modPKE_ternary_noise_bound params k N s e
    (expandR c) (expandE1 c) (expandE2 c)
    (hr_tern c) hs_tern he_norm (he1_norm c) (he2_norm c)
  have h_noise : 2 * normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e (expandR c) + expandE2 c -
        dotProductR (NegacyclicPoly (Zq params) N) k s (expandE1 c)).coeffs < Δ := by omega
  exact modPKE_decrypt_correct params k N Δ t A s e (expandR c) (expandE1 c) (expandE2 c)
    m.1 ht_le m.2 h_noise

def ModPKECiphertext.equivProd {R : Type*} {k : ℕ} :
    ModPKECiphertext R k ≃ (VectorR R k × R) where
  toFun ct := (ct.u, ct.v)
  invFun p := { u := p.1, v := p.2 }
  left_inv ct := by cases ct; rfl
  right_inv p := by cases p; rfl

instance instDecidableEqModPKECiphertext {R : Type*} {k : ℕ} [DecidableEq R] :
    DecidableEq (ModPKECiphertext R k) :=
  fun ct1 ct2 =>
    decidable_of_iff (ModPKECiphertext.equivProd ct1 = ModPKECiphertext.equivProd ct2)
      ModPKECiphertext.equivProd.injective.eq_iff

instance instFintypeModPKECiphertext {R : Type*} {k : ℕ} [Fintype R] :
    Fintype (ModPKECiphertext R k) :=
  Fintype.ofEquiv (VectorR R k × R) ModPKECiphertext.equivProd.symm

def bfvDecodeElemMod (params : LWEParams) (Δ t : ℕ) [ht : Fact (0 < t)] (y : Zq params) : Fin t :=
  ⟨bfvDecodeElem params Δ y % t, Nat.mod_lt _ ht.out⟩

def bfvDecodePolyMod (params : LWEParams) (N Δ t : ℕ) [Fact (0 < t)]
    (p : NegacyclicPoly (Zq params) N) : Fin N → Fin t :=
  fun k => bfvDecodeElemMod params Δ t (p.coeffs k)

def bfvEncodePolyFin (params : LWEParams) (N Δ t : ℕ) (m : Fin N → Fin t) :
    NegacyclicPoly (Zq params) N :=
  bfvEncodePoly params N Δ (fun k => (m k : ℕ))

theorem bfvDecodePolyMod_eq_of_bfvDecodePoly_eq (params : LWEParams) (N Δ t : ℕ) [Fact (0 < t)]
    (p : NegacyclicPoly (Zq params) N) (m : Fin N → Fin t)
    (h : bfvDecodePoly params N Δ p = fun k => (m k : ℕ)) :
    bfvDecodePolyMod params N Δ t p = m := by
  funext k
  apply Fin.ext
  dsimp [bfvDecodePolyMod, bfvDecodeElemMod]
  have hk := congrFun h k
  dsimp [bfvDecodePoly] at hk
  rw [hk, Nat.mod_eq_of_lt (m k).isLt]

def modFOEncPKE {Coins : Type*} (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (m : Fin N → Fin t) (c : Coins) :
    ModPKECiphertext (NegacyclicPoly (Zq params) N) k :=
  modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
    (expandR c) (expandE1 c) (expandE2 c) (bfvEncodePolyFin params N Δ t m)

def modFODecPKE (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) : Fin N → Fin t :=
  bfvDecodePolyMod params N Δ t (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s)

def modKEMEncapsFin {Key Coins : Type*} (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (m : Fin N → Fin t) :
    ModPKECiphertext (NegacyclicPoly (Zq params) N) k × Key :=
  let kc := G pk m
  let ct := modFOEncPKE params k N Δ t expandR expandE1 expandE2 pk m kc.2
  (ct, kc.1)

def modKEMDecapsFin {Key Coins Seed : Type*} (params : LWEParams) (k N Δ t : ℕ)
    [Fact (0 < N)] [Fact (0 < t)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) : Key :=
  let m' := modFODecPKE params k N Δ t s ct
  let kc' := G pk m'
  let ct' := modFOEncPKE params k N Δ t expandR expandE1 expandE2 pk m' kc'.2
  if ct = ct' then kc'.1 else J z ct

theorem modKEMDecapsFin_eq_foDecapsReal {Key Coins Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) :
    modKEMDecapsFin params k N Δ t G expandR expandE1 expandE2 J pk s z ct =
      foDecapsReal
        (modFOEncPKE params k N Δ t expandR expandE1 expandE2)
        (modFODecPKE params k N Δ t) G J pk s z ct := by
  dsimp [modKEMDecapsFin, foDecapsReal, foEncDet]
  have h_comm :
      (ct = modFOEncPKE params k N Δ t expandR expandE1 expandE2 pk
        (modFODecPKE params k N Δ t s ct)
        (G pk (modFODecPKE params k N Δ t s ct)).2) ↔
      (modFOEncPKE params k N Δ t expandR expandE1 expandE2 pk
        (modFODecPKE params k N Δ t s ct)
        (G pk (modFODecPKE params k N Δ t s ct)).2 = ct) := eq_comm
  by_cases h : ct = modFOEncPKE params k N Δ t expandR expandE1 expandE2 pk
      (modFODecPKE params k N Δ t s ct) (G pk (modFODecPKE params k N Δ t s ct)).2
  · rw [if_pos h, if_pos (h_comm.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (h_comm.mpr h'))]

theorem modPKE_instIsCorrectFOPKE (params : LWEParams) (k N Δ t : ℕ)
    [Fact (0 < N)] [Fact (0 < t)] {Coins Key : Type*}
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (ht_le : Δ * t ≤ params.q)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin k, normInf params (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf params (expandE2 c).coeffs ≤ 1)
    (h_zero_fail : 2 * (2 * k * N + 1) < Δ) :
    IsCorrectFOPKE
      (modFOEncPKE params k N Δ t expandR expandE1 expandE2)
      (modFODecPKE params k N Δ t) G
      (modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e) s := by
  intro m
  let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
  set c := (G pk m).2
  have h_bound := modPKE_ternary_noise_bound params k N s e
    (expandR c) (expandE1 c) (expandE2 c)
    (hr_tern c) hs_tern he_norm (he1_norm c) (he2_norm c)
  have h_noise : 2 * normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e (expandR c) + expandE2 c -
        dotProductR (NegacyclicPoly (Zq params) N) k s (expandE1 c)).coeffs < Δ := by omega
  have h_dec := modPKE_decrypt_correct params k N Δ t A s e
    (expandR c) (expandE1 c) (expandE2 c) (fun idx => (m idx : ℕ)) ht_le
    (fun idx => (m idx).isLt) h_noise
  exact bfvDecodePolyMod_eq_of_bfvDecodePoly_eq params N Δ t _ m h_dec

theorem foBadDecapsEvent_reprogramKey_iff {PK SK Msg Coins Key CT : Type*} [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (m_star : Msg) (k_new : Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (ct : CT) :
    foBadDecapsEvent encPKE decPKE (foReprogramKey G m_star k_new) Q_G pk sk ct ↔
      foBadDecapsEvent encPKE decPKE G Q_G pk sk ct := by
  dsimp [foBadDecapsEvent]
  rw [foEncDet_reprogramKey_eq]

theorem FinDist.eventMass_congr {α : Type*} [Fintype α] (dist : FinDist α)
    (E1 E2 : α → Prop) [DecidablePred E1] [DecidablePred E2]
    (h_iff : ∀ x : α, E1 x ↔ E2 x) :
    dist.eventMass E1 = dist.eventMass E2 := by
  dsimp [FinDist.eventMass]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : E1 x
  · rw [if_pos hx, if_pos ((h_iff x).mp hx)]
  · rw [if_neg hx, if_neg (fun h => hx ((h_iff x).mpr h))]

theorem fo_non_challenge_valid_ne_m_star {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK) {m_star : Msg} {ct : CT}
    (h_ne : ct ≠ foEncDet encPKE G pk m_star)
    (h_enc : foEncDet encPKE G pk (decPKE sk ct) = ct) :
    decPKE sk ct ≠ m_star := by
  intro h_m
  rw [h_m] at h_enc
  exact h_ne h_enc.symm

theorem modKEM_fo_ind_cca2_end_to_end
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)] [Fact (0 < t)]
    {Coins Key Seed : Type*} [Fintype Key] {q_D : ℕ}
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (Q_G : (Fin N → Fin t) → Finset (Fin N → Fin t))
    (ct_queries : (Fin N → Fin t) → Fin q_D → ModPKECiphertext (NegacyclicPoly (Zq params) N) k)
    (adv : ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key → (Fin q_D → Key) → Bool)
    (ht_le : Δ * t ≤ params.q)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin k, normInf params (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf params (expandE2 c).coeffs ≤ 1)
    (h_zero_fail : 2 * (2 * k * N + 1) < Δ)
    (h_non_chal : ∀ (m_star : Fin N → Fin t) (i : Fin q_D),
      ct_queries m_star i ≠
        (modKEMEncapsFin params k N Δ t G expandR expandE1 expandE2
          (modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e) m_star).1) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let encPKE := modFOEncPKE params k N Δ t expandR expandE1 expandE2
    let decPKE := modFODecPKE params k N Δ t
    IsCorrectFOPKE encPKE decPKE G pk s ∧
    Function.Injective (foEncDet encPKE G pk) ∧
    (∀ m : Fin N → Fin t,
      let enc := modKEMEncapsFin params k N Δ t G expandR expandE1 expandE2 pk m
      modKEMDecapsFin params k N Δ t G expandR expandE1 expandE2 J pk s z enc.1 = enc.2) ∧
    (∀ (m_star : Fin N → Fin t) (i : Fin q_D),
      foEncDet encPKE G pk (decPKE s (ct_queries m_star i)) = ct_queries m_star i →
        decPKE s (ct_queries m_star i) ≠ m_star) ∧
    (let Ω := (Fin N → Fin t) × (Key × Key)
     let dist : FinDist Ω := uniformFinDist Ω
     let RealKEM0 : Ω → Bool := fun ω =>
       let m_star := ω.1
       let k0 := ω.2.1
       let G' := foReprogramKey G m_star k0
       let ct_star := (modKEMEncapsFin params k N Δ t G' expandR expandE1 expandE2 pk m_star).1
       adv ct_star k0
         (fun i => modKEMDecapsFin params k N Δ t G' expandR expandE1 expandE2 J pk s z
           (ct_queries m_star i))
     let RealKEM1 : Ω → Bool := fun ω =>
       let m_star := ω.1
       let k0 := ω.2.1
       let k1 := ω.2.2
       let G' := foReprogramKey G m_star k0
       let ct_star := (modKEMEncapsFin params k N Δ t G' expandR expandE1 expandE2 pk m_star).1
       adv ct_star k1
         (fun i => modKEMDecapsFin params k N Δ t G' expandR expandE1 expandE2 J pk s z
           (ct_queries m_star i))
     let BadDecapsG : Ω → Prop := fun ω =>
       ∃ i : Fin q_D, foBadDecapsEvent encPKE decPKE G (Q_G ω.1) pk s (ct_queries ω.1 i)
     let QueryChallenge : Ω → Prop := fun ω => ω.1 ∈ Q_G ω.1
     (dist.acceptWeight RealKEM0 - dist.acceptWeight RealKEM1).natAbs ≤
       2 * dist.eventMass BadDecapsG + 2 * dist.eventMass QueryChallenge) := by
  intro pk encPKE decPKE
  have h_corr : IsCorrectFOPKE encPKE decPKE G pk s :=
    modPKE_instIsCorrectFOPKE params k N Δ t G expandR expandE1 expandE2 A s e
      ht_le hs_tern he_norm hr_tern he1_norm he2_norm h_zero_fail
  refine ⟨h_corr, foEncDet_injective_of_correct encPKE decPKE G pk s h_corr, ?_, ?_, ?_⟩
  · intro m enc
    have hm : decPKE s (foEncDet encPKE G pk m) = m := h_corr m
    change modKEMDecapsFin params k N Δ t G expandR expandE1 expandE2 J pk s z
      (foEncDet encPKE G pk m) = (G pk m).1
    rw [modKEMDecapsFin_eq_foDecapsReal]
    dsimp [foDecapsReal]
    dsimp only [decPKE, encPKE] at hm
    rw [hm, if_pos rfl]
  · intro m_star i h_enc
    exact fo_non_challenge_valid_ne_m_star encPKE decPKE G pk s (h_non_chal m_star i) h_enc
  · intro Ω dist RealKEM0 RealKEM1 BadDecapsG QueryChallenge
    have h_red := fo_concrete_ind_cca2_reduction encPKE decPKE G J pk s z Q_G ct_queries adv
    have h_dec_eq :
        ∀ (G' : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → Fin t) → Key × Coins)
          (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k),
          modKEMDecapsFin params k N Δ t G' expandR expandE1 expandE2 J pk s z ct =
            foDecapsReal encPKE decPKE G' J pk s z ct :=
      fun G' ct => modKEMDecapsFin_eq_foDecapsReal params k N Δ t G' expandR expandE1 expandE2
        J pk s z ct
    have h_rk0 :
        RealKEM0 =
          (fun ω : Ω =>
            let G' := foReprogramKey G ω.1 ω.2.1
            adv (foEncDet encPKE G' pk ω.1) ω.2.1
              (fun i => foDecapsReal encPKE decPKE G' J pk s z (ct_queries ω.1 i))) := by
      ext ω
      dsimp [RealKEM0, modKEMEncapsFin, foEncDet]
      simp_rw [h_dec_eq]
      rfl
    have h_rk1 :
        RealKEM1 =
          (fun ω : Ω =>
            let G' := foReprogramKey G ω.1 ω.2.1
            adv (foEncDet encPKE G' pk ω.1) ω.2.2
              (fun i => foDecapsReal encPKE decPKE G' J pk s z (ct_queries ω.1 i))) := by
      ext ω
      dsimp [RealKEM1, modKEMEncapsFin, foEncDet]
      simp_rw [h_dec_eq]
      rfl
    have h_bad_mass :
        dist.eventMass
            (fun ω : Ω =>
              ∃ i : Fin q_D,
                foBadDecapsEvent encPKE decPKE (foReprogramKey G ω.1 ω.2.1) (Q_G ω.1) pk s
                  (ct_queries ω.1 i)) =
          dist.eventMass BadDecapsG := by
      apply FinDist.eventMass_congr
      intro ω
      dsimp [BadDecapsG]
      exact exists_congr (fun i =>
        foBadDecapsEvent_reprogramKey_iff encPKE decPKE G ω.1 ω.2.1 (Q_G ω.1) pk s
          (ct_queries ω.1 i))
    rw [h_rk0, h_rk1]
    rw [← h_bad_mass]
    exact h_red

end FujisakiOkamotoINDCCA2Reduction

section BitPackingSerialization

open scoped BigOperators

def packDigits (B : ℕ) : ∀ {N : ℕ}, (Fin N → ℕ) → ℕ
  | 0, _ => 0
  | _ + 1, c => c 0 + B * packDigits B (fun i => c i.succ)

def unpackDigits (B N : ℕ) (P : ℕ) (i : Fin N) : ℕ :=
  (P / B ^ (i : ℕ)) % B

theorem packDigits_eq_sum (B : ℕ) :
    ∀ (N : ℕ) (c : Fin N → ℕ), packDigits B c = ∑ i : Fin N, c i * B ^ (i : ℕ)
  | 0, _ => by simp [packDigits]
  | N + 1, c => by
    rw [packDigits, packDigits_eq_sum B N (fun i => c i.succ), Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ']
    ring

theorem packDigits_lt (B : ℕ) (hB : 0 < B) :
    ∀ (N : ℕ) (c : Fin N → ℕ), (∀ i : Fin N, c i < B) → packDigits B c < B ^ N
  | 0, _, _ => by simp [packDigits]
  | N + 1, c, hc => by
    rw [packDigits, pow_succ']
    have h0 : c 0 < B := hc 0
    have h_tail : packDigits B (fun i => c i.succ) < B ^ N :=
      packDigits_lt B hB N (fun i => c i.succ) (fun i => hc i.succ)
    have h_le : packDigits B (fun i => c i.succ) + 1 ≤ B ^ N := h_tail
    have h_mul : B * (packDigits B (fun i => c i.succ) + 1) ≤ B * B ^ N :=
      Nat.mul_le_mul_left B h_le
    rw [Nat.mul_add, Nat.mul_one] at h_mul
    omega

theorem unpackDigits_packDigits_id (B : ℕ) (hB : 0 < B) :
    ∀ (N : ℕ) (c : Fin N → ℕ), (∀ i : Fin N, c i < B) →
      unpackDigits B N (packDigits B c) = c
  | 0, c, _ => by
    ext i
    exact Fin.elim0 i
  | N + 1, c, hc => by
    ext i
    cases i using Fin.cases with
    | zero =>
      dsimp [unpackDigits, packDigits]
      simp only [Nat.div_one]
      have h_mod : (c 0 + B * packDigits B (fun j => c j.succ)) % B = c 0 % B :=
        Nat.add_mul_mod_self_left (c 0) B (packDigits B (fun j => c j.succ))
      rw [h_mod, Nat.mod_eq_of_lt (hc 0)]
    | succ j =>
      dsimp [unpackDigits, packDigits]
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      have h_div :
          (c 0 + B * packDigits B (fun k => c k.succ)) / B =
            c 0 / B + packDigits B (fun k => c k.succ) :=
        Nat.add_mul_div_left (c 0) (packDigits B (fun k => c k.succ)) hB
      rw [h_div, Nat.div_eq_of_lt (hc 0), zero_add]
      have ih := unpackDigits_packDigits_id B hB N (fun k => c k.succ) (fun k => hc k.succ)
      exact congr_fun ih j

def packBitsToBytes (d N M : ℕ) (c : Fin N → ℕ) : Fin M → ℕ :=
  unpackDigits 256 M (packDigits (2 ^ d) c)

def unpackBitsFromBytes (d N M : ℕ) (bytes : Fin M → ℕ) : Fin N → ℕ :=
  unpackDigits (2 ^ d) N (∑ k : Fin M, bytes k * 256 ^ (k : ℕ))

theorem unpackBitsFromBytes_packBitsToBytes_id (d N M : ℕ)
    (h_len : N * d ≤ 8 * M) (c : Fin N → ℕ) (hc : ∀ i : Fin N, c i < 2 ^ d) :
    unpackBitsFromBytes d N M (packBitsToBytes d N M c) = c := by
  dsimp [unpackBitsFromBytes, packBitsToBytes]
  have hd_pos : 0 < 2 ^ d := Nat.pow_pos (by decide)
  have h_lt_pow : packDigits (2 ^ d) c < (2 ^ d) ^ N := packDigits_lt (2 ^ d) hd_pos N c hc
  have h_pow_eq : (2 ^ d) ^ N = 2 ^ (N * d) := by
    rw [← Nat.pow_mul, Nat.mul_comm d N]
  have h_256_eq : 256 ^ M = 2 ^ (8 * M) := by
    have h8 : (256 : ℕ) = 2 ^ 8 := by decide
    rw [h8, ← Nat.pow_mul]
  have h_le_pow : 2 ^ (N * d) ≤ 2 ^ (8 * M) :=
    Nat.pow_le_pow_right (by decide) h_len
  have h_lt_bytes : packDigits (2 ^ d) c < 256 ^ M := by omega
  have h_byte_sum := nat_base_decomp_sum 256 M (packDigits (2 ^ d) c) h_lt_bytes
  dsimp [unpackDigits]
  rw [h_byte_sum]
  exact unpackDigits_packDigits_id (2 ^ d) hd_pos N c hc

theorem unpackBitsFromBytes_packBitsToBytes_compress_id (q d N M : ℕ)
    (h_len : N * d ≤ 8 * M) (x : Fin N → ℕ) :
    unpackBitsFromBytes d N M (packBitsToBytes d N M (fun i => lweCompressCoeff q d (x i))) =
      fun i => lweCompressCoeff q d (x i) :=
  unpackBitsFromBytes_packBitsToBytes_id d N M h_len (fun i => lweCompressCoeff q d (x i))
    (fun i => lweCompressCoeff_lt q d (x i))

end BitPackingSerialization

section FullRNSCRTAndGadget

open scoped BigOperators

def rnsCRTEquiv (q1 q2 : ℕ) (h_coprime : Nat.Coprime q1 q2) :
    ZMod (q1 * q2) ≃+* ZMod q1 × ZMod q2 :=
  ZMod.chineseRemainder h_coprime

def rnsPolyToPair {R1 R2 : Type*} {N : ℕ}
    (p : NegacyclicPoly (R1 × R2) N) : NegacyclicPoly R1 N × NegacyclicPoly R2 N :=
  (⟨fun k => (p.coeffs k).1⟩, ⟨fun k => (p.coeffs k).2⟩)

def rnsPairToPoly {R1 R2 : Type*} {N : ℕ}
    (pair : NegacyclicPoly R1 N × NegacyclicPoly R2 N) : NegacyclicPoly (R1 × R2) N :=
  ⟨fun k => (pair.1.coeffs k, pair.2.coeffs k)⟩

theorem rnsPairToPoly_rnsPolyToPair {R1 R2 : Type*} {N : ℕ}
    (p : NegacyclicPoly (R1 × R2) N) :
    rnsPairToPoly (rnsPolyToPair p) = p := by
  ext k <;> rfl

theorem rnsPolyToPair_rnsPairToPoly {R1 R2 : Type*} {N : ℕ}
    (pair : NegacyclicPoly R1 N × NegacyclicPoly R2 N) :
    rnsPolyToPair (rnsPairToPoly pair) = pair := by
  cases pair
  rfl

theorem rnsPolyToPair_add {R1 R2 : Type*} [CommRing R1] [CommRing R2] {N : ℕ}
    (p q : NegacyclicPoly (R1 × R2) N) :
    rnsPolyToPair (p + q) = rnsPolyToPair p + rnsPolyToPair q := by
  rfl

theorem rnsPolyToPair_mul {R1 R2 : Type*} [CommRing R1] [CommRing R2] {N : ℕ} [Fact (0 < N)]
    (p q : NegacyclicPoly (R1 × R2) N) :
    rnsPolyToPair (p * q) = rnsPolyToPair p * rnsPolyToPair q := by
  ext k
  · simp only [rnsPolyToPair, Prod.fst_mul, NegacyclicPoly.mul_coeffs, Prod.fst_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · simp [NegacyclicPoly.negacyclicSign]
    · rfl
  · simp only [rnsPolyToPair, Prod.snd_mul, NegacyclicPoly.mul_coeffs, Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · simp [NegacyclicPoly.negacyclicSign]
    · rfl

def rnsLimbGadget {L : ℕ} (R : Type*) [CommRing R] : VectorR (Fin L → R) L :=
  fun i j => if i = j then 1 else 0

def rnsLimbDecomp {L : ℕ} (R : Type*) [CommRing R]
    (x : Fin L → R) : VectorR (Fin L → R) L :=
  fun i j => if i = j then x j else 0

theorem rnsLimbDecomp_isValid {L : ℕ} (R : Type*) [CommRing R] :
    IsValidDecomposition (rnsLimbGadget R (L := L)) (rnsLimbDecomp R (L := L)) := by
  intro x
  ext j
  rw [Finset.sum_apply]
  dsimp [rnsLimbGadget, rnsLimbDecomp]
  have h_term : ∀ i : Fin L,
      (if i = j then x j else 0) * (if i = j then (1 : R) else 0) =
        if i = j then x j else 0 := by
    intro i
    split_ifs <;> ring
  simp_rw [h_term]
  simp

theorem rnsBFVGadgetRelinearize_phase {L : ℕ} (R : Type*) [CommRing R]
    (s d0 d1 d2 : Fin L → R)
    (a_rk e_rk : VectorR (Fin L → R) L) :
    let rk := mkBFVGadgetRelinKey (Fin L → R) a_rk e_rk s (rnsLimbGadget R)
    let ct_relin := bfvGadgetRelinearize (Fin L → R) d0 d1 d2 (rnsLimbDecomp R) rk
    bfvPhase (Fin L → R) ct_relin s =
      (d0 + d1 * s + d2 * (s * s)) - ∑ i : Fin L, rnsLimbDecomp R d2 i * e_rk i :=
  bfvGadgetRelinearize_phase (Fin L → R) s d0 d1 d2 a_rk e_rk
    (rnsLimbGadget R) (rnsLimbDecomp R) (rnsLimbDecomp_isValid R)

theorem fastBconv_sum_le (L Q : ℕ) (hQ : 0 < Q) (term : Fin L → ℕ)
    (h_term : ∀ i : Fin L, term i < Q) :
    (∑ i : Fin L, term i) ≤ L * (Q - 1) := by
  have h_le : ∀ i : Fin L, term i ≤ Q - 1 := by
    intro i
    have hi := h_term i
    omega
  have h_sum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin L))) (fun i _ => h_le i)
  simpa using h_sum

theorem fastBconv_eq_add_mul_overflow (L Q x : ℕ) (term : Fin L → ℕ)
    (h_mod : (∑ i : Fin L, term i) % Q = x) :
    (∑ i : Fin L, term i) = x + ((∑ i : Fin L, term i) / Q) * Q := by
  have h_div := Nat.mod_add_div (∑ i : Fin L, term i) Q
  rw [h_mod, Nat.mul_comm Q] at h_div
  exact h_div.symm

theorem fastBconv_overflow_lt (L Q : ℕ) (hL : 0 < L) (hQ : 0 < Q)
    (term : Fin L → ℕ) (h_term : ∀ i : Fin L, term i < Q) :
    (∑ i : Fin L, term i) / Q < L := by
  have h_sum_le := fastBconv_sum_le L Q hQ term h_term
  have h_lt : (∑ i : Fin L, term i) < Q * L := by
    have h_expand : L * (Q - 1) + L = L * Q := by
      cases Q with
      | zero => omega
      | succ q' =>
        simp [Nat.mul_add]
    have h_comm : L * Q = Q * L := Nat.mul_comm L Q
    omega
  exact Nat.div_lt_of_lt_mul h_lt

lemma coprime_finset_prod_right {ι : Type*} (a : ℕ) (s : Finset ι) (f : ι → ℕ)
    (h : ∀ j ∈ s, Nat.Coprime a (f j)) :
    Nat.Coprime a (∏ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.prod_insert hb]
    exact (h b (Finset.mem_insert_self b s)).mul_right
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma coprime_finset_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℕ) (b : ℕ)
    (h : ∀ j ∈ s, Nat.Coprime (f j) b) :
    Nat.Coprime (∏ j ∈ s, f j) b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul_left
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma finset_prod_dvd_of_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ) (m : ℕ)
    (h_cop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ j ∈ s, f j ∣ m) :
    (∏ j ∈ s, f j) ∣ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.prod_insert hb]
    have hb_dvd : f b ∣ m := hdvd b (Finset.mem_insert_self b s)
    have hs_dvd : (∏ j ∈ s, f j) ∣ m := by
      apply ih
      · intro i hi j hj hij
        exact h_cop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      · intro j hj
        exact hdvd j (Finset.mem_insert_of_mem hj)
    have h_cop_prod : Nat.Coprime (f b) (∏ j ∈ s, f j) := by
      apply coprime_finset_prod_right
      intro j hj
      have hne : b ≠ j := fun h => hb (h ▸ hj)
      exact h_cop b (Finset.mem_insert_self b s) j (Finset.mem_insert_of_mem hj) hne
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h_cop_prod hb_dvd hs_dvd

def zmodCongr {a b : ℕ} (h : a = b) : ZMod a ≃+* ZMod b := by
  subst h
  exact RingEquiv.refl (ZMod a)

def piFinSuccRingEquiv {L : ℕ} (R : Fin (L + 1) → Type*) [∀ j, CommRing (R j)] :
    R 0 × (∀ j : Fin L, R j.succ) ≃+* (∀ j : Fin (L + 1), R j) where
  toFun p j := Fin.cases p.1 p.2 j
  invFun f := (f 0, fun j => f j.succ)
  left_inv p := by
    rcases p with ⟨a, b⟩
    ext
    · simp
    · simp
  right_inv f := by
    ext j
    cases j using Fin.cases <;> simp
  map_mul' p q := by
    ext j
    cases j using Fin.cases <;> simp
  map_add' p q := by
    ext j
    cases j using Fin.cases <;> simp

def rnsModulusProd {L : ℕ} (q : Fin L → ℕ) : ℕ :=
  ∏ j : Fin L, q j

def rnsMultiCRTEquiv :
    ∀ {L : ℕ} (q : Fin L → ℕ),
      Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)) →
      ZMod (∏ j : Fin L, q j) ≃+* (∀ j : Fin L, ZMod (q j))
  | 0, q, _ =>
    let h_one : (∏ j : Fin 0, q j) = 1 := by simp
    let e0 : ZMod 1 ≃+* (∀ j : Fin 0, ZMod (q j)) :=
      { toFun := fun _ j => Fin.elim0 j
        invFun := fun _ => 0
        left_inv := fun x => by
          haveI : NeZero 1 := ⟨one_ne_zero⟩
          have hlt := ZMod.val_lt x
          have hv : ZMod.val x = 0 := by omega
          rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_zero]
        right_inv := fun f => funext fun j => Fin.elim0 j
        map_mul' := fun _ _ => funext fun j => Fin.elim0 j
        map_add' := fun _ _ => funext fun j => Fin.elim0 j }
    (zmodCongr h_one).trans e0
  | L + 1, q, h_cop =>
    let h_prod : (∏ j : Fin (L + 1), q j) = q 0 * ∏ j : Fin L, q j.succ := Fin.prod_univ_succ q
    let h_cop_head : Nat.Coprime (q 0) (∏ j : Fin L, q j.succ) :=
      coprime_finset_prod_right (q 0) Finset.univ (fun j : Fin L => q j.succ)
        (fun j _ => h_cop (fun h => by
          have hv := congrArg Fin.val h
          rw [Fin.val_zero, Fin.val_succ] at hv
          exact Nat.zero_ne_add_one _ hv))
    let h_cop_tail : Pairwise (fun i j : Fin L => Nat.Coprime (q i.succ) (q j.succ)) :=
      fun _ _ hij => h_cop (fun h => hij (Fin.ext (by
        have hv := congrArg Fin.val h
        rw [Fin.val_succ, Fin.val_succ] at hv
        exact Nat.succ.inj hv)))
    (zmodCongr h_prod).trans
      ((ZMod.chineseRemainder h_cop_head).trans
        ((RingEquiv.prodCongr (RingEquiv.refl (ZMod (q 0)))
          (rnsMultiCRTEquiv (fun j => q j.succ) h_cop_tail)).trans
          (piFinSuccRingEquiv (fun j => ZMod (q j)))))

theorem rnsMultiCRTEquiv_natCast {L : ℕ} (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (n : ℕ) (j : Fin L) :
    rnsMultiCRTEquiv q h_cop (n : ZMod (∏ i : Fin L, q i)) j = (n : ZMod (q j)) := by
  rw [map_natCast]
  rfl

theorem rnsMultiCRTEquiv_intCast {L : ℕ} (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (z : ℤ) (j : Fin L) :
    rnsMultiCRTEquiv q h_cop (z : ZMod (∏ i : Fin L, q i)) j = (z : ZMod (q j)) := by
  rw [map_intCast]
  rfl

theorem rnsMultiCRTEquiv_symm_intCast {L : ℕ} (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j))) (z : ℤ) :
    (rnsMultiCRTEquiv q h_cop).symm (fun j : Fin L => (z : ZMod (q j))) =
      (z : ZMod (∏ i : Fin L, q i)) := by
  apply (rnsMultiCRTEquiv q h_cop).injective
  rw [(rnsMultiCRTEquiv q h_cop).apply_symm_apply]
  ext j
  exact (rnsMultiCRTEquiv_intCast q h_cop z j).symm

theorem rnsMultiCRTEquiv_apply_castHom {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ZMod (∏ i : Fin L, q i)) (j : Fin L) :
    rnsMultiCRTEquiv q h_cop x j =
      ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ j)) (ZMod (q j)) x := by
  haveI : NeZero (∏ i : Fin L, q i) := ⟨ne_of_gt (Finset.prod_pos (fun i _ => hq_pos i))⟩
  rw [← ZMod.natCast_zmod_val x, rnsMultiCRTEquiv_natCast, map_natCast]

def rnsHatQ {L : ℕ} (q : Fin L → ℕ) (i : Fin L) : ℕ :=
  ∏ j ∈ Finset.univ.erase i, q j

lemma rnsHatQ_mul_eq_prod {L : ℕ} (q : Fin L → ℕ) (i : Fin L) :
    q i * rnsHatQ q i = ∏ j : Fin L, q j :=
  Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i)

lemma coprime_rnsHatQ {L : ℕ} (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j))) (i : Fin L) :
    Nat.Coprime (rnsHatQ q i) (q i) := by
  apply coprime_finset_prod_left
  intro j hj
  exact h_cop (Finset.mem_erase.mp hj).1

def rnsCRTWeight {L : ℕ} (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ∀ j : Fin L, ZMod (q j)) (i : Fin L) : ℕ :=
  ZMod.val
    (x i *
      (((ZMod.unitOfCoprime (rnsHatQ q i) (coprime_rnsHatQ q h_cop i))⁻¹ : (ZMod (q i))ˣ) :
        ZMod (q i)))

theorem rnsCRTReconstruct_sum_cast_eq_symm {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ∀ j : Fin L, ZMod (q j)) :
    (((∑ i : Fin L, rnsCRTWeight q h_cop x i * rnsHatQ q i : ℕ) :
        ZMod (∏ j : Fin L, q j))) =
      (rnsMultiCRTEquiv q h_cop).symm x := by
  apply (rnsMultiCRTEquiv q h_cop).injective
  rw [(rnsMultiCRTEquiv q h_cop).apply_symm_apply]
  ext j
  rw [rnsMultiCRTEquiv_natCast]
  push_cast
  rw [Finset.sum_eq_single j]
  · haveI : NeZero (q j) := ⟨ne_of_gt (hq_pos j)⟩
    let u := ZMod.unitOfCoprime (rnsHatQ q j) (coprime_rnsHatQ q h_cop j)
    have h_val : (rnsCRTWeight q h_cop x j : ZMod (q j)) =
        x j * ((u⁻¹ : (ZMod (q j))ˣ) : ZMod (q j)) :=
      ZMod.natCast_zmod_val (x j * ((u⁻¹ : (ZMod (q j))ˣ) : ZMod (q j)))
    have h_hat : ((rnsHatQ q j : ℕ) : ZMod (q j)) = (u : ZMod (q j)) :=
      (ZMod.coe_unitOfCoprime (rnsHatQ q j) (coprime_rnsHatQ q h_cop j)).symm
    rw [h_val, h_hat, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  · intro i _ hij
    have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    have hdvd : q j ∣ rnsHatQ q i := Finset.dvd_prod_of_mem q hj_mem
    have h_zero : ((rnsHatQ q i : ℕ) : ZMod (q j)) = 0 :=
      (ZMod.natCast_eq_zero_iff (rnsHatQ q i) (q j)).mpr hdvd
    rw [h_zero, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

theorem rnsCRTReconstruct_overflow_lt {L : ℕ} (hL : 0 < L) (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ∀ j : Fin L, ZMod (q j)) :
    (∑ i : Fin L, rnsCRTWeight q h_cop x i * rnsHatQ q i) / (∏ j : Fin L, q j) < L := by
  let Q : ℕ := ∏ j : Fin L, q j
  have hQ_pos : 0 < Q := Finset.prod_pos (fun j _ => hq_pos j)
  apply fastBconv_overflow_lt L Q hL hQ_pos
  intro i
  haveI : NeZero (q i) := ⟨ne_of_gt (hq_pos i)⟩
  have hw_lt : rnsCRTWeight q h_cop x i < q i := ZMod.val_lt _
  have h_hat_pos : 0 < rnsHatQ q i := by
    dsimp [rnsHatQ]
    exact Finset.prod_pos (fun j _ => hq_pos j)
  have h_mul_lt := Nat.mul_lt_mul_of_pos_right hw_lt h_hat_pos
  rwa [rnsHatQ_mul_eq_prod q i] at h_mul_lt

def negacyclicMapHom {R S : Type*} [CommRing R] [CommRing S] (N : ℕ) [Fact (0 < N)]
    (f : R →+* S) : NegacyclicPoly R N →+* NegacyclicPoly S N where
  toFun p := ⟨fun k => f (p.coeffs k)⟩
  map_one' := by
    ext k
    change f (if (k : ℕ) = 0 then (1 : R) else 0) = if (k : ℕ) = 0 then (1 : S) else 0
    split_ifs <;> simp
  map_mul' p q := by
    ext k
    simp only [NegacyclicPoly.mul_coeffs, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [map_mul, map_mul]
      congr 2
      unfold NegacyclicPoly.negacyclicSign
      rw [map_pow, map_neg, map_one]
    · exact map_zero f
  map_zero' := by
    ext k
    exact map_zero f
  map_add' p q := by
    ext k
    exact map_add f (p.coeffs k) (q.coeffs k)

lemma negacyclicMapHom_coeffs {R S : Type*} [CommRing R] [CommRing S] (N : ℕ) [Fact (0 < N)]
    (f : R →+* S) (p : NegacyclicPoly R N) (k : Fin N) :
    (negacyclicMapHom N f p).coeffs k = f (p.coeffs k) := rfl

def negacyclicMapRingEquiv {R S : Type*} [CommRing R] [CommRing S] (N : ℕ) [Fact (0 < N)]
    (e : R ≃+* S) : NegacyclicPoly R N ≃+* NegacyclicPoly S N where
  toFun := negacyclicMapHom N e.toRingHom
  invFun := negacyclicMapHom N e.symm.toRingHom
  left_inv p := by
    ext k
    exact e.left_inv (p.coeffs k)
  right_inv p := by
    ext k
    exact e.right_inv (p.coeffs k)
  map_mul' := (negacyclicMapHom N e.toRingHom).map_mul
  map_add' := (negacyclicMapHom N e.toRingHom).map_add

def negacyclicPiRingEquiv {L N : ℕ} [Fact (0 < N)]
    (R : Fin L → Type*) [∀ j, CommRing (R j)] :
    NegacyclicPoly (∀ j : Fin L, R j) N ≃+* (∀ j : Fin L, NegacyclicPoly (R j) N) where
  toFun p j := ⟨fun k => p.coeffs k j⟩
  invFun f := ⟨fun k j => (f j).coeffs k⟩
  left_inv p := by
    ext k j
    rfl
  right_inv f := by
    funext j
    ext k
    rfl
  map_mul' p q := by
    funext j
    ext k
    simp only [NegacyclicPoly.mul_coeffs, Pi.mul_apply, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs
    · have h_sign : (NegacyclicPoly.negacyclicSign N ((a : ℕ) + (b : ℕ)) : ∀ i, R i) j =
          NegacyclicPoly.negacyclicSign N ((a : ℕ) + (b : ℕ)) := by
        unfold NegacyclicPoly.negacyclicSign
        simp
      change (NegacyclicPoly.negacyclicSign N ((a : ℕ) + (b : ℕ)) : ∀ i, R i) j *
          p.coeffs a j * q.coeffs b j = _
      rw [h_sign]
    · rfl
  map_add' p q := by
    funext j
    ext k
    rfl

def rnsPolyMultiCRTEquiv {L N : ℕ} [Fact (0 < N)] (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j))) :
    NegacyclicPoly (ZMod (∏ j : Fin L, q j)) N ≃+* (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N) :=
  (negacyclicMapRingEquiv N (rnsMultiCRTEquiv q h_cop)).trans
    (negacyclicPiRingEquiv (fun j => ZMod (q j)))

lemma rnsPolyMultiCRTEquiv_coeffs {L N : ℕ} [Fact (0 < N)] (q : Fin L → ℕ)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (p : NegacyclicPoly (ZMod (∏ j : Fin L, q j)) N) (j : Fin L) (k : Fin N) :
    (rnsPolyMultiCRTEquiv q h_cop p j).coeffs k = rnsMultiCRTEquiv q h_cop (p.coeffs k) j := rfl

def rnsParams {L : ℕ} (q : Fin L → ℕ) (hq_pos : ∀ j : Fin L, 0 < q j) : LWEParams :=
  { n := 1,
    m := 1,
    q := ∏ j : Fin L, q j,
    q_pos := ⟨Finset.prod_pos (fun j _ => hq_pos j)⟩ }

def rnsLimbParams {L : ℕ} (q : Fin L → ℕ) (hq_pos : ∀ j : Fin L, 0 < q j) (i : Fin L) :
    LWEParams :=
  { n := 1,
    m := 1,
    q := q i,
    q_pos := ⟨hq_pos i⟩ }

def rnsCRTGadget {L : ℕ} (q : Fin L → ℕ) : VectorR (∀ j : Fin L, ZMod (q j)) L :=
  fun i j => if i = j then 1 else 0

def rnsZeroPadDecomp {L : ℕ} (q : Fin L → ℕ) (x : ∀ j : Fin L, ZMod (q j)) :
    VectorR (∀ j : Fin L, ZMod (q j)) L :=
  fun i j => if h : j = i then h ▸ x i else 0

theorem rnsZeroPadDecomp_isValid {L : ℕ} (q : Fin L → ℕ) :
    IsValidDecomposition (rnsCRTGadget q) (rnsZeroPadDecomp q) := by
  intro x
  funext j
  rw [Finset.sum_apply]
  dsimp [rnsCRTGadget, rnsZeroPadDecomp]
  rw [Finset.sum_eq_single j]
  · rw [dif_pos rfl, if_pos rfl, mul_one]
  · intro i _ hij
    rw [if_neg hij, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

theorem rnsZeroPadDecomp_crt_norm_ge_hatQ {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ∀ j : Fin L, ZMod (q j)) (i : Fin L) (hx : x i ≠ 0) :
    rnsHatQ q i ≤
      norm (rnsParams q hq_pos) ((rnsMultiCRTEquiv q h_cop).symm (rnsZeroPadDecomp q x i)) := by
  let pQ := rnsParams q hq_pos
  let u : Zq pQ := (rnsMultiCRTEquiv q h_cop).symm (rnsZeroPadDecomp q x i)
  let z : ℤ := centeredLift pQ u
  have hz_cast : (z : Zq pQ) = u := intCast_centeredLift pQ u
  have hz_limb : ∀ j : Fin L, (z : ZMod (q j)) = rnsZeroPadDecomp q x i j := by
    intro j
    calc
      (z : ZMod (q j)) = rnsMultiCRTEquiv q h_cop (z : Zq pQ) j :=
        (rnsMultiCRTEquiv_intCast q h_cop z j).symm
      _ = rnsMultiCRTEquiv q h_cop u j := by rw [hz_cast]
      _ = rnsZeroPadDecomp q x i j := by
        dsimp [u]
        rw [(rnsMultiCRTEquiv q h_cop).apply_symm_apply]
  have hz_ne : z ≠ 0 := by
    intro hz0
    have hi := hz_limb i
    rw [hz0, Int.cast_zero] at hi
    dsimp [rnsZeroPadDecomp] at hi
    rw [if_pos rfl] at hi
    exact hx hi.symm
  have hz_abs_pos : 0 < z.natAbs := Int.natAbs_pos.mpr hz_ne
  have hdvd_each : ∀ j ∈ Finset.univ.erase i, q j ∣ z.natAbs := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hj_zero : (z : ZMod (q j)) = 0 := by
      rw [hz_limb j]
      dsimp [rnsZeroPadDecomp]
      split_ifs with h
      · exact absurd h hji
      · rfl
    have hj_zdvd : (q j : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z (q j)).mp hj_zero
    rcases hj_zdvd with ⟨k, hk⟩
    refine ⟨k.natAbs, ?_⟩
    have h_abs : z.natAbs = ((q j : ℤ) * k).natAbs := by rw [hk]
    rw [h_abs, Int.natAbs_mul, Int.natAbs_natCast]
  have hdvd_hat : rnsHatQ q i ∣ z.natAbs := by
    apply finset_prod_dvd_of_coprime (Finset.univ.erase i) q z.natAbs
    · intro a _ b _ hab
      exact h_cop hab
    · exact hdvd_each
  exact Nat.le_of_dvd hz_abs_pos hdvd_hat

def rnsCenteredFastBconvDecomp {L : ℕ} (q : Fin L → ℕ) (hq_pos : ∀ j : Fin L, 0 < q j)
    (x : ∀ j : Fin L, ZMod (q j)) : VectorR (∀ j : Fin L, ZMod (q j)) L :=
  fun i _ => Int.cast (centeredLift (rnsLimbParams q hq_pos i) (x i))

theorem rnsCenteredFastBconvDecomp_isValid {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j) :
    IsValidDecomposition (rnsCRTGadget q) (rnsCenteredFastBconvDecomp q hq_pos) := by
  intro x
  funext j
  rw [Finset.sum_apply]
  dsimp [rnsCRTGadget, rnsCenteredFastBconvDecomp]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
    exact intCast_centeredLift (rnsLimbParams q hq_pos j) (x j)
  · intro i _ hij
    rw [if_neg hij, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

theorem rnsCenteredFastBconvDecomp_crt_symm {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ∀ j : Fin L, ZMod (q j)) (i : Fin L) :
    (rnsMultiCRTEquiv q h_cop).symm (rnsCenteredFastBconvDecomp q hq_pos x i) =
      Int.cast (centeredLift (rnsLimbParams q hq_pos i) (x i)) :=
  rnsMultiCRTEquiv_symm_intCast q h_cop (centeredLift (rnsLimbParams q hq_pos i) (x i))

theorem rnsCenteredFastBconvDecomp_crt_norm_le {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (x : ∀ j : Fin L, ZMod (q j)) (i : Fin L) :
    norm (rnsParams q hq_pos)
        ((rnsMultiCRTEquiv q h_cop).symm (rnsCenteredFastBconvDecomp q hq_pos x i)) ≤
      q i / 2 := by
  rw [rnsCenteredFastBconvDecomp_crt_symm]
  have h1 := norm_intCast_le_natAbs (rnsParams q hq_pos)
    (centeredLift (rnsLimbParams q hq_pos i) (x i))
  have h2 : (centeredLift (rnsLimbParams q hq_pos i) (x i)).natAbs ≤ q i / 2 :=
    norm_le_div_two (rnsLimbParams q hq_pos i) (x i)
  exact le_trans h1 h2

theorem rns_two_limb_decomp_contrast_97_113 :
    let q : Fin 2 → ℕ := ![97, 113]
    have hq_pos : ∀ j : Fin 2, 0 < q j := fun j => by fin_cases j <;> decide
    have h_cop : Pairwise (fun i j : Fin 2 => Nat.Coprime (q i) (q j)) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · decide
      · decide
      · exact False.elim (hij rfl)
    let x : ∀ j : Fin 2, ZMod (q j) := fun _ => 1
    113 ≤ norm (rnsParams q hq_pos) ((rnsMultiCRTEquiv q h_cop).symm (rnsZeroPadDecomp q x 0)) ∧
      norm (rnsParams q hq_pos)
        ((rnsMultiCRTEquiv q h_cop).symm (rnsCenteredFastBconvDecomp q hq_pos x 0)) ≤ 48 := by
  intro q hq_pos h_cop x
  have hx : x 0 ≠ 0 := by
    change (1 : ZMod 97) ≠ 0
    decide
  have h_hat : rnsHatQ q 0 = 113 := by
    dsimp [rnsHatQ, q]
    decide
  have h_ge := rnsZeroPadDecomp_crt_norm_ge_hatQ q hq_pos h_cop x 0 hx
  rw [h_hat] at h_ge
  have h_le := rnsCenteredFastBconvDecomp_crt_norm_le q hq_pos h_cop x 0
  have h_half : q 0 / 2 = 48 := by decide
  rw [h_half] at h_le
  exact ⟨h_ge, h_le⟩

def rnsPolyCRTGadget {L : ℕ} (q : Fin L → ℕ) (N : ℕ) [Fact (0 < N)] :
    VectorR (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N) L :=
  fun i j => if i = j then 1 else 0

def rnsPolyCenteredFastBconvDecomp {L : ℕ} (q : Fin L → ℕ) (hq_pos : ∀ j : Fin L, 0 < q j)
    (N : ℕ) (p : ∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N) :
    VectorR (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N) L :=
  fun i _ => ⟨fun k => Int.cast (centeredLift (rnsLimbParams q hq_pos i) ((p i).coeffs k))⟩

theorem rnsPolyCenteredFastBconvDecomp_isValid {L : ℕ} (q : Fin L → ℕ)
    (hq_pos : ∀ j : Fin L, 0 < q j) (N : ℕ) [Fact (0 < N)] :
    IsValidDecomposition (rnsPolyCRTGadget q N) (rnsPolyCenteredFastBconvDecomp q hq_pos N) := by
  intro p
  funext j
  rw [Finset.sum_apply]
  dsimp [rnsPolyCRTGadget, rnsPolyCenteredFastBconvDecomp]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, mul_one]
    ext k
    exact intCast_centeredLift (rnsLimbParams q hq_pos j) ((p j).coeffs k)
  · intro i _ hij
    rw [if_neg hij, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ j))

theorem rnsPolyCenteredFastBconv_relin_phase_and_noise_bound {L N B_rk : ℕ} [Fact (0 < N)]
    (q : Fin L → ℕ) (hq_pos : ∀ j : Fin L, 0 < q j)
    (h_cop : Pairwise (fun i j : Fin L => Nat.Coprime (q i) (q j)))
    (s d0 d1 d2 : ∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N)
    (a_rk e_rk : VectorR (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N) L)
    (herk : ∀ i : Fin L,
      normInf (rnsParams q hq_pos)
        ((rnsPolyMultiCRTEquiv q h_cop).symm (e_rk i)).coeffs ≤ B_rk) :
    let pQ := rnsParams q hq_pos
    let e_poly := rnsPolyMultiCRTEquiv q h_cop
    let rk := mkBFVGadgetRelinKey (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N)
      a_rk e_rk s (rnsPolyCRTGadget q N)
    let ct_relin := bfvGadgetRelinearize (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N)
      d0 d1 d2 (rnsPolyCenteredFastBconvDecomp q hq_pos N) rk
    let S : NegacyclicPoly (Zq pQ) N := e_poly.symm s
    let D0 : NegacyclicPoly (Zq pQ) N := e_poly.symm d0
    let D1 : NegacyclicPoly (Zq pQ) N := e_poly.symm d1
    let D2 : NegacyclicPoly (Zq pQ) N := e_poly.symm d2
    let ct_Q : BFVCiphertext (NegacyclicPoly (Zq pQ) N) :=
      { c0 := e_poly.symm ct_relin.c0, c1 := e_poly.symm ct_relin.c1 }
    ∃ E_relin : NegacyclicPoly (Zq pQ) N,
      bfvPhase (NegacyclicPoly (Zq pQ) N) ct_Q S = (D0 + D1 * S + D2 * (S * S)) - E_relin ∧
      normInf pQ E_relin.coeffs ≤ ∑ i : Fin L, N * (q i / 2) * B_rk := by
  intro pQ e_poly rk ct_relin S D0 D1 D2 ct_Q
  have h_rns := bfvGadgetRelinearize_phase (∀ j : Fin L, NegacyclicPoly (ZMod (q j)) N)
    s d0 d1 d2 a_rk e_rk (rnsPolyCRTGadget q N) (rnsPolyCenteredFastBconvDecomp q hq_pos N)
    (rnsPolyCenteredFastBconvDecomp_isValid q hq_pos N)
  dsimp only at h_rns
  let decomp := rnsPolyCenteredFastBconvDecomp q hq_pos N d2
  let E_relin : NegacyclicPoly (Zq pQ) N :=
    ∑ i : Fin L, e_poly.symm (decomp i) * e_poly.symm (e_rk i)
  refine ⟨E_relin, ?_, ?_⟩
  · have h_crt := congrArg e_poly.symm h_rns
    have h_lhs : e_poly.symm (bfvPhase _ ct_relin s) =
        bfvPhase (NegacyclicPoly (Zq pQ) N) ct_Q S := by
      change e_poly.symm (ct_relin.c0 + ct_relin.c1 * s) =
        e_poly.symm ct_relin.c0 + e_poly.symm ct_relin.c1 * e_poly.symm s
      rw [map_add, map_mul]
    have h_rhs :
        e_poly.symm ((d0 + d1 * s + d2 * (s * s)) - ∑ i : Fin L, decomp i * e_rk i) =
          (D0 + D1 * S + D2 * (S * S)) - E_relin := by
      dsimp [D0, D1, D2, S, E_relin, decomp]
      rw [map_sub, map_add, map_add, map_mul, map_mul, map_mul, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact map_mul e_poly.symm _ _
    exact h_lhs.symm.trans (h_crt.trans h_rhs)
  · have h_sum_le := normInf_finset_sum_poly_le pQ N Finset.univ
      (fun i : Fin L => e_poly.symm (decomp i) * e_poly.symm (e_rk i))
    have h_each : ∀ i ∈ (Finset.univ : Finset (Fin L)),
        normInf pQ (e_poly.symm (decomp i) * e_poly.symm (e_rk i)).coeffs ≤
          N * (q i / 2) * B_rk := by
      intro i _
      have h_mul := NegacyclicPoly.normInf_mul_le pQ N
        (e_poly.symm (decomp i)) (e_poly.symm (e_rk i))
      let Di_z : NegacyclicPoly ℤ N :=
        ⟨fun k => centeredLift (rnsLimbParams q hq_pos i) ((d2 i).coeffs k)⟩
      have h_lift_eq : e_poly.symm (decomp i) = NegacyclicPoly.intCastPolyHom pQ N Di_z := by
        apply e_poly.injective
        rw [e_poly.apply_symm_apply]
        funext j
        ext k
        rw [rnsPolyMultiCRTEquiv_coeffs, NegacyclicPoly.intCastPolyHom_coeffs]
        change (decomp i j).coeffs k =
          rnsMultiCRTEquiv q h_cop ((Di_z.coeffs k : ℤ) : ZMod (∏ i : Fin L, q i)) j
        rw [rnsMultiCRTEquiv_intCast]
        rfl
      have hDi_norm : NegacyclicPoly.intPolyNormInf Di_z ≤ q i / 2 := by
        dsimp [NegacyclicPoly.intPolyNormInf, Di_z]
        apply Finset.sup_le
        intro k _
        exact norm_le_div_two (rnsLimbParams q hq_pos i) ((d2 i).coeffs k)
      have h_dec_norm : normInf pQ (e_poly.symm (decomp i)).coeffs ≤ q i / 2 := by
        rw [h_lift_eq]
        exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le pQ N Di_z) hDi_norm
      have h1 : N * normInf pQ (e_poly.symm (decomp i)).coeffs ≤ N * (q i / 2) :=
        Nat.mul_le_mul_left N h_dec_norm
      exact le_trans h_mul (Nat.mul_le_mul h1 (herk i))
    exact le_trans h_sum_le (Finset.sum_le_sum h_each)

end FullRNSCRTAndGadget

section BGVAndCKKSFHE

open scoped BigOperators

def bgvKeygen (R : Type*) [CommRing R] (t a s e : R) : BFVPublicKey R :=
  { a := a, b := -(a * s + t * e) }

def bgvEncrypt (R : Type*) [CommRing R] (t : R) (pk : BFVPublicKey R)
    (u e0 e1 m : R) : BFVCiphertext R :=
  { c0 := pk.b * u + t * e0 + m,
    c1 := pk.a * u + t * e1 }

theorem bgvEncrypt_phase (R : Type*) [CommRing R] (t a s e u e0 e1 m : R) :
    bfvPhase R (bgvEncrypt R t (bgvKeygen R t a s e) u e0 e1 m) s =
      m + t * (e0 + e1 * s - e * u) := by
  dsimp [bfvPhase, bgvEncrypt, bgvKeygen]
  ring

theorem bgvAdd_phase_eq (R : Type*) [CommRing R] (t s m1 m2 E1 E2 : R)
    (ct1 ct2 : BFVCiphertext R)
    (h1 : bfvPhase R ct1 s = m1 + t * E1)
    (h2 : bfvPhase R ct2 s = m2 + t * E2) :
    bfvPhase R (bfvAdd R ct1 ct2) s = (m1 + m2) + t * (E1 + E2) := by
  rw [bfvAdd_phase, h1, h2]
  ring

theorem bgvMul_tensor_phase_eq (R : Type*) [CommRing R] (t s m1 m2 E1 E2 : R)
    (ct1 ct2 : BFVCiphertext R)
    (h1 : bfvPhase R ct1 s = m1 + t * E1)
    (h2 : bfvPhase R ct2 s = m2 + t * E2) :
    ct1.c0 * ct2.c0 + (ct1.c0 * ct2.c1 + ct1.c1 * ct2.c0) * s +
        (ct1.c1 * ct2.c1) * (s * s) =
      m1 * m2 + t * (m1 * E2 + m2 * E1 + t * E1 * E2) := by
  have h_prod :
      ct1.c0 * ct2.c0 + (ct1.c0 * ct2.c1 + ct1.c1 * ct2.c0) * s +
          (ct1.c1 * ct2.c1) * (s * s) =
        bfvPhase R ct1 s * bfvPhase R ct2 s := by
    dsimp [bfvPhase]
    ring
  rw [h_prod, h1, h2]
  ring

def bgvDecodeElem (params : LWEParams) (t : ℕ) (v : Zq params) : ℕ :=
  (ZMod.val v) % t

theorem bgvDecodeElem_correct (params : LWEParams) (t m e : ℕ)
    (hm : m < t) (h_lt : m + t * e < params.q) :
    bgvDecodeElem params t ((m + t * e : ℕ) : Zq params) = m := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  dsimp [bgvDecodeElem]
  have h_val : ZMod.val ((m + t * e : ℕ) : Zq params) = m + t * e :=
    ZMod.val_natCast_of_lt h_lt
  rw [h_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]

theorem bgvModSwitch_phase_identity (R : Type*) [CommRing R]
    (q_last r t s c0 c1 c0' c1' d0 d1 m E : R)
    (h_c0 : q_last * c0' = r * c0 + t * d0)
    (h_c1 : q_last * c1' = r * c1 + t * d1)
    (h_phase : c0 + c1 * s = m + t * E) :
    q_last * (c0' + c1' * s) = r * m + t * (r * E + d0 + d1 * s) := by
  calc
    q_last * (c0' + c1' * s)
      = q_last * c0' + (q_last * c1') * s := by ring
    _ = (r * c0 + t * d0) + (r * c1 + t * d1) * s := by rw [h_c0, h_c1]
    _ = r * (c0 + c1 * s) + t * (d0 + d1 * s) := by ring
    _ = r * (m + t * E) + t * (d0 + d1 * s) := by rw [h_phase]
    _ = r * m + t * (r * E + d0 + d1 * s) := by ring

theorem bgvModSwitch_congruent_mod_t (R : Type*) [CommRing R]
    (q_last r k t s c0 c1 c0' c1' d0 d1 m E : R)
    (h_r : r = q_last - t * k)
    (h_c0 : q_last * c0' = r * c0 + t * d0)
    (h_c1 : q_last * c1' = r * c1 + t * d1)
    (h_phase : c0 + c1 * s = m + t * E) :
    q_last * (c0' + c1' * s - m) = t * (r * E + d0 + d1 * s - k * m) := by
  have h_id := bgvModSwitch_phase_identity R q_last r t s c0 c1 c0' c1' d0 d1 m E
    h_c0 h_c1 h_phase
  calc
    q_last * (c0' + c1' * s - m)
      = q_last * (c0' + c1' * s) - q_last * m := by ring
    _ = (r * m + t * (r * E + d0 + d1 * s)) - q_last * m := by rw [h_id]
    _ = ((q_last - t * k) * m + t * (r * E + d0 + d1 * s)) - q_last * m := by rw [h_r]
    _ = t * (r * E + d0 + d1 * s - k * m) := by ring

theorem ckks_rescale_phase_identity (R : Type*) [CommRing R]
    (q_last s c0 c1 c0' c1' d0 d1 m_scaled e_mul : R)
    (h_c0 : q_last * c0' = c0 - d0)
    (h_c1 : q_last * c1' = c1 - d1)
    (h_phase : c0 + c1 * s = m_scaled + e_mul) :
    q_last * (c0' + c1' * s) = m_scaled + (e_mul - (d0 + d1 * s)) := by
  calc
    q_last * (c0' + c1' * s)
      = q_last * c0' + (q_last * c1') * s := by ring
    _ = (c0 - d0) + (c1 - d1) * s := by rw [h_c0, h_c1]
    _ = (c0 + c1 * s) - (d0 + d1 * s) := by ring
    _ = m_scaled + (e_mul - (d0 + d1 * s)) := by
      rw [h_phase]
      ring

theorem ckks_slot_embedding_mul_error {PolyR SlotR : Type*} [CommRing PolyR] [CommRing SlotR]
    {S : ℕ} (emb : NTTHom PolyR S SlotR)
    (s m1 m2 e1 e2 : PolyR) (ct1 ct2 : BFVCiphertext PolyR)
    (h1 : bfvPhase PolyR ct1 s = m1 + e1)
    (h2 : bfvPhase PolyR ct2 s = m2 + e2) :
    emb.toFun (bfvPhase PolyR ct1 s * bfvPhase PolyR ct2 s) =
      emb.toFun m1 * emb.toFun m2 +
        emb.toFun (m1 * e2 + m2 * e1 + e1 * e2) := by
  have h_expand :
      bfvPhase PolyR ct1 s * bfvPhase PolyR ct2 s =
        m1 * m2 + (m1 * e2 + m2 * e1 + e1 * e2) := by
    rw [h1, h2]
    ring
  rw [h_expand, emb.map_add, emb.map_mul]

lemma intCastPolyHom_eq_exists_mul_q (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (A B : NegacyclicPoly ℤ N)
    (h_eq : NegacyclicPoly.intCastPolyHom params N A =
      NegacyclicPoly.intCastPolyHom params N B) :
    ∃ K : NegacyclicPoly ℤ N, A = B + (params.q : NegacyclicPoly ℤ N) * K := by
  let diff := A - B
  have h_zero : NegacyclicPoly.intCastPolyHom params N diff = 0 := by
    dsimp [diff]
    rw [map_sub, h_eq, sub_self]
  have hk_dvd : ∀ k : Fin N, ∃ kz : ℤ, diff.coeffs k = (params.q : ℤ) * kz := by
    intro k
    have hk0 : ((diff.coeffs k : ℤ) : Zq params) = 0 := congrArg (fun p => p.coeffs k) h_zero
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (diff.coeffs k) params.q).mp hk0
  let K : NegacyclicPoly ℤ N := ⟨fun k => Classical.choose (hk_dvd k)⟩
  refine ⟨K, ?_⟩
  have h_diff_eq : diff = (params.q : NegacyclicPoly ℤ N) * K := by
    ext k
    have h_cm : ((params.q : NegacyclicPoly ℤ N) * K).coeffs k = (params.q : ℤ) * K.coeffs k :=
      NegacyclicPoly.constPoly_mul_coeffs (R := ℤ) (params.q : ℤ) K k
    rw [h_cm]
    exact Classical.choose_spec (hk_dvd k)
  dsimp [diff] at h_diff_eq
  exact (sub_eq_iff_eq_add.mp h_diff_eq).trans (add_comm _ _)

def bgvCenteredDecodeElem (params : LWEParams) (t : ℕ) (v : Zq params) : ℕ :=
  ((centeredLift params v) % (t : ℤ)).toNat

def bgvCenteredDecodePoly (params : LWEParams) (N t : ℕ) (p : NegacyclicPoly (Zq params) N) :
    Fin N → ℕ :=
  fun k => bgvCenteredDecodeElem params t (p.coeffs k)

def bgvDecryptPoly (params : LWEParams) (N t : ℕ) [Fact (0 < N)]
    (s : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N)) : Fin N → ℕ :=
  bgvCenteredDecodePoly params N t (bfvPhase (NegacyclicPoly (Zq params) N) ct s)

theorem bgvCenteredDecodeElem_lt (params : LWEParams) (t : ℕ) (ht : 0 < t) (v : Zq params) :
    bgvCenteredDecodeElem params t v < t := by
  dsimp [bgvCenteredDecodeElem]
  have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
  have h0 := Int.emod_nonneg (centeredLift params v) (ne_of_gt ht_pos)
  have hlt := Int.emod_lt_of_pos (centeredLift params v) ht_pos
  omega

theorem bgvCenteredDecodeElem_correct (params : LWEParams) (t m : ℕ) (e : ℤ) (hm : m < t)
    (h_bound : 2 * ((m : ℤ) + (t : ℤ) * e).natAbs < params.q) :
    bgvCenteredDecodeElem params t (((m : ℤ) + (t : ℤ) * e : ℤ) : Zq params) = m := by
  let z : ℤ := (m : ℤ) + (t : ℤ) * e
  have hz_mem : z ∈ Finset.Icc (-(z.natAbs : ℤ)) (z.natAbs : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  have h_cl : centeredLift params (z : Zq params) = z :=
    centeredLift_intCast_of_mem_Icc params h_bound hz_mem
  have ht_z : (m : ℤ) < (t : ℤ) := by exact_mod_cast hm
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
  dsimp [bgvCenteredDecodeElem]
  rw [h_cl]
  change (((m : ℤ) + (t : ℤ) * e) % (t : ℤ)).toNat = m
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hm0 ht_z, Int.toNat_natCast]

theorem bgvUnsignedDecode_neg_noise_counterexample :
    let p17 : LWEParams := { n := 1, m := 1, q := 17, q_pos := ⟨by decide⟩ }
    let v : Zq p17 := ((0 : ℤ) + (2 : ℤ) * (-1 : ℤ) : ℤ)
    2 * ((0 : ℤ) + (2 : ℤ) * (-1 : ℤ)).natAbs < p17.q ∧
      bgvDecodeElem p17 2 v = 1 ∧ bgvCenteredDecodeElem p17 2 v = 0 := by
  intro p17 v
  have h_bnd : 2 * ((0 : ℤ) + (2 : ℤ) * (-1 : ℤ)).natAbs < p17.q := by decide
  have hv_eq : v = ((15 : ℕ) : ZMod 17) := by decide
  have h_val : ZMod.val v = 15 := by
    rw [hv_eq, ZMod.val_natCast_of_lt (by decide)]
  have h_unsign : bgvDecodeElem p17 2 v = 1 := by
    dsimp [bgvDecodeElem]
    rw [h_val]
  have h_center : bgvCenteredDecodeElem p17 2 v = 0 :=
    bgvCenteredDecodeElem_correct p17 2 0 (-1) (by decide) h_bnd
  exact ⟨h_bnd, h_unsign, h_center⟩

theorem bgvDecryptPoly_of_phase_eq (params : LWEParams) (N t : ℕ) [Fact (0 < N)]
    (s E : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (h_phase :
      bfvPhase (NegacyclicPoly (Zq params) N) ct s =
        bfvPlainPoly params N m + (t : NegacyclicPoly (Zq params) N) * E)
    (h_noise : 2 * ((t - 1) + t * normInf params E.coeffs) < params.q) :
    bgvDecryptPoly params N t s ct = m := by
  ext k
  unfold bgvDecryptPoly bgvCenteredDecodePoly
  rw [h_phase, NegacyclicPoly.add_coeffs]
  have h_tE : ((t : NegacyclicPoly (Zq params) N) * E).coeffs k =
      (t : Zq params) * E.coeffs k := by
    change (NegacyclicPoly.constPoly ((t : ℕ) : Zq params) * E).coeffs k = _
    exact NegacyclicPoly.constPoly_mul_coeffs (R := Zq params) ((t : ℕ) : Zq params) E k
  have h_plain : (bfvPlainPoly params N m).coeffs k = ((m k : ℤ) : Zq params) := by
    dsimp [bfvPlainPoly]
    rw [Int.cast_natCast]
  have h_rhs :
      (bfvPlainPoly params N m).coeffs k + ((t : NegacyclicPoly (Zq params) N) * E).coeffs k =
        (((m k : ℤ) + (t : ℤ) * centeredLift params (E.coeffs k) : ℤ) : Zq params) := by
    conv_lhs =>
      rw [h_plain, h_tE, ← intCast_centeredLift params (E.coeffs k), ← Int.cast_natCast t,
        ← Int.cast_mul, ← Int.cast_add]
  rw [h_rhs]
  have h_abs : ((m k : ℤ) + (t : ℤ) * centeredLift params (E.coeffs k)).natAbs ≤
      (t - 1) + t * normInf params E.coeffs := by
    have h_add := Int.natAbs_add_le (m k : ℤ) ((t : ℤ) * centeredLift params (E.coeffs k))
    rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h_add
    have hk := hm k
    have he_le : (centeredLift params (E.coeffs k)).natAbs ≤ normInf params E.coeffs :=
      Finset.le_sup (f := fun j => norm params (E.coeffs j)) (Finset.mem_univ k)
    have hm_le : m k ≤ t - 1 := by omega
    have h_mul_le := Nat.mul_le_mul_left t he_le
    omega
  have hk_bnd :
      2 * ((m k : ℤ) + (t : ℤ) * centeredLift params (E.coeffs k)).natAbs < params.q := by
    omega
  exact bgvCenteredDecodeElem_correct params t (m k) (centeredLift params (E.coeffs k))
    (hm k) hk_bnd

theorem bgvDecryptPoly_encrypt_ternary_correct (params : LWEParams) (N t B_e : ℕ) [Fact (0 < N)]
    (a s e u e0 e1 : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hu : NegacyclicPoly.IsTernaryPoly u)
    (he : normInf params e.coeffs ≤ B_e)
    (he0 : normInf params e0.coeffs ≤ B_e)
    (he1 : normInf params e1.coeffs ≤ B_e)
    (h_noise : 2 * ((t - 1) + t * ((2 * N + 1) * B_e)) < params.q) :
    let pk := bgvKeygen (NegacyclicPoly (Zq params) N) (t : NegacyclicPoly (Zq params) N) a s e
    let ct := bgvEncrypt (NegacyclicPoly (Zq params) N) (t : NegacyclicPoly (Zq params) N)
      pk u e0 e1 (bfvPlainPoly params N m)
    bgvDecryptPoly params N t s ct = m := by
  intro pk ct
  have h_phase := bgvEncrypt_phase (NegacyclicPoly (Zq params) N)
    (t : NegacyclicPoly (Zq params) N) a s e u e0 e1 (bfvPlainPoly params N m)
  have h_e1s : normInf params (e1 * s).coeffs ≤ N * B_e := by
    rw [mul_comm]
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N s e1 hs
    have h2 : N * normInf params e1.coeffs ≤ N * B_e := Nat.mul_le_mul_left N he1
    omega
  have h_eu : normInf params (e * u).coeffs ≤ N * B_e := by
    rw [mul_comm]
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N u e hu
    have h2 : N * normInf params e.coeffs ≤ N * B_e := Nat.mul_le_mul_left N he
    omega
  have h_sum1 := norm_add_le params e0.coeffs (e1 * s).coeffs
  have h_sub := norm_sub_le params (e0 + e1 * s).coeffs (e * u).coeffs
  change normInf params (e0 + e1 * s).coeffs ≤
    normInf params e0.coeffs + normInf params (e1 * s).coeffs at h_sum1
  change normInf params (e0 + e1 * s - e * u).coeffs ≤
    normInf params (e0 + e1 * s).coeffs + normInf params (e * u).coeffs at h_sub
  have h_norm : normInf params (e0 + e1 * s - e * u).coeffs ≤ (2 * N + 1) * B_e := by
    have h_eq : B_e + N * B_e + N * B_e = (2 * N + 1) * B_e := by ring
    omega
  have h_mul_le := Nat.mul_le_mul_left t h_norm
  have h_tot : 2 * ((t - 1) + t * normInf params (e0 + e1 * s - e * u).coeffs) < params.q := by
    omega
  exact bgvDecryptPoly_of_phase_eq params N t s (e0 + e1 * s - e * u) ct m hm h_phase h_tot

theorem bgvDecryptPoly_add_mod_t_correct (params : LWEParams) (N t B1 B2 : ℕ) [Fact (0 < N)]
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hE1 : normInf params E1.coeffs ≤ B1)
    (hE2 : normInf params E2.coeffs ≤ B2)
    (h_phase1 :
      bfvPhase (NegacyclicPoly (Zq params) N) ct1 s =
        bfvPlainPoly params N m1 + (t : NegacyclicPoly (Zq params) N) * E1)
    (h_phase2 :
      bfvPhase (NegacyclicPoly (Zq params) N) ct2 s =
        bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * E2)
    (h_noise : 2 * ((t - 1) + t * (B1 + B2 + 1)) < params.q) :
    bgvDecryptPoly params N t s (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) =
      fun k => (m1 k + m2 k) % t := by
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) (hm1 ⟨0, Fact.out⟩)
  let Q_add : NegacyclicPoly (Zq params) N :=
    ⟨fun k => (((m1 k + m2 k) / t : ℕ) : Zq params)⟩
  have h_plain_add :
      bfvPlainPoly params N m1 + bfvPlainPoly params N m2 =
        bfvPlainPoly params N (fun k => (m1 k + m2 k) % t) +
          (t : NegacyclicPoly (Zq params) N) * Q_add := by
    ext k
    rw [NegacyclicPoly.add_coeffs, NegacyclicPoly.add_coeffs]
    change ((m1 k : ℕ) : Zq params) + ((m2 k : ℕ) : Zq params) =
      (((m1 k + m2 k) % t : ℕ) : Zq params) +
        (NegacyclicPoly.constPoly ((t : ℕ) : Zq params) * Q_add).coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    dsimp [Q_add]
    rw [← Nat.cast_add, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  have hQ_norm : normInf params Q_add.coeffs ≤ 1 := by
    dsimp [normInf, Q_add]
    apply Finset.sup_le
    intro k _
    rw [← Int.cast_natCast]
    have h_le := norm_intCast_le_natAbs params (((m1 k + m2 k) / t : ℕ) : ℤ)
    rw [Int.natAbs_natCast] at h_le
    have hk1 := hm1 k
    have hk2 := hm2 k
    have h_div : (m1 k + m2 k) / t ≤ 1 := Nat.div_lt_of_lt_mul (by omega) |> Nat.le_of_lt_succ
    omega
  have h_phase_sum :
      bfvPhase (NegacyclicPoly (Zq params) N) (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) s =
        bfvPlainPoly params N (fun k => (m1 k + m2 k) % t) +
          (t : NegacyclicPoly (Zq params) N) * (E1 + E2 + Q_add) := by
    rw [bfvAdd_phase, h_phase1, h_phase2]
    calc
      bfvPlainPoly params N m1 + (t : NegacyclicPoly (Zq params) N) * E1 +
          (bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * E2)
        = (bfvPlainPoly params N m1 + bfvPlainPoly params N m2) +
            (t : NegacyclicPoly (Zq params) N) * (E1 + E2) := by ring
      _ = bfvPlainPoly params N (fun k => (m1 k + m2 k) % t) +
            (t : NegacyclicPoly (Zq params) N) * (E1 + E2 + Q_add) := by
          rw [h_plain_add]
          ring
  have h_tri1 := norm_add_le params (E1 + E2).coeffs Q_add.coeffs
  have h_tri2 := norm_add_le params E1.coeffs E2.coeffs
  change normInf params (E1 + E2 + Q_add).coeffs ≤
    normInf params (E1 + E2).coeffs + normInf params Q_add.coeffs at h_tri1
  change normInf params (E1 + E2).coeffs ≤
    normInf params E1.coeffs + normInf params E2.coeffs at h_tri2
  have hE_tot : normInf params (E1 + E2 + Q_add).coeffs ≤ B1 + B2 + 1 := by omega
  have h_mul_le := Nat.mul_le_mul_left t hE_tot
  have h_tot : 2 * ((t - 1) + t * normInf params (E1 + E2 + Q_add).coeffs) < params.q := by omega
  exact bgvDecryptPoly_of_phase_eq params N t s (E1 + E2 + Q_add)
    (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) (fun k => (m1 k + m2 k) % t)
    (fun k => Nat.mod_lt _ ht) h_phase_sum h_tot

def bgvMulTotalNoiseBound (N t B1 B2 B l B_rk : ℕ) : ℕ :=
  bfvPlainCarryBound N t + N * (t - 1) * B2 + N * B1 * (t - 1) +
    t * (N * B1 * B2) + l * (N * (B - 1) * B_rk)

theorem bgvDecryptPoly_mul_correct (params : LWEParams) (N t B1 B2 B l B_rk : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (hB : 0 < B)
    (h2B : 2 * B ≤ params.q)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hE1 : normInf params E1.coeffs ≤ B1)
    (hE2 : normInf params E2.coeffs ≤ B2)
    (herk : ∀ i : Fin l, normInf params (e_rk i).coeffs ≤ B_rk)
    (h_phase1 :
      bfvPhase (NegacyclicPoly (Zq params) N) ct1 s =
        bfvPlainPoly params N m1 + (t : NegacyclicPoly (Zq params) N) * E1)
    (h_phase2 :
      bfvPhase (NegacyclicPoly (Zq params) N) ct2 s =
        bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * E2)
    (h_noise : 2 * ((t - 1) + t * bgvMulTotalNoiseBound N t B1 B2 B l B_rk) < params.q) :
    let d0 := ct1.c0 * ct2.c0
    let d1 := ct1.c0 * ct2.c1 + ct1.c1 * ct2.c0
    let d2 := ct1.c1 * ct2.c1
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk
      (fun i => (t : NegacyclicPoly (Zq params) N) * e_rk i) s
      (NegacyclicPoly.negacyclicGadget params N B l)
    let ct_mul := bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
      (NegacyclicPoly.negacyclicDecomp params N B l) rk
    bgvDecryptPoly params N t s ct_mul = bfvPlainMulMod N t m1 m2 := by
  intro d0 d1 d2 rk ct_mul
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) (hm1 ⟨0, Fact.out⟩)
  let M1 : NegacyclicPoly ℤ N := ⟨fun k => (m1 k : ℤ)⟩
  let M2 : NegacyclicPoly ℤ N := ⟨fun k => (m2 k : ℤ)⟩
  let Q_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k / (t : ℤ)⟩
  let P_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k % (t : ℤ)⟩
  have hM1_norm : NegacyclicPoly.intPolyNormInf M1 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M1]
    apply Finset.sup_le
    intro k _
    have hk := hm1 k
    omega
  have hM2_norm : NegacyclicPoly.intPolyNormInf M2 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M2]
    apply Finset.sup_le
    intro k _
    have hk := hm2 k
    omega
  have hM12_norm : NegacyclicPoly.intPolyNormInf (M1 * M2) ≤ N * (t - 1) * (t - 1) :=
    le_trans (NegacyclicPoly.intPolyNormInf_mul_le M1 M2)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hM1_norm) hM2_norm)
  have hQM_norm : NegacyclicPoly.intPolyNormInf Q_M ≤ bfvPlainCarryBound N t := by
    dsimp [NegacyclicPoly.intPolyNormInf, Q_M, bfvPlainCarryBound]
    apply Finset.sup_le
    intro k _
    exact ediv_natAbs_le ht
      (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf (M1 * M2) k) hM12_norm)
  have h_split : M1 * M2 = (t : NegacyclicPoly ℤ N) * Q_M + P_M := by
    ext k
    rw [NegacyclicPoly.add_coeffs]
    change (M1 * M2).coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * Q_M).coeffs k + P_M.coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    dsimp [Q_M, P_M]
    rw [add_comm]
    exact (Int.emod_add_mul_ediv ((M1 * M2).coeffs k) (t : ℤ)).symm
  have hM1_zq : NegacyclicPoly.intCastPolyHom params N M1 = bfvPlainPoly params N m1 := by
    ext k
    exact Int.cast_natCast (m1 k)
  have hM2_zq : NegacyclicPoly.intCastPolyHom params N M2 = bfvPlainPoly params N m2 := by
    ext k
    exact Int.cast_natCast (m2 k)
  have hP_zq :
      NegacyclicPoly.intCastPolyHom params N P_M =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) := by
    ext k
    rw [NegacyclicPoly.intCastPolyHom_coeffs]
    have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
    have h_eq := Int.toNat_of_nonneg (Int.emod_nonneg ((M1 * M2).coeffs k) (ne_of_gt ht_pos))
    change Int.cast ((M1 * M2).coeffs k % (t : ℤ)) =
      (((M1 * M2).coeffs k % (t : ℤ)).toNat : Zq params)
    exact (congrArg (Int.cast : ℤ → Zq params) h_eq).symm.trans (Int.cast_natCast _)
  let q_m_zq := NegacyclicPoly.intCastPolyHom params N Q_M
  have h_m12_zq :
      bfvPlainPoly params N m1 * bfvPlainPoly params N m2 =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
          (t : NegacyclicPoly (Zq params) N) * q_m_zq := by
    calc
      bfvPlainPoly params N m1 * bfvPlainPoly params N m2
        = NegacyclicPoly.intCastPolyHom params N (M1 * M2) := by
          rw [← hM1_zq, ← hM2_zq, ← map_mul]
      _ = NegacyclicPoly.intCastPolyHom params N ((t : NegacyclicPoly ℤ N) * Q_M + P_M) := by
          rw [h_split]
      _ = bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
            (t : NegacyclicPoly (Zq params) N) * q_m_zq := by
          rw [map_add, map_mul, map_natCast, hP_zq]
          ring
  let relin_err := ∑ i : Fin l, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i
  let E_tot :=
    q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
      (t : NegacyclicPoly (Zq params) N) * (E1 * E2) - relin_err
  have h_relin_alg := bfvGadgetRelinearize_phase (NegacyclicPoly (Zq params) N)
    s d0 d1 d2 a_rk (fun i => (t : NegacyclicPoly (Zq params) N) * e_rk i)
    (NegacyclicPoly.negacyclicGadget params N B l)
    (NegacyclicPoly.negacyclicDecomp params N B l)
    (NegacyclicPoly.negacyclicDecomp_isValid params N B l hq)
  have h_pull_t :
      (∑ i : Fin l,
        NegacyclicPoly.negacyclicDecomp params N B l d2 i *
          ((t : NegacyclicPoly (Zq params) N) * e_rk i)) =
        (t : NegacyclicPoly (Zq params) N) * relin_err := by
    dsimp [relin_err]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_tensor_id : d0 + d1 * s + d2 * (s * s) =
      bfvPhase (NegacyclicPoly (Zq params) N) ct1 s *
        bfvPhase (NegacyclicPoly (Zq params) N) ct2 s := by
    dsimp [d0, d1, d2, bfvPhase]
    ring
  have h_phase :
      bfvPhase (NegacyclicPoly (Zq params) N) ct_mul s =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
          (t : NegacyclicPoly (Zq params) N) * E_tot := by
    dsimp only [ct_mul, rk]
    rw [h_relin_alg, h_pull_t, h_tensor_id, h_phase1, h_phase2]
    dsimp [E_tot]
    calc
      (bfvPlainPoly params N m1 + (t : NegacyclicPoly (Zq params) N) * E1) *
            (bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * E2) -
          (t : NegacyclicPoly (Zq params) N) * relin_err
        = (bfvPlainPoly params N m1 * bfvPlainPoly params N m2) +
            (t : NegacyclicPoly (Zq params) N) *
              (bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
                (t : NegacyclicPoly (Zq params) N) * (E1 * E2) - relin_err) := by ring
      _ = bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
            (t : NegacyclicPoly (Zq params) N) *
              (q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
                (t : NegacyclicPoly (Zq params) N) * (E1 * E2) - relin_err) := by
          rw [h_m12_zq]
          ring
  have hqm_zq : normInf params q_m_zq.coeffs ≤ bfvPlainCarryBound N t :=
    le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params N Q_M) hQM_norm
  have hm1_zq : normInf params (bfvPlainPoly params N m1).coeffs ≤ t - 1 := by
    rw [← hM1_zq]
    exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params N M1) hM1_norm
  have hm2_zq : normInf params (bfvPlainPoly params N m2).coeffs ≤ t - 1 := by
    rw [← hM2_zq]
    exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params N M2) hM2_norm
  have hm1E2 : normInf params (bfvPlainPoly params N m1 * E2).coeffs ≤ N * (t - 1) * B2 :=
    le_trans (NegacyclicPoly.normInf_mul_le params N _ _)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hm1_zq) hE2)
  have hE1m2 : normInf params (E1 * bfvPlainPoly params N m2).coeffs ≤ N * B1 * (t - 1) :=
    le_trans (NegacyclicPoly.normInf_mul_le params N _ _)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hE1) hm2_zq)
  have hE12 : normInf params (E1 * E2).coeffs ≤ N * B1 * B2 :=
    le_trans (NegacyclicPoly.normInf_mul_le params N _ _)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hE1) hE2)
  have htE12 :
      normInf params ((t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs ≤
        t * (N * B1 * B2) := by
    dsimp [normInf]
    apply Finset.sup_le
    intro k _
    change norm params
      ((NegacyclicPoly.constPoly ((t : ℕ) : Zq params) * (E1 * E2)).coeffs k) ≤ _
    rw [NegacyclicPoly.constPoly_mul_coeffs, ← intCast_centeredLift params ((E1 * E2).coeffs k),
      ← Int.cast_natCast t, ← Int.cast_mul]
    have h1 := norm_intCast_le_natAbs params ((t : ℤ) * centeredLift params ((E1 * E2).coeffs k))
    rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
    have h2 : (centeredLift params ((E1 * E2).coeffs k)).natAbs ≤ normInf params (E1 * E2).coeffs :=
      Finset.le_sup (f := fun j => norm params ((E1 * E2).coeffs j)) (Finset.mem_univ k)
    exact le_trans h1 (Nat.mul_le_mul_left t (le_trans h2 hE12))
  have h_relin_norm : normInf params relin_err.coeffs ≤ l * (N * (B - 1) * B_rk) :=
    NegacyclicPoly.normInf_gadgetRelin_noise_le params N B l B_rk hB h2B d2 e_rk herk
  have hs1 := norm_sub_le params
    (q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
      (t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs relin_err.coeffs
  have hs2 := norm_add_le params
    (q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2).coeffs
    ((t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs
  have hs3 := norm_add_le params
    (q_m_zq + bfvPlainPoly params N m1 * E2).coeffs
    (E1 * bfvPlainPoly params N m2).coeffs
  have hs4 := norm_add_le params q_m_zq.coeffs (bfvPlainPoly params N m1 * E2).coeffs
  have hs1' : normInf params E_tot.coeffs ≤
      normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
        (t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs +
        normInf params relin_err.coeffs := hs1
  have hs2' : normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 +
        E1 * bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs ≤
      normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 +
        E1 * bfvPlainPoly params N m2).coeffs +
        normInf params ((t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs := hs2
  have hs3' : normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 +
        E1 * bfvPlainPoly params N m2).coeffs ≤
      normInf params (q_m_zq + bfvPlainPoly params N m1 * E2).coeffs +
        normInf params (E1 * bfvPlainPoly params N m2).coeffs := hs3
  have hs4' : normInf params (q_m_zq + bfvPlainPoly params N m1 * E2).coeffs ≤
      normInf params q_m_zq.coeffs + normInf params (bfvPlainPoly params N m1 * E2).coeffs := hs4
  have hEtot_le : normInf params E_tot.coeffs ≤ bgvMulTotalNoiseBound N t B1 B2 B l B_rk := by
    dsimp only [bgvMulTotalNoiseBound]
    omega
  have h_mul_t := Nat.mul_le_mul_left t hEtot_le
  have h_tot_bnd : 2 * ((t - 1) + t * normInf params E_tot.coeffs) < params.q := by omega
  exact bgvDecryptPoly_of_phase_eq params N t s E_tot ct_mul (bfvPlainMulMod N t m1 m2)
    (bfvPlainMulMod_lt ht m1 m2) h_phase h_tot_bnd

def bgvCongruentDelta (q_last t : ℕ) [hq : Fact (0 < q_last)]
    (h_cop : Nat.Coprime t q_last) (w : ℤ) : ℤ :=
  let p_last : LWEParams := { n := 1, m := 1, q := q_last, q_pos := hq }
  let u_t : (ZMod q_last)ˣ := ZMod.unitOfCoprime t h_cop
  centeredLift p_last (-((w : ZMod q_last) * ((u_t⁻¹ : (ZMod q_last)ˣ) : ZMod q_last)))

lemma bgvCongruentDelta_natAbs_le (q_last t : ℕ) [hq : Fact (0 < q_last)]
    (h_cop : Nat.Coprime t q_last) (w : ℤ) :
    (bgvCongruentDelta q_last t h_cop w).natAbs ≤ q_last / 2 :=
  norm_le_div_two { n := 1, m := 1, q := q_last, q_pos := hq } _

lemma bgvCongruentDelta_mul_div (q_last t : ℕ) [hq : Fact (0 < q_last)]
    (h_cop : Nat.Coprime t q_last) (w : ℤ) :
    (q_last : ℤ) * ((w + (t : ℤ) * bgvCongruentDelta q_last t h_cop w) / (q_last : ℤ)) =
      w + (t : ℤ) * bgvCongruentDelta q_last t h_cop w := by
  let p_last : LWEParams := { n := 1, m := 1, q := q_last, q_pos := hq }
  let u_t : (ZMod q_last)ˣ := ZMod.unitOfCoprime t h_cop
  have h_cl :
      ((bgvCongruentDelta q_last t h_cop w : ℤ) : ZMod q_last) =
        -((w : ZMod q_last) * ((u_t⁻¹ : (ZMod q_last)ˣ) : ZMod q_last)) :=
    intCast_centeredLift p_last _
  have h_mod0 : ((w + (t : ℤ) * bgvCongruentDelta q_last t h_cop w : ℤ) : ZMod q_last) = 0 := by
    rw [Int.cast_add, Int.cast_mul, h_cl, Int.cast_natCast, ← ZMod.coe_unitOfCoprime t h_cop]
    calc
      (w : ZMod q_last) +
          (u_t : ZMod q_last) * -((w : ZMod q_last) * ((u_t⁻¹ : (ZMod q_last)ˣ) : ZMod q_last))
        = (w : ZMod q_last) -
            (w : ZMod q_last) * ((u_t : ZMod q_last) * ((u_t⁻¹ : (ZMod q_last)ˣ) : ZMod q_last)) :=
          by ring
      _ = (w : ZMod q_last) - (w : ZMod q_last) * 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = 0 := by ring
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ q_last).mp h_mod0 with ⟨k, hk⟩
  have hq_ne : (q_last : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hq.out)
  rw [hk, Int.mul_ediv_cancel_left k hq_ne]

def bgvModSwitchDropLimbPoly (params_old params_new : LWEParams) (N q_last t : ℕ)
    [Fact (0 < q_last)] (h_cop : Nat.Coprime t q_last)
    (p : NegacyclicPoly (Zq params_old) N) : NegacyclicPoly (Zq params_new) N :=
  ⟨fun k =>
    let w := ((q_last % t : ℕ) : ℤ) * centeredLift params_old (p.coeffs k)
    let δ := bgvCongruentDelta q_last t h_cop w
    Int.cast ((w + (t : ℤ) * δ) / (q_last : ℤ))⟩

def bgvModSwitchDropLimbCiphertext (params_old params_new : LWEParams) (N q_last t : ℕ)
    [Fact (0 < q_last)] (h_cop : Nat.Coprime t q_last)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params_old) N)) :
    BFVCiphertext (NegacyclicPoly (Zq params_new) N) :=
  { c0 := bgvModSwitchDropLimbPoly params_old params_new N q_last t h_cop ct.c0,
    c1 := bgvModSwitchDropLimbPoly params_old params_new N q_last t h_cop ct.c1 }

def bgvModSwitchNoiseBound (q_last N t B_s B_e : ℕ) : ℕ :=
  ((q_last % t) * B_e + (q_last / t) * (t - 1) + (N * B_s + 1) * (q_last / 2)) / q_last

theorem bgvModSwitchDropLimb_phase_bound
    (params_old params_new : LWEParams) (N q_last t B_s B_e : ℕ)
    [Fact (0 < N)] [hq_last : Fact (0 < q_last)]
    (hq_prod : params_old.q = params_new.q * q_last)
    (h_cop : Nat.Coprime t q_last)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params_old) N))
    (s E : NegacyclicPoly (Zq params_old) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : normInf params_old s.coeffs ≤ B_s)
    (hE : normInf params_old E.coeffs ≤ B_e)
    (h_phase :
      bfvPhase (NegacyclicPoly (Zq params_old) N) ct s =
        bfvPlainPoly params_old N m + (t : NegacyclicPoly (Zq params_old) N) * E) :
    ∃ E_sw : NegacyclicPoly (Zq params_new) N,
      bfvPhase (NegacyclicPoly (Zq params_new) N)
          (bgvModSwitchDropLimbCiphertext params_old params_new N q_last t h_cop ct)
          (liftPolyToModulus params_old params_new N s) =
        bfvPlainPoly params_new N m + (t : NegacyclicPoly (Zq params_new) N) * E_sw ∧
      normInf params_new E_sw.coeffs ≤ bgvModSwitchNoiseBound q_last N t B_s B_e := by
  let r : ℕ := q_last % t
  let k_qt : ℕ := q_last / t
  let C0 := NegacyclicPoly.liftPolyCentered params_old N ct.c0
  let C1 := NegacyclicPoly.liftPolyCentered params_old N ct.c1
  let S := NegacyclicPoly.liftPolyCentered params_old N s
  let E_hat := NegacyclicPoly.liftPolyCentered params_old N E
  let M : NegacyclicPoly ℤ N := ⟨fun k => (m k : ℤ)⟩
  have h_hom_eq :
      NegacyclicPoly.intCastPolyHom params_old N (C0 + C1 * S) =
        NegacyclicPoly.intCastPolyHom params_old N
          (M + (t : NegacyclicPoly ℤ N) * E_hat) := by
    rw [map_add, map_add, map_mul, map_mul, map_natCast,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered]
    have hM_zq : NegacyclicPoly.intCastPolyHom params_old N M = bfvPlainPoly params_old N m := by
      ext k
      exact Int.cast_natCast (m k)
    rw [hM_zq]
    exact h_phase
  rcases intCastPolyHom_eq_exists_mul_q params_old N (C0 + C1 * S)
      (M + (t : NegacyclicPoly ℤ N) * E_hat) h_hom_eq with ⟨K, hK_eq⟩
  let δ0 : NegacyclicPoly ℤ N :=
    ⟨fun k => bgvCongruentDelta q_last t h_cop ((r : ℤ) * C0.coeffs k)⟩
  let δ1 : NegacyclicPoly ℤ N :=
    ⟨fun k => bgvCongruentDelta q_last t h_cop ((r : ℤ) * C1.coeffs k)⟩
  let C0' : NegacyclicPoly ℤ N :=
    ⟨fun k => (((r : ℤ) * C0.coeffs k + (t : ℤ) * δ0.coeffs k) / (q_last : ℤ))⟩
  let C1' : NegacyclicPoly ℤ N :=
    ⟨fun k => (((r : ℤ) * C1.coeffs k + (t : ℤ) * δ1.coeffs k) / (q_last : ℤ))⟩
  have hC0'_eq : (q_last : NegacyclicPoly ℤ N) * C0' =
      (r : NegacyclicPoly ℤ N) * C0 + (t : NegacyclicPoly ℤ N) * δ0 := by
    ext k
    change (NegacyclicPoly.constPoly (q_last : ℤ) * C0').coeffs k =
      (NegacyclicPoly.constPoly (r : ℤ) * C0).coeffs k +
        (NegacyclicPoly.constPoly (t : ℤ) * δ0).coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs, NegacyclicPoly.constPoly_mul_coeffs,
      NegacyclicPoly.constPoly_mul_coeffs]
    exact bgvCongruentDelta_mul_div q_last t h_cop ((r : ℤ) * C0.coeffs k)
  have hC1'_eq : (q_last : NegacyclicPoly ℤ N) * C1' =
      (r : NegacyclicPoly ℤ N) * C1 + (t : NegacyclicPoly ℤ N) * δ1 := by
    ext k
    change (NegacyclicPoly.constPoly (q_last : ℤ) * C1').coeffs k =
      (NegacyclicPoly.constPoly (r : ℤ) * C1).coeffs k +
        (NegacyclicPoly.constPoly (t : ℤ) * δ1).coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs, NegacyclicPoly.constPoly_mul_coeffs,
      NegacyclicPoly.constPoly_mul_coeffs]
    exact bgvCongruentDelta_mul_div q_last t h_cop ((r : ℤ) * C1.coeffs k)
  have hq_old_z : (params_old.q : NegacyclicPoly ℤ N) =
      (params_new.q : NegacyclicPoly ℤ N) * (q_last : NegacyclicPoly ℤ N) := by
    rw [hq_prod, Nat.cast_mul]
  have hr_z : (r : NegacyclicPoly ℤ N) =
      (q_last : NegacyclicPoly ℤ N) -
        (t : NegacyclicPoly ℤ N) * (k_qt : NegacyclicPoly ℤ N) := by
    have h_nat : r + t * k_qt = q_last := Nat.mod_add_div q_last t
    have h_c := congrArg (fun n : ℕ => (n : NegacyclicPoly ℤ N)) h_nat
    push_cast at h_c
    exact eq_sub_of_add_eq h_c
  let rhs : NegacyclicPoly ℤ N :=
    (r : NegacyclicPoly ℤ N) * E_hat - (k_qt : NegacyclicPoly ℤ N) * M + (δ0 + δ1 * S)
  let lhs_core : NegacyclicPoly ℤ N :=
    (C0' + C1' * S) - M - (params_new.q : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * K)
  have h_alg : (q_last : NegacyclicPoly ℤ N) * lhs_core = (t : NegacyclicPoly ℤ N) * rhs := by
    calc
      (q_last : NegacyclicPoly ℤ N) * lhs_core
        = ((q_last : NegacyclicPoly ℤ N) * C0' + ((q_last : NegacyclicPoly ℤ N) * C1') * S) -
            (q_last : NegacyclicPoly ℤ N) * M -
            (params_new.q : NegacyclicPoly ℤ N) * (q_last : NegacyclicPoly ℤ N) *
              ((r : NegacyclicPoly ℤ N) * K) := by
          dsimp [lhs_core]
          ring
      _ = (r : NegacyclicPoly ℤ N) * (C0 + C1 * S) + (t : NegacyclicPoly ℤ N) * (δ0 + δ1 * S) -
            (q_last : NegacyclicPoly ℤ N) * M -
            (params_old.q : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * K) := by
          rw [hC0'_eq, hC1'_eq, hq_old_z]
          ring
      _ = (r : NegacyclicPoly ℤ N) *
              (M + (t : NegacyclicPoly ℤ N) * E_hat + (params_old.q : NegacyclicPoly ℤ N) * K) +
            (t : NegacyclicPoly ℤ N) * (δ0 + δ1 * S) -
            (q_last : NegacyclicPoly ℤ N) * M -
            (params_old.q : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * K) := by
          rw [hK_eq]
      _ = (r : NegacyclicPoly ℤ N) * M - (q_last : NegacyclicPoly ℤ N) * M +
            (t : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * E_hat + (δ0 + δ1 * S)) := by
          ring
      _ = ((q_last : NegacyclicPoly ℤ N) -
              (t : NegacyclicPoly ℤ N) * (k_qt : NegacyclicPoly ℤ N)) * M -
            (q_last : NegacyclicPoly ℤ N) * M +
            (t : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * E_hat + (δ0 + δ1 * S)) := by
          rw [hr_z]
      _ = (t : NegacyclicPoly ℤ N) * rhs := by
          dsimp [rhs]
          ring
  let E_sw_z : NegacyclicPoly ℤ N := ⟨fun k => rhs.coeffs k / (q_last : ℤ)⟩
  have h_div_exact : ∀ k : Fin N, (q_last : ℤ) * E_sw_z.coeffs k = rhs.coeffs k := by
    intro k
    have hk_eq := congrArg (fun p => p.coeffs k) h_alg
    change (NegacyclicPoly.constPoly (q_last : ℤ) * lhs_core).coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * rhs).coeffs k at hk_eq
    rw [NegacyclicPoly.constPoly_mul_coeffs, NegacyclicPoly.constPoly_mul_coeffs] at hk_eq
    have h_zm := congrArg (fun z : ℤ => (z : ZMod q_last)) hk_eq
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul,
      Int.cast_mul, Int.cast_natCast] at h_zm
    let u_t := ZMod.unitOfCoprime t h_cop
    rw [← ZMod.coe_unitOfCoprime t h_cop] at h_zm
    have h_uinv := congrArg (fun z : ZMod q_last => ((u_t⁻¹ : (ZMod q_last)ˣ) : ZMod q_last) * z)
      h_zm
    rw [mul_zero, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h_uinv
    rcases (ZMod.intCast_zmod_eq_zero_iff_dvd (rhs.coeffs k) q_last).mp h_uinv.symm with ⟨w, hw⟩
    have hq_ne : (q_last : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hq_last.out)
    dsimp [E_sw_z]
    rw [hw, Int.mul_ediv_cancel_left w hq_ne]
  have h_lhs_eq : lhs_core = (t : NegacyclicPoly ℤ N) * E_sw_z := by
    ext k
    have hk_eq := congrArg (fun p => p.coeffs k) h_alg
    change (NegacyclicPoly.constPoly (q_last : ℤ) * lhs_core).coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * rhs).coeffs k at hk_eq
    rw [NegacyclicPoly.constPoly_mul_coeffs, NegacyclicPoly.constPoly_mul_coeffs] at hk_eq
    rw [← h_div_exact k] at hk_eq
    have hq_ne : (q_last : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hq_last.out)
    have hk_mul : (q_last : ℤ) * lhs_core.coeffs k =
        (q_last : ℤ) * ((t : ℤ) * E_sw_z.coeffs k) := by
      rw [hk_eq]
      ring
    have hk_cancel := mul_left_cancel₀ hq_ne hk_mul
    change _ = (NegacyclicPoly.constPoly (t : ℤ) * E_sw_z).coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    exact hk_cancel
  let E_sw : NegacyclicPoly (Zq params_new) N :=
    NegacyclicPoly.intCastPolyHom params_new N E_sw_z
  refine ⟨E_sw, ?_, ?_⟩
  · have h_recombine : C0' + C1' * S =
        M + (t : NegacyclicPoly ℤ N) * E_sw_z +
          (params_new.q : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * K) := by
      rw [← h_lhs_eq]
      dsimp [lhs_core]
      ring
    have hc0_hom :
        bgvModSwitchDropLimbPoly params_old params_new N q_last t h_cop ct.c0 =
          NegacyclicPoly.intCastPolyHom params_new N C0' := rfl
    have hc1_hom :
        bgvModSwitchDropLimbPoly params_old params_new N q_last t h_cop ct.c1 =
          NegacyclicPoly.intCastPolyHom params_new N C1' := rfl
    have hs_hom : liftPolyToModulus params_old params_new N s =
        NegacyclicPoly.intCastPolyHom params_new N S := rfl
    have hM_hom :
        NegacyclicPoly.intCastPolyHom params_new N M = bfvPlainPoly params_new N m := by
      ext k
      exact Int.cast_natCast (m k)
    calc
      bfvPhase (NegacyclicPoly (Zq params_new) N)
          (bgvModSwitchDropLimbCiphertext params_old params_new N q_last t h_cop ct)
          (liftPolyToModulus params_old params_new N s)
        = NegacyclicPoly.intCastPolyHom params_new N (C0' + C1' * S) := by
          dsimp [bfvPhase, bgvModSwitchDropLimbCiphertext]
          rw [hc0_hom, hc1_hom, hs_hom, map_add, map_mul]
      _ = NegacyclicPoly.intCastPolyHom params_new N
            (M + (t : NegacyclicPoly ℤ N) * E_sw_z +
              (params_new.q : NegacyclicPoly ℤ N) * ((r : NegacyclicPoly ℤ N) * K)) := by
          rw [h_recombine]
      _ = bfvPlainPoly params_new N m + (t : NegacyclicPoly (Zq params_new) N) * E_sw := by
          rw [map_add, map_add, map_mul, map_mul, map_natCast, hM_hom,
            NegacyclicPoly.intCastPolyHom_q_zero, zero_mul, add_zero]
  · have hM_norm : NegacyclicPoly.intPolyNormInf M ≤ t - 1 := by
      dsimp [NegacyclicPoly.intPolyNormInf, M]
      apply Finset.sup_le
      intro k _
      have hk := hm k
      omega
    have hδ0 : NegacyclicPoly.intPolyNormInf δ0 ≤ q_last / 2 := by
      dsimp [NegacyclicPoly.intPolyNormInf, δ0]
      apply Finset.sup_le
      intro k _
      exact bgvCongruentDelta_natAbs_le q_last t h_cop _
    have hδ1 : NegacyclicPoly.intPolyNormInf δ1 ≤ q_last / 2 := by
      dsimp [NegacyclicPoly.intPolyNormInf, δ1]
      apply Finset.sup_le
      intro k _
      exact bgvCongruentDelta_natAbs_le q_last t h_cop _
    have hS_norm : NegacyclicPoly.intPolyNormInf S ≤ B_s := hs
    have hE_norm : NegacyclicPoly.intPolyNormInf E_hat ≤ B_e := hE
    have hrE : NegacyclicPoly.intPolyNormInf ((r : NegacyclicPoly ℤ N) * E_hat) ≤ r * B_e := by
      have h_cm := NegacyclicPoly.intPolyNormInf_intCast_mul_le (N := N) (r : ℤ) E_hat
      rw [Int.natAbs_natCast] at h_cm
      exact le_trans h_cm (Nat.mul_le_mul_left r hE_norm)
    have hkM :
        NegacyclicPoly.intPolyNormInf ((k_qt : NegacyclicPoly ℤ N) * M) ≤ k_qt * (t - 1) := by
      have h_cm := NegacyclicPoly.intPolyNormInf_intCast_mul_le (N := N) (k_qt : ℤ) M
      rw [Int.natAbs_natCast] at h_cm
      exact le_trans h_cm (Nat.mul_le_mul_left k_qt hM_norm)
    have hδ1S : NegacyclicPoly.intPolyNormInf (δ1 * S) ≤ N * (q_last / 2) * B_s :=
      le_trans (NegacyclicPoly.intPolyNormInf_mul_le δ1 S)
        (Nat.mul_le_mul (Nat.mul_le_mul_left N hδ1) hS_norm)
    have h_rhs_norm :
        NegacyclicPoly.intPolyNormInf rhs ≤
          r * B_e + k_qt * (t - 1) + (N * B_s + 1) * (q_last / 2) := by
      dsimp [rhs]
      have h1 := NegacyclicPoly.intPolyNormInf_add_le
        ((r : NegacyclicPoly ℤ N) * E_hat - (k_qt : NegacyclicPoly ℤ N) * M) (δ0 + δ1 * S)
      have h2 := NegacyclicPoly.intPolyNormInf_sub_le
        ((r : NegacyclicPoly ℤ N) * E_hat) ((k_qt : NegacyclicPoly ℤ N) * M)
      have h3 := NegacyclicPoly.intPolyNormInf_add_le δ0 (δ1 * S)
      have h_mul_eq : N * (q_last / 2) * B_s + q_last / 2 = (N * B_s + 1) * (q_last / 2) := by
        ring
      omega
    have hE_sw_norm : NegacyclicPoly.intPolyNormInf E_sw_z ≤
        bgvModSwitchNoiseBound q_last N t B_s B_e := by
      dsimp [NegacyclicPoly.intPolyNormInf, bgvModSwitchNoiseBound]
      apply Finset.sup_le
      intro k _
      exact natAbs_le_div_of_mul_eq hq_last.out (h_div_exact k)
        (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf rhs k) h_rhs_norm)
    exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params_new N E_sw_z) hE_sw_norm

theorem bgvDecryptPoly_modSwitchDropLimb_correct
    (params_old params_new : LWEParams) (N q_last t B_s B_e : ℕ)
    [Fact (0 < N)] [Fact (0 < q_last)]
    (hq_prod : params_old.q = params_new.q * q_last)
    (h_cop : Nat.Coprime t q_last)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params_old) N))
    (s E : NegacyclicPoly (Zq params_old) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : normInf params_old s.coeffs ≤ B_s)
    (hE : normInf params_old E.coeffs ≤ B_e)
    (h_phase :
      bfvPhase (NegacyclicPoly (Zq params_old) N) ct s =
        bfvPlainPoly params_old N m + (t : NegacyclicPoly (Zq params_old) N) * E)
    (h_noise : 2 * ((t - 1) + t * bgvModSwitchNoiseBound q_last N t B_s B_e) < params_new.q) :
    bgvDecryptPoly params_new N t (liftPolyToModulus params_old params_new N s)
      (bgvModSwitchDropLimbCiphertext params_old params_new N q_last t h_cop ct) = m := by
  rcases bgvModSwitchDropLimb_phase_bound params_old params_new N q_last t B_s B_e hq_prod h_cop
    ct s E m hm hs hE h_phase with ⟨E_sw, h_sw_phase, h_sw_norm⟩
  have h_mul_le := Nat.mul_le_mul_left t h_sw_norm
  have h_tot : 2 * ((t - 1) + t * normInf params_new E_sw.coeffs) < params_new.q := by omega
  exact bgvDecryptPoly_of_phase_eq params_new N t
    (liftPolyToModulus params_old params_new N s) E_sw
    (bgvModSwitchDropLimbCiphertext params_old params_new N q_last t h_cop ct)
    m hm h_sw_phase h_tot

theorem bgvDecryptPoly_modSwitchDropLimb_ternary_correct
    (params_old params_new : LWEParams) (N q_last t B_e : ℕ)
    [Fact (0 < N)] [Fact (0 < q_last)]
    (hq_prod : params_old.q = params_new.q * q_last)
    (h_cop : Nat.Coprime t q_last)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params_old) N))
    (s E : NegacyclicPoly (Zq params_old) N)
    (m : Fin N → ℕ)
    (hm : ∀ k : Fin N, m k < t)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hE : normInf params_old E.coeffs ≤ B_e)
    (h_phase :
      bfvPhase (NegacyclicPoly (Zq params_old) N) ct s =
        bfvPlainPoly params_old N m + (t : NegacyclicPoly (Zq params_old) N) * E)
    (h_noise : 2 * ((t - 1) + t * bgvModSwitchNoiseBound q_last N t 1 B_e) < params_new.q) :
    bgvDecryptPoly params_new N t (liftPolyToModulus params_old params_new N s)
      (bgvModSwitchDropLimbCiphertext params_old params_new N q_last t h_cop ct) = m :=
  bgvDecryptPoly_modSwitchDropLimb_correct params_old params_new N q_last t 1 B_e hq_prod h_cop
    ct s E m hm (NegacyclicPoly.normInf_le_one_of_isTernaryPoly params_old N s hs) hE
    h_phase h_noise

structure CKKSFixedCiphertext (R : Type*) where
  c0 : R
  c1 : R
  scale : ℕ

def ckksPhase (R : Type*) [CommRing R] (ct : CKKSFixedCiphertext R) (s : R) : R :=
  ct.c0 + ct.c1 * s

def ckksFixedDecodeElem (params : LWEParams) (Δ : ℕ) (v : Zq params) : ℤ :=
  divRoundInt (centeredLift params v) Δ

def ckksFixedDecodePoly (params : LWEParams) (N Δ : ℕ) (p : NegacyclicPoly (Zq params) N) :
    Fin N → ℤ :=
  fun k => ckksFixedDecodeElem params Δ (p.coeffs k)

theorem ckksFixedDecodeElem_correct (params : LWEParams) (Δ : ℕ) (m e : ℤ)
    (hm_bound : 2 * ((Δ : ℤ) * m + e).natAbs < params.q)
    (he_bound : 2 * e.natAbs < Δ) :
    ckksFixedDecodeElem params Δ (((Δ : ℤ) * m + e : ℤ) : Zq params) = m := by
  have hΔ_pos : 0 < Δ := by omega
  have hΔ_z : (0 : ℤ) < (Δ : ℤ) := Int.natCast_pos.mpr hΔ_pos
  let z : ℤ := (Δ : ℤ) * m + e
  have hz_mem : z ∈ Finset.Icc (-(z.natAbs : ℤ)) (z.natAbs : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  have h_cl : centeredLift params (z : Zq params) = z :=
    centeredLift_intCast_of_mem_Icc params hm_bound hz_mem
  dsimp [ckksFixedDecodeElem, divRoundInt]
  rw [h_cl]
  set q' := (z + ((Δ / 2 : ℕ) : ℤ)) / (Δ : ℤ)
  set r' := (z + ((Δ / 2 : ℕ) : ℤ)) % (Δ : ℤ)
  have h_dm : r' + (Δ : ℤ) * q' = z + ((Δ / 2 : ℕ) : ℤ) := Int.emod_add_mul_ediv _ _
  have hr0 : 0 ≤ r' := Int.emod_nonneg _ (ne_of_gt hΔ_z)
  have hrΔ : r' < (Δ : ℤ) := Int.emod_lt_of_pos _ hΔ_z
  have h_mul_eq : (Δ : ℤ) * (q' - m) = e + ((Δ / 2 : ℕ) : ℤ) - r' := by
    dsimp [z] at h_dm
    rw [mul_sub]
    omega
  have h_not_ge1 : ¬ 1 ≤ q' - m := by
    intro h1
    have h_mul := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔ_z)
    omega
  have h_not_le_neg1 : ¬ q' - m ≤ -1 := by
    intro h1
    have h_mul := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔ_z)
    omega
  change q' = m
  omega

def ckksRescalePoly (params_old params_new : LWEParams) (N q_last : ℕ)
    (p : NegacyclicPoly (Zq params_old) N) : NegacyclicPoly (Zq params_new) N :=
  ⟨fun k => Int.cast (divRoundInt (centeredLift params_old (p.coeffs k)) q_last)⟩

def ckksRescaleCiphertext (params_old params_new : LWEParams) (N q_last : ℕ)
    (ct : CKKSFixedCiphertext (NegacyclicPoly (Zq params_old) N)) :
    CKKSFixedCiphertext (NegacyclicPoly (Zq params_new) N) :=
  { c0 := ckksRescalePoly params_old params_new N q_last ct.c0,
    c1 := ckksRescalePoly params_old params_new N q_last ct.c1,
    scale := ct.scale / q_last }

def ckksRescaleNoiseBound (q_last N B_s B_mul : ℕ) : ℕ :=
  (B_mul + (N * B_s + 1) * (q_last / 2)) / q_last

theorem ckksRescale_phase_bound
    (params_old params_new : LWEParams) (N q_last B_s B_mul : ℕ) [Fact (0 < N)]
    (hq_prod : params_old.q = params_new.q * q_last)
    (hq_last : 0 < q_last)
    (ct : CKKSFixedCiphertext (NegacyclicPoly (Zq params_old) N))
    (s E_mul : NegacyclicPoly (Zq params_old) N)
    (M_next : NegacyclicPoly ℤ N)
    (hs : normInf params_old s.coeffs ≤ B_s)
    (hE : normInf params_old E_mul.coeffs ≤ B_mul)
    (h_phase :
      ckksPhase (NegacyclicPoly (Zq params_old) N) ct s =
        NegacyclicPoly.intCastPolyHom params_old N ((q_last : NegacyclicPoly ℤ N) * M_next) +
          E_mul) :
    ∃ E_res : NegacyclicPoly (Zq params_new) N,
      ckksPhase (NegacyclicPoly (Zq params_new) N)
          (ckksRescaleCiphertext params_old params_new N q_last ct)
          (liftPolyToModulus params_old params_new N s) =
        NegacyclicPoly.intCastPolyHom params_new N M_next + E_res ∧
      normInf params_new E_res.coeffs ≤ ckksRescaleNoiseBound q_last N B_s B_mul := by
  let C0 := NegacyclicPoly.liftPolyCentered params_old N ct.c0
  let C1 := NegacyclicPoly.liftPolyCentered params_old N ct.c1
  let S := NegacyclicPoly.liftPolyCentered params_old N s
  let E_hat := NegacyclicPoly.liftPolyCentered params_old N E_mul
  have h_hom_eq :
      NegacyclicPoly.intCastPolyHom params_old N (C0 + C1 * S) =
        NegacyclicPoly.intCastPolyHom params_old N
          ((q_last : NegacyclicPoly ℤ N) * M_next + E_hat) := by
    rw [map_add, map_add, map_mul,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered,
      NegacyclicPoly.intCastPolyHom_liftPolyCentered]
    exact h_phase
  rcases intCastPolyHom_eq_exists_mul_q params_old N (C0 + C1 * S)
      ((q_last : NegacyclicPoly ℤ N) * M_next + E_hat) h_hom_eq with ⟨K, hK_eq⟩
  let C0' : NegacyclicPoly ℤ N := ⟨fun k => divRoundInt (C0.coeffs k) q_last⟩
  let C1' : NegacyclicPoly ℤ N := ⟨fun k => divRoundInt (C1.coeffs k) q_last⟩
  let τ0 : NegacyclicPoly ℤ N := (q_last : NegacyclicPoly ℤ N) * C0' - C0
  let τ1 : NegacyclicPoly ℤ N := (q_last : NegacyclicPoly ℤ N) * C1' - C1
  have h_tau_le : ∀ (C_p C_p' τ_p : NegacyclicPoly ℤ N),
      C_p' = ⟨fun k => divRoundInt (C_p.coeffs k) q_last⟩ →
      τ_p = (q_last : NegacyclicPoly ℤ N) * C_p' - C_p →
      NegacyclicPoly.intPolyNormInf τ_p ≤ q_last / 2 := by
    intro C_p C_p' τ_p hCp' hτp
    subst hCp' hτp
    change Finset.univ.sup (fun k =>
      (((q_last : NegacyclicPoly ℤ N) * ⟨fun j => divRoundInt (C_p.coeffs j) q_last⟩ -
        C_p).coeffs k).natAbs) ≤ q_last / 2
    apply Finset.sup_le
    intro k _
    rw [NegacyclicPoly.sub_coeffs]
    change ((NegacyclicPoly.constPoly (q_last : ℤ) * _).coeffs k - C_p.coeffs k).natAbs ≤
      q_last / 2
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    exact divRoundInt_mul_sub_bounds hq_last (C_p.coeffs k)
  have hτ0 : NegacyclicPoly.intPolyNormInf τ0 ≤ q_last / 2 := h_tau_le C0 C0' τ0 rfl rfl
  have hτ1 : NegacyclicPoly.intPolyNormInf τ1 ≤ q_last / 2 := h_tau_le C1 C1' τ1 rfl rfl
  have hq_old_z : (params_old.q : NegacyclicPoly ℤ N) =
      (params_new.q : NegacyclicPoly ℤ N) * (q_last : NegacyclicPoly ℤ N) := by
    rw [hq_prod, Nat.cast_mul]
  let E_res_z : NegacyclicPoly ℤ N :=
    (C0' + C1' * S) - M_next - (params_new.q : NegacyclicPoly ℤ N) * K
  have h_qE_res : (q_last : NegacyclicPoly ℤ N) * E_res_z = E_hat + τ0 + τ1 * S := by
    have h0 : (q_last : NegacyclicPoly ℤ N) * C0' = C0 + τ0 := by dsimp [τ0]; ring
    have h1 : (q_last : NegacyclicPoly ℤ N) * C1' = C1 + τ1 := by dsimp [τ1]; ring
    calc
      (q_last : NegacyclicPoly ℤ N) * E_res_z
        = (q_last : NegacyclicPoly ℤ N) * C0' + ((q_last : NegacyclicPoly ℤ N) * C1') * S -
            (q_last : NegacyclicPoly ℤ N) * M_next -
            (params_new.q : NegacyclicPoly ℤ N) * (q_last : NegacyclicPoly ℤ N) * K := by
          dsimp [E_res_z]
          ring
      _ = (C0 + C1 * S) + τ0 + τ1 * S - (q_last : NegacyclicPoly ℤ N) * M_next -
            (params_old.q : NegacyclicPoly ℤ N) * K := by
          rw [h0, h1, hq_old_z]
          ring
      _ = ((q_last : NegacyclicPoly ℤ N) * M_next + E_hat +
              (params_old.q : NegacyclicPoly ℤ N) * K) + τ0 + τ1 * S -
            (q_last : NegacyclicPoly ℤ N) * M_next -
            (params_old.q : NegacyclicPoly ℤ N) * K := by rw [hK_eq]
      _ = E_hat + τ0 + τ1 * S := by ring
  have hS_norm : NegacyclicPoly.intPolyNormInf S ≤ B_s := hs
  have hE_norm : NegacyclicPoly.intPolyNormInf E_hat ≤ B_mul := hE
  have hτ1S : NegacyclicPoly.intPolyNormInf (τ1 * S) ≤ N * (q_last / 2) * B_s :=
    le_trans (NegacyclicPoly.intPolyNormInf_mul_le τ1 S)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hτ1) hS_norm)
  have h_rhs_norm :
      NegacyclicPoly.intPolyNormInf (E_hat + τ0 + τ1 * S) ≤
        B_mul + (N * B_s + 1) * (q_last / 2) := by
    have h1 := NegacyclicPoly.intPolyNormInf_add_le (E_hat + τ0) (τ1 * S)
    have h2 := NegacyclicPoly.intPolyNormInf_add_le E_hat τ0
    have h_mul_eq : N * (q_last / 2) * B_s + q_last / 2 = (N * B_s + 1) * (q_last / 2) := by ring
    omega
  have hE_res_norm :
      NegacyclicPoly.intPolyNormInf E_res_z ≤ ckksRescaleNoiseBound q_last N B_s B_mul := by
    dsimp [NegacyclicPoly.intPolyNormInf, ckksRescaleNoiseBound]
    apply Finset.sup_le
    intro k _
    have hk := congrArg (fun p => p.coeffs k) h_qE_res
    have h_cm : ((q_last : NegacyclicPoly ℤ N) * E_res_z).coeffs k =
        (q_last : ℤ) * E_res_z.coeffs k :=
      NegacyclicPoly.constPoly_mul_coeffs (R := ℤ) (q_last : ℤ) E_res_z k
    rw [h_cm] at hk
    exact natAbs_le_div_of_mul_eq hq_last hk
      (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf _ k) h_rhs_norm)
  let E_res : NegacyclicPoly (Zq params_new) N :=
    NegacyclicPoly.intCastPolyHom params_new N E_res_z
  refine ⟨E_res, ?_, ?_⟩
  · have h_recombine : C0' + C1' * S =
        M_next + (params_new.q : NegacyclicPoly ℤ N) * K + E_res_z := by
      dsimp [E_res_z]
      ring
    have hc0_hom : ckksRescalePoly params_old params_new N q_last ct.c0 =
        NegacyclicPoly.intCastPolyHom params_new N C0' := rfl
    have hc1_hom : ckksRescalePoly params_old params_new N q_last ct.c1 =
        NegacyclicPoly.intCastPolyHom params_new N C1' := rfl
    have hs_hom : liftPolyToModulus params_old params_new N s =
        NegacyclicPoly.intCastPolyHom params_new N S := rfl
    calc
      ckksPhase (NegacyclicPoly (Zq params_new) N)
          (ckksRescaleCiphertext params_old params_new N q_last ct)
          (liftPolyToModulus params_old params_new N s)
        = NegacyclicPoly.intCastPolyHom params_new N (C0' + C1' * S) := by
          dsimp [ckksPhase, ckksRescaleCiphertext]
          rw [hc0_hom, hc1_hom, hs_hom, map_add, map_mul]
      _ = NegacyclicPoly.intCastPolyHom params_new N
            (M_next + (params_new.q : NegacyclicPoly ℤ N) * K + E_res_z) := by
          rw [h_recombine]
      _ = NegacyclicPoly.intCastPolyHom params_new N M_next + E_res := by
          rw [map_add, map_add, map_mul, NegacyclicPoly.intCastPolyHom_q_zero, zero_mul, add_zero]
  · exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params_new N E_res_z) hE_res_norm

theorem ckksRescale_fixedDecode_correct
    (params_old params_new : LWEParams) (N q_last Δ_next B_s B_mul B_m : ℕ) [Fact (0 < N)]
    (hq_prod : params_old.q = params_new.q * q_last)
    (hq_last : 0 < q_last)
    (ct : CKKSFixedCiphertext (NegacyclicPoly (Zq params_old) N))
    (h_scale : ct.scale = q_last * Δ_next)
    (s E_mul : NegacyclicPoly (Zq params_old) N)
    (M_plain : NegacyclicPoly ℤ N)
    (hs : normInf params_old s.coeffs ≤ B_s)
    (hE : normInf params_old E_mul.coeffs ≤ B_mul)
    (hM : NegacyclicPoly.intPolyNormInf M_plain ≤ B_m)
    (h_phase :
      ckksPhase (NegacyclicPoly (Zq params_old) N) ct s =
        NegacyclicPoly.intCastPolyHom params_old N
            ((q_last : NegacyclicPoly ℤ N) * ((Δ_next : NegacyclicPoly ℤ N) * M_plain)) +
          E_mul)
    (h_noise : 2 * ckksRescaleNoiseBound q_last N B_s B_mul < Δ_next)
    (h_wrap : 2 * (Δ_next * B_m + ckksRescaleNoiseBound q_last N B_s B_mul) < params_new.q) :
    let ct_res := ckksRescaleCiphertext params_old params_new N q_last ct
    ckksFixedDecodePoly params_new N ct_res.scale
        (ckksPhase (NegacyclicPoly (Zq params_new) N) ct_res
          (liftPolyToModulus params_old params_new N s)) =
      M_plain.coeffs := by
  intro ct_res
  rcases ckksRescale_phase_bound params_old params_new N q_last B_s B_mul hq_prod hq_last
    ct s E_mul ((Δ_next : NegacyclicPoly ℤ N) * M_plain) hs hE h_phase with
    ⟨E_res, h_res_phase, h_res_norm⟩
  have h_scale_eq : ct_res.scale = Δ_next := by
    dsimp [ct_res, ckksRescaleCiphertext]
    rw [h_scale, Nat.mul_div_cancel_left Δ_next hq_last]
  ext k
  rw [h_scale_eq]
  unfold ckksFixedDecodePoly
  rw [h_res_phase, NegacyclicPoly.add_coeffs, NegacyclicPoly.intCastPolyHom_coeffs]
  change ckksFixedDecodeElem params_new Δ_next
    (Int.cast ((NegacyclicPoly.constPoly (Δ_next : ℤ) * M_plain).coeffs k) + E_res.coeffs k) = _
  rw [NegacyclicPoly.constPoly_mul_coeffs, ← intCast_centeredLift params_new (E_res.coeffs k),
    ← Int.cast_add]
  have he_le : (centeredLift params_new (E_res.coeffs k)).natAbs ≤
      ckksRescaleNoiseBound q_last N B_s B_mul :=
    le_trans (Finset.le_sup (f := fun j => norm params_new (E_res.coeffs j)) (Finset.mem_univ k))
      h_res_norm
  have hm_le : (M_plain.coeffs k).natAbs ≤ B_m :=
    le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf M_plain k) hM
  have h_abs :
      ((Δ_next : ℤ) * M_plain.coeffs k + centeredLift params_new (E_res.coeffs k)).natAbs ≤
        Δ_next * B_m + ckksRescaleNoiseBound q_last N B_s B_mul := by
    have h_add := Int.natAbs_add_le ((Δ_next : ℤ) * M_plain.coeffs k)
      (centeredLift params_new (E_res.coeffs k))
    rw [Int.natAbs_mul, Int.natAbs_natCast] at h_add
    have h_mul := Nat.mul_le_mul_left Δ_next hm_le
    omega
  exact ckksFixedDecodeElem_correct params_new Δ_next (M_plain.coeffs k)
    (centeredLift params_new (E_res.coeffs k)) (by omega) (by omega)

theorem ckksRescale_ternary_fixedDecode_correct
    (params_old params_new : LWEParams) (N q_last Δ_next B_mul B_m : ℕ) [Fact (0 < N)]
    (hq_prod : params_old.q = params_new.q * q_last)
    (hq_last : 0 < q_last)
    (ct : CKKSFixedCiphertext (NegacyclicPoly (Zq params_old) N))
    (h_scale : ct.scale = q_last * Δ_next)
    (s E_mul : NegacyclicPoly (Zq params_old) N)
    (M_plain : NegacyclicPoly ℤ N)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hE : normInf params_old E_mul.coeffs ≤ B_mul)
    (hM : NegacyclicPoly.intPolyNormInf M_plain ≤ B_m)
    (h_phase :
      ckksPhase (NegacyclicPoly (Zq params_old) N) ct s =
        NegacyclicPoly.intCastPolyHom params_old N
            ((q_last : NegacyclicPoly ℤ N) * ((Δ_next : NegacyclicPoly ℤ N) * M_plain)) +
          E_mul)
    (h_noise : 2 * ckksRescaleNoiseBound q_last N 1 B_mul < Δ_next)
    (h_wrap : 2 * (Δ_next * B_m + ckksRescaleNoiseBound q_last N 1 B_mul) < params_new.q) :
    let ct_res := ckksRescaleCiphertext params_old params_new N q_last ct
    ckksFixedDecodePoly params_new N ct_res.scale
        (ckksPhase (NegacyclicPoly (Zq params_new) N) ct_res
          (liftPolyToModulus params_old params_new N s)) =
      M_plain.coeffs :=
  ckksRescale_fixedDecode_correct params_old params_new N q_last Δ_next 1 B_mul B_m
    hq_prod hq_last ct h_scale s E_mul M_plain
    (NegacyclicPoly.normInf_le_one_of_isTernaryPoly params_old N s hs) hE hM h_phase h_noise h_wrap

def ckksNaiveAdd {R : Type*} [Add R] (ct1 ct2 : CKKSFixedCiphertext R) : CKKSFixedCiphertext R :=
  { c0 := ct1.c0 + ct2.c0,
    c1 := ct1.c1 + ct2.c1,
    scale := ct1.scale }

def ckksScaleAlignMul {R : Type*} [CommRing R] (factor : ℕ) (ct : CKKSFixedCiphertext R) :
    CKKSFixedCiphertext R :=
  { c0 := (factor : R) * ct.c0,
    c1 := (factor : R) * ct.c1,
    scale := factor * ct.scale }

theorem ckksNaiveAdd_mismatched_scale_bias (R : Type*) [CommRing R]
    (ct1 ct2 : CKKSFixedCiphertext R) (s Δ1 Δ2 m1 m2 e1 e2 : R)
    (h1 : ckksPhase R ct1 s = Δ1 * m1 + e1)
    (h2 : ckksPhase R ct2 s = Δ2 * m2 + e2) :
    ckksPhase R (ckksNaiveAdd ct1 ct2) s =
      Δ1 * (m1 + m2) + ((Δ2 - Δ1) * m2 + (e1 + e2)) := by
  have h_sum : ckksPhase R (ckksNaiveAdd ct1 ct2) s = ckksPhase R ct1 s + ckksPhase R ct2 s := by
    dsimp [ckksPhase, ckksNaiveAdd]
    ring
  rw [h_sum, h1, h2]
  ring

theorem ckksNaiveAdd_mismatched_scale_counterexample :
    let p97 : LWEParams := { n := 1, m := 1, q := 97, q_pos := ⟨by decide⟩ }
    let s : Zq p97 := 0
    let ct1 : CKKSFixedCiphertext (Zq p97) :=
      { c0 := ((16 * 1 : ℕ) : Zq p97), c1 := 0, scale := 16 }
    let ct2 : CKKSFixedCiphertext (Zq p97) := { c0 := ((8 * 2 : ℕ) : Zq p97), c1 := 0, scale := 8 }
    let ct_naive := ckksNaiveAdd ct1 ct2
    let ct_aligned := ckksNaiveAdd ct1 (ckksScaleAlignMul 2 ct2)
    ckksFixedDecodeElem p97 ct1.scale (ckksPhase (Zq p97) ct1 s) = 1 ∧
      ckksFixedDecodeElem p97 ct2.scale (ckksPhase (Zq p97) ct2 s) = 2 ∧
      ckksFixedDecodeElem p97 ct_naive.scale (ckksPhase (Zq p97) ct_naive s) ≠ 3 ∧
      ckksFixedDecodeElem p97 ct_aligned.scale (ckksPhase (Zq p97) ct_aligned s) = 3 := by
  intro p97 s ct1 ct2 ct_naive ct_aligned
  have h1 : ckksFixedDecodeElem p97 ct1.scale (ckksPhase (Zq p97) ct1 s) = 1 := by
    have hp : ckksPhase (Zq p97) ct1 s = (((16 : ℤ) * 1 + 0 : ℤ) : Zq p97) := by
      dsimp [ckksPhase, ct1, s]
      decide
    rw [hp]
    exact ckksFixedDecodeElem_correct p97 16 1 0 (by decide) (by decide)
  have h2 : ckksFixedDecodeElem p97 ct2.scale (ckksPhase (Zq p97) ct2 s) = 2 := by
    have hp : ckksPhase (Zq p97) ct2 s = (((8 : ℤ) * 2 + 0 : ℤ) : Zq p97) := by
      dsimp [ckksPhase, ct2, s]
      decide
    rw [hp]
    exact ckksFixedDecodeElem_correct p97 8 2 0 (by decide) (by decide)
  have h_naive : ckksFixedDecodeElem p97 ct_naive.scale (ckksPhase (Zq p97) ct_naive s) = 2 := by
    have hp : ckksPhase (Zq p97) ct_naive s = (((16 : ℤ) * 2 + 0 : ℤ) : Zq p97) := by
      dsimp [ckksPhase, ct_naive, ckksNaiveAdd, ct1, ct2, s]
      decide
    dsimp [ct_naive, ckksNaiveAdd, ct1] at hp ⊢
    rw [hp]
    exact ckksFixedDecodeElem_correct p97 16 2 0 (by decide) (by decide)
  have h_aligned :
      ckksFixedDecodeElem p97 ct_aligned.scale (ckksPhase (Zq p97) ct_aligned s) = 3 := by
    have hp : ckksPhase (Zq p97) ct_aligned s = (((16 : ℤ) * 3 + 0 : ℤ) : Zq p97) := by
      dsimp [ckksPhase, ct_aligned, ckksNaiveAdd, ckksScaleAlignMul, ct1, ct2, s]
      decide
    dsimp [ct_aligned, ckksNaiveAdd, ct1] at hp ⊢
    rw [hp]
    exact ckksFixedDecodeElem_correct p97 16 3 0 (by decide) (by decide)
  exact ⟨h1, h2, by omega, h_aligned⟩

end BGVAndCKKSFHE

section ConcreteWitnessesAndMaster

open scoped BigOperators

local instance : Fact (0 < 2) := ⟨by decide⟩
local instance : Fact (0 < 4) := ⟨by decide⟩
local instance : Fact (0 < 113) := ⟨by decide⟩
local instance : Fact (0 < 256) := ⟨by decide⟩

theorem noZeroDivisors_zmod_of_prime {p : ℕ} (hp : Nat.Prime p) :
    NoZeroDivisors (ZMod p) where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} hab := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have h_prod : ((a.val * b.val : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hab
    have hdvd : p ∣ a.val * b.val := (ZMod.natCast_eq_zero_iff (a.val * b.val) p).mp h_prod
    rcases hp.dvd_mul.mp hdvd with ha | hb
    · left
      rw [← ZMod.natCast_zmod_val a]
      exact (ZMod.natCast_eq_zero_iff a.val p).mpr ha
    · right
      rw [← ZMod.natCast_zmod_val b]
      exact (ZMod.natCast_eq_zero_iff b.val p).mpr hb

lemma zmod_unit_ne_zero_of_prime {p : ℕ} (hp : Nat.Prime p) (u : (ZMod p)ˣ) :
    (u : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro h0
  have h1 : ((1 : ℕ) : ZMod p) = 0 := by
    calc
      ((1 : ℕ) : ZMod p) = (u : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        rw [Nat.cast_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = 0 := by rw [h0, zero_mul]
  have hdvd := (ZMod.natCast_eq_zero_iff 1 p).mp h1
  have hle : p ≤ 1 := Nat.le_of_dvd Nat.zero_lt_one hdvd
  have hlt := hp.one_lt
  omega

lemma coprime_val_of_ne_zero_prime {p : ℕ} (hp : Nat.Prime p) {x : ZMod p} (hx : x ≠ 0) :
    Nat.Coprime x.val p := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_pos : 0 < x.val := by
    by_contra h0
    have hv0 : x.val = 0 := by omega
    have hx0 : x = 0 := by rw [← ZMod.natCast_zmod_val x, hv0, Nat.cast_zero]
    exact hx hx0
  have h_lt : x.val < p := ZMod.val_lt x
  have h_ndvd : ¬ p ∣ x.val := Nat.not_dvd_of_pos_of_lt h_pos h_lt
  exact (hp.coprime_iff_not_dvd.mpr h_ndvd).symm

lemma card_zmod_units_of_prime {p : ℕ} [NeZero p] (hp : Nat.Prime p) :
    Fintype.card (ZMod p)ˣ = p - 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_bij :
      (Finset.univ : Finset (ZMod p)ˣ).card =
        ((Finset.univ : Finset (ZMod p)).erase 0).card := by
    refine Finset.card_bij (fun (u : (ZMod p)ˣ) _ => (u : ZMod p)) ?_ ?_ ?_
    · intro u _
      exact Finset.mem_erase.mpr ⟨zmod_unit_ne_zero_of_prime hp u, Finset.mem_univ _⟩
    · intro u₁ _ u₂ _ h_eq
      exact Units.ext h_eq
    · intro x hx
      have hx_ne : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have h_cop := coprime_val_of_ne_zero_prime hp hx_ne
      refine ⟨ZMod.unitOfCoprime x.val h_cop, Finset.mem_univ _, ?_⟩
      exact (ZMod.coe_unitOfCoprime x.val h_cop).trans (ZMod.natCast_zmod_val x)
  change (Finset.univ : Finset (ZMod p)ˣ).card = p - 1
  rw [h_bij, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
    ZMod.card p]

theorem zmod_pow_pred_eq_one_of_prime {p : ℕ} (hp : Nat.Prime p) {x : ZMod p} (hx : x ≠ 0) :
    x ^ (p - 1) = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_cop := coprime_val_of_ne_zero_prime hp hx
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime x.val h_cop
  have hu_pow : u ^ Fintype.card (ZMod p)ˣ = 1 := pow_card_eq_one
  rw [card_zmod_units_of_prime hp] at hu_pow
  have h_val := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) hu_pow
  rw [Units.val_pow_eq_pow_val, Units.val_one] at h_val
  have hu_x : (u : ZMod p) = x :=
    (ZMod.coe_unitOfCoprime x.val h_cop).trans (ZMod.natCast_zmod_val x)
  rwa [hu_x] at h_val

theorem not_exists_negacyclic_root_of_odd_quotient {p N m : ℕ}
    (hp : Nat.Prime p) (hp_odd : 2 < p) (hN : 0 < N) (hm : Odd m) (h_eq : p - 1 = N * m) :
    ¬ ∃ ψ : ZMod p, ψ ^ N = -1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h_neg1_ne_one : (-1 : ZMod p) ≠ 1 := by
    intro h_eq1
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      have hsub : (1 : ZMod p) - (-1 : ZMod p) = 0 := by rw [h_eq1, sub_self]
      have h2_eq : ((2 : ℕ) : ZMod p) = (1 : ZMod p) - (-1 : ZMod p) := by
        rw [Nat.cast_two]
        ring
      rwa [h2_eq]
    have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    omega
  rintro ⟨ψ, hψ⟩
  have hψ_ne : ψ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (ne_of_gt hN)] at hψ
    have hz : (-1 : ZMod p) = 0 := hψ.symm
    have h1 : (1 : ZMod p) = 0 := by
      rw [← neg_neg (1 : ZMod p), hz, neg_zero]
    exact h_neg1_ne_one (hz.trans h1.symm)
  have h_fermat := zmod_pow_pred_eq_one_of_prime hp hψ_ne
  rw [h_eq, pow_mul, hψ] at h_fermat
  rcases hm with ⟨k, rfl⟩
  have h_odd : (-1 : ZMod p) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul, pow_one]
    have h2 : (-1 : ZMod p) ^ 2 = 1 := by ring
    rw [h2, one_pow, one_mul]
  rw [h_odd] at h_fermat
  exact h_neg1_ne_one h_fermat

def toyZeroFailureParams : LWEParams :=
  { n := 4, m := 4, q := 97, q_pos := ⟨by decide⟩ }

def toyZeroFailureNTTEquiv :
    NegacyclicPoly (Zq toyZeroFailureParams) 4 ≃+* (Fin 4 → Zq toyZeroFailureParams) :=
  letI : NoZeroDivisors (Zq toyZeroFailureParams) := noZeroDivisors_zmod_of_prime (by decide)
  concreteNTTRingEquivPowTwo 2 (33 : Zq toyZeroFailureParams) (73 : Zq toyZeroFailureParams)
    (by decide) (by decide) (by decide)

theorem toyZeroFailureParams_verified :
    Nat.Prime toyZeroFailureParams.q ∧
      (33 : Zq toyZeroFailureParams) ^ 4 = -1 ∧
      48 * 2 ≤ toyZeroFailureParams.q ∧
      2 * (2 * 2 * 4 + 1) < 48 ∧
      2 * ((2 * 2 * 4 + 1) +
        ((toyZeroFailureParams.q + 2 ^ 4) / 2 ^ (4 + 1) +
          2 * 4 * ((toyZeroFailureParams.q + 2 ^ 7) / 2 ^ (7 + 1)))) < 48 := by
  decide

def mlkemPrimeParams : LWEParams :=
  { n := 256, m := 256, q := 3329, q_pos := ⟨by decide⟩ }

def noDivisorIn : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, 0 => true
  | _ + 1, p, a, 1 => p % a != 0
  | fuel + 1, p, a, m + 2 =>
    let h := (m + 2) / 2
    noDivisorIn fuel p a h && noDivisorIn fuel p (a + h) (m + 2 - h)

theorem forall_not_dvd_of_noDivisorIn :
    ∀ (fuel p a n : ℕ), noDivisorIn fuel p a n = true →
      ∀ d : ℕ, a ≤ d → d < a + n → ¬ d ∣ p := by
  intro fuel
  induction fuel with
  | zero =>
    intro p a n h
    simp [noDivisorIn] at h
  | succ fuel ih =>
    intro p a n h d hda hdn
    cases n with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        simp only [noDivisorIn, bne_iff_ne] at h
        have hda_eq : d = a := by omega
        subst hda_eq
        exact fun hdvd => h (Nat.mod_eq_zero_of_dvd hdvd)
      | succ m =>
        simp only [noDivisorIn, Bool.and_eq_true] at h
        by_cases hd : d < a + (m + 2) / 2
        · exact ih p a ((m + 2) / 2) h.1 d hda hd
        · exact ih p (a + (m + 2) / 2) (m + 2 - (m + 2) / 2) h.2 d (by omega) (by omega)

theorem nat_prime_of_noDivisorIn {p M : ℕ} (fuel : ℕ) (hp2 : 2 ≤ p) (hM2 : 2 ≤ M)
    (hsq : p < M * M) (hchk : noDivisorIn fuel p 2 (M - 2) = true) : Nat.Prime p := by
  rw [Nat.prime_def]
  refine ⟨hp2, fun d hd => ?_⟩
  rcases hd with ⟨k, hk⟩
  by_cases hd0 : d = 0
  · subst hd0
    omega
  by_cases hd1 : d = 1
  · exact Or.inl hd1
  by_cases hk0 : k = 0
  · subst hk0
    omega
  by_cases hk1 : k = 1
  · subst hk1
    right
    omega
  have hd2 : 2 ≤ d := by omega
  have hk2 : 2 ≤ k := by omega
  have hnd := forall_not_dvd_of_noDivisorIn fuel p 2 (M - 2) hchk
  have hsub : 2 + (M - 2) = M := by omega
  rw [hsub] at hnd
  by_cases hdm : d < M
  · exact False.elim (hnd d hd2 hdm ⟨k, hk⟩)
  by_cases hkm : k < M
  · exact False.elim (hnd k hk2 hkm ⟨d, hk.trans (mul_comm d k)⟩)
  have hmul : M * M ≤ d * k := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem mlkemPrimeParams_prime : Nat.Prime mlkemPrimeParams.q :=
  nat_prime_of_noDivisorIn (p := 3329) (M := 60) 10
    (by decide) (by decide) (by decide) (by decide)

theorem pow_17_pow2_7_mlkem : (17 : Zq mlkemPrimeParams) ^ 2 ^ 7 = -1 := by
  have h1 : (17 : Zq mlkemPrimeParams) ^ 2 = 289 := by decide
  have h2 : (289 : Zq mlkemPrimeParams) ^ 2 = 296 := by decide
  have h3 : (296 : Zq mlkemPrimeParams) ^ 2 = 1062 := by decide
  have h4 : (1062 : Zq mlkemPrimeParams) ^ 2 = 2642 := by decide
  have h5 : (2642 : Zq mlkemPrimeParams) ^ 2 = 2580 := by decide
  have h6 : (2580 : Zq mlkemPrimeParams) ^ 2 = 1729 := by decide
  have h7 : (1729 : Zq mlkemPrimeParams) ^ 2 = -1 := by decide
  have ha : (17 : Zq mlkemPrimeParams) ^ 4 = 296 := by
    calc
      (17 : Zq mlkemPrimeParams) ^ 4 = ((17 : Zq mlkemPrimeParams) ^ 2) ^ 2 := by ring
      _ = 296 := by rw [h1, h2]
  have hb : (17 : Zq mlkemPrimeParams) ^ 8 = 1062 := by
    calc
      (17 : Zq mlkemPrimeParams) ^ 8 = ((17 : Zq mlkemPrimeParams) ^ 4) ^ 2 := by ring
      _ = 1062 := by rw [ha, h3]
  have hc : (17 : Zq mlkemPrimeParams) ^ 16 = 2642 := by
    calc
      (17 : Zq mlkemPrimeParams) ^ 16 = ((17 : Zq mlkemPrimeParams) ^ 8) ^ 2 := by ring
      _ = 2642 := by rw [hb, h4]
  have hd : (17 : Zq mlkemPrimeParams) ^ 32 = 2580 := by
    calc
      (17 : Zq mlkemPrimeParams) ^ 32 = ((17 : Zq mlkemPrimeParams) ^ 16) ^ 2 := by ring
      _ = 2580 := by rw [hc, h5]
  have he : (17 : Zq mlkemPrimeParams) ^ 64 = 1729 := by
    calc
      (17 : Zq mlkemPrimeParams) ^ 64 = ((17 : Zq mlkemPrimeParams) ^ 32) ^ 2 := by ring
      _ = 1729 := by rw [hd, h6]
  calc
    (17 : Zq mlkemPrimeParams) ^ 2 ^ 7 = ((17 : Zq mlkemPrimeParams) ^ 64) ^ 2 := by ring
    _ = -1 := by rw [he, h7]

def mlkem128NTTEquiv :
    NegacyclicPoly (Zq mlkemPrimeParams) 128 ≃+* (Fin 128 → Zq mlkemPrimeParams) :=
  letI : NoZeroDivisors (Zq mlkemPrimeParams) :=
    noZeroDivisors_zmod_of_prime mlkemPrimeParams_prime
  concreteNTTRingEquivPowTwo 7 (17 : Zq mlkemPrimeParams) (3303 : Zq mlkemPrimeParams)
    (by decide) pow_17_pow2_7_mlkem (by decide)

theorem not_exists_negacyclic_root_3329_256 :
    ¬ ∃ ψ : Zq mlkemPrimeParams, ψ ^ 256 = -1 :=
  not_exists_negacyclic_root_of_odd_quotient (p := 3329) (N := 256) (m := 13)
    mlkemPrimeParams_prime (by decide) (by decide) ⟨6, rfl⟩ rfl

theorem mlkem_worst_case_ternary_noise_overflow :
    Nat.Prime mlkemPrimeParams.q ∧
      (17 : Zq mlkemPrimeParams) ^ 128 = -1 ∧
      ¬ (2 * (2 * 2 * 256 + 1) < mlkemPrimeParams.q / 2) ∧
      ¬ (2 * (2 * 3 * 256 + 1) < mlkemPrimeParams.q / 2) ∧
      ¬ (2 * (2 * 4 * 256 + 1) < mlkemPrimeParams.q / 2) :=
  ⟨mlkemPrimeParams_prime, pow_17_pow2_7_mlkem, by decide, by decide, by decide⟩

def standardZeroFailureParams : LWEParams :=
  { n := 256, m := 256, q := 12289, q_pos := ⟨by decide⟩ }

theorem standardZeroFailureParams_prime : Nat.Prime standardZeroFailureParams.q :=
  nat_prime_of_noDivisorIn (p := 12289) (M := 112) 10
    (by decide) (by decide) (by decide) (by decide)

theorem pow_3_pow2_8_std : (3 : Zq standardZeroFailureParams) ^ 2 ^ 8 = -1 := by
  have h1 : (3 : Zq standardZeroFailureParams) ^ 2 = 9 := by decide
  have h2 : (9 : Zq standardZeroFailureParams) ^ 2 = 81 := by decide
  have h3 : (81 : Zq standardZeroFailureParams) ^ 2 = 6561 := by decide
  have h4 : (6561 : Zq standardZeroFailureParams) ^ 2 = 10643 := by decide
  have h5 : (10643 : Zq standardZeroFailureParams) ^ 2 = 5736 := by decide
  have h6 : (5736 : Zq standardZeroFailureParams) ^ 2 = 4043 := by decide
  have h7 : (4043 : Zq standardZeroFailureParams) ^ 2 = 1479 := by decide
  have h8 : (1479 : Zq standardZeroFailureParams) ^ 2 = -1 := by decide
  have ha : (3 : Zq standardZeroFailureParams) ^ 4 = 81 := by
    calc
      (3 : Zq standardZeroFailureParams) ^ 4 = ((3 : Zq standardZeroFailureParams) ^ 2) ^ 2 := by
        ring
      _ = 81 := by rw [h1, h2]
  have hb : (3 : Zq standardZeroFailureParams) ^ 8 = 6561 := by
    calc
      (3 : Zq standardZeroFailureParams) ^ 8 = ((3 : Zq standardZeroFailureParams) ^ 4) ^ 2 := by
        ring
      _ = 6561 := by rw [ha, h3]
  have hc : (3 : Zq standardZeroFailureParams) ^ 16 = 10643 := by
    calc
      (3 : Zq standardZeroFailureParams) ^ 16 =
          ((3 : Zq standardZeroFailureParams) ^ 8) ^ 2 := by ring
      _ = 10643 := by rw [hb, h4]
  have hd : (3 : Zq standardZeroFailureParams) ^ 32 = 5736 := by
    calc
      (3 : Zq standardZeroFailureParams) ^ 32 =
          ((3 : Zq standardZeroFailureParams) ^ 16) ^ 2 := by ring
      _ = 5736 := by rw [hc, h5]
  have he : (3 : Zq standardZeroFailureParams) ^ 64 = 4043 := by
    calc
      (3 : Zq standardZeroFailureParams) ^ 64 =
          ((3 : Zq standardZeroFailureParams) ^ 32) ^ 2 := by ring
      _ = 4043 := by rw [hd, h6]
  have hf : (3 : Zq standardZeroFailureParams) ^ 128 = 1479 := by
    calc
      (3 : Zq standardZeroFailureParams) ^ 128 =
          ((3 : Zq standardZeroFailureParams) ^ 64) ^ 2 := by ring
      _ = 1479 := by rw [he, h7]
  calc
    (3 : Zq standardZeroFailureParams) ^ 2 ^ 8 =
        ((3 : Zq standardZeroFailureParams) ^ 128) ^ 2 := by ring
    _ = -1 := by rw [hf, h8]

def standardZeroFailureNTTEquiv :
    NegacyclicPoly (Zq standardZeroFailureParams) 256 ≃+*
      (Fin 256 → Zq standardZeroFailureParams) :=
  letI : NoZeroDivisors (Zq standardZeroFailureParams) :=
    noZeroDivisors_zmod_of_prime standardZeroFailureParams_prime
  concreteNTTRingEquivPowTwo 8 (3 : Zq standardZeroFailureParams)
    (12241 : Zq standardZeroFailureParams)
    (by decide) pow_3_pow2_8_std (by decide)

theorem standardZeroFailureParams_verified :
    Nat.Prime standardZeroFailureParams.q ∧
      (3 : Zq standardZeroFailureParams) ^ 256 = -1 ∧
      6144 * 2 ≤ standardZeroFailureParams.q ∧
      2 * (2 * 4 * 256 + 1) < 6144 ∧
      2 * ((2 * 2 * 256 + 1) +
        ((standardZeroFailureParams.q + 2 ^ 5) / 2 ^ (5 + 1) +
          2 * 256 * ((standardZeroFailureParams.q + 2 ^ 12) / 2 ^ (12 + 1)))) < 6144 :=
  ⟨standardZeroFailureParams_prime, pow_3_pow2_8_std, by decide, by decide, by decide⟩

def twoLimbRNSModuli : Fin 2 → ℕ := ![97, 113]

lemma twoLimbRNSModuli_pos : ∀ j : Fin 2, 0 < twoLimbRNSModuli j := by
  intro j
  fin_cases j <;> decide

lemma twoLimbRNSModuli_coprime :
    Pairwise (fun i j : Fin 2 => Nat.Coprime (twoLimbRNSModuli i) (twoLimbRNSModuli j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · decide
  · decide
  · exact False.elim (hij rfl)

def twoLimbRNSParams : LWEParams :=
  rnsParams twoLimbRNSModuli twoLimbRNSModuli_pos

def limb113Params : LWEParams :=
  { n := 4, m := 4, q := 113, q_pos := ⟨by decide⟩ }

def limb113NTTEquiv :
    NegacyclicPoly (Zq limb113Params) 4 ≃+* (Fin 4 → Zq limb113Params) :=
  letI : NoZeroDivisors (Zq limb113Params) := noZeroDivisors_zmod_of_prime (by decide)
  concreteNTTRingEquivPowTwo 2 (18 : Zq limb113Params) (85 : Zq limb113Params)
    (by decide) (by decide) (by decide)

theorem twoLimbRNSWitness_verified (p : NegacyclicPoly (Zq twoLimbRNSParams) 4) :
    twoLimbRNSParams.q = 10961 ∧
      (Nat.Prime (twoLimbRNSModuli 0) ∧ Nat.Prime (twoLimbRNSModuli 1)) ∧
      ((33 : Zq toyZeroFailureParams) ^ 4 = -1 ∧ (18 : Zq limb113Params) ^ 4 = -1) ∧
      (rnsPolyMultiCRTEquiv (N := 4) twoLimbRNSModuli twoLimbRNSModuli_coprime).symm
        (rnsPolyMultiCRTEquiv (N := 4) twoLimbRNSModuli twoLimbRNSModuli_coprime p) = p := by
  have h_facts :
      twoLimbRNSParams.q = 10961 ∧
        (Nat.Prime (twoLimbRNSModuli 0) ∧ Nat.Prime (twoLimbRNSModuli 1)) ∧
        ((33 : Zq toyZeroFailureParams) ^ 4 = -1 ∧ (18 : Zq limb113Params) ^ 4 = -1) := by
    decide
  exact ⟨h_facts.1, h_facts.2.1, h_facts.2.2,
    (rnsPolyMultiCRTEquiv (N := 4) twoLimbRNSModuli twoLimbRNSModuli_coprime).left_inv p⟩

lemma bfv_ternary_encrypt_noise_le (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (s e u e0 e1 : NegacyclicPoly (Zq params) N)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hu : NegacyclicPoly.IsTernaryPoly u)
    (he : normInf params e.coeffs ≤ 1)
    (he0 : normInf params e0.coeffs ≤ 1)
    (he1 : normInf params e1.coeffs ≤ 1) :
    normInf params (e0 + e1 * s - e * u).coeffs ≤ 2 * N + 1 := by
  have h_e1s : normInf params (e1 * s).coeffs ≤ N := by
    rw [mul_comm]
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N s e1 hs
    have h2 : N * normInf params e1.coeffs ≤ N * 1 := Nat.mul_le_mul_left N he1
    omega
  have h_eu : normInf params (e * u).coeffs ≤ N := by
    rw [mul_comm]
    have h1 := NegacyclicPoly.normInf_ternary_mul_le params N u e hu
    have h2 : N * normInf params e.coeffs ≤ N * 1 := Nat.mul_le_mul_left N he
    omega
  have h_sum := norm_add_le params e0.coeffs (e1 * s).coeffs
  have h_sub := norm_sub_le params (e0 + e1 * s).coeffs (e * u).coeffs
  change normInf params (e0 + e1 * s).coeffs ≤
    normInf params e0.coeffs + normInf params (e1 * s).coeffs at h_sum
  change normInf params (e0 + e1 * s - e * u).coeffs ≤
    normInf params (e0 + e1 * s).coeffs + normInf params (e * u).coeffs at h_sub
  omega

theorem bfvMul_phase_bound (params : LWEParams) (N Δ t B_s B_1 B_2 B l B_rk : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (hB : 0 < B)
    (h2B : 2 * B ≤ params.q)
    (ht : 0 < t)
    (hΔ : Δ = params.q / t)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hs : normInf params s.coeffs ≤ B_s)
    (hE1 : normInf params E1.coeffs ≤ B_1)
    (hE2 : normInf params E2.coeffs ≤ B_2)
    (herk : ∀ i : Fin l, normInf params (e_rk i).coeffs ≤ B_rk)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    ∃ E_mul : NegacyclicPoly (Zq params) N,
      bfvPhase (NegacyclicPoly (Zq params) N) (bfvMul params N t B l ct1 ct2 rk) s =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) + E_mul ∧
      normInf params E_mul.coeffs ≤ bfvMulTotalNoiseBound params.q N t B_s B_1 B_2 B l B_rk := by
  intro rk
  rcases bfvTensorScale_phase_bound params N Δ t B_s B_1 B_2 ht hΔ ct1 ct2 s E1 E2 m1 m2
    hm1 hm2 hs hE1 hE2 h_phase1 h_phase2 with ⟨E_scale, h_scale_phase, h_scale_norm⟩
  let d0 := bfvTensorScalePoly params N t (bfvTensorD0 params N ct1 ct2)
  let d1 := bfvTensorScalePoly params N t (bfvTensorD1 params N ct1 ct2)
  let d2 := bfvTensorScalePoly params N t (bfvTensorD2 params N ct1 ct2)
  let relin_err := ∑ i : Fin l, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i
  have h_relin := concrete_bfvGadgetRelinearize_phase params hq s d0 d1 d2 a_rk e_rk
  dsimp only at h_relin
  have h_phase :
      bfvPhase (NegacyclicPoly (Zq params) N) (bfvMul params N t B l ct1 ct2 rk) s =
        bfvEncodePoly params N Δ (bfvPlainMulMod N t m1 m2) + (E_scale - relin_err) := by
    change bfvPhase (NegacyclicPoly (Zq params) N)
      (bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
        (NegacyclicPoly.negacyclicDecomp params N B l) rk) s = _
    rw [h_relin, h_scale_phase]
    dsimp [relin_err]
    ring
  have h_relin_norm : normInf params relin_err.coeffs ≤ l * (N * (B - 1) * B_rk) :=
    NegacyclicPoly.normInf_gadgetRelin_noise_le params N B l B_rk hB h2B d2 e_rk herk
  have h_sub := norm_sub_le params E_scale.coeffs relin_err.coeffs
  change normInf params (E_scale - relin_err).coeffs ≤
    normInf params E_scale.coeffs + normInf params relin_err.coeffs at h_sub
  refine ⟨E_scale - relin_err, h_phase, ?_⟩
  dsimp only [bfvMulTotalNoiseBound]
  omega

theorem bgvMul_phase_bound (params : LWEParams) (N t B1 B2 B l B_rk : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (hB : 0 < B)
    (h2B : 2 * B ≤ params.q)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m1 m2 : Fin N → ℕ)
    (hm1 : ∀ k : Fin N, m1 k < t)
    (hm2 : ∀ k : Fin N, m2 k < t)
    (hE1 : normInf params E1.coeffs ≤ B1)
    (hE2 : normInf params E2.coeffs ≤ B2)
    (herk : ∀ i : Fin l, normInf params (e_rk i).coeffs ≤ B_rk)
    (h_phase1 :
      bfvPhase (NegacyclicPoly (Zq params) N) ct1 s =
        bfvPlainPoly params N m1 + (t : NegacyclicPoly (Zq params) N) * E1)
    (h_phase2 :
      bfvPhase (NegacyclicPoly (Zq params) N) ct2 s =
        bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * E2) :
    let d0 := ct1.c0 * ct2.c0
    let d1 := ct1.c0 * ct2.c1 + ct1.c1 * ct2.c0
    let d2 := ct1.c1 * ct2.c1
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk
      (fun i => (t : NegacyclicPoly (Zq params) N) * e_rk i) s
      (NegacyclicPoly.negacyclicGadget params N B l)
    let ct_mul := bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
      (NegacyclicPoly.negacyclicDecomp params N B l) rk
    ∃ E_mul : NegacyclicPoly (Zq params) N,
      bfvPhase (NegacyclicPoly (Zq params) N) ct_mul s =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
          (t : NegacyclicPoly (Zq params) N) * E_mul ∧
      normInf params E_mul.coeffs ≤ bgvMulTotalNoiseBound N t B1 B2 B l B_rk := by
  intro d0 d1 d2 rk ct_mul
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) (hm1 ⟨0, Fact.out⟩)
  let M1 : NegacyclicPoly ℤ N := ⟨fun k => (m1 k : ℤ)⟩
  let M2 : NegacyclicPoly ℤ N := ⟨fun k => (m2 k : ℤ)⟩
  let Q_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k / (t : ℤ)⟩
  let P_M : NegacyclicPoly ℤ N := ⟨fun k => (M1 * M2).coeffs k % (t : ℤ)⟩
  have hM1_norm : NegacyclicPoly.intPolyNormInf M1 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M1]
    apply Finset.sup_le
    intro k _
    have hk := hm1 k
    omega
  have hM2_norm : NegacyclicPoly.intPolyNormInf M2 ≤ t - 1 := by
    dsimp [NegacyclicPoly.intPolyNormInf, M2]
    apply Finset.sup_le
    intro k _
    have hk := hm2 k
    omega
  have hM12_norm : NegacyclicPoly.intPolyNormInf (M1 * M2) ≤ N * (t - 1) * (t - 1) :=
    le_trans (NegacyclicPoly.intPolyNormInf_mul_le M1 M2)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hM1_norm) hM2_norm)
  have hQM_norm : NegacyclicPoly.intPolyNormInf Q_M ≤ bfvPlainCarryBound N t := by
    dsimp [NegacyclicPoly.intPolyNormInf, Q_M, bfvPlainCarryBound]
    apply Finset.sup_le
    intro k _
    exact ediv_natAbs_le ht
      (le_trans (NegacyclicPoly.natAbs_coeffs_le_intPolyNormInf (M1 * M2) k) hM12_norm)
  have h_split : M1 * M2 = (t : NegacyclicPoly ℤ N) * Q_M + P_M := by
    ext k
    rw [NegacyclicPoly.add_coeffs]
    change (M1 * M2).coeffs k =
      (NegacyclicPoly.constPoly (t : ℤ) * Q_M).coeffs k + P_M.coeffs k
    rw [NegacyclicPoly.constPoly_mul_coeffs]
    dsimp [Q_M, P_M]
    rw [add_comm]
    exact (Int.emod_add_mul_ediv ((M1 * M2).coeffs k) (t : ℤ)).symm
  have hM1_zq : NegacyclicPoly.intCastPolyHom params N M1 = bfvPlainPoly params N m1 := by
    ext k
    exact Int.cast_natCast (m1 k)
  have hM2_zq : NegacyclicPoly.intCastPolyHom params N M2 = bfvPlainPoly params N m2 := by
    ext k
    exact Int.cast_natCast (m2 k)
  have hP_zq :
      NegacyclicPoly.intCastPolyHom params N P_M =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) := by
    ext k
    rw [NegacyclicPoly.intCastPolyHom_coeffs]
    have ht_pos : (0 : ℤ) < (t : ℤ) := Int.natCast_pos.mpr ht
    have h_eq := Int.toNat_of_nonneg (Int.emod_nonneg ((M1 * M2).coeffs k) (ne_of_gt ht_pos))
    change Int.cast ((M1 * M2).coeffs k % (t : ℤ)) =
      (((M1 * M2).coeffs k % (t : ℤ)).toNat : Zq params)
    exact (congrArg (Int.cast : ℤ → Zq params) h_eq).symm.trans (Int.cast_natCast _)
  let q_m_zq := NegacyclicPoly.intCastPolyHom params N Q_M
  have h_m12_zq :
      bfvPlainPoly params N m1 * bfvPlainPoly params N m2 =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
          (t : NegacyclicPoly (Zq params) N) * q_m_zq := by
    calc
      bfvPlainPoly params N m1 * bfvPlainPoly params N m2
        = NegacyclicPoly.intCastPolyHom params N (M1 * M2) := by
          rw [← hM1_zq, ← hM2_zq, ← map_mul]
      _ = NegacyclicPoly.intCastPolyHom params N ((t : NegacyclicPoly ℤ N) * Q_M + P_M) := by
          rw [h_split]
      _ = bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
            (t : NegacyclicPoly (Zq params) N) * q_m_zq := by
          rw [map_add, map_mul, map_natCast, hP_zq]
          ring
  let relin_err := ∑ i : Fin l, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i
  let E_tot :=
    q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
      (t : NegacyclicPoly (Zq params) N) * (E1 * E2) - relin_err
  have h_relin_alg := bfvGadgetRelinearize_phase (NegacyclicPoly (Zq params) N)
    s d0 d1 d2 a_rk (fun i => (t : NegacyclicPoly (Zq params) N) * e_rk i)
    (NegacyclicPoly.negacyclicGadget params N B l)
    (NegacyclicPoly.negacyclicDecomp params N B l)
    (NegacyclicPoly.negacyclicDecomp_isValid params N B l hq)
  have h_pull_t :
      (∑ i : Fin l,
        NegacyclicPoly.negacyclicDecomp params N B l d2 i *
          ((t : NegacyclicPoly (Zq params) N) * e_rk i)) =
        (t : NegacyclicPoly (Zq params) N) * relin_err := by
    dsimp [relin_err]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_tensor_id : d0 + d1 * s + d2 * (s * s) =
      bfvPhase (NegacyclicPoly (Zq params) N) ct1 s *
        bfvPhase (NegacyclicPoly (Zq params) N) ct2 s := by
    dsimp [d0, d1, d2, bfvPhase]
    ring
  have h_phase :
      bfvPhase (NegacyclicPoly (Zq params) N) ct_mul s =
        bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
          (t : NegacyclicPoly (Zq params) N) * E_tot := by
    dsimp only [ct_mul, rk]
    rw [h_relin_alg, h_pull_t, h_tensor_id, h_phase1, h_phase2]
    dsimp [E_tot]
    calc
      (bfvPlainPoly params N m1 + (t : NegacyclicPoly (Zq params) N) * E1) *
            (bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * E2) -
          (t : NegacyclicPoly (Zq params) N) * relin_err
        = (bfvPlainPoly params N m1 * bfvPlainPoly params N m2) +
            (t : NegacyclicPoly (Zq params) N) *
              (bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
                (t : NegacyclicPoly (Zq params) N) * (E1 * E2) - relin_err) := by ring
      _ = bfvPlainPoly params N (bfvPlainMulMod N t m1 m2) +
            (t : NegacyclicPoly (Zq params) N) *
              (q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
                (t : NegacyclicPoly (Zq params) N) * (E1 * E2) - relin_err) := by
          rw [h_m12_zq]
          ring
  have hqm_zq : normInf params q_m_zq.coeffs ≤ bfvPlainCarryBound N t :=
    le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params N Q_M) hQM_norm
  have hm1_zq : normInf params (bfvPlainPoly params N m1).coeffs ≤ t - 1 := by
    rw [← hM1_zq]
    exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params N M1) hM1_norm
  have hm2_zq : normInf params (bfvPlainPoly params N m2).coeffs ≤ t - 1 := by
    rw [← hM2_zq]
    exact le_trans (NegacyclicPoly.normInf_intCastPolyHom_le params N M2) hM2_norm
  have hm1E2 : normInf params (bfvPlainPoly params N m1 * E2).coeffs ≤ N * (t - 1) * B2 :=
    le_trans (NegacyclicPoly.normInf_mul_le params N _ _)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hm1_zq) hE2)
  have hE1m2 : normInf params (E1 * bfvPlainPoly params N m2).coeffs ≤ N * B1 * (t - 1) :=
    le_trans (NegacyclicPoly.normInf_mul_le params N _ _)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hE1) hm2_zq)
  have hE12 : normInf params (E1 * E2).coeffs ≤ N * B1 * B2 :=
    le_trans (NegacyclicPoly.normInf_mul_le params N _ _)
      (Nat.mul_le_mul (Nat.mul_le_mul_left N hE1) hE2)
  have htE12 :
      normInf params ((t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs ≤
        t * (N * B1 * B2) := by
    dsimp [normInf]
    apply Finset.sup_le
    intro k _
    change norm params
      ((NegacyclicPoly.constPoly ((t : ℕ) : Zq params) * (E1 * E2)).coeffs k) ≤ _
    rw [NegacyclicPoly.constPoly_mul_coeffs, ← intCast_centeredLift params ((E1 * E2).coeffs k),
      ← Int.cast_natCast t, ← Int.cast_mul]
    have h1 := norm_intCast_le_natAbs params ((t : ℤ) * centeredLift params ((E1 * E2).coeffs k))
    rw [Int.natAbs_mul, Int.natAbs_natCast] at h1
    have h2 : (centeredLift params ((E1 * E2).coeffs k)).natAbs ≤ normInf params (E1 * E2).coeffs :=
      Finset.le_sup (f := fun j => norm params ((E1 * E2).coeffs j)) (Finset.mem_univ k)
    exact le_trans h1 (Nat.mul_le_mul_left t (le_trans h2 hE12))
  have h_relin_norm : normInf params relin_err.coeffs ≤ l * (N * (B - 1) * B_rk) :=
    NegacyclicPoly.normInf_gadgetRelin_noise_le params N B l B_rk hB h2B d2 e_rk herk
  have hs1 : normInf params E_tot.coeffs ≤
      normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 + E1 * bfvPlainPoly params N m2 +
        (t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs +
        normInf params relin_err.coeffs :=
    norm_sub_le params _ _
  have hs2 : normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 +
        E1 * bfvPlainPoly params N m2 + (t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs ≤
      normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 +
        E1 * bfvPlainPoly params N m2).coeffs +
        normInf params ((t : NegacyclicPoly (Zq params) N) * (E1 * E2)).coeffs :=
    norm_add_le params _ _
  have hs3 : normInf params (q_m_zq + bfvPlainPoly params N m1 * E2 +
        E1 * bfvPlainPoly params N m2).coeffs ≤
      normInf params (q_m_zq + bfvPlainPoly params N m1 * E2).coeffs +
        normInf params (E1 * bfvPlainPoly params N m2).coeffs :=
    norm_add_le params _ _
  have hs4 : normInf params (q_m_zq + bfvPlainPoly params N m1 * E2).coeffs ≤
      normInf params q_m_zq.coeffs + normInf params (bfvPlainPoly params N m1 * E2).coeffs :=
    norm_add_le params _ _
  refine ⟨E_tot, h_phase, ?_⟩
  dsimp only [bgvMulTotalNoiseBound]
  omega

lemma odd_coprime_four {g : ℕ} (hg : Odd g) : Nat.Coprime g 4 := by
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, Nat.gcd_rec 4 g]
  rcases hg with ⟨k, rfl⟩
  have hmod : (2 * k + 1) % 4 = 1 ∨ (2 * k + 1) % 4 = 3 := by omega
  rcases hmod with h | h <;> rw [h] <;> decide

theorem lwe_modkem_fo_cca2_master
    {Coins Key Seed : Type*} [Fintype Key] {q_D : ℕ}
    (p1 p2 : NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (G : ModPKEPublicKey (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      (Fin 256 → Fin 2) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (expandE2 : Coins → NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 → Key)
    (A : MatrixR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4)
    (s e : VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (z : Seed)
    (Q_G : (Fin 256 → Fin 2) → Finset (Fin 256 → Fin 2))
    (ct_queries : (Fin 256 → Fin 2) → Fin q_D →
      ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (adv : ModPKECiphertext (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 →
      Key → (Fin q_D → Key) → Bool)
    (hs_tern : ∀ i : Fin 4, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin 4, normInf standardZeroFailureParams (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin 4, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin 4,
      normInf standardZeroFailureParams (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf standardZeroFailureParams (expandE2 c).coeffs ≤ 1)
    (h_non_chal : ∀ (m_star : Fin 256 → Fin 2) (i : Fin q_D),
      ct_queries m_star i ≠
        (modKEMEncapsFin standardZeroFailureParams 4 256 6144 2 G expandR expandE1 expandE2
          (modPKEKeygen (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 A s e) m_star).1)
    (A_c : MatrixR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 2 2)
    (s_c e_c r_c e1_c : VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 2)
    (e2_c : NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (m_c : Fin 256 → ℕ)
    (hs_c : ∀ i : Fin 2, NegacyclicPoly.IsTernaryPoly (s_c i))
    (hr_c : ∀ i : Fin 2, NegacyclicPoly.IsTernaryPoly (r_c i))
    (he_c : ∀ i : Fin 2, normInf standardZeroFailureParams (e_c i).coeffs ≤ 1)
    (he1_c : ∀ i : Fin 2, normInf standardZeroFailureParams (e1_c i).coeffs ≤ 1)
    (he2_c : normInf standardZeroFailureParams e2_c.coeffs ≤ 1)
    (hm_c : ∀ idx : Fin 256, m_c idx < 2) :
    let p := standardZeroFailureParams
    let pk := modPKEKeygen (NegacyclicPoly (Zq p) 256) 4 A s e
    let encPKE := modFOEncPKE p 4 256 6144 2 expandR expandE1 expandE2
    let decPKE := modFODecPKE p 4 256 6144 2
    let pk_c := modPKEKeygen (NegacyclicPoly (Zq p) 256) 2 A_c s_c e_c
    let ct_c := modPKEEncrypt (NegacyclicPoly (Zq p) 256) 2 pk_c r_c e1_c e2_c
      (bfvEncodePoly p 256 6144 m_c)
    let qct_c := modPKECompressCiphertext p 256 2 12 5 ct_c
    let ct_dec_c := modPKEDecompressCiphertext p 256 2 12 5 qct_c
    standardZeroFailureNTTEquiv.symm
        (standardZeroFailureNTTEquiv p1 * standardZeroFailureNTTEquiv p2) = p1 * p2 ∧
      IsCorrectFOPKE encPKE decPKE G pk s ∧
      Function.Injective (foEncDet encPKE G pk) ∧
      (∀ m : Fin 256 → Fin 2,
        let enc := modKEMEncapsFin p 4 256 6144 2 G expandR expandE1 expandE2 pk m
        modKEMDecapsFin p 4 256 6144 2 G expandR expandE1 expandE2 J pk s z enc.1 = enc.2) ∧
      (∀ (m_star : Fin 256 → Fin 2) (i : Fin q_D),
        foEncDet encPKE G pk (decPKE s (ct_queries m_star i)) = ct_queries m_star i →
          decPKE s (ct_queries m_star i) ≠ m_star) ∧
      (let Ω := (Fin 256 → Fin 2) × (Key × Key)
       let dist : FinDist Ω := uniformFinDist Ω
       let RealKEM0 : Ω → Bool := fun ω =>
         let G' := foReprogramKey G ω.1 ω.2.1
         let ct_star := (modKEMEncapsFin p 4 256 6144 2 G' expandR expandE1 expandE2 pk ω.1).1
         adv ct_star ω.2.1
           (fun i => modKEMDecapsFin p 4 256 6144 2 G' expandR expandE1 expandE2 J pk s z
             (ct_queries ω.1 i))
       let RealKEM1 : Ω → Bool := fun ω =>
         let G' := foReprogramKey G ω.1 ω.2.1
         let ct_star := (modKEMEncapsFin p 4 256 6144 2 G' expandR expandE1 expandE2 pk ω.1).1
         adv ct_star ω.2.2
           (fun i => modKEMDecapsFin p 4 256 6144 2 G' expandR expandE1 expandE2 J pk s z
             (ct_queries ω.1 i))
       let BadDecapsG : Ω → Prop := fun ω =>
         ∃ i : Fin q_D, foBadDecapsEvent encPKE decPKE G (Q_G ω.1) pk s (ct_queries ω.1 i)
       let QueryChallenge : Ω → Prop := fun ω => ω.1 ∈ Q_G ω.1
       (dist.acceptWeight RealKEM0 - dist.acceptWeight RealKEM1).natAbs ≤
         2 * dist.eventMass BadDecapsG + 2 * dist.eventMass QueryChallenge) ∧
      bfvDecodePoly p 256 6144 (modPKEPhase (NegacyclicPoly (Zq p) 256) 2 ct_dec_c s_c) = m_c ∧
      (∀ i : Fin 2,
        unpackBitsFromBytes 12 256 384 (packBitsToBytes 12 256 384 (qct_c.u_comp i)) =
          qct_c.u_comp i) := by
  intro p pk encPKE decPKE pk_c ct_c qct_c ct_dec_c
  have h_ntt :
      standardZeroFailureNTTEquiv.symm
          (standardZeroFailureNTTEquiv p1 * standardZeroFailureNTTEquiv p2) = p1 * p2 := by
    rw [← map_mul, standardZeroFailureNTTEquiv.symm_apply_apply]
  have h_cca := modKEM_fo_ind_cca2_end_to_end p 4 256 6144 2
    G expandR expandE1 expandE2 J A s e z Q_G ct_queries adv
    (by dsimp only [p]; decide)
    hs_tern he_norm hr_tern he1_norm he2_norm
    (by decide) h_non_chal
  have h_pke_c := modPKE_ternary_noise_bound p 2 256 s_c e_c r_c e1_c e2_c
    hr_c hs_c he_c he1_c he2_c
  have h_comp_noise : 2 * (normInf p
      (dotProductR (NegacyclicPoly (Zq p) 256) 2 e_c r_c + e2_c -
        dotProductR (NegacyclicPoly (Zq p) 256) 2 s_c e1_c).coeffs +
      ((p.q + 2 ^ 5) / 2 ^ (5 + 1) + 2 * 256 * ((p.q + 2 ^ 12) / 2 ^ (12 + 1)))) < 6144 := by
    have h_v : 2 * ((2 * 2 * 256 + 1) +
        ((p.q + 2 ^ 5) / 2 ^ (5 + 1) + 2 * 256 * ((p.q + 2 ^ 12) / 2 ^ (12 + 1)))) < 6144 := by
      dsimp only [p]
      decide
    omega
  have h_comp_dec := modPKE_actual_compress_decrypt_correct p 2 256 6144 2 12 5
    A_c s_c e_c r_c e1_c e2_c m_c hs_c
    (by dsimp only [p]; decide) hm_c h_comp_noise
  have h_pack : ∀ i : Fin 2,
      unpackBitsFromBytes 12 256 384 (packBitsToBytes 12 256 384 (qct_c.u_comp i)) =
        qct_c.u_comp i := fun i => by
    dsimp only [qct_c, modPKECompressCiphertext, lweCompressPoly, lweCompressElem]
    exact unpackBitsFromBytes_packBitsToBytes_compress_id p.q 12 256 384
      (by decide) (fun idx => ZMod.val ((ct_c.u i).coeffs idx))
  exact ⟨h_ntt, h_cca.1, h_cca.2.1, h_cca.2.2.1, h_cca.2.2.2.1, h_cca.2.2.2.2,
    h_comp_dec, h_pack⟩

theorem bfv_fhe_end_to_end_master
    (pt_simd : NegacyclicPoly (Zq toyZeroFailureParams) 4)
    (a s e u1 e10 e11 u2 e20 e21 : NegacyclicPoly (Zq standardZeroFailureParams) 4)
    (a_rk e_rk a_gk e_gk : VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 4) 4)
    (m1 m2 : Fin 4 → ℕ)
    (g : ℕ) (hg : Odd g)
    (hs : NegacyclicPoly.IsTernaryPoly s)
    (hu1 : NegacyclicPoly.IsTernaryPoly u1)
    (hu2 : NegacyclicPoly.IsTernaryPoly u2)
    (he : normInf standardZeroFailureParams e.coeffs ≤ 1)
    (he10 : normInf standardZeroFailureParams e10.coeffs ≤ 1)
    (he11 : normInf standardZeroFailureParams e11.coeffs ≤ 1)
    (he20 : normInf standardZeroFailureParams e20.coeffs ≤ 1)
    (he21 : normInf standardZeroFailureParams e21.coeffs ≤ 1)
    (herk : ∀ i : Fin 4, normInf standardZeroFailureParams (e_rk i).coeffs ≤ 1)
    (hegk : ∀ i : Fin 4, normInf standardZeroFailureParams (e_gk i).coeffs ≤ 1)
    (hm1 : ∀ idx : Fin 4, m1 idx < 2)
    (hm2 : ∀ idx : Fin 4, m2 idx < 2) :
    let p_old := standardZeroFailureParams
    let p_new := toyZeroFailureParams
    let pk := bfvKeygen (NegacyclicPoly (Zq p_old) 4) a s e
    let ct1 := bfvEncrypt (NegacyclicPoly (Zq p_old) 4) pk u1 e10 e11
      (bfvEncodePoly p_old 4 6144 m1)
    let ct2 := bfvEncrypt (NegacyclicPoly (Zq p_old) 4) pk u2 e20 e21
      (bfvEncodePoly p_old 4 6144 m2)
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq p_old) 4) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget p_old 4 16 4)
    let ct_mul := bfvMul p_old 4 2 16 4 ct1 ct2 rk
    let ct_sw := bfvModSwitchCiphertext p_old p_new 4 ct_mul
    let σ := NegacyclicPoly.negacyclicGaloisHom (R := Zq p_old) (N := 4) g hg
    let gk := mkBFVGaloisKey (NegacyclicPoly (Zq p_old) 4) σ a_gk e_gk s
      (NegacyclicPoly.negacyclicGadget p_old 4 16 4)
    let ct_gal := bfvApplyGalois (NegacyclicPoly (Zq p_old) 4) σ ct1
      (NegacyclicPoly.negacyclicDecomp p_old 4 16 4) gk
    bfvBatchEncode (50 : Zq p_new) (73 : Zq p_new)
        (bfvBatchDecode (33 : Zq p_new) pt_simd) = pt_simd ∧
      bfvDecryptPoly p_old 4 6144 s ct1 = m1 ∧
      bfvDecryptPoly p_old 4 6144 s (bfvAdd (NegacyclicPoly (Zq p_old) 4) ct1 ct2) =
        (fun idx => (m1 idx + m2 idx) % 2) ∧
      bfvDecryptPoly p_old 4 6144 s ct_mul = bfvPlainMulMod 4 2 m1 m2 ∧
      bfvDecryptPoly p_new 4 48 (liftPolyToModulus p_old p_new 4 s) ct_sw =
        bfvPlainMulMod 4 2 m1 m2 ∧
      bfvDecryptPoly p_old 4 6144 s ct_gal = bfvPlainGaloisMod 4 2 g m1 := by
  intro p_old p_new pk ct1 ct2 rk ct_mul ct_sw σ gk ct_gal
  haveI : NoZeroDivisors (Zq p_new) := by
    dsimp only [p_new]
    exact noZeroDivisors_zmod_of_prime (by decide)
  have h_simd :
      bfvBatchEncode (50 : Zq p_new) (73 : Zq p_new)
        (bfvBatchDecode (33 : Zq p_new) pt_simd) = pt_simd := by
    apply bfvBatchEncode_decode
    dsimp only [p_new]
    have h_prim := pow_two_prim_of_pow_eq_neg_one (k := 2) (ψ := (33 : Zq toyZeroFailureParams))
      (ψ_inv := (50 : Zq toyZeroFailureParams)) (by decide) (by decide) (by decide)
    exact isValidNTTInverse_of_primitive (33 : Zq toyZeroFailureParams)
      (50 : Zq toyZeroFailureParams) (73 : Zq toyZeroFailureParams)
      (by decide) (by decide) (by decide) h_prim
  have h_e1_le : normInf p_old (e10 + e11 * s - e * u1).coeffs ≤ 9 := by
    have h := bfv_ternary_encrypt_noise_le p_old 4 s e u1 e10 e11 hs hu1 he he10 he11
    omega
  have h_e2_le : normInf p_old (e20 + e21 * s - e * u2).coeffs ≤ 9 := by
    have h := bfv_ternary_encrypt_noise_le p_old 4 s e u2 e20 e21 hs hu2 he he20 he21
    omega
  have h_phase1 :
      bfvPhase (NegacyclicPoly (Zq p_old) 4) ct1 s =
        bfvEncodePoly p_old 4 6144 m1 + (e10 + e11 * s - e * u1) := by
    dsimp only [ct1, pk]
    exact bfvEncrypt_phase (NegacyclicPoly (Zq p_old) 4) a s e u1 e10 e11
      (bfvEncodePoly p_old 4 6144 m1)
  have h_phase2 :
      bfvPhase (NegacyclicPoly (Zq p_old) 4) ct2 s =
        bfvEncodePoly p_old 4 6144 m2 + (e20 + e21 * s - e * u2) := by
    dsimp only [ct2, pk]
    exact bfvEncrypt_phase (NegacyclicPoly (Zq p_old) 4) a s e u2 e20 e21
      (bfvEncodePoly p_old 4 6144 m2)
  have h_dec1 : bfvDecryptPoly p_old 4 6144 s ct1 = m1 :=
    bfvDecryptPoly_of_phase_eq p_old 4 6144 2 s _ ct1 m1
      (by dsimp only [p_old]; decide) hm1 h_phase1 (by omega)
  have h_add :
      bfvDecryptPoly p_old 4 6144 s (bfvAdd (NegacyclicPoly (Zq p_old) 4) ct1 ct2) =
        fun idx => (m1 idx + m2 idx) % 2 :=
    bfvDecryptPoly_add_mod_t_correct p_old 4 6144 2
      (by decide) s
      (e10 + e11 * s - e * u1) (e20 + e21 * s - e * u2) ct1 ct2 m1 m2
      (by dsimp only [p_old]; decide) hm1 hm2
      h_phase1 h_phase2
      (by
        have h_pq : p_old.q - 6144 * 2 = 1 := by
          dsimp only [p_old]
          decide
        rw [h_pq]
        omega)
  have hs_norm : normInf p_old s.coeffs ≤ 1 :=
    NegacyclicPoly.normInf_le_one_of_isTernaryPoly p_old 4 s hs
  have h_mul_bnd :
      2 * bfvMulTotalNoiseBound p_old.q 4 2 1 9 9 16 4 1 < 6144 := by
    dsimp only [p_old]
    decide
  have h_mul : bfvDecryptPoly p_old 4 6144 s ct_mul = bfvPlainMulMod 4 2 m1 m2 :=
    bfvDecryptPoly_bfvMul_ternary_correct p_old 4 6144 2 9 9 16 4 1
      (by dsimp only [p_old]; decide)
      (by decide)
      (by dsimp only [p_old]; decide)
      (by decide)
      (by dsimp only [p_old]; decide)
      (by dsimp only [p_old]; decide) ct1 ct2 s
      (e10 + e11 * s - e * u1) (e20 + e21 * s - e * u2) a_rk e_rk m1 m2 hm1 hm2 hs
      h_e1_le h_e2_le herk h_phase1 h_phase2 h_mul_bnd
  rcases bfvMul_phase_bound p_old 4 6144 2 1 9 9 16 4 1
      (by dsimp only [p_old]; decide)
      (by decide)
      (by dsimp only [p_old]; decide)
      (by decide)
      (by dsimp only [p_old]; decide) ct1 ct2 s
      (e10 + e11 * s - e * u1) (e20 + e21 * s - e * u2)
      a_rk e_rk m1 m2 hm1 hm2 hs_norm h_e1_le h_e2_le herk h_phase1 h_phase2 with
    ⟨E_mul, h_mul_phase, h_mul_norm⟩
  have h_sw_bnd :
      2 * bfvModSwitchNoiseBound p_old.q p_new.q 4 6144 48 2 1
        (bfvMulTotalNoiseBound p_old.q 4 2 1 9 9 16 4 1) < 48 := by
    dsimp only [p_old, p_new]
    decide
  have h_sw :
      bfvDecryptPoly p_new 4 48 (liftPolyToModulus p_old p_new 4 s) ct_sw =
        bfvPlainMulMod 4 2 m1 m2 :=
    bfvDecryptPoly_modSwitch_ternary_correct p_old p_new 4 6144 48 2
      (bfvMulTotalNoiseBound p_old.q 4 2 1 9 9 16 4 1)
      (by dsimp only [p_old]; decide)
      (by dsimp only [p_new]; decide) ct_mul s E_mul
      (bfvPlainMulMod 4 2 m1 m2) (bfvPlainMulMod_lt (by decide) m1 m2) hs h_mul_norm
      h_mul_phase h_sw_bnd
  have h_gal_bnd :
      2 * (normInf p_old (e10 + e11 * s - e * u1).coeffs + (p_old.q - 6144 * 2) +
        4 * (4 * (16 - 1) * 1)) < 6144 := by
    have h_num : 2 * (9 + 1 + 4 * (4 * (16 - 1) * 1)) < 6144 := by decide
    have h_pq : p_old.q - 6144 * 2 = 1 := by
      dsimp only [p_old]
      decide
    rw [h_pq]
    omega
  have h_gal : bfvDecryptPoly p_old 4 6144 s ct_gal = bfvPlainGaloisMod 4 2 g m1 :=
    bfvDecryptPoly_applyGalois_mod_t_correct p_old 4 6144 2 g 16 4 1 hg (odd_coprime_four hg)
      (by dsimp only [p_old]; decide)
      (by decide)
      (by dsimp only [p_old]; decide)
      (by decide)
      (by dsimp only [p_old]; decide) ct1 s _ a_gk e_gk m1 hm1
      h_phase1 hegk h_gal_bnd
  exact ⟨h_simd, h_dec1, h_add, h_mul, h_sw, h_gal⟩

theorem rns_bgv_ckks_master
    (s_rns d0_rns d1_rns d2_rns : ∀ j : Fin 2, NegacyclicPoly (ZMod (twoLimbRNSModuli j)) 4)
    (a_rns e_rns : VectorR (∀ j : Fin 2, NegacyclicPoly (ZMod (twoLimbRNSModuli j)) 4) 2)
    (herk_rns : ∀ i : Fin 2,
      normInf twoLimbRNSParams
        ((rnsPolyMultiCRTEquiv twoLimbRNSModuli twoLimbRNSModuli_coprime).symm (e_rns i)).coeffs ≤
        1)
    (a_bgv s_bgv e_bgv u1 e10 e11 u2 e20 e21 : NegacyclicPoly (Zq twoLimbRNSParams) 4)
    (a_rk_bgv e_rk_bgv : VectorR (NegacyclicPoly (Zq twoLimbRNSParams) 4) 4)
    (m1 m2 : Fin 4 → ℕ)
    (hs_bgv : NegacyclicPoly.IsTernaryPoly s_bgv)
    (hu1_bgv : NegacyclicPoly.IsTernaryPoly u1)
    (hu2_bgv : NegacyclicPoly.IsTernaryPoly u2)
    (he_bgv : normInf twoLimbRNSParams e_bgv.coeffs ≤ 1)
    (he10_bgv : normInf twoLimbRNSParams e10.coeffs ≤ 1)
    (he11_bgv : normInf twoLimbRNSParams e11.coeffs ≤ 1)
    (he20_bgv : normInf twoLimbRNSParams e20.coeffs ≤ 1)
    (he21_bgv : normInf twoLimbRNSParams e21.coeffs ≤ 1)
    (herk_bgv : ∀ i : Fin 4, normInf twoLimbRNSParams (e_rk_bgv i).coeffs ≤ 1)
    (hm1 : ∀ idx : Fin 4, m1 idx < 2)
    (hm2 : ∀ idx : Fin 4, m2 idx < 2)
    (ct_ckks : CKKSFixedCiphertext (NegacyclicPoly (Zq twoLimbRNSParams) 4))
    (h_ckks_scale : ct_ckks.scale = 113 * 16)
    (s_ckks E_ckks : NegacyclicPoly (Zq twoLimbRNSParams) 4)
    (M_ckks : NegacyclicPoly ℤ 4)
    (hs_ckks : NegacyclicPoly.IsTernaryPoly s_ckks)
    (hE_ckks : normInf twoLimbRNSParams E_ckks.coeffs ≤ 50)
    (hM_ckks : NegacyclicPoly.intPolyNormInf M_ckks ≤ 2)
    (h_ckks_phase :
      ckksPhase (NegacyclicPoly (Zq twoLimbRNSParams) 4) ct_ckks s_ckks =
        NegacyclicPoly.intCastPolyHom twoLimbRNSParams 4
            ((113 : NegacyclicPoly ℤ 4) * ((16 : NegacyclicPoly ℤ 4) * M_ckks)) +
          E_ckks) :
    let pQ := twoLimbRNSParams
    let p_new := toyZeroFailureParams
    let e_poly := rnsPolyMultiCRTEquiv (N := 4) twoLimbRNSModuli twoLimbRNSModuli_coprime
    let rk_rns := mkBFVGadgetRelinKey
      (∀ j : Fin 2, NegacyclicPoly (ZMod (twoLimbRNSModuli j)) 4)
      a_rns e_rns s_rns (rnsPolyCRTGadget twoLimbRNSModuli 4)
    let ct_relin_rns := bfvGadgetRelinearize
      (∀ j : Fin 2, NegacyclicPoly (ZMod (twoLimbRNSModuli j)) 4)
      d0_rns d1_rns d2_rns (rnsPolyCenteredFastBconvDecomp twoLimbRNSModuli twoLimbRNSModuli_pos 4)
      rk_rns
    let S_rns : NegacyclicPoly (Zq pQ) 4 := e_poly.symm s_rns
    let D0_rns : NegacyclicPoly (Zq pQ) 4 := e_poly.symm d0_rns
    let D1_rns : NegacyclicPoly (Zq pQ) 4 := e_poly.symm d1_rns
    let D2_rns : NegacyclicPoly (Zq pQ) 4 := e_poly.symm d2_rns
    let ct_relin_Q : BFVCiphertext (NegacyclicPoly (Zq pQ) 4) :=
      { c0 := e_poly.symm ct_relin_rns.c0, c1 := e_poly.symm ct_relin_rns.c1 }
    let pk_bgv := bgvKeygen (NegacyclicPoly (Zq pQ) 4)
      (2 : NegacyclicPoly (Zq pQ) 4) a_bgv s_bgv e_bgv
    let ct1_bgv := bgvEncrypt (NegacyclicPoly (Zq pQ) 4) (2 : NegacyclicPoly (Zq pQ) 4)
      pk_bgv u1 e10 e11 (bfvPlainPoly pQ 4 m1)
    let ct2_bgv := bgvEncrypt (NegacyclicPoly (Zq pQ) 4) (2 : NegacyclicPoly (Zq pQ) 4)
      pk_bgv u2 e20 e21 (bfvPlainPoly pQ 4 m2)
    let rk_bgv := mkBFVGadgetRelinKey (NegacyclicPoly (Zq pQ) 4) a_rk_bgv
      (fun i => (2 : NegacyclicPoly (Zq pQ) 4) * e_rk_bgv i) s_bgv
      (NegacyclicPoly.negacyclicGadget pQ 4 16 4)
    let ct_mul_bgv := bfvGadgetRelinearize (NegacyclicPoly (Zq pQ) 4)
      (ct1_bgv.c0 * ct2_bgv.c0)
      (ct1_bgv.c0 * ct2_bgv.c1 + ct1_bgv.c1 * ct2_bgv.c0)
      (ct1_bgv.c1 * ct2_bgv.c1)
      (NegacyclicPoly.negacyclicDecomp pQ 4 16 4) rk_bgv
    let ct_sw_bgv := bgvModSwitchDropLimbCiphertext pQ p_new 4 113 2 (by decide) ct_mul_bgv
    let ct_res_ckks := ckksRescaleCiphertext pQ p_new 4 113 ct_ckks
    (∃ E_relin : NegacyclicPoly (Zq pQ) 4,
      bfvPhase (NegacyclicPoly (Zq pQ) 4) ct_relin_Q S_rns =
        (D0_rns + D1_rns * S_rns + D2_rns * (S_rns * S_rns)) - E_relin ∧
      normInf pQ E_relin.coeffs ≤ 416) ∧
      bgvDecryptPoly pQ 4 2 s_bgv ct_mul_bgv = bfvPlainMulMod 4 2 m1 m2 ∧
      bgvDecryptPoly p_new 4 2 (liftPolyToModulus pQ p_new 4 s_bgv) ct_sw_bgv =
        bfvPlainMulMod 4 2 m1 m2 ∧
      ckksFixedDecodePoly p_new 4 ct_res_ckks.scale
          (ckksPhase (NegacyclicPoly (Zq p_new) 4) ct_res_ckks
            (liftPolyToModulus pQ p_new 4 s_ckks)) =
        M_ckks.coeffs := by
  intro pQ p_new e_poly rk_rns ct_relin_rns S_rns D0_rns D1_rns D2_rns ct_relin_Q
    pk_bgv ct1_bgv ct2_bgv rk_bgv ct_mul_bgv ct_sw_bgv ct_res_ckks
  rcases rnsPolyCenteredFastBconv_relin_phase_and_noise_bound (N := 4) (B_rk := 1)
      twoLimbRNSModuli twoLimbRNSModuli_pos twoLimbRNSModuli_coprime
      s_rns d0_rns d1_rns d2_rns a_rns e_rns herk_rns with
    ⟨E_relin, h_relin_phase, h_relin_norm⟩
  have h_sum_416 : (∑ i : Fin 2, 4 * (twoLimbRNSModuli i / 2) * 1) = 416 := by decide
  rw [h_sum_416] at h_relin_norm
  have h_e1_le : normInf pQ (e10 + e11 * s_bgv - e_bgv * u1).coeffs ≤ 9 := by
    have h := bfv_ternary_encrypt_noise_le pQ 4 s_bgv e_bgv u1 e10 e11
      hs_bgv hu1_bgv he_bgv he10_bgv he11_bgv
    omega
  have h_e2_le : normInf pQ (e20 + e21 * s_bgv - e_bgv * u2).coeffs ≤ 9 := by
    have h := bfv_ternary_encrypt_noise_le pQ 4 s_bgv e_bgv u2 e20 e21
      hs_bgv hu2_bgv he_bgv he20_bgv he21_bgv
    omega
  have h_phase1 :
      bfvPhase (NegacyclicPoly (Zq pQ) 4) ct1_bgv s_bgv =
        bfvPlainPoly pQ 4 m1 +
          (2 : NegacyclicPoly (Zq pQ) 4) * (e10 + e11 * s_bgv - e_bgv * u1) := by
    dsimp only [ct1_bgv, pk_bgv]
    exact bgvEncrypt_phase (NegacyclicPoly (Zq pQ) 4) (2 : NegacyclicPoly (Zq pQ) 4)
      a_bgv s_bgv e_bgv u1 e10 e11 (bfvPlainPoly pQ 4 m1)
  have h_phase2 :
      bfvPhase (NegacyclicPoly (Zq pQ) 4) ct2_bgv s_bgv =
        bfvPlainPoly pQ 4 m2 +
          (2 : NegacyclicPoly (Zq pQ) 4) * (e20 + e21 * s_bgv - e_bgv * u2) := by
    dsimp only [ct2_bgv, pk_bgv]
    exact bgvEncrypt_phase (NegacyclicPoly (Zq pQ) 4) (2 : NegacyclicPoly (Zq pQ) 4)
      a_bgv s_bgv e_bgv u2 e20 e21 (bfvPlainPoly pQ 4 m2)
  have h_bgv_mul_bnd :
      2 * ((2 - 1) + 2 * bgvMulTotalNoiseBound 4 2 9 9 16 4 1) < pQ.q := by
    dsimp only [pQ]
    decide
  have h_bgv_mul : bgvDecryptPoly pQ 4 2 s_bgv ct_mul_bgv = bfvPlainMulMod 4 2 m1 m2 :=
    bgvDecryptPoly_mul_correct pQ 4 2 9 9 16 4 1
      (by dsimp only [pQ]; decide)
      (by decide)
      (by dsimp only [pQ]; decide)
      ct1_bgv ct2_bgv s_bgv (e10 + e11 * s_bgv - e_bgv * u1) (e20 + e21 * s_bgv - e_bgv * u2)
      a_rk_bgv e_rk_bgv m1 m2 hm1 hm2 h_e1_le h_e2_le herk_bgv h_phase1 h_phase2 h_bgv_mul_bnd
  rcases bgvMul_phase_bound pQ 4 2 9 9 16 4 1
      (by dsimp only [pQ]; decide)
      (by decide)
      (by dsimp only [pQ]; decide)
      ct1_bgv ct2_bgv s_bgv (e10 + e11 * s_bgv - e_bgv * u1) (e20 + e21 * s_bgv - e_bgv * u2)
      a_rk_bgv e_rk_bgv m1 m2 hm1 hm2 h_e1_le h_e2_le herk_bgv h_phase1 h_phase2 with
    ⟨E_mul_bgv, h_bgv_phase, h_bgv_norm⟩
  have h_bgv_sw_bnd :
      2 * ((2 - 1) + 2 * bgvModSwitchNoiseBound 113 4 2 1 (bgvMulTotalNoiseBound 4 2 9 9 16 4 1)) <
        p_new.q := by
    dsimp only [p_new]
    decide
  have h_bgv_sw :
      bgvDecryptPoly p_new 4 2 (liftPolyToModulus pQ p_new 4 s_bgv) ct_sw_bgv =
        bfvPlainMulMod 4 2 m1 m2 :=
    bgvDecryptPoly_modSwitchDropLimb_ternary_correct pQ p_new 4 113 2
      (bgvMulTotalNoiseBound 4 2 9 9 16 4 1)
      (by dsimp only [pQ, p_new]; decide)
      (by decide) ct_mul_bgv s_bgv E_mul_bgv
      (bfvPlainMulMod 4 2 m1 m2) (bfvPlainMulMod_lt (by decide) m1 m2) hs_bgv h_bgv_norm
      h_bgv_phase h_bgv_sw_bnd
  have h_ckks_res :
      ckksFixedDecodePoly p_new 4 ct_res_ckks.scale
          (ckksPhase (NegacyclicPoly (Zq p_new) 4) ct_res_ckks
            (liftPolyToModulus pQ p_new 4 s_ckks)) =
        M_ckks.coeffs :=
    ckksRescale_ternary_fixedDecode_correct pQ p_new 4 113 16 50 2
      (by dsimp only [pQ, p_new]; decide)
      (by decide)
      ct_ckks h_ckks_scale s_ckks E_ckks M_ckks hs_ckks hE_ckks hM_ckks h_ckks_phase
      (by decide)
      (by dsimp only [p_new]; decide)
  exact ⟨⟨E_relin, h_relin_phase, h_relin_norm⟩, h_bgv_mul, h_bgv_sw, h_ckks_res⟩

theorem zkp_hvzk_soundness_master
    (A : MatrixR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4)
    (wit : ModZKPSecretWitness (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4)
    (y_s y_e : VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (c : NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (z_s z_e : VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (c1 c2 : NegacyclicPoly (Zq standardZeroFailureParams) 256)
    (w : VectorR (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4)
    (resp1 resp2 : ModZKPResponse (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : ∀ j : Fin 4, normInf standardZeroFailureParams (wit.s j).coeffs ≤ 1)
    (he : ∀ i : Fin 4, normInf standardZeroFailureParams (wit.e i).coeffs ≤ 1)
    (hys : ∀ j : Fin 4, normInf standardZeroFailureParams (y_s j).coeffs ≤ 1024)
    (hye : ∀ i : Fin 4, normInf standardZeroFailureParams (y_e i).coeffs ≤ 1024)
    (hz_bnd :
      modZkpVerifyBound (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4 ⟨z_s, z_e⟩ 1280)
    (hc_ne : c1 ≠ c2)
    (ha1 :
      modZkpVerifyAlgebraic (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4
        (mkModZKPPublicInfo (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4 A wit)
        c1 w resp1)
    (ha2 :
      modZkpVerifyAlgebraic (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4
        (mkModZKPPublicInfo (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4 A wit)
        c2 w resp2)
    (hb1 : modZkpVerifyBound (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4 resp1 1280)
    (hb2 : modZkpVerifyBound (NegacyclicPoly (Zq standardZeroFailureParams) 256) 4 4 resp2 1280) :
    let p := standardZeroFailureParams
    let R := NegacyclicPoly (Zq p) 256
    let pub := mkModZKPPublicInfo R 4 4 A wit
    let com := modZkpCommit R 4 4 A y_s y_e
    let resp := modZkpRespond R 4 4 y_s y_e c wit
    (modZkpVerifyAlgebraic R 4 4 pub c com resp ∧ modZkpVerifyBound R 4 4 resp 1280) ∧
      (∃! y ∈ modZkpAcceptedMasks 4 4 p 256 1536 256 c wit,
        modZkpRespond R 4 4 y.1 y.2 c wit = ⟨z_s, z_e⟩) ∧
      ((modZkpAcceptedMasks 4 4 p 256 1536 256 c wit).card = 2561 ^ 2048 ∧
        0 < (modZkpAcceptedMasks 4 4 p 256 1536 256 c wit).card) ∧
      (c1 - c2 ≠ 0 ∧
        evaluate R 4 4 pub.A (resp1.z_s - resp2.z_s) (resp1.z_e - resp2.z_e) =
          (fun i => (c1 - c2) * pub.t i) ∧
        (∀ j : Fin 4, normInf p ((resp1.z_s - resp2.z_s) j).coeffs ≤ 2560) ∧
        (∀ i : Fin 4, normInf p ((resp1.z_e - resp2.z_e) i).coeffs ≤ 2560) ∧
        2560 < p.q / 2) ∧
      (∃ δ z_star : Zq p,
        norm p δ ≤ 256 ∧ norm p z_star ≤ 1792 ∧
        (∃ y ∈ boundedBall p 1536, y + δ = z_star) ∧
        (∀ y ∈ boundedBall p 1536, y + 0 ≠ z_star)) := by
  intro p R pub com resp
  have h_alg := mod_zkp_completeness R 4 4 A y_s y_e c wit
  have hys' : ∀ j : Fin 4, normInf p (y_s j).coeffs + 256 ≤ 1280 := fun j => by
    have hj : normInf p (y_s j).coeffs ≤ 1024 := hys j
    omega
  have hye' : ∀ i : Fin 4, normInf p (y_e i).coeffs + 256 ≤ 1280 := fun i => by
    have hi : normInf p (y_e i).coeffs ≤ 1024 := hye i
    omega
  have h_bnd := concrete_mod_zkp_respond_passes_verify 4 4 p 256 1280 256 1
    y_s y_e c wit hc hs he (by decide) hys' hye'
  have hz_bnd0 : modZkpVerifyBound (NegacyclicPoly (Zq p) 256) 4 4 ⟨z_s, z_e⟩ 1280 := by
    dsimp only [p]
    exact hz_bnd
  have h_diff : 1536 - 256 = 1280 := rfl
  have hz_bnd' :
      modZkpVerifyBound (NegacyclicPoly (Zq p) 256) 4 4 ⟨z_s, z_e⟩ (1536 - 256) :=
    h_diff.symm ▸ hz_bnd0
  have h_uniq := existsUnique_modZkpMask_of_verifyBound 4 4 p 256 1536 256 1
    (by decide)
    c wit hc hs he (by decide) hz_bnd'
  have h_card_raw := card_modZkpAcceptedMasks_eq 4 4 p 256 1536 256 1
    (by dsimp only [p]; decide)
    (by decide)
    c wit hc hs he (by decide)
  have h_base : 2 * (1536 - 256) + 1 = 2561 := by decide
  have h_exp : (4 + 4) * 256 = 2048 := by decide
  have h_card : (modZkpAcceptedMasks 4 4 p 256 1536 256 c wit).card = 2561 ^ 2048 ∧
      0 < (modZkpAcceptedMasks 4 4 p 256 1536 256 c wit).card := by
    rcases h_card_raw with ⟨h_eq, h_pos⟩
    rw [h_base, h_exp] at h_eq
    exact ⟨h_eq, h_pos⟩
  have h_sound := mod_zkp_special_soundness_nonvacuous 4 4 p 256 1280
    (by dsimp only [p]; decide) pub
    c1 c2 w resp1 resp2 hc_ne ha1 ha2 hb1 hb2
  have h_sound' :
      c1 - c2 ≠ 0 ∧
        evaluate R 4 4 pub.A (resp1.z_s - resp2.z_s) (resp1.z_e - resp2.z_e) =
          (fun i => (c1 - c2) * pub.t i) ∧
        (∀ j : Fin 4, normInf p ((resp1.z_s - resp2.z_s) j).coeffs ≤ 2560) ∧
        (∀ i : Fin 4, normInf p ((resp1.z_e - resp2.z_e) i).coeffs ≤ 2560) ∧
        2560 < p.q / 2 := by
    have h_m : 2 * 1280 = 2560 := rfl
    simpa [h_m] using h_sound
  have h_leak := zkp_no_rejection_leaks_witness p 1536 256
    (by decide)
    (by dsimp only [p]; decide)
  have h_sum_1792 : 1536 + 256 = 1792 := rfl
  rw [h_sum_1792] at h_leak
  exact ⟨⟨h_alg, h_bnd⟩, h_uniq, h_card, h_sound', h_leak⟩

end ConcreteWitnessesAndMaster

end LWE
