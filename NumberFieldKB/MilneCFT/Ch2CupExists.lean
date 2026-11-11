import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2CupUnique

/-!
# Milne, *Class Field Theory*, Chapter II §1: existence of cup products

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

We prove the existence half of Proposition 1.38 (p. 73) by Milne's cochain formula on Mathlib's inhomogeneous
cochains: for `φ : (Fin r → G) → M` and `ψ : (Fin s → G) → N`,
$(\varphi \cup \psi)(g_1,\dots,g_{r+s}) = \varphi(g_1,\dots,g_r) \otimes g_1\cdots g_r\,\psi(g_{r+1},\dots,g_{r+s})$
(`cupC`; indices are 0-based). The Leibniz rule `cupC_leibniz`,
$d(\varphi\cup\psi) = d\varphi\cup\psi + (-1)^r \varphi\cup d\psi$, shows that the cup product of cocycles is a
cocycle and descends to cohomology (`cupH`); the axioms (a)–(d) of `CupProductFamily` are then checked on cochains.
-/

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology Limits MonoidalCategory

variable {G : Type} [Group G]

/-- The ordered product $a_0 a_1 \cdots a_{r-1}$ of a tuple (`Fin.partialProd` at the last index). -/
noncomputable def fprod {r : ℕ} (a : Fin r → G) : G := Fin.partialProd a (Fin.last r)

/-- The first `r` entries of `g : Fin n → G` (where `r + s = n`). -/
def hdF {r s n : ℕ} (h : r + s = n) (g : Fin n → G) : Fin r → G :=
  fun i => g (Fin.cast h (Fin.castAdd s i))

/-- The last `s` entries of `g : Fin n → G` (where `r + s = n`). -/
def tlF {r s n : ℕ} (h : r + s = n) (g : Fin n → G) : Fin s → G :=
  fun i => g (Fin.cast h (Fin.natAdd r i))

/-- **The cup product of cochains** (Milne, CFT v4.03, Ch. II, Prop. 1.38, p. 73, cochain formula):
$(\varphi \cup \psi)(g) = \varphi(g_1,\dots,g_r) \otimes g_1\cdots g_r\,\psi(g_{r+1},\dots,g_{r+s})$ for
`g : Fin n → G`, `r + s = n`. -/
noncomputable def cupC {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) (g : Fin n → G) : (M ⊗ N : Rep ℤ G) :=
  TensorProduct.tmul ℤ (M := M) (N := N) (φ (hdF h g)) (N.ρ (fprod (hdF h g)) (ψ (tlF h g)))

lemma cupC_apply {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) (g : Fin n → G) :
    cupC h φ ψ g = rtmul (A := M) (B := N) (φ (hdF h g)) (N.ρ (fprod (hdF h g)) (ψ (tlF h g))) := rfl

lemma zsmul_sum' {X ι : Type*} [AddCommGroup X] (n : ℤ) (s : Finset ι) (f : ι → X) :
    n • ∑ i ∈ s, f i = ∑ i ∈ s, n • f i := Finset.smul_sum

lemma zsmul_add' {X : Type*} [AddCommGroup X] (n : ℤ) (a b : X) :
    n • (a + b) = n • a + n • b := smul_add n a b

lemma tensor_ρ_tmul (M N : Rep ℤ G) (g : G) (a : M) (b : N) :
    (M ⊗ N).ρ g (TensorProduct.tmul ℤ (M := M) (N := N) a b) =
      TensorProduct.tmul ℤ (M := M) (N := N) (M.ρ g a) (N.ρ g b) := rfl

lemma d_apply' (A : Rep ℤ G) (n : ℕ) (f : (Fin n → G) → A) (g : Fin (n+1) → G) :
    inhomogeneousCochains.d A n f g = A.ρ (g 0) (f fun i => g i.succ) + ∑ j : Fin (n + 1),
        (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
  rw [inhomogeneousCochains.d_hom_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (int_smul_eq_zsmul _ _ _).symm.symm

lemma fprod_succ {r : ℕ} (a : Fin (r+1) → G) : fprod a = a 0 * fprod (Fin.tail a) := by
  unfold fprod
  exact Fin.partialProd_succ' a (Fin.last r)

lemma fprod_snoc {r : ℕ} (a : Fin (r+1) → G) : fprod a = fprod (Fin.init a) * a (Fin.last r) := by
  unfold fprod
  have := Fin.partialProd_succ a (Fin.last r)
  rw [Fin.succ_last] at this
  rw [this, Fin.partialProd_init]

lemma fprod_contractNth {r : ℕ} (a : Fin (r+1) → G) (j : Fin r) :
    fprod (Fin.contractNth j.castSucc (· * ·) a) = fprod a := by
  unfold fprod
  have := congrFun (Fin.partialProd_contractNth a j.castSucc) (Fin.last r)
  rw [this]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_le_castSucc]
  · simp
  · simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    omega

section pointwise

local macro "fin_ext" : tactic => `(tactic| (apply Fin.ext; (try simp) <;> omega))

variable {r s : ℕ} (g : Fin (r+s+1) → G)

lemma hdF_tail : hdF (rfl : r + s = r + s) (fun i => g i.succ) =
    Fin.tail (hdF (by omega : r+1+s = r+s+1) g) := by
  funext i
  simp only [hdF, Fin.tail]
  congr! 2 <;> fin_ext

lemma tlF_tail : tlF (rfl : r + s = r + s) (fun i => g i.succ) =
    tlF (by omega : r+1+s = r+s+1) g := by
  funext i
  simp only [tlF]
  congr! 2 <;> fin_ext

lemma hdF_contract_lt (j : Fin r) :
    hdF (rfl : r + s = r + s) (Fin.contractNth (Fin.castAdd (s+1) j) (· * ·) g) =
    Fin.contractNth j.castSucc (· * ·) (hdF (by omega : r+1+s = r+s+1) g) := by
  funext i
  simp only [hdF, Fin.contractNth, Fin.val_castAdd, Fin.val_cast, Fin.val_castSucc]
  split_ifs <;> first | (exfalso; omega) | (congr! 2 <;> fin_ext)

lemma tlF_contract_lt (j : Fin r) :
    tlF (rfl : r + s = r + s) (Fin.contractNth (Fin.castAdd (s+1) j) (· * ·) g) =
    tlF (by omega : r+1+s = r+s+1) g := by
  funext i
  simp only [tlF, Fin.contractNth, Fin.val_castAdd, Fin.val_cast, Fin.val_natAdd]
  split_ifs <;> first | (exfalso; omega) | (congr! 2 <;> fin_ext)

lemma hdF_contract_ge (k : Fin (s+1)) :
    hdF (rfl : r + s = r + s) (Fin.contractNth (Fin.natAdd r k) (· * ·) g) =
    hdF (r := r) (s := s+1) rfl g := by
  funext i
  simp only [hdF, Fin.contractNth, Fin.val_natAdd, Fin.val_cast, Fin.val_castAdd]
  split_ifs <;> first | (exfalso; omega) | (congr! 2 <;> fin_ext)

lemma tlF_contract_ge (k : Fin (s+1)) :
    tlF (rfl : r + s = r + s) (Fin.contractNth (Fin.natAdd r k) (· * ·) g) =
    Fin.contractNth k (· * ·) (tlF (r := r) (s := s+1) rfl g) := by
  funext i
  simp only [tlF, Fin.contractNth, Fin.val_natAdd, Fin.val_cast, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> first | (exfalso; omega) | (congr! 2 <;> fin_ext)

lemma hdF_h2_eq_init : hdF (r := r) (s := s+1) rfl g = Fin.init (hdF (by omega : r+1+s = r+s+1) g) := by
  funext i
  simp only [hdF, Fin.init]
  exact congrArg g (Fin.ext (by (try simp) <;> omega))

lemma last_eq_zero : (hdF (by omega : r+1+s = r+s+1) g) (Fin.last r) =
    (tlF (r := r) (s := s+1) rfl g) 0 := by
  simp only [hdF, tlF]
  exact congrArg g (Fin.ext (by (try simp) <;> omega))

lemma hdF_zero : (hdF (by omega : r+1+s = r+s+1) g) 0 = g 0 := by
  simp only [hdF]
  congr! 2 <;> fin_ext

lemma tail_tlF_h2 : Fin.tail (tlF (r := r) (s := s+1) rfl g) = tlF (by omega : r+1+s = r+s+1) g := by
  funext i
  simp only [tlF, Fin.tail]
  exact congrArg g (Fin.ext (by (try simp) <;> omega))

end pointwise

lemma contractNth_last {r : ℕ} (A : Fin (r+1) → G) :
    Fin.contractNth (Fin.last r) (· * ·) A = Fin.init A := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  rfl

lemma zsmul_rtmul {M N : Rep ℤ G} (n : ℤ) (a : M) (b : N) :
    n • rtmul (A := M) (B := N) a b = rtmul (A := M) (B := N) (n • a) b :=
  (map_zsmul (AddMonoidHom.mk' (fun a : M => rtmul (A := M) (B := N) a b)
    (fun x y => TensorProduct.add_tmul x y b)) n a).symm

lemma zsmul_rtmul' {M N : Rep ℤ G} (n : ℤ) (a : M) (b : N) :
    n • rtmul (A := M) (B := N) a b = rtmul (A := M) (B := N) a (n • b) :=
  (map_zsmul (AddMonoidHom.mk' (fun b : N => rtmul (A := M) (B := N) a b)
    (fun x y => TensorProduct.tmul_add a x y)) n b).symm

lemma d_tmul_left {M N : Rep ℤ G} (r : ℕ) (φ : (Fin r → G) → M) (A : Fin (r+1) → G) (b : N) :
    rtmul (A := M) (B := N) (inhomogeneousCochains.d M r φ A) b =
      rtmul (M.ρ (A 0) (φ (Fin.tail A))) b +
      ∑ j : Fin r, (-1 : ℤ) ^ ((j : ℕ) + 1) •
        rtmul (A := M) (B := N) (φ (Fin.contractNth j.castSucc (· * ·) A)) b +
      (-1 : ℤ) ^ (r + 1) • rtmul (A := M) (B := N) (φ (Fin.init A)) b := by
  rw [d_apply', rtmul, TensorProduct.add_tmul, TensorProduct.sum_tmul, Fin.sum_univ_castSucc]
  simp only [zsmul_rtmul, Fin.val_castSucc, Fin.val_last, contractNth_last, ← add_assoc]
  rfl

lemma d_tmul_right {M N : Rep ℤ G} (s : ℕ) (ψ : (Fin s → G) → N) (B : Fin (s+1) → G) (a : M) (x : G) :
    rtmul (A := M) (B := N) a (N.ρ x (inhomogeneousCochains.d N s ψ B)) =
      rtmul (A := M) (B := N) a (N.ρ (x * B 0) (ψ (Fin.tail B))) +
      ∑ k : Fin (s+1), (-1 : ℤ) ^ ((k : ℕ) + 1) •
        rtmul (A := M) (B := N) a (N.ρ x (ψ (Fin.contractNth k (· * ·) B))) := by
  rw [d_apply', map_add, map_sum, rtmul, TensorProduct.tmul_add, TensorProduct.tmul_sum]
  simp only [map_zsmul, ← zsmul_rtmul', map_mul]
  rfl

/-- **Leibniz rule** for the cup product of cochains (Milne, CFT v4.03, Ch. II, Prop. 1.38, p. 73):
$d(\varphi \cup \psi) = d\varphi \cup \psi + (-1)^r\, \varphi \cup d\psi$ for an $r$-cochain $\varphi$ and an
$s$-cochain $\psi$. -/
theorem cupC_leibniz {M N : Rep ℤ G} (r s : ℕ) (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    inhomogeneousCochains.d (M ⊗ N) (r + s) (cupC rfl φ ψ) =
      cupC (by omega : r + 1 + s = r + s + 1) (inhomogeneousCochains.d M r φ) ψ +
      (-1 : ℤ) ^ r • cupC (rfl : r + (s + 1) = r + s + 1) φ (inhomogeneousCochains.d N s ψ) := by
  funext g
  rw [d_apply']
  simp only [Pi.add_apply, Pi.smul_apply]
  -- abbreviations
  have h1 : r + 1 + s = r + s + 1 := by omega
  have e1 : (M ⊗ N).ρ (g 0) (cupC rfl φ ψ (fun i => g i.succ)) =
      rtmul (M.ρ (g 0) (φ (Fin.tail (hdF h1 g)))) (N.ρ (fprod (hdF h1 g)) (ψ (tlF h1 g))) := by
    unfold cupC
    rw [tensor_ρ_tmul, hdF_tail, tlF_tail, fprod_succ (hdF h1 g), hdF_zero, map_mul]
    rfl
  have e2 : ∀ j : Fin r, (-1 : ℤ) ^ (((Fin.castAdd (s+1) j : Fin (r+s+1)) : ℕ) + 1) •
      cupC rfl φ ψ (Fin.contractNth (Fin.castAdd (s+1) j) (· * ·) g) =
      (-1 : ℤ) ^ ((j : ℕ) + 1) • rtmul (φ (Fin.contractNth j.castSucc (· * ·) (hdF h1 g)))
        (N.ρ (fprod (hdF h1 g)) (ψ (tlF h1 g))) := by
    intro j
    unfold cupC
    rw [hdF_contract_lt, tlF_contract_lt, fprod_contractNth]
    simp
  have e3 : ∀ k : Fin (s+1), (-1 : ℤ) ^ (((Fin.natAdd r k : Fin (r+s+1)) : ℕ) + 1) •
      cupC rfl φ ψ (Fin.contractNth (Fin.natAdd r k) (· * ·) g) =
      (-1 : ℤ) ^ r • ((-1 : ℤ) ^ ((k : ℕ) + 1) • rtmul (φ (hdF (r := r) (s := s+1) rfl g))
        (N.ρ (fprod (hdF (r := r) (s := s+1) rfl g)) (ψ (Fin.contractNth k (· * ·)
          (tlF (r := r) (s := s+1) rfl g))))) := by
    intro k
    unfold cupC
    rw [hdF_contract_ge, tlF_contract_ge, smul_smul, ← pow_add]
    simp only [Fin.val_natAdd]
    congr 2
  have hsum := Fin.sum_univ_add (a := r) (b := s + 1)
    (fun j : Fin (r + s + 1) => (-1 : ℤ) ^ ((j : ℕ) + 1) •
      cupC rfl φ ψ (Fin.contractNth j (· * ·) g))
  have hX : rtmul (A := M) (B := N) (φ (hdF (r := r) (s := s+1) rfl g))
        (N.ρ (fprod (hdF h1 g)) (ψ (tlF h1 g))) =
      rtmul (A := M) (B := N) (φ (hdF (r := r) (s := s+1) rfl g))
        (N.ρ (fprod (hdF (r := r) (s := s+1) rfl g) * (tlF (r := r) (s := s+1) rfl g) 0)
          (ψ (Fin.tail (tlF (r := r) (s := s+1) rfl g)))) := by
    rw [fprod_snoc (hdF h1 g), ← hdF_h2_eq_init, last_eq_zero, tail_tlF_h2]
  have hcancel : ∀ X : (M ⊗ N : Rep ℤ G), (-1 : ℤ) ^ (r + 1) • X + (-1 : ℤ) ^ r • X = 0 := by
    intro X
    rw [pow_succ, mul_neg_one, neg_zsmul, neg_add_cancel]
  rw [e1]
  erw [hsum]
  simp only [e2, e3]
  rw [cupC_apply h1 (inhomogeneousCochains.d M r φ) ψ g,
    cupC_apply (rfl : r + (s + 1) = r + s + 1) φ (inhomogeneousCochains.d N s ψ) g]
  rw [d_tmul_left, d_tmul_right, ← hdF_h2_eq_init, hdF_zero]
  rw [hX]
  rw [← zsmul_sum']
  rw [zsmul_add']
  rw [add_assoc (_ + _) ((-1 : ℤ) ^ (r + 1) • _) _, ← add_assoc ((-1 : ℤ) ^ (r + 1) • _) _ _,
    hcancel, zero_add, ← add_assoc]

/-- Leibniz rule with arbitrary degree proofs. -/
theorem cupC_leibniz' {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n) (h1 : r + 1 + s = n + 1)
    (h2 : r + (s + 1) = n + 1) (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) :
    inhomogeneousCochains.d (M ⊗ N) n (cupC h φ ψ) =
      cupC h1 (inhomogeneousCochains.d M r φ) ψ +
      (-1 : ℤ) ^ r • cupC h2 φ (inhomogeneousCochains.d N s ψ) := by
  subst h
  exact cupC_leibniz r s φ ψ

/-! ### Bi-additivity -/

lemma cupC_add_left {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n) (φ₁ φ₂ : (Fin r → G) → M)
    (ψ : (Fin s → G) → N) : cupC h (φ₁ + φ₂) ψ = cupC h φ₁ ψ + cupC h φ₂ ψ := by
  funext g
  simp only [cupC_apply, Pi.add_apply, rtmul, TensorProduct.add_tmul]

lemma cupC_add_right {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n) (φ : (Fin r → G) → M)
    (ψ₁ ψ₂ : (Fin s → G) → N) : cupC h φ (ψ₁ + ψ₂) = cupC h φ ψ₁ + cupC h φ ψ₂ := by
  funext g
  simp only [cupC_apply, Pi.add_apply, rtmul, map_add, TensorProduct.tmul_add]

lemma cupC_zero_left {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n) (ψ : (Fin s → G) → N) :
    cupC h (0 : (Fin r → G) → M) ψ = 0 := by
  funext g
  simp only [cupC_apply, Pi.zero_apply, rtmul, TensorProduct.zero_tmul]

lemma cupC_zero_right {M N : Rep ℤ G} {r s n : ℕ} (h : r + s = n) (φ : (Fin r → G) → M) :
    cupC h φ (0 : (Fin s → G) → N) = 0 := by
  funext g
  simp only [cupC_apply, Pi.zero_apply, rtmul, map_zero, TensorProduct.tmul_zero]

/-! ### Cocycles and coboundaries -/

lemma iCocycles_d (A : Rep ℤ G) (n : ℕ) (z : cocycles A n) :
    inhomogeneousCochains.d A n (iCocycles A n z) = 0 := by
  have := (inhomogeneousCochains A).iCycles_d n (n + 1)
  have h2 := congr($(this) z)
  simpa [inhomogeneousCochains.d_def] using h2

lemma iCocycles_injective (A : Rep ℤ G) (n : ℕ) : Function.Injective (iCocycles A n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- A cocycle that maps to zero in cohomology is a coboundary (for `n = 0`, it is zero). -/
lemma exists_of_π_eq_zero (A : Rep ℤ G) (n i : ℕ) (hi : (ComplexShape.up ℕ).prev n = i)
    (z : cocycles A n) (hz : π A n z = 0) :
    ∃ y : (inhomogeneousCochains A).X i, iCocycles A n z = (inhomogeneousCochains A).d i n y := by
  have hex := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk ((inhomogeneousCochains A).toCycles i n) ((inhomogeneousCochains A).homologyπ n)
      ((inhomogeneousCochains A).toCycles_comp_homologyπ i n))
    ((inhomogeneousCochains A).homologyIsCokernel i n hi)
  rw [ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨y, hy⟩ := hex z hz
  refine ⟨y, ?_⟩
  have := congr($((inhomogeneousCochains A).toCycles_i i n) y)
  rw [← hy]
  exact this

lemma π_eq_zero_of_boundary (A : Rep ℤ G) (n : ℕ) (y : (Fin n → G) → A) (z : cocycles A (n + 1))
    (hz : iCocycles A (n + 1) z = inhomogeneousCochains.d A n y) : π A (n + 1) z = 0 := by
  have h1 : z = (inhomogeneousCochains A).toCycles n (n + 1) y := by
    apply iCocycles_injective
    have := congr($((inhomogeneousCochains A).toCycles_i n (n + 1)) y)
    rw [hz, ← inhomogeneousCochains.d_def]
    exact this.symm
  rw [h1]
  exact congr($((inhomogeneousCochains A).toCycles_comp_homologyπ n (n + 1)) y)

lemma cupC_boundary_left {M N : Rep ℤ G} {r s n : ℕ} (h : r + 1 + s = n + 1) (h' : r + s = n)
    (y : (Fin r → G) → M) (ψ : (Fin s → G) → N) (hψ : inhomogeneousCochains.d N s ψ = 0) :
    cupC h (inhomogeneousCochains.d M r y) ψ = inhomogeneousCochains.d (M ⊗ N) n (cupC h' y ψ) := by
  rw [cupC_leibniz' h' h (by omega) y ψ, hψ, cupC_zero_right, zsmul_zero, add_zero]

lemma cupC_boundary_right {M N : Rep ℤ G} {r s n : ℕ} (h : r + (s + 1) = n + 1) (h' : r + s = n)
    (φ : (Fin r → G) → M) (hφ : inhomogeneousCochains.d M r φ = 0) (y : (Fin s → G) → N) :
    cupC h φ (inhomogeneousCochains.d N s y) =
      inhomogeneousCochains.d (M ⊗ N) n ((-1 : ℤ) ^ r • cupC h' φ y) := by
  rw [map_zsmul, cupC_leibniz' h' (by omega) h φ y, hφ, cupC_zero_left, zero_add, smul_smul,
    ← pow_add, ← two_mul, pow_mul]
  simp

/-! ### Descent to cohomology -/

/-- Descent of a bi-additive map along two surjections. -/
lemma descend2 {X₁ X₂ H₁ H₂ Y : Type*} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup H₁]
    [AddCommGroup H₂] [AddCommGroup Y] (p₁ : X₁ →+ H₁) (p₂ : X₂ →+ H₂)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Surjective p₂) (β : X₁ →+ X₂ →+ Y)
    (h₁ : ∀ x₁, p₁ x₁ = 0 → ∀ x₂, β x₁ x₂ = 0) (h₂ : ∀ x₂, p₂ x₂ = 0 → ∀ x₁, β x₁ x₂ = 0) :
    ∃ β' : H₁ →+ H₂ →+ Y, ∀ x₁ x₂, β' (p₁ x₁) (p₂ x₂) = β x₁ x₂ := by
  let β₁ : H₁ →+ (X₂ →+ Y) := AddMonoidHom.liftOfSurjective p₁ hp₁
    ⟨β, fun x₁ hx => AddMonoidHom.ext fun x₂ => h₁ x₁ hx x₂⟩
  have hβ₁ : ∀ x₁, β₁ (p₁ x₁) = β x₁ := fun x₁ =>
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x₁
  let β₂ : H₂ →+ (H₁ →+ Y) := AddMonoidHom.liftOfSurjective p₂ hp₂
    ⟨β₁.flip, fun x₂ hx => AddMonoidHom.ext fun h => by
      obtain ⟨x₁, rfl⟩ := hp₁ h
      exact (congrArg (fun f => f x₂) (hβ₁ x₁)).trans (h₂ x₂ hx x₁)⟩
  refine ⟨β₂.flip, fun x₁ x₂ => ?_⟩
  have h3 : β₂ (p₂ x₂) = β₁.flip x₂ :=
    AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x₂
  change β₂ (p₂ x₂) (p₁ x₁) = _
  rw [h3]
  exact congrArg (fun f => f x₂) (hβ₁ x₁)

variable {M N : Rep ℤ G} {r s n : ℕ}

/-- The cup product of two cocycles, as a cocycle. -/
noncomputable def cupZ (h : r + s = n) (z₁ : cocycles M r) (z₂ : cocycles N s) :
    cocycles (M ⊗ N) n :=
  cocyclesMk (cupC h (iCocycles M r z₁) (iCocycles N s z₂))
    (by
      rw [cupC_leibniz' h (by omega) (by omega), iCocycles_d, iCocycles_d, cupC_zero_left,
        cupC_zero_right, zsmul_zero, add_zero])

lemma iCocycles_cupZ (h : r + s = n) (z₁ : cocycles M r) (z₂ : cocycles N s) :
    iCocycles (M ⊗ N) n (cupZ h z₁ z₂) = cupC h (iCocycles M r z₁) (iCocycles N s z₂) :=
  by unfold cupZ; exact iCocycles_mk _ _

lemma cupZ_add_left (h : r + s = n) (z₁ z₁' : cocycles M r) (z₂ : cocycles N s) :
    cupZ h (z₁ + z₁') z₂ = cupZ h z₁ z₂ + cupZ h z₁' z₂ := by
  apply iCocycles_injective
  rw [map_add, iCocycles_cupZ, iCocycles_cupZ, iCocycles_cupZ, map_add, cupC_add_left]

lemma cupZ_add_right (h : r + s = n) (z₁ : cocycles M r) (z₂ z₂' : cocycles N s) :
    cupZ h z₁ (z₂ + z₂') = cupZ h z₁ z₂ + cupZ h z₁ z₂' := by
  apply iCocycles_injective
  rw [map_add, iCocycles_cupZ, iCocycles_cupZ, iCocycles_cupZ, map_add, cupC_add_right]

/-- The bi-additive cup product on cocycles with values in cohomology. -/
noncomputable def cupβ (h : r + s = n) :
    cocycles M r →+ cocycles N s →+ groupCohomology (M ⊗ N) n :=
  AddMonoidHom.mk' (fun z₁ => AddMonoidHom.mk' (fun z₂ => π (M ⊗ N) n (cupZ h z₁ z₂))
      (fun a b => by rw [cupZ_add_right, map_add]))
    (fun a b => AddMonoidHom.ext fun z₂ => by
      change π (M ⊗ N) n (cupZ h (a + b) z₂) = π (M ⊗ N) n (cupZ h a z₂) + π (M ⊗ N) n (cupZ h b z₂)
      rw [cupZ_add_left, map_add])

lemma cupβ_apply (h : r + s = n) (z₁ : cocycles M r) (z₂ : cocycles N s) :
    cupβ h z₁ z₂ = π (M ⊗ N) n (cupZ h z₁ z₂) := rfl

lemma eq_zero_of_π_eq_zero_zero (A : Rep ℤ G) (z : cocycles A 0) (hz : π A 0 z = 0) : z = 0 := by
  obtain ⟨y, hy⟩ := exists_of_π_eq_zero A 0 0 CochainComplex.prev_nat_zero z hz
  apply iCocycles_injective
  rw [hy, map_zero]
  exact (inhomogeneousCochains A).shape 0 0 (by simp) ▸ rfl

lemma cupβ_left_boundary (h : r + s = n) (z₁ : cocycles M r) (hz : π M r z₁ = 0)
    (z₂ : cocycles N s) : cupβ h z₁ z₂ = 0 := by
  cases r with
  | zero =>
    rw [eq_zero_of_π_eq_zero_zero M z₁ hz, map_zero]
    rfl
  | succ r' =>
    obtain ⟨y, hy⟩ := exists_of_π_eq_zero M (r' + 1) r' (CochainComplex.prev_nat_succ r') z₁ hz
    obtain rfl : n = r' + s + 1 := by omega
    rw [cupβ_apply]
    refine π_eq_zero_of_boundary _ (r' + s) (cupC rfl y (iCocycles N s z₂)) _ ?_
    rw [iCocycles_cupZ, hy]
    rw [inhomogeneousCochains.d_def]
    exact cupC_boundary_left h rfl y _ (iCocycles_d _ _ _)

lemma cupβ_right_boundary (h : r + s = n) (z₂ : cocycles N s) (hz : π N s z₂ = 0)
    (z₁ : cocycles M r) : cupβ h z₁ z₂ = 0 := by
  cases s with
  | zero =>
    rw [eq_zero_of_π_eq_zero_zero N z₂ hz, map_zero]
  | succ s' =>
    obtain ⟨y, hy⟩ := exists_of_π_eq_zero N (s' + 1) s' (CochainComplex.prev_nat_succ s') z₂ hz
    obtain rfl : n = r + s' + 1 := by omega
    rw [cupβ_apply]
    refine π_eq_zero_of_boundary _ (r + s') ((-1 : ℤ) ^ r • cupC rfl (iCocycles M r z₁) y) _ ?_
    rw [iCocycles_cupZ, hy]
    rw [inhomogeneousCochains.d_def]
    exact cupC_boundary_right h rfl _ (iCocycles_d _ _ _) y

set_option backward.isDefEq.respectTransparency false in
lemma exists_cupH (h : r + s = n) :
    ∃ β' : groupCohomology M r →+ groupCohomology N s →+ groupCohomology (M ⊗ N) n,
      ∀ z₁ z₂, β' (π M r z₁) (π N s z₂) = π (M ⊗ N) n (cupZ h z₁ z₂) :=
  descend2 (π M r).hom.toAddMonoidHom (π N s).hom.toAddMonoidHom
    ((ModuleCat.epi_iff_surjective (π M r)).1 inferInstance)
    ((ModuleCat.epi_iff_surjective (π N s)).1 inferInstance) (cupβ h)
    (fun z₁ hz z₂ => cupβ_left_boundary h z₁ hz z₂)
    (fun z₂ hz z₁ => cupβ_right_boundary h z₂ hz z₁)

/-- **Cup product in cohomology** (Milne, CFT v4.03, Ch. II, Prop. 1.38, p. 73): the bi-additive map
$H^r(G, M) \times H^s(G, N) \to H^{r+s}(G, M \otimes N)$ induced by the cochain formula `cupC`. -/
noncomputable def cupH (h : r + s = n) :
    groupCohomology M r →+ groupCohomology N s →+ groupCohomology (M ⊗ N) n :=
  Classical.choose (exists_cupH h)

lemma cupH_π (h : r + s = n) (z₁ : cocycles M r) (z₂ : cocycles N s) :
    cupH h (π M r z₁) (π N s z₂) = π (M ⊗ N) n (cupZ h z₁ z₂) :=
  Classical.choose_spec (exists_cupH h) z₁ z₂

/-! ### (a) Naturality -/

lemma iCocycles_cocyclesMap {A B : Rep ℤ G} (f : A ⟶ B) (m : ℕ) (z : cocycles A m)
    (x : Fin m → G) :
    iCocycles B m (cocyclesMap (MonoidHom.id G) f m z) x = f.hom (iCocycles A m z x) := by
  have := congr($(HomologicalComplex.cyclesMap_i (cochainsMap (MonoidHom.id G) f) m) z)
  exact congrFun this x

lemma cupC_natural {M M' N N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N') {r s n : ℕ} (h : r + s = n)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) (x : Fin n → G) :
    (f ⊗ₘ g).hom (cupC h φ ψ x) = cupC h (fun a => f.hom (φ a)) (fun b => g.hom (ψ b)) x := by
  rw [cupC_apply, cupC_apply]
  refine (Representation.IntertwiningMap.tensor_apply f.hom g.hom _ _).trans ?_
  rw [← hom_comm_apply g]

lemma functor_map_π {A B : Rep ℤ G} (f : A ⟶ B) (m : ℕ) (z : cocycles A m) :
    (groupCohomology.functor ℤ G m).map f (π A m z) =
      π B m (cocyclesMap (MonoidHom.id G) f m z) :=
  π_map_apply (MonoidHom.id G) f m z

lemma cocyclesMap_cupZ {M M' N N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N') {r s n : ℕ}
    (h : r + s = n) (z₁ : cocycles M r) (z₂ : cocycles N s) :
    cocyclesMap (MonoidHom.id G) (f ⊗ₘ g) n (cupZ h z₁ z₂) =
      cupZ h (cocyclesMap (MonoidHom.id G) f r z₁) (cocyclesMap (MonoidHom.id G) g s z₂) := by
  apply iCocycles_injective
  funext x
  rw [iCocycles_cocyclesMap]
  erw [iCocycles_cupZ]
  rw [iCocycles_cupZ, cupC_natural]
  congr 1 <;> funext a <;> exact (iCocycles_cocyclesMap _ _ _ a).symm

/-- **(a) Naturality** of the cup product in `(M, N)`. -/
theorem cupH_natural {M M' N N' : Rep ℤ G} (f : M ⟶ M') (g : N ⟶ N') (r s n : ℕ) (h : r + s = n)
    (x : groupCohomology M r) (y : groupCohomology N s) :
    cupH h ((functor ℤ G r).map f x) ((functor ℤ G s).map g y) =
      (functor ℤ G n).map (f ⊗ₘ g) (cupH h x y) := by
  refine groupCohomology_induction_on x fun z₁ => groupCohomology_induction_on y fun z₂ => ?_
  rw [functor_map_π, functor_map_π, cupH_π, cupH_π, functor_map_π, cocyclesMap_cupZ]

/-! ### (b) Degree zero -/

lemma H0Iso_inv_eq_π (A : Rep ℤ G) (m : A.ρ.invariants) :
    (H0Iso A).inv m = π A 0 ((cocyclesIso₀ A).inv m) := by
  have h1 : (H0Iso A).hom (π A 0 ((cocyclesIso₀ A).inv m)) = m := by
    rw [π_comp_H0Iso_hom_apply]
    simp
  calc (H0Iso A).inv m = (H0Iso A).inv ((H0Iso A).hom (π A 0 ((cocyclesIso₀ A).inv m))) := by
        rw [h1]
    _ = π A 0 ((cocyclesIso₀ A).inv m) := (H0Iso A).hom_inv_id_apply _

lemma iCocycles_cocyclesIso₀_inv (A : Rep ℤ G) (m : A.ρ.invariants) (x : Fin 0 → G) :
    iCocycles A 0 ((cocyclesIso₀ A).inv m) x = (m : A) := by
  rw [cocyclesIso₀_inv_comp_iCocycles_apply]
  rfl

lemma fprod_fin_zero (a : Fin 0 → G) : fprod a = 1 := by
  simp [fprod]

/-- **(b) Degree zero**: for `r = s = 0` the pairing is `(m, n) ↦ m ⊗ n`. -/
theorem cupH_zero (M N : Rep ℤ G) (m : M.ρ.invariants) (n : N.ρ.invariants) :
    ((H0Iso (M ⊗ N)).hom
      (cupH (rfl : 0 + 0 = 0) ((H0Iso M).inv m) ((H0Iso N).inv n)) : (M ⊗ N : Rep ℤ G)) =
      TensorProduct.tmul ℤ (m : M) (n : N) := by
  rw [H0Iso_inv_eq_π, H0Iso_inv_eq_π, cupH_π, π_comp_H0Iso_hom_apply]
  have := cocyclesIso₀_hom_comp_f_apply (M ⊗ N) (cupZ rfl ((cocyclesIso₀ M).inv m)
    ((cocyclesIso₀ N).inv n))
  change ((shortComplexH0 (M ⊗ N)).f
    ((cocyclesIso₀ (M ⊗ N)).hom (cupZ rfl ((cocyclesIso₀ M).inv m) ((cocyclesIso₀ N).inv n))) :
      (M ⊗ N : Rep ℤ G)) = _
  refine this.trans ?_
  change iCocycles (M ⊗ N) 0 (cupZ rfl ((cocyclesIso₀ M).inv m) ((cocyclesIso₀ N).inv n)) default = _
  rw [iCocycles_cupZ, cupC_apply, iCocycles_cocyclesIso₀_inv, iCocycles_cocyclesIso₀_inv,
    fprod_fin_zero, map_one]
  rfl

/-! ### (c), (d) Compatibility with connecting homomorphisms -/

/-- The connecting map on the class of a cocycle `z`, computed from a lift `Y` of `z` and a lift
`X` of `dY` (Mathlib's `groupCohomology.δ_apply`). -/
lemma delta_lift {T : ShortComplex (Rep ℤ G)} (hT : T.ShortExact) (i : ℕ) (z : cocycles T.X₃ i)
    (Y : (Fin i → G) → T.X₂) (hY : ∀ a, T.g.hom (Y a) = iCocycles T.X₃ i z a)
    (X : (Fin (i + 1) → G) → T.X₁)
    (hX : ∀ a, T.f.hom (X a) = inhomogeneousCochains.d T.X₂ i Y a)
    (z' : cocycles T.X₁ (i + 1)) (hz' : iCocycles T.X₁ (i + 1) z' = X) :
    δ hT i (i + 1) rfl (π T.X₃ i z) = π T.X₁ (i + 1) z' := by
  have hz : (inhomogeneousCochains T.X₃).d i (i + 1) (iCocycles T.X₃ i z) = 0 := by
    rw [inhomogeneousCochains.d_def]
    exact iCocycles_d _ _ z
  have e : cocyclesMk (iCocycles T.X₃ i z) (by simpa [CochainComplex.of.d] using! hz) = z := by
    apply iCocycles_injective
    exact iCocycles_mk _ _
  have h1 := δ_apply hT (rfl : i + 1 = i + 1) (iCocycles T.X₃ i z) hz Y (funext hY) X
    (by rw [inhomogeneousCochains.d_def]; exact funext hX)
  rw [e] at h1
  rw [h1]
  congr 1
  apply iCocycles_injective
  rw [hz']
  exact iCocycles_mk _ _

lemma d_comp_hom {A B : Rep ℤ G} (f : A ⟶ B) (m : ℕ) (φ : (Fin m → G) → A) (a : Fin (m + 1) → G) :
    f.hom (inhomogeneousCochains.d A m φ a) =
      inhomogeneousCochains.d B m (fun x => f.hom (φ x)) a := by
  rw [d_apply', d_apply', map_add, map_sum, hom_comm_apply]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact map_zsmul f.hom _ _

lemma cupC_whiskerRight {M M' : Rep ℤ G} (f : M ⟶ M') (N : Rep ℤ G) {r s n : ℕ} (h : r + s = n)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) (x : Fin n → G) :
    (f ▷ N).hom (cupC h φ ψ x) = cupC h (fun a => f.hom (φ a)) ψ x := by
  rw [cupC_apply, cupC_apply]
  rfl

lemma cupC_whiskerLeft (M : Rep ℤ G) {N N' : Rep ℤ G} (g : N ⟶ N') {r s n : ℕ} (h : r + s = n)
    (φ : (Fin r → G) → M) (ψ : (Fin s → G) → N) (x : Fin n → G) :
    (M ◁ g).hom (cupC h φ ψ x) = cupC h φ (fun b => g.hom (ψ b)) x := by
  rw [cupC_apply, cupC_apply]
  refine (Representation.IntertwiningMap.tensor_apply _ _ _ _).trans ?_
  rw [← hom_comm_apply g]
  rfl

/-- **(c)** for classes of cocycles. -/
theorem delta_cup_left_aux {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact) {N : Rep ℤ G}
    (hSN : (S.map (tensorRight N)).ShortExact) {r s n : ℕ} (h : r + s = n)
    (z : cocycles S.X₃ r) (w : cocycles N s) :
    cupH (by omega : r + 1 + s = n + 1) (δ hS r (r + 1) rfl (π S.X₃ r z)) (π N s w) =
      δ hSN n (n + 1) rfl (π (S.X₃ ⊗ N) n (cupZ h z w)) := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := functionExact_of_shortExact hS
  choose Y hY using fun x : Fin r → G => hg (iCocycles S.X₃ r z x)
  have hYf : (fun x => S.g.hom (Y x)) = iCocycles S.X₃ r z := funext hY
  have hdY : ∀ a, S.g.hom (inhomogeneousCochains.d S.X₂ r Y a) = 0 := by
    intro a
    rw [d_comp_hom, hYf, iCocycles_d]
    rfl
  choose X hX using fun a => (hex _).1 (hdY a)
  have hXf : (fun a => S.f.hom (X a)) = inhomogeneousCochains.d S.X₂ r Y := funext hX
  have hXd : S.f.hom ∘ X = (inhomogeneousCochains S.X₂).d r (r + 1) Y := by
    rw [inhomogeneousCochains.d_def]
    exact funext hX
  let zx := cocyclesMkOfCompEqD hS hXd
  have hzx : iCocycles S.X₁ (r + 1) zx = X := iCocycles_mk _ _
  have e1 : δ hS r (r + 1) rfl (π S.X₃ r z) = π S.X₁ (r + 1) zx :=
    delta_lift hS r z Y hY X hX zx hzx
  rw [e1, cupH_π]
  refine (delta_lift hSN n (cupZ h z w) (cupC h Y (iCocycles N s w)) ?_
    (cupC (by omega : r + 1 + s = n + 1) X (iCocycles N s w)) ?_
    (cupZ (by omega : r + 1 + s = n + 1) zx w) ?_).symm
  · intro a
    change (S.g ▷ N).hom _ = _
    rw [cupC_whiskerRight, hYf]
    erw [iCocycles_cupZ]
  · intro a
    change (S.f ▷ N).hom _ = _
    rw [cupC_whiskerRight, hXf, cupC_boundary_left _ h Y _ (iCocycles_d N s w)]
    rfl
  · erw [iCocycles_cupZ]
    rw [hzx]

/-- **(d)** for classes of cocycles. -/
theorem delta_cup_right_aux {M : Rep ℤ G} {S : ShortComplex (Rep ℤ G)} (hS : S.ShortExact)
    (hMS : (S.map (tensorLeft M)).ShortExact) {r s n : ℕ} (h : r + s = n)
    (w : cocycles M r) (z : cocycles S.X₃ s) :
    cupH (by omega : r + (s + 1) = n + 1) (π M r w) (δ hS s (s + 1) rfl (π S.X₃ s z)) =
      (-1 : ℤ) ^ r • δ hMS n (n + 1) rfl (π (M ⊗ S.X₃) n (cupZ h w z)) := by
  have hg : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  have hex := functionExact_of_shortExact hS
  choose Y hY using fun x : Fin s → G => hg (iCocycles S.X₃ s z x)
  have hYf : (fun x => S.g.hom (Y x)) = iCocycles S.X₃ s z := funext hY
  have hdY : ∀ a, S.g.hom (inhomogeneousCochains.d S.X₂ s Y a) = 0 := by
    intro a
    rw [d_comp_hom, hYf, iCocycles_d]
    rfl
  choose X hX using fun a => (hex _).1 (hdY a)
  have hXf : (fun a => S.f.hom (X a)) = inhomogeneousCochains.d S.X₂ s Y := funext hX
  have hXd : S.f.hom ∘ X = (inhomogeneousCochains S.X₂).d s (s + 1) Y := by
    rw [inhomogeneousCochains.d_def]
    exact funext hX
  let zx := cocyclesMkOfCompEqD hS hXd
  have hzx : iCocycles S.X₁ (s + 1) zx = X := iCocycles_mk _ _
  have e1 : δ hS s (s + 1) rfl (π S.X₃ s z) = π S.X₁ (s + 1) zx :=
    delta_lift hS s z Y hY X hX zx hzx
  rw [e1, cupH_π]
  have e2 : (-1 : ℤ) ^ r • δ hMS n (n + 1) rfl (π (M ⊗ S.X₃) n (cupZ h w z)) =
      δ hMS n (n + 1) rfl (π (M ⊗ S.X₃) n ((-1 : ℤ) ^ r • cupZ h w z)) := by
    rw [map_zsmul, map_zsmul]
  rw [e2]
  refine (delta_lift hMS n ((-1 : ℤ) ^ r • cupZ h w z) ((-1 : ℤ) ^ r • cupC h (iCocycles M r w) Y) ?_
    (cupC (by omega : r + (s + 1) = n + 1) (iCocycles M r w) X) ?_
    (cupZ (by omega : r + (s + 1) = n + 1) w zx) ?_).symm
  · intro a
    change (M ◁ S.g).hom _ = _
    rw [Pi.smul_apply, map_zsmul, cupC_whiskerLeft, hYf, map_zsmul, Pi.smul_apply]
    erw [iCocycles_cupZ]
  · intro a
    change (M ◁ S.f).hom _ = _
    rw [cupC_whiskerLeft, hXf, cupC_boundary_right _ h _ (iCocycles_d M r w)]
    rfl
  · erw [iCocycles_cupZ]
    rw [hzx]

/-- **The cup-product family** given by Milne's cochain formula (CFT v4.03, Ch. II, Prop. 1.38,
p. 73): the pairings `cupH` satisfy (a)–(d). -/
noncomputable def cupProductFamilyOfCochains : CupProductFamily G where
  cup _ _ _ _ _ h := cupH h
  natural f g r s n h x y := cupH_natural f g r s n h x y
  zero M N m n := Subtype.ext (cupH_zero M N m n)
  delta_left S hS N hSN r s n h x y := by
    refine groupCohomology_induction_on x fun z => groupCohomology_induction_on y fun w => ?_
    rw [cupH_π]
    exact delta_cup_left_aux hS hSN h z w
  delta_right M S hS hMS r s n h x y := by
    refine groupCohomology_induction_on x fun w => groupCohomology_induction_on y fun z => ?_
    rw [cupH_π]
    exact delta_cup_right_aux hS hMS h w z

/-- **Proposition 1.38, existence** (Milne, CFT v4.03, Ch. II, p. 73): a family of cup-product pairings
with the properties (a)–(d) exists, namely the one given by the cochain formula
$(\varphi \cup \psi)(g_1,\dots,g_{r+s}) = \varphi(g_1,\dots,g_r) \otimes g_1\cdots g_r\,\psi(g_{r+1},\dots,g_{r+s})$
(`cupProductFamilyOfCochains`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.38, existence, p. 73"]
theorem cupProductFamily_nonempty (G : Type) [Group G] : Nonempty (CupProductFamily G) :=
  ⟨cupProductFamilyOfCochains⟩

/-- **Proposition 1.38** (Milne, CFT v4.03, Ch. II, p. 73): for every group $G$ there is one and only one
family of cup-product pairings with the properties (a)–(d). Existence is `cupProductFamily_nonempty`
(cochain formula, Leibniz rule `cupC_leibniz`), uniqueness is `cupProductFamily_cup_unique` (dimension
shifting). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.38, p. 73"]
theorem prop1_38 : Prop1_38 :=
  ⟨fun G _ => ⟨cupProductFamily_nonempty G, fun c₁ c₂ => cupProductFamily_cup_unique c₁ c₂⟩⟩

end NumberFieldKB.MilneCFT
