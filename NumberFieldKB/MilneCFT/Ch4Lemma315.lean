import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4CrossedProduct

/-!
# Milne, Class Field Theory, Chapter IV, §3: Lemma 3.15

J. S. Milne, *Class Field Theory* (version 4.03, 2020; bibliography key `milne2020cft`):
$A(\varphi\varphi') \sim A(\varphi) \otimes_K A(\varphi')$.  Milne only sketches the proof (he refers to
Blanchard 1972 and Farb–Dennis 1993).  Locators give the printed page (= pdf page − 9).

Proof used here.  Put $A = A(\varphi)$, $B = A(\varphi')$, $C = A(\varphi\varphi')$ and
$V = A \otimes_L B$ ($A$, $B$ are $L$-modules by left multiplication by $L = L e_1$).  The algebra
$C$ acts on the left on $V$ by $(l e''_\sigma)(a \otimes b) = l e_\sigma a \otimes e'_\sigma b$ and
$A^{\mathrm{opp}}$, $B^{\mathrm{opp}}$ act on the right; the actions commute.  This gives a
$K$-algebra map $C \otimes_K (A^{\mathrm{opp}} \otimes_K B^{\mathrm{opp}}) \to \mathrm{End}_K(V)$,
injective since the source is simple, and bijective by dimension count ($n^6 = (n^3)^2$).  Hence
$[C] [A]^{-1} [B]^{-1} = 1$ in $\mathrm{Br}(K)$.
-/

open scoped TensorProduct

namespace NumberFieldKB.MilneCFT.Ch4

universe u

variable {K : Type u} [Field K] {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

namespace CrossedProduct

section Aux

variable (φ φ' : NormalizedCocycle K L)

instance : IsScalarTower K L (CrossedProduct φ) :=
  inferInstanceAs (IsScalarTower K L ((L ≃ₐ[K] L) → L))

instance : SMulCommClass L K (CrossedProduct φ) :=
  inferInstanceAs (SMulCommClass L K ((L ≃ₐ[K] L) → L))

instance : SMulCommClass K L (CrossedProduct φ) :=
  inferInstanceAs (SMulCommClass K L ((L ≃ₐ[K] L) → L))

instance : Module.Free L (CrossedProduct φ) :=
  inferInstanceAs (Module.Free L ((L ≃ₐ[K] L) → L))

instance : Module.Finite L (CrossedProduct φ) :=
  inferInstanceAs (Module.Finite L ((L ≃ₐ[K] L) → L))

theorem smul_eq_incl_mul (l : L) (x : CrossedProduct φ) : l • x = single φ 1 l * x := by
  funext ρ
  rw [single_one_mul_apply]
  rfl

theorem finrank_L : Module.finrank L (CrossedProduct φ) = Module.finrank K L := by
  have h : Module.finrank L (CrossedProduct φ) = Module.finrank L ((L ≃ₐ[K] L) → L) := rfl
  rw [h, Module.finrank_pi, ← Nat.card_eq_fintype_card]
  exact IsGalois.card_aut_eq_finrank K L

/-- The module $V = A \otimes_L B$ of the proof, with $A, B$ viewed as $L$-modules by left
multiplication by $L = L e_1$. -/
abbrev Vmod := CrossedProduct φ ⊗[L] CrossedProduct φ'

instance : Module.Finite K (Vmod φ φ') := Module.Finite.trans L (Vmod φ φ')

theorem finrank_V :Module.finrank K (Vmod φ φ') = Module.finrank K L ^ 3 := by
  rw [← Module.finrank_mul_finrank K L (Vmod φ φ'),
    Module.finrank_tensorProduct, finrank_L, finrank_L]
  ring

theorem ext_V {f g : Vmod φ φ' →ₗ[K] Vmod φ φ'}
    (h : ∀ a b, f (a ⊗ₜ[L] b) = g (a ⊗ₜ[L] b)) : f = g := by
  refine LinearMap.ext fun v => ?_
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => exact h a b
  | add x y hx hy => simp [hx, hy]

open Classical in
theorem single_add (σ : L ≃ₐ[K] L) (a b : L) :
    single φ σ (a + b) = single φ σ a + single φ σ b := by
  funext ρ
  show single φ σ (a + b) ρ = single φ σ a ρ + single φ σ b ρ
  simp only [single_apply]
  split_ifs <;> simp

open Classical in
theorem single_zero (σ : L ≃ₐ[K] L) : single φ σ 0 = 0 := by
  unfold single
  exact Pi.single_zero σ

theorem single_smul_K (σ : L ≃ₐ[K] L) (k : K) (a : L) :
    single φ σ (k • a) = k • single φ σ a := by
  funext ρ
  show single φ σ (k • a) ρ = k • single φ σ a ρ
  simp only [single_apply]
  split_ifs <;> simp

theorem single_smul_L (σ : L ≃ₐ[K] L) (c a : L) :
    c • single φ σ a = single φ σ (c * a) := by
  funext ρ
  show c * single φ σ a ρ = single φ σ (c * a) ρ
  simp only [single_apply]
  split_ifs <;> simp

theorem smul_mul_L (c : L) (x y : CrossedProduct φ) : (c • x) * y = c • (x * y) := by
  rw [smul_eq_incl_mul, smul_eq_incl_mul, mul_assoc]

theorem single_mul_smul (σ : L ≃ₐ[K] L) (l l' : L) (a : CrossedProduct φ) :
    single φ σ l * (l' • a) = (σ l') • (single φ σ l * a) := by
  rw [smul_eq_incl_mul, smul_eq_incl_mul, ← mul_assoc, ← mul_assoc, single_mul_single,
    single_mul_single]
  simp [NormalizedCocycle.one_left, NormalizedCocycle.one_right, mul_comm]

/-! ### The right action of $A^{\mathrm{opp}}$ and $B^{\mathrm{opp}}$ on $V$ -/

/-- Right multiplication by $a'$ is $L$-linear for the left $L$-structure. -/
noncomputable def rmulL (a' : CrossedProduct φ) : CrossedProduct φ →ₗ[L] CrossedProduct φ where
  toFun x := x * a'
  map_add' x y := add_mul x y a'
  map_smul' l x := by
    simp only [smul_eq_incl_mul, RingHom.id_apply, mul_assoc]

noncomputable def rightA (a : CrossedProduct φ) : Vmod φ φ' →ₗ[K] Vmod φ φ' :=
  (TensorProduct.map (rmulL φ a) LinearMap.id).restrictScalars K

noncomputable def rightB (b : CrossedProduct φ') : Vmod φ φ' →ₗ[K] Vmod φ φ' :=
  (TensorProduct.map LinearMap.id (rmulL φ' b)).restrictScalars K

@[simp] theorem rightA_tmul (a x : CrossedProduct φ) (y : CrossedProduct φ') :
    rightA φ φ' a (x ⊗ₜ[L] y) = (x * a) ⊗ₜ[L] y := rfl

@[simp] theorem rightB_tmul (b : CrossedProduct φ') (x : CrossedProduct φ) (y : CrossedProduct φ') :
    rightB φ φ' b (x ⊗ₜ[L] y) = x ⊗ₜ[L] (y * b) := rfl

theorem rightA_one : rightA φ φ' 1 = 1 := ext_V φ φ' fun a b => by simp

theorem rightB_one : rightB φ φ' 1 = 1 := ext_V φ φ' fun a b => by simp

theorem rightA_mul (a a' : CrossedProduct φ) :
    rightA φ φ' (a * a') = rightA φ φ' a' * rightA φ φ' a :=
  ext_V φ φ' fun x y => by simp [mul_assoc]

theorem rightB_mul (b b' : CrossedProduct φ') :
    rightB φ φ' (b * b') = rightB φ φ' b' * rightB φ φ' b :=
  ext_V φ φ' fun x y => by simp [mul_assoc]

theorem rightA_add (a a' : CrossedProduct φ) :
    rightA φ φ' (a + a') = rightA φ φ' a + rightA φ φ' a' :=
  ext_V φ φ' fun x y => by simp [mul_add, TensorProduct.add_tmul]

theorem rightB_add (b b' : CrossedProduct φ') :
    rightB φ φ' (b + b') = rightB φ φ' b + rightB φ φ' b' :=
  ext_V φ φ' fun x y => by simp [mul_add, TensorProduct.tmul_add]

theorem rightA_smul (k : K) (a : CrossedProduct φ) :
    rightA φ φ' (k • a) = k • rightA φ φ' a :=
  ext_V φ φ' fun x y => by
    simp [mul_smul_comm', TensorProduct.smul_tmul']

theorem rightB_smul (k : K) (b : CrossedProduct φ') :
    rightB φ φ' (k • b) = k • rightB φ φ' b :=
  ext_V φ φ' fun x y => by
    simp [mul_smul_comm', TensorProduct.tmul_smul]

theorem rightA_rightB (a : CrossedProduct φ) (b : CrossedProduct φ') :
    rightA φ φ' a * rightB φ φ' b = rightB φ φ' b * rightA φ φ' a :=
  ext_V φ φ' fun x y => by simp

noncomputable def rhoA : (CrossedProduct φ)ᵐᵒᵖ →ₐ[K] Module.End K (Vmod φ φ') where
  toFun a := rightA φ φ' a.unop
  map_one' := rightA_one φ φ'
  map_mul' x y := by
    show rightA φ φ' (x * y).unop = _
    rw [MulOpposite.unop_mul, rightA_mul]
  map_zero' := ext_V φ φ' fun x y => by simp
  map_add' x y := rightA_add φ φ' _ _
  commutes' k := by
    show rightA φ φ' (k • (1 : CrossedProduct φ)) = _
    rw [rightA_smul, rightA_one, Algebra.algebraMap_eq_smul_one]

noncomputable def rhoB : (CrossedProduct φ')ᵐᵒᵖ →ₐ[K] Module.End K (Vmod φ φ') where
  toFun b := rightB φ φ' b.unop
  map_one' := rightB_one φ φ'
  map_mul' x y := by
    show rightB φ φ' (x * y).unop = _
    rw [MulOpposite.unop_mul, rightB_mul]
  map_zero' := ext_V φ φ' fun x y => by simp
  map_add' x y := rightB_add φ φ' _ _
  commutes' k := by
    show rightB φ φ' (k • (1 : CrossedProduct φ')) = _
    rw [rightB_smul, rightB_one, Algebra.algebraMap_eq_smul_one]

noncomputable def rhoR :
    (CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ →ₐ[K] Module.End K (Vmod φ φ') :=
  Algebra.TensorProduct.lift (rhoA φ φ') (rhoB φ φ')
    (fun x y => rightA_rightB φ φ' x.unop y.unop)

/-! ### The left action of $C$ on $V$ -/

noncomputable def psiBil (σ : L ≃ₐ[K] L) (l : L) :
    CrossedProduct φ →+ CrossedProduct φ' →+ Vmod φ φ' :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun b => (single φ σ l * a) ⊗ₜ[L] (single φ' σ 1 * b))
      (fun b b' => by rw [mul_add, TensorProduct.tmul_add]))
    (fun a a' => AddMonoidHom.ext fun b => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, mul_add, TensorProduct.add_tmul])

theorem psiBil_balanced (σ : L ≃ₐ[K] L) (l l' : L) (a : CrossedProduct φ) (b : CrossedProduct φ') :
    psiBil φ φ' σ l (l' • a) b = psiBil φ φ' σ l a (l' • b) := by
  show (single φ σ l * (l' • a)) ⊗ₜ[L] (single φ' σ 1 * b) =
    (single φ σ l * a) ⊗ₜ[L] (single φ' σ 1 * (l' • b))
  rw [single_mul_smul, single_mul_smul, TensorProduct.smul_tmul]

noncomputable def psiAdd (σ : L ≃ₐ[K] L) (l : L) : Vmod φ φ' →+ Vmod φ φ' :=
  TensorProduct.liftAddHom (psiBil φ φ' σ l) (psiBil_balanced φ φ' σ l)

/-- The operator $a \otimes b \mapsto l e_\sigma a \otimes e'_\sigma b$ on $V$. -/
noncomputable def psi (σ : L ≃ₐ[K] L) (l : L) : Vmod φ φ' →ₗ[K] Vmod φ φ' where
  toFun := psiAdd φ φ' σ l
  map_add' := map_add _
  map_smul' k v := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show psiAdd φ φ' σ l (k • (a ⊗ₜ[L] b)) = k • psiAdd φ φ' σ l (a ⊗ₜ[L] b)
      rw [TensorProduct.smul_tmul']
      show (single φ σ l * (k • a)) ⊗ₜ[L] (single φ' σ 1 * b) =
        k • ((single φ σ l * a) ⊗ₜ[L] (single φ' σ 1 * b))
      rw [mul_smul_comm', TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [map_add, smul_add, map_add, smul_add, hx, hy]

@[simp] theorem psi_tmul (σ : L ≃ₐ[K] L) (l : L) (a : CrossedProduct φ) (b : CrossedProduct φ') :
    psi φ φ' σ l (a ⊗ₜ[L] b) = (single φ σ l * a) ⊗ₜ[L] (single φ' σ 1 * b) := rfl

theorem psi_zero_l (σ : L ≃ₐ[K] L) : psi φ φ' σ 0 = 0 :=
  ext_V φ φ' fun a b => by simp [single_zero]

theorem psi_add_l (σ : L ≃ₐ[K] L) (l l' : L) :
    psi φ φ' σ (l + l') = psi φ φ' σ l + psi φ φ' σ l' :=
  ext_V φ φ' fun a b => by simp [single_add, add_mul, TensorProduct.add_tmul]

theorem psi_smul_l (σ : L ≃ₐ[K] L) (k : K) (l : L) :
    psi φ φ' σ (k • l) = k • psi φ φ' σ l :=
  ext_V φ φ' fun a b => by
    simp [single_smul_K, smul_mul_assoc', TensorProduct.smul_tmul']

theorem psi_mul (σ τ : L ≃ₐ[K] L) (l m : L) :
    psi φ φ' σ l * psi φ φ' τ m =
      psi φ φ' (σ * τ) (l * σ m * ((φ (σ, τ) : Lˣ) : L) * ((φ' (σ, τ) : Lˣ) : L)) := by
  refine ext_V φ φ' fun a b => ?_
  show psi φ φ' σ l (psi φ φ' τ m (a ⊗ₜ[L] b)) = _
  simp only [psi_tmul]
  rw [← mul_assoc, ← mul_assoc, single_mul_single, single_mul_single]
  have h1 : single φ' (σ * τ) (1 * σ 1 * ((φ' (σ, τ) : Lˣ) : L)) =
      ((φ' (σ, τ) : Lˣ) : L) • single φ' (σ * τ) 1 := by
    rw [single_smul_L]; simp
  have h2 : single φ (σ * τ) (l * σ m * ((φ (σ, τ) : Lˣ) : L) * ((φ' (σ, τ) : Lˣ) : L)) =
      ((φ' (σ, τ) : Lˣ) : L) • single φ (σ * τ) (l * σ m * ((φ (σ, τ) : Lˣ) : L)) := by
    rw [single_smul_L]; congr 1; ring
  rw [h1, h2, smul_mul_L, smul_mul_L, TensorProduct.smul_tmul]

theorem psi_rightA (σ : L ≃ₐ[K] L) (l : L) (a : CrossedProduct φ) :
    psi φ φ' σ l * rightA φ φ' a = rightA φ φ' a * psi φ φ' σ l :=
  ext_V φ φ' fun x y => by simp [mul_assoc]

theorem psi_rightB (σ : L ≃ₐ[K] L) (l : L) (b : CrossedProduct φ') :
    psi φ φ' σ l * rightB φ φ' b = rightB φ φ' b * psi φ φ' σ l :=
  ext_V φ φ' fun x y => by simp [mul_assoc]

/-- The operator of $c = \sum_\sigma c_\sigma e''_\sigma \in C$ on $V$. -/
noncomputable def rhoCFun (c : CrossedProduct (NormalizedCocycle.mul φ φ')) :
    Module.End K (Vmod φ φ') :=
  ∑ σ, psi φ φ' σ (c σ)

open Classical in
theorem rhoCFun_single (σ : L ≃ₐ[K] L) (l : L) :
    rhoCFun φ φ' (single (NormalizedCocycle.mul φ φ') σ l) = psi φ φ' σ l := by
  unfold rhoCFun
  rw [Finset.sum_eq_single σ]
  · simp [single_apply]
  · intro τ _ hτ
    simp [single_apply, hτ, psi_zero_l]
  · simp

theorem rhoCFun_add (x y : CrossedProduct (NormalizedCocycle.mul φ φ')) :
    rhoCFun φ φ' (x + y) = rhoCFun φ φ' x + rhoCFun φ φ' y := by
  unfold rhoCFun
  simp only [add_apply, psi_add_l, Finset.sum_add_distrib]

theorem rhoCFun_zero : rhoCFun φ φ' 0 = 0 := by
  simp [rhoCFun, psi_zero_l]

theorem rhoCFun_smul (k : K) (x : CrossedProduct (NormalizedCocycle.mul φ φ')) :
    rhoCFun φ φ' (k • x) = k • rhoCFun φ φ' x := by
  unfold rhoCFun
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact psi_smul_l φ φ' σ k (x σ)

theorem rhoCFun_mul (x y : CrossedProduct (NormalizedCocycle.mul φ φ')) :
    rhoCFun φ φ' (x * y) = rhoCFun φ φ' x * rhoCFun φ φ' y := by
  refine induction_on _ (fun x => rhoCFun φ φ' (x * y) = rhoCFun φ φ' x * rhoCFun φ φ' y) x
    ?_ ?_ ?_
  · rw [zero_mul, rhoCFun_zero, zero_mul]
  · intro a b ha hb
    rw [add_mul, rhoCFun_add, rhoCFun_add, ha, hb, add_mul]
  intro σ l
  refine induction_on _ (fun y => rhoCFun φ φ' (single _ σ l * y) =
    rhoCFun φ φ' (single _ σ l) * rhoCFun φ φ' y) y ?_ ?_ ?_
  · rw [mul_zero, rhoCFun_zero, mul_zero]
  · intro a b ha hb
    rw [mul_add, rhoCFun_add, rhoCFun_add, ha, hb, mul_add]
  intro τ m
  rw [single_mul_single, rhoCFun_single, rhoCFun_single, rhoCFun_single, psi_mul,
    show ((((NormalizedCocycle.mul φ φ') (σ, τ)) : Lˣ) : L) =
      ((φ (σ, τ) : Lˣ) : L) * ((φ' (σ, τ) : Lˣ) : L) from rfl, ← mul_assoc]

theorem rhoCFun_rightA (c : CrossedProduct (NormalizedCocycle.mul φ φ')) (a : CrossedProduct φ) :
    rhoCFun φ φ' c * rightA φ φ' a = rightA φ φ' a * rhoCFun φ φ' c := by
  unfold rhoCFun
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => psi_rightA φ φ' σ _ a

theorem rhoCFun_rightB (c : CrossedProduct (NormalizedCocycle.mul φ φ')) (b : CrossedProduct φ') :
    rhoCFun φ φ' c * rightB φ φ' b = rightB φ φ' b * rhoCFun φ φ' c := by
  unfold rhoCFun
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => psi_rightB φ φ' σ _ b

/-- The left action of $C = A(\varphi\varphi')$ on $V$. -/
noncomputable def rhoC :
    CrossedProduct (NormalizedCocycle.mul φ φ') →ₐ[K] Module.End K (Vmod φ φ') where
  toFun := rhoCFun φ φ'
  map_one' := by
    show rhoCFun φ φ' (single _ 1 1) = 1
    rw [rhoCFun_single]
    exact ext_V φ φ' fun a b => by
      show (single φ 1 1 * a) ⊗ₜ[L] (single φ' 1 1 * b) = a ⊗ₜ[L] b
      have h1 : single φ 1 1 = 1 := rfl
      have h2 : single φ' 1 1 = 1 := rfl
      rw [h1, h2, one_mul, one_mul]
  map_mul' := rhoCFun_mul φ φ'
  map_zero' := rhoCFun_zero φ φ'
  map_add' := rhoCFun_add φ φ'
  commutes' k := by
    show rhoCFun φ φ' (algebraMap K _ k) = _
    rw [Algebra.algebraMap_eq_smul_one, rhoCFun_smul]
    have h1 : rhoCFun φ φ' (1 : CrossedProduct (NormalizedCocycle.mul φ φ')) = 1 := by
      show rhoCFun φ φ' (single _ 1 1) = 1
      rw [rhoCFun_single]
      exact ext_V φ φ' fun a b => by
        show (single φ 1 1 * a) ⊗ₜ[L] (single φ' 1 1 * b) = a ⊗ₜ[L] b
        have h1 : single φ 1 1 = 1 := rfl
        have h2 : single φ' 1 1 = 1 := rfl
        rw [h1, h2, one_mul, one_mul]
    rw [h1, Algebra.algebraMap_eq_smul_one]

theorem commute_rhoC_rhoR (c : CrossedProduct (NormalizedCocycle.mul φ φ'))
    (t : (CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ) :
    Commute (rhoC φ φ' c) (rhoR φ φ' t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have h1 : rhoR φ φ' (a ⊗ₜ[K] b) = rightA φ φ' a.unop * rightB φ φ' b.unop :=
      Algebra.TensorProduct.lift_tmul _ _ _ _ _
    rw [h1]
    exact Commute.mul_right (rhoCFun_rightA φ φ' c a.unop) (rhoCFun_rightB φ φ' c b.unop)
  | add x y hx hy =>
    rw [map_add]
    exact hx.add_right hy

/-- The $K$-algebra map $C \otimes_K (A^{\mathrm{opp}} \otimes_K B^{\mathrm{opp}}) \to
\mathrm{End}_K(V)$. -/
noncomputable def Theta :
    CrossedProduct (NormalizedCocycle.mul φ φ') ⊗[K]
        ((CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ) →ₐ[K] Module.End K (Vmod φ φ') :=
  Algebra.TensorProduct.lift (rhoC φ φ') (rhoR φ φ') (commute_rhoC_rhoR φ φ')

theorem Theta_bijective : Function.Bijective (Theta φ φ') := by
  haveI := isCentral φ
  haveI := isSimpleRing φ
  haveI := isCentral φ'
  haveI := isSimpleRing φ'
  haveI := isCentral (NormalizedCocycle.mul φ φ')
  haveI := isSimpleRing (NormalizedCocycle.mul φ φ')
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  haveI : Nontrivial (Vmod φ φ') := Module.nontrivial_of_finrank_pos (R := K) (by
    rw [finrank_V]; positivity)
  haveI : Algebra.IsCentral K (CrossedProduct φ)ᵐᵒᵖ := inferInstance
  haveI : IsSimpleRing (CrossedProduct φ)ᵐᵒᵖ := inferInstance
  haveI : Algebra.IsCentral K (CrossedProduct φ')ᵐᵒᵖ := inferInstance
  haveI : IsSimpleRing (CrossedProduct φ')ᵐᵒᵖ := inferInstance
  haveI : Algebra.IsCentral K ((CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ) :=
    isCentral_tensorProduct _ _
  haveI : IsSimpleRing ((CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ) :=
    isSimpleRing_tensorProduct _ _
  haveI : IsSimpleRing (CrossedProduct (NormalizedCocycle.mul φ φ') ⊗[K]
        ((CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ)) := isSimpleRing_tensorProduct _ _
  haveI : Nontrivial (Module.End K (Vmod φ φ')) := inferInstance
  have hinj0 : Function.Injective (Theta φ φ').toRingHom :=
    RingHom.injective (R := CrossedProduct (NormalizedCocycle.mul φ φ') ⊗[K]
        ((CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ)) (S := Module.End K (Vmod φ φ')) _
  have hinj : Function.Injective (Theta φ φ') := hinj0
  have hdim : Module.finrank K (CrossedProduct (NormalizedCocycle.mul φ φ') ⊗[K]
        ((CrossedProduct φ)ᵐᵒᵖ ⊗[K] (CrossedProduct φ')ᵐᵒᵖ)) =
      Module.finrank K (Module.End K (Vmod φ φ')) := by
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct,
      ← (MulOpposite.opLinearEquiv K (M := CrossedProduct φ)).finrank_eq,
      ← (MulOpposite.opLinearEquiv K (M := CrossedProduct φ')).finrank_eq, finrank_eq, finrank_eq,
      finrank_eq, Module.finrank_linearMap, finrank_V]
    ring
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (Theta φ φ').toLinearMap)).mp hinj⟩

end Aux

end CrossedProduct

/-- Lemma 3.15 of Milne: $A(\varphi + \varphi') \sim A(\varphi) \otimes_K A(\varphi')$ ($\varphi + \varphi'$
is the product cocycle). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Lem. 3.15, p. 137"]
theorem lemma_3_15 (φ φ' : NormalizedCocycle K L) :
    IsBrauerEquivalent (CrossedProduct.toCSA (NormalizedCocycle.mul φ φ'))
      (CSA.tensor (CrossedProduct.toCSA φ) (CrossedProduct.toCSA φ')) := by
  have hb := CrossedProduct.Theta_bijective φ φ'
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  haveI : Nontrivial (CrossedProduct.Vmod φ φ') := Module.nontrivial_of_finrank_pos (R := K) (by
    rw [CrossedProduct.finrank_V]; positivity)
  have hN : Module.finrank K (CrossedProduct.Vmod φ φ') ≠ 0 := Module.finrank_pos.ne'
  let e := (AlgEquiv.ofBijective _ hb).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis K (CrossedProduct.Vmod φ φ')))
  have h1 : BrauerGroup.mk (CSA.tensor (CrossedProduct.toCSA (NormalizedCocycle.mul φ φ'))
      (CSA.tensor (CSA.op (CrossedProduct.toCSA φ)) (CSA.op (CrossedProduct.toCSA φ')))) = 1 :=
    (BrauerGroup.mk_eq_one_iff _).2 ⟨_, hN, ⟨e⟩⟩
  rw [← BrauerGroup.mk_mul_mk, ← BrauerGroup.mk_mul_mk, ← BrauerGroup.inv_mk,
    ← BrauerGroup.inv_mk, ← mul_inv, mul_inv_eq_one] at h1
  rw [← BrauerGroup.mk_eq_mk_iff, ← BrauerGroup.mk_mul_mk]
  exact h1

end NumberFieldKB.MilneCFT.Ch4
