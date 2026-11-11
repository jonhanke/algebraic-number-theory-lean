import Mathlib.FieldTheory.IsSepClosed
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Hilbert
import NumberFieldKB.MilneCFT.Ch3Prop36
import NumberFieldKB.MilneCFT.Ch2CupExists

/-!
# Milne, *Class Field Theory*, Chapter III §4, Steps 2–3: $\chi \cup \delta b$ in bidegree $(1,1)$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`,
Ch. III, §4, Steps 2–3, p. 112.

The cohomological computation behind the identity $(\chi, b) = \mathrm{inv}(b \cup \delta\chi)$: for
$\chi : \operatorname{Gal}(M/K) \to \mathbb Z/n$ and $\beta^n = b \in K^\times$, the image in $H^2(M^\times)$ of
$\chi \cup \delta b \in H^2(\mu_n)$ equals the image of $\delta\chi \in H^2(\mathbb Z)$ under $k \mapsto b^k$
(`cup_charClass_kummerClass`).

Proof (cochain level). With $\tilde\chi(g) \in [0, n)$ the representative of $\chi(g)$, the cup product is the
cocycle $c(g, h) = (gh\beta/g\beta)^{\tilde\chi(g)}$. For $f(g) = (g\beta)^{\tilde\chi(g)}$ one has
$(df)(g, h) = c(g, h)^{-1} b^{k(g,h)}$ with $k(g,h) = (\tilde\chi(g) + \tilde\chi(h) - \tilde\chi(gh))/n$ the carry
(`coboundary_alg`, `carry_mul`), so $c$ and $b^k$ differ by a coboundary.

* `zmodToQZ` — $\mathbb Z/n \to \mathbb Q/\mathbb Z$, $k \mapsto k/n$.
* `cupCocycle_apply` — the explicit cocycle of the cup product.
* `cup_charClass_kummerClass` — the statement.
-/

open scoped ValuativeRel
namespace NumberFieldKB.MilneCFT.Ch3
open CategoryTheory MonoidalCategory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory TauCeti.ContCohomology
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (n : ℕ)

/-- The inclusion $\mathbb Z/n \to \mathbb Q/\mathbb Z$, $k \mapsto k/n$. -/
noncomputable def zmodToQZ [NeZero n] : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (qz (1 / (n : ℚ))), by
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
    change (n : ℤ) • qz (1 / (n : ℚ)) = 0
    rw [qz_zsmul, qz_eq_zero_iff]
    exact ⟨1, by push_cast; field_simp⟩⟩

theorem zmodToQZ_natCast [NeZero n] (m : ℕ) : zmodToQZ n (m : ZMod n) = qz ((m : ℚ) / n) := by
  have : ((m : ℕ) : ZMod n) = ((m : ℤ) : ZMod n) := by simp
  rw [this, zmodToQZ, ZMod.lift_coe]
  change (m : ℤ) • qz (1 / (n : ℚ)) = _
  rw [qz_zsmul]
  congr 1
  push_cast
  ring

theorem qzLift_qz {r : ℚ} (h0 : 0 ≤ r) (h1 : r < 1) : qzLift (qz r) = r := by
  have h : Ch4.addCircleEquivQZ.symm (qz r) = ((r : ℚ) : AddCircle (1 : ℚ)) := rfl
  rw [qzLift, h]
  have := AddCircle.equivIco_coe_of_mem (p := (1 : ℚ)) (a := 0) (y := r) ⟨h0, by simpa using h1⟩
  simpa using this

/-- The representative in $[0, 1)$ of $k/n$ is $\tilde k / n$ with $\tilde k \in [0, n)$. -/
theorem qzLift_zmodToQZ [NeZero n] (k : ZMod n) : qzLift (zmodToQZ n k) = (k.val : ℚ) / n := by
  have hn : (0 : ℚ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [show zmodToQZ n k = qz ((k.val : ℚ) / n) from by
    rw [← zmodToQZ_natCast, ZMod.natCast_zmod_val]]
  apply qzLift_qz (by positivity)
  rw [div_lt_one hn]
  exact_mod_cast ZMod.val_lt k

/-- $n \cdot k(g,h) = \tilde\chi(g) + \tilde\chi(h) - \tilde\chi(gh)$ for the carry $k$ of $\chi/n$. -/
theorem carry_mul [NeZero n] {G : Type} [Group G] (χ : Additive G →+ ZMod n) (g h : G) :
    (n : ℤ) * characterCarry (toCircle ((zmodToQZ n).comp χ)) g h =
      (χ (.ofMul g)).val + (χ (.ofMul h)).val - (χ (.ofMul (g * h))).val := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_mul, intCast_characterCarry_toCircle]
  simp only [AddMonoidHom.comp_apply, qzLift_zmodToQZ]
  push_cast
  field_simp
  ring

theorem iso₂_hom_apply {G : Type} [Group G] (A : Rep ℤ G) (w : cocycles A 2) (g h : G) :
    ((isoCocycles₂ A).hom w : G × G → A) (g, h) = iCocycles A 2 w ![g, h] :=
  congrFun (isoCocycles₂_hom_comp_i_apply A w) (g, h)

theorem iCocycles_iso₁_inv {G : Type} [Group G] (A : Rep ℤ G) (z : cocycles₁ A) (x : Fin 1 → G) :
    iCocycles A 1 ((isoCocycles₁ A).inv z) x = z (x 0) :=
  congrFun (isoCocycles₁_inv_comp_iCocycles_apply A z) x

/-- **The coboundary identity**, additively: with $E = \rho_g F(h)$, $F(x) = -\tilde\chi(x) \cdot (x\beta)$, the
difference of the cup cocycle $a \cdot (P - Q)$ and $k \cdot B$ ($B = nP$, $nk = a + b - c$) is a coboundary. -/
theorem coboundary_alg {X : Type*} [AddCommGroup X] (P Q Bx Y E : X) (a b c : ℕ) (k : ℤ) (n : ℕ)
    (hP : n • P = Bx) (hcar : (n : ℤ) * k = a + b - c) (hd : Y = P - Q) (hE : E = -(b • P)) :
    E - -(c • P) + -(a • Q) = a • Y - k • Bx := by
  subst hd hE hP
  have h : k • n • P = ((a : ℤ) + b - c) • P := by
    rw [← natCast_zsmul, ← mul_smul, mul_comm, hcar]
  rw [h]
  simp only [← natCast_zsmul]
  module

section Main

variable [NeZero n] (M : IntermediateField K Ω)

theorem zmodAct_val (k : ZMod n) (y : muRep n M) : zmodAct n M k y = k.val • y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k, ← Int.cast_natCast (R := ZMod n)]
  simp only [zmodAct, ZMod.lift_coe, zmultiplesHom_apply, AddMonoidHom.smul_apply,
    AddMonoidHom.id_apply, natCast_zsmul]

/-- **The explicit cup cocycle**: the 2-cocycle of $\chi \cup \delta\beta$ (cochain formula, pushed to $M^\times$)
is $(g, h) \mapsto (g \cdot (h\beta/\beta))^{\tilde\chi(g)}$, written additively. -/
theorem cupCocycle_apply (χ : Additive Gal(M/K) →+ ZMod n) (β : Mˣ)
    (hβ : ∀ σ : Gal(M/K), σ • β ^ n = β ^ n) (g h : Gal(M/K)) :
    ((isoCocycles₂ _).hom (cocyclesMap (MonoidHom.id _) (zmodMu n M ≫ stableIncl _ _ _) 2
      (cupZ (r := 1) (s := 1) rfl
        ((isoCocycles₁ (Rep.trivial ℤ Gal(M/K) (ZMod n))).inv ((cocycles₁IsoOfIsTrivial _).inv χ))
        ((isoCocycles₁ (muRep n M)).inv ⟨kummerFun n M β hβ, kummerFun_mem n M β hβ⟩))) :
        Gal(M/K) × Gal(M/K) → Rep.ofAlgebraAutOnUnits K M) (g, h) =
      (χ (.ofMul g)).val • Additive.ofMul (g • (h • β * β⁻¹)) := by
  rw [iso₂_hom_apply, iCocycles_cocyclesMap, iCocycles_cupZ, cupC_apply, iCocycles_iso₁_inv,
    iCocycles_iso₁_inv]
  have e1 : fprod (hdF (rfl : 1 + 1 = 2) ![g, h]) = g := by
    rw [fprod_succ, fprod_fin_zero, mul_one]; rfl
  have e2 : hdF (rfl : 1 + 1 = 2) ![g, h] 0 = g := rfl
  have e3 : tlF (rfl : 1 + 1 = 2) ![g, h] 0 = h := rfl
  rw [e1, e2, e3]
  change (zmodAct n M (χ (.ofMul g)) (((muRep n M).ρ g) (kummerFun n M β hβ h))).1 = _
  rw [zmodAct_val]
  rfl

set_option maxHeartbeats 1000000 in
/-- **$\chi \cup \delta b = \delta\chi$ pushed along $k \mapsto b^k$** (Milne, CFT v4.03, Ch. III, §4,
Steps 2–3, p. 112): for $\chi : \operatorname{Gal}(M/K) \to \mathbb Z/n$ and $\beta \in M^\times$ with
$\beta^n = b \in K^\times$, the image in $H^2(\operatorname{Gal}(M/K), M^\times)$ of the cup product
$\chi \cup \delta b \in H^2(\mu_n)$ (via $\mathbb Z/n \otimes \mu_n \to \mu_n \subseteq M^\times$) equals the image
of the class of the carry cocycle $\delta\chi \in H^2(\mathbb Z)$ under $\mathbb Z \to M^\times$, $k \mapsto b^k$.
Holds for every cup-product family `c` (unique by Prop. 1.38). -/
@[kb "milne2020cft" "v4.03, Ch. III, §4, Steps 2–3, χ ∪ δb = b ∪ δχ, p. 112"]
theorem cup_charClass_kummerClass (c : CupProductFamily Gal(M/K))
    (χ : Additive Gal(M/K) →+ ZMod n) (β : Mˣ) (b : Kˣ) (hb : β ^ n = embUnits M b) :
    ((functor ℤ Gal(M/K) 2).map (zmodMu n M ≫ stableIncl _ _ _)).hom
        (c.cup _ _ 1 1 2 rfl (charClass n M χ) (kummerClass n M β (fixed_of_pow_eq n M hb))) =
      ((functor ℤ Gal(M/K) 2).map (powHom M b)).hom (H2π _ (carryZ ((zmodToQZ n).comp χ))) := by
  rw [cupProductFamily_cup_unique c cupProductFamilyOfCochains]
  change ((functor ℤ Gal(M/K) 2).map (zmodMu n M ≫ stableIncl _ _ _)).hom
    (cupH (rfl : 1 + 1 = 2)
      (π (Rep.trivial ℤ Gal(M/K) (ZMod n)) 1 ((isoCocycles₁ (Rep.trivial ℤ Gal(M/K) (ZMod n))).inv
        ((cocycles₁IsoOfIsTrivial _).inv χ)))
      (π (muRep n M) 1 ((isoCocycles₁ (muRep n M)).inv
        ⟨kummerFun n M β (fixed_of_pow_eq n M hb), kummerFun_mem n M β (fixed_of_pow_eq n M hb)⟩))) = _
  rw [cupH_π]
  erw [functor_map_π]
  rw [functor_map]
  erw [H2π_comp_map_apply]
  set W := cocyclesMap (MonoidHom.id Gal(M/K)) (zmodMu n M ≫ stableIncl _ _ _) 2
    (cupZ (r := 1) (s := 1) rfl
      ((isoCocycles₁ (Rep.trivial ℤ Gal(M/K) (ZMod n))).inv ((cocycles₁IsoOfIsTrivial _).inv χ))
      ((isoCocycles₁ (muRep n M)).inv ⟨kummerFun n M β (fixed_of_pow_eq n M hb),
        kummerFun_mem n M β (fixed_of_pow_eq n M hb)⟩)) with hW
  have hπ : π (Rep.ofAlgebraAutOnUnits K M) 2 W =
      H2π (Rep.ofAlgebraAutOnUnits K M) ((isoCocycles₂ _).hom W) := by
    change _ = π _ 2 ((isoCocycles₂ _).inv ((isoCocycles₂ _).hom W))
    rw [Iso.hom_inv_id_apply]
  rw [hπ]
  refine (H2π_eq_iff (A := Rep.ofAlgebraAutOnUnits K M) _ _).2 ?_
  let F : Gal(M/K) → Rep.ofAlgebraAutOnUnits K M :=
    fun g => -((χ (.ofMul g)).val • Additive.ofMul (g • β))
  refine ⟨F, funext fun p => ?_⟩
  obtain ⟨g, h⟩ := p
  have hc := cupCocycle_apply n M χ β (fixed_of_pow_eq n M hb) g h
  have hm : ((mapCocycles₂ (MonoidHom.id Gal(M/K)) (powHom M b) (carryZ ((zmodToQZ n).comp χ)) :
      Gal(M/K) × Gal(M/K) → Rep.ofAlgebraAutOnUnits K M) (g, h)) =
      (characterCarry (toCircle ((zmodToQZ n).comp χ)) g h) • Additive.ofMul (embUnits M b) := rfl
  change (Rep.ofAlgebraAutOnUnits K M).ρ g (F h) - F (g * h) + F g = _
  erw [Pi.sub_apply, hm, hc]
  have hρ : ∀ (σ : Gal(M/K)) (x : Additive Mˣ),
      (Rep.ofAlgebraAutOnUnits K M).ρ σ x = Additive.ofMul (σ • x.toMul) := fun _ _ => rfl
  have hP : n • Additive.ofMul ((g * h) • β) = Additive.ofMul (embUnits M b) := by
    rw [← ofMul_pow, ← smul_pow', hb, gal_smul_embUnits]
  have hd : Additive.ofMul (g • (h • β * β⁻¹)) =
      Additive.ofMul ((g * h) • β) - Additive.ofMul (g • β) := by
    have hd' : g • (h • β * β⁻¹) = (g * h) • β / (g • β) := by
      rw [smul_mul', smul_inv', ← mul_smul, div_eq_mul_inv]
    rw [hd']
    exact ofMul_div _ _
  have hcar := carry_mul n χ g h
  have hρ2 : (Rep.ofAlgebraAutOnUnits K M).ρ g (Additive.ofMul (h • β)) =
      Additive.ofMul ((g * h) • β) := by
    change Additive.ofMul (g • h • β) = Additive.ofMul ((g * h) • β)
    rw [mul_smul]
  have hρF : (Rep.ofAlgebraAutOnUnits K M).ρ g (F h) =
      -((χ (.ofMul h)).val • Additive.ofMul ((g * h) • β) : Additive Mˣ) := by
    have h1 := map_neg ((Rep.ofAlgebraAutOnUnits K M).ρ g)
      ((χ (.ofMul h)).val • Additive.ofMul (h • β) : Additive Mˣ)
    have h2 := map_nsmul ((Rep.ofAlgebraAutOnUnits K M).ρ g) (χ (.ofMul h)).val
      (Additive.ofMul (h • β) : Additive Mˣ)
    exact h1.trans (congrArg Neg.neg (h2.trans (congrArg (fun y => (χ (.ofMul h)).val • y) hρ2)))
  exact coboundary_alg (Additive.ofMul ((g * h) • β) : Additive Mˣ) (Additive.ofMul (g • β))
    (Additive.ofMul (embUnits M b)) _ _ _ _ _ _ _ hP hcar hd hρF

end Main

end NumberFieldKB.MilneCFT.Ch3
