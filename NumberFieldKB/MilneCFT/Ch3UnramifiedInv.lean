import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Unramified
import NumberFieldKB.MilneCFT.Ch3Invariant

/-!
# Milne, *Class Field Theory*, Chapter III §1: the invariant map of an unramified extension

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

* `theorem_1_7`, `theorem_1_7_infl` — Theorem 1.7 at finite level: for $L/K$ finite unramified of degree $n$, the
  invariant map is an isomorphism $H^2(L/K) \simeq \frac1n\mathbb Z/\mathbb Z$, and the invariant maps are compatible
  with inflation (so they define $\mathrm{inv}_K$ on $H^2(K^{\mathrm{un}}/K) = \varinjlim H^2(L/K)$, with image
  $\bigcup_n \frac1n\mathbb Z/\mathbb Z = \mathbb Q/\mathbb Z$ since $K$ has unramified extensions of every degree).
  Proved from Proposition 1.1 and the named inputs of §1.
* `Prop1_8` — Proposition 1.8 at finite level (named statement).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Inflation** $\mathrm{Inf} : H^2(M/K) \to H^2(E/K)$ for $M \subseteq E$, $M/K$ normal (Milne, II, 1.27 (c)),
defined by the compatible pair $\operatorname{Gal}(E/K) \to \operatorname{Gal}(M/K)$ (restriction),
$M^\times \hookrightarrow E^\times$. -/
noncomputable def inflK {M E : IntermediateField K Ω} (h : M ≤ E) [Normal K M] : H2 M ⟶ H2 E :=
  groupCohomology.map (galRestrict h)
    (Rep.ofHom ⟨(AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive
      (Units.map (IntermediateField.inclusion h).toRingHom.toMonoidHom))), fun σ => by
    ext x
    exact galRestrict_apply h σ ((Additive.toMul (α := Mˣ) x : Mˣ) : M)⟩) 2

/-- $\operatorname{Gal}(M/L) \subseteq \operatorname{Gal}(M/K)$ for $K \subseteq L \subseteq M$: the automorphisms
fixing $L$ pointwise. -/
def galOver {L M : IntermediateField K Ω} (h : L ≤ M) : Subgroup Gal(M/K) where
  carrier := {σ | ∀ x : L, σ (IntermediateField.inclusion h x) = IntermediateField.inclusion h x}
  mul_mem' hσ hτ x := by simp [hσ x, hτ x]
  one_mem' x := rfl
  inv_mem' {σ} hσ x := by
    have := congrArg σ.symm (hσ x)
    simp only [AlgEquiv.symm_apply_apply] at this
    exact this.symm

/-- **Restriction** $H^2(E/K) \to H^2(M/F)$ for $E \subseteq M$ and $F = M^H$, defined by the compatible pair
$H \to \operatorname{Gal}(E/K)$, $\tau \mapsto \tau|_E$, and $E^\times \hookrightarrow M^\times$ (Milne, II, 1.27 (b);
in Proposition 1.8, $E \subseteq K^{\mathrm{un}}$, $M = EL \subseteq L^{\mathrm{un}}$, $H = \operatorname{Gal}(M/L)$). -/
noncomputable def resToRel {E M : IntermediateField K Ω} (h : E ≤ M) [Normal K E] (H : Subgroup Gal(M/K)) :
    H2 E ⟶ H2rel M H :=
  groupCohomology.map ((galRestrict h).comp H.subtype)
    (Rep.ofHom ⟨(AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive
      (Units.map (IntermediateField.inclusion h).toRingHom.toMonoidHom))), fun σ => by
    ext x
    apply Units.ext
    apply Subtype.ext
    exact galRestrict_apply h σ.1 ((Additive.toMul (α := Eˣ) x : Eˣ) : E)⟩) 2

/-- The exact sequence $0 \to U_L \to L^\times \xrightarrow{\mathrm{ord}_L} \mathbb Z \to 0$ of
$\operatorname{Gal}(L/K)$-modules. -/
noncomputable def ordSeq {L : IntermediateField K Ω} {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) :
    ShortComplex (Rep ℤ Gal(L/K)) :=
  ShortComplex.mk (unitsIncl L) (ordRep hv) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    exact (hv.ker _).2 (Additive.toMul u).2)

theorem ordSeq_shortExact {L : IntermediateField K Ω} {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) :
    (ordSeq hv).ShortExact := by
  have h1 : (ordSeq hv).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful (ordSeq hv) (F := forget₂ (Rep ℤ Gal(L/K)) (ModuleCat ℤ)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨y, rfl⟩
      exact (hv.ker _).2 (Additive.toMul y).2
    · intro hx
      exact ⟨Additive.ofMul ⟨Additive.toMul x, (hv.ker _).1 hx⟩, rfl⟩
  have h2 : Mono (ordSeq hv).f := by
    rw [Rep.mono_iff_injective]
    intro a b h
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg Additive.toMul h
  have h3 : Epi (ordSeq hv).g := by
    rw [Rep.epi_iff_surjective]
    exact hv.surj
  exact { exact := h1, mono_f := h2, epi_g := h3 }

theorem ord_h2_bijective (h26 : UnitPrimeDecomposition K Ω) (hcyc : UnramifiedCyclic K Ω)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (hL : IsUnramifiedExt L)
    {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) :
    Function.Bijective ((functor ℤ Gal(L/K) 2).map (ordRep hv)).hom := by
  have hz : ∀ n : ℕ, 0 < n → IsZero (groupCohomology (unitsRep L) n) := fun n hn => by
    have : NeZero n := ⟨hn.ne'⟩
    exact IsZero.of_iso (prop_1_1 h26 hcyc L hL n)
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L/K)) n).app _).symm
  have hS := ordSeq_shortExact hv
  constructor
  · have hex := (ShortComplex.moduleCat_exact_iff _).1 (mapShortComplex₂_exact hS 2)
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := hex x hx
    have : y = 0 := ((ModuleCat.isZero_iff_subsingleton).1 (hz 2 (by norm_num))).elim y 0
    rw [this]; exact map_zero _
  · have hex := (ShortComplex.moduleCat_exact_iff _).1 (mapShortComplex₃_exact hS (i := 2) rfl)
    intro y
    exact hex y (((ModuleCat.isZero_iff_subsingleton).1 (hz 3 (by norm_num))).elim _ _)

/-- **Theorem 1.7** (p. 100), at finite level. Let $L/K$ be a finite unramified extension of degree $n$, Galois with
group $G$, $v = \mathrm{ord}_L$ and $\sigma = \mathrm{Frob}_{L/K}$. Then the invariant map
$\mathrm{inv}_{L/K} : H^2(L/K) \to \mathbb Q/\mathbb Z$ is injective with image $\frac1n\mathbb Z/\mathbb Z$.
(Compatibility with inflation is `theorem_1_7_infl`, in `Ch3InvInfl`; together they give Milne's isomorphism
$\mathrm{inv}_K : H^2(K^{\mathrm{un}}/K) \to \mathbb Q/\mathbb Z$ on the direct limit.) Milne's proof ("immediate
from the above discussion"): $H^2(G, U_L) = H^3(G, U_L) = 0$ (Proposition 1.1), so $\mathrm{ord}_L$ induces
$H^2(G, L^\times) \simeq H^2(G, \mathbb Z)$; $\delta$ is an isomorphism; evaluation at the generator $\sigma$ is an
isomorphism $\operatorname{Hom}(G, \mathbb Q/\mathbb Z) \simeq \frac1n\mathbb Z/\mathbb Z$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 1.7, p. 100"]
theorem theorem_1_7 (h26 : UnitPrimeDecomposition K Ω) (hcyc : UnramifiedCyclic K Ω)
    (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (hL : IsUnramifiedExt L)
    {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) {σ : Gal(L/K)} (hσ : IsFrobenius L σ) :
    Function.Injective (invK L hv σ) ∧ (invK L hv σ).range = qzOver (Module.finrank K L) := by
  have hA := ord_h2_bijective h26 hcyc L hL hv
  have hB := h2IntToHom_bijective (G := Gal(L/K))
  have hgen := hcyc.frob_generator L hL σ hσ
  have hinv : ∀ x, invK L hv σ x = h2IntToHom.hom (((functor ℤ Gal(L/K) 2).map (ordRep hv)).hom x)
      (Additive.ofMul σ) := fun x => rfl
  refine ⟨fun x y hxy => ?_, ?_⟩
  · rw [hinv, hinv] at hxy
    exact hA.1 (hB.1 (eval_injective hgen hxy))
  · ext y
    rw [AddMonoidHom.mem_range, ← IsGalois.card_aut_eq_finrank, ← eval_range hgen]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, (hinv x).symm⟩
    · rintro ⟨f, rfl⟩
      obtain ⟨z, hz⟩ := hB.2 f
      obtain ⟨x, rfl⟩ := hA.2 z
      exact ⟨x, (hinv x).trans (by rw [hz])⟩

variable (K Ω)

/-- **Proposition 1.8** (named statement; Milne, p. 100), at finite level. Let $L$ be a finite extension of $K$ of
degree $n$. For $E$ finite unramified Galois over $K$ ($E \subseteq K^{\mathrm{un}}$) put $M = EL$
($\subseteq L^{\mathrm{un}}$, unramified Galois over $L$). Then $\mathrm{inv}_{M/L} \circ \mathrm{Res} =
n \cdot \mathrm{inv}_{E/K}$ on $H^2(E/K)$, where $\mathrm{Res} : H^2(E/K) \to H^2(M/L)$ is defined by restriction
$\operatorname{Gal}(M/L) \to \operatorname{Gal}(E/K)$ and $E^\times \subseteq M^\times$, and the invariant maps use
the normalized valuations and the Frobenius elements. (On the direct limits this is the commutative square (27).)
Milne's proof compares the three squares: $\mathrm{ord}_L = e\,\mathrm{ord}_K$ on $K^{\mathrm{un}}$, $\delta$
commutes with restriction, and $\mathrm{Frob}_L|_{K^{\mathrm{un}}} = \mathrm{Frob}_K^f$, with $n = ef$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 1.8, p. 100 (input)"]
structure Prop1_8 : Prop where
  res_inv : ∀ (L E : IntermediateField K Ω) [FiniteDimensional K L] [FiniteDimensional K E] [IsGalois K E]
    [FiniteDimensional K ↥(E ⊔ L)], IsUnramifiedExt E →
    ∀ {vE : Additive Eˣ →+ ℤ} (hvE : IsNormalizedOrd E vE) {σE : Gal(E/K)}, IsFrobenius E σE →
    ∀ {vM : Additive (↥(E ⊔ L))ˣ →+ ℤ} (hvM : IsNormalizedOrd (E ⊔ L) vM) (σM : Gal(↥(E ⊔ L)/K))
      (hσM : IsFrobeniusOver (E ⊔ L) (galOver (le_sup_right : L ≤ E ⊔ L)) σM) (x : H2 E),
      invRel (E ⊔ L) hvM (galOver (le_sup_right : L ≤ E ⊔ L)) ⟨σM, hσM.1⟩
          ((resToRel (le_sup_left : E ≤ E ⊔ L) (galOver (le_sup_right : L ≤ E ⊔ L))).hom x) =
        Module.finrank K L • invK E hvE σE x

end NumberFieldKB.MilneCFT.Ch3
