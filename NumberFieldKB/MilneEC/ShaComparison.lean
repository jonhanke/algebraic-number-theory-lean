import NumberFieldKB.MilneEC.ContH1
import NumberFieldKB.MilneEC.Ch4BSDUncond

/-!
# The two Tate–Shafarevich groups

`tateShafarevich K W` (`Ch4Selmer.lean`, Milne, *Elliptic Curves*, IV, §2, pdf p. 117) is a subgroup of the
abstract $H^1(\operatorname{Gal}(\bar K/K), E(\bar K))$: continuous classes whose image under every localization map
$H^1(K, E(\bar K)) \to H^1(K_v, E(\bar K_v))$ (`locPoints`, Milne IV.1.9) vanishes.

Formal Conjectures' `tateShafarevich W` is a subgroup of Mathlib's `continuousCohomology 1` (homogeneous continuous
cochains) of the discrete module $E(\bar K)$: classes whose restriction to $\operatorname{Gal}(\bar K_v/K_v)$, *with
the same module* $E(\bar K)$, vanishes for every place $v$.

* `ContH1.equiv` (`ContH1.lean`) identifies the two cochain models of continuous $H^1$.
* `decompHom_eq_absoluteGaloisGroup_map` (`Ch4BSDComparisons.lean`): Milne's map
  $\operatorname{Gal}(\bar K_v/K_v) \to \operatorname{Gal}(\bar K/K)$ is Mathlib's `Field.absoluteGaloisGroup.map`.
* `locPoints_eq_zero_of_restrict_eq_zero`: the Formal Conjectures local condition implies Milne's (functoriality
  along $E(\bar K) \to E(\bar K_v)$). Hence `shaFCToMilne`, an injective homomorphism from Formal Conjectures'
  group into Milne's, unconditionally.
* The converse needs the injectivity of $H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K)) \to
  H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K_v))$ on continuous classes (Milne, *Arithmetic Duality
  Theorems*, Remark I.3.10, by Greenberg approximation at finite places). It is the named statement
  `LocalPointsInjective`, from which `shaComparison_of_localPointsInjective` proves
  `ShaComparison`.
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain NumberField
open scoped Classical

namespace NumberFieldKB.MilneEC

/-- Membership in $B^1$, unfolded: $f(g) = g\,m - m$ for some $m$. -/
theorem mem_coboundaries₁_iff' {G : Type} [Group G] {M : Rep.{0} ℤ G} (f : G → M) :
    f ∈ coboundaries₁ M ↔ ∃ m : M, ∀ g, M.ρ g m - m = f g :=
  ⟨fun ⟨m, hm⟩ => ⟨m, fun g => congrFun hm g⟩, fun ⟨m, hm⟩ => ⟨m, funext hm⟩⟩

/-! ## The named local statement -/

section Local

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (Kv : Type) [Field Kv] [Algebra K Kv]

/-- **Local injectivity at $K_v$** (named statement, not proved here): a continuous crossed homomorphism $c$ of
$\operatorname{Gal}(\bar K_v/K_v)$ into $E(\bar K)$ (acting through `decompHom`) whose image in $E(\bar K_v)$
(`localizePoints`) is principal is itself principal. Equivalently, the map
$H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K)) \to H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K_v))$ is
injective on continuous classes (Milne, *Arithmetic Duality Theorems*, Remark I.3.10: by Greenberg approximation,
$H^1(\operatorname{Gal}(\bar K_v/K_v), E(\bar K)) \cong H^1(K_v, E)$). -/
def LocalPointsInjectiveAt : Prop :=
  ∀ c : cocycles₁ (Rep.res (decompHom Kv) (pointsRep W (AlgebraicClosure K))),
    @Continuous _ (pointsRep W (AlgebraicClosure K)) _ ⊥ c →
    (fun σ => (localizePoints Kv W).hom (c σ)) ∈ coboundaries₁ (localPointsRep Kv W) →
    ⇑c ∈ coboundaries₁ (Rep.res (decompHom Kv) (pointsRep W (AlgebraicClosure K)))

end Local

/-- `LocalPointsInjectiveAt` at every finite place (the adic completions) and every infinite place of a number
field. -/
def LocalPointsInjectiveEverywhere (K : Type) [Field K] [DecidableEq K] [NumberField K] (W : WeierstrassCurve K) :
    Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), LocalPointsInjectiveAt W (v.adicCompletion K)) ∧
    ∀ w : InfinitePlace K, LocalPointsInjectiveAt W w.Completion

/-- **Local injectivity for elliptic curves over $\mathbb Q$** (named statement, not proved here):
`LocalPointsInjectiveAt` at every finite place (the adic completions) and the infinite place. Milne,
*Arithmetic Duality Theorems*, Remark I.3.10 (Greenberg approximation) at the finite places; at the real place it
follows from the Tarski–Seidenberg transfer between the real algebraic numbers and $\mathbb R$. -/
structure LocalPointsInjective : Prop where
  holds : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], LocalPointsInjectiveEverywhere ℚ E

/-! ## The comparison over a number field -/

section Comparison

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- Formal Conjectures' Galois module $E(\bar K)$. -/
noncomputable abbrev fcRep : TopRep ℤ (Field.absoluteGaloisGroup K) := FormalConjectures.galoisRepresentation W.toAffine

/-- Milne's Galois module $E(\bar K)$. -/
noncomputable abbrev milneRep : Rep.{0} ℤ (Field.absoluteGaloisGroup K) := pointsRep W (AlgebraicClosure K)

instance : DiscreteTopology (fcRep W) := ⟨rfl⟩

/-- The identity of $E(\bar K)$, from Formal Conjectures' module to Milne's. -/
noncomputable def pointsEquiv : fcRep W ≃+ milneRep W where
  toFun P := P
  invFun P := P
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem pointsEquiv_ρ (g : Field.absoluteGaloisGroup K) (a : fcRep W) :
    pointsEquiv W ((fcRep W).ρ g a) = (milneRep W).ρ g (pointsEquiv W a) := rfl

theorem fcRep_isOpen (a : fcRep W) : IsOpen {g : Field.absoluteGaloisGroup K | (fcRep W).ρ g a = a} :=
  pointsRep_isDiscreteModule W (AlgebraicClosure K) a

/-- Degree-one continuous cohomology of Formal Conjectures' module is Milne's $H^1$. -/
noncomputable def fcEquiv : continuousCohomology 1 (fcRep W) ≃+ H1cont (milneRep W) :=
  ContH1.equiv (fcRep W) (milneRep W) (pointsEquiv W) (pointsEquiv_ρ W) (fcRep_isOpen W)

/-- `fcEquiv`, as a class in Milne's $H^1$ of $\operatorname{Gal}(\bar K/K)$. -/
noncomputable def fcH1 (x : continuousCohomology 1 (fcRep W)) : H1 (pointsRep W (AlgebraicClosure K)) :=
  (fcEquiv W x).1

theorem fcH1_mem (x : continuousCohomology 1 (fcRep W)) :
    fcH1 W x ∈ H1cont (pointsRep W (AlgebraicClosure K)) :=
  (fcEquiv W x).2

theorem fcH1_injective : Function.Injective (fcH1 W) := fun x y h =>
  (fcEquiv W).injective (Subtype.ext h)

theorem fcH1_add (x y : continuousCohomology 1 (fcRep W)) : fcH1 W (x + y) = fcH1 W x + fcH1 W y := by
  simp only [fcH1, map_add]
  rfl

theorem fcH1_zero : fcH1 W 0 = 0 := by
  simp only [fcH1, map_zero]
  rfl

/-! ### One place -/

variable (Kv : Type) [Field Kv] [Algebra K Kv]

theorem decompHom_apply (σ : AlgebraicClosure Kv ≃ₐ[Kv] AlgebraicClosure Kv) :
    decompHom Kv σ = Field.absoluteGaloisGroup.map (algebraMap K Kv) σ :=
  (DFunLike.congr_fun (decompHom_eq_absoluteGaloisGroup_map (K := K) Kv) σ).symm

/-- Milne's local condition on the class of a crossed homomorphism $c$: $\iota \circ c \circ$ `decompHom` is
principal. -/
theorem locPoints_H1π_eq_zero_iff (c : cocycles₁ (pointsRep W (AlgebraicClosure K))) :
    locPoints Kv W (H1π (pointsRep W (AlgebraicClosure K)) c) = 0 ↔
      ∃ Q : localPointsRep Kv W, ∀ σ, (localPointsRep Kv W).ρ σ Q - Q =
        (localizePoints Kv W).hom (c (decompHom Kv σ)) := by
  have h3 : locPoints Kv W (H1π (pointsRep W (AlgebraicClosure K)) c) =
      H1π _ (mapCocycles₁ (decompHom Kv) (localizePoints Kv W) c) :=
    congrArg (fun m => m.hom c) (groupCohomology.H1π_comp_map (decompHom Kv) (localizePoints Kv W))
  rw [h3, H1π_eq_zero_iff, mem_coboundaries₁_iff']
  rfl

/-- The restriction of Formal Conjectures' module to $\operatorname{Gal}(\bar K_v/K_v)$. -/
noncomputable abbrev fcRepRes : TopRep ℤ (Field.absoluteGaloisGroup Kv) :=
  TopRep.res (Field.absoluteGaloisGroup.map (algebraMap K Kv) : _ →* _) (fcRep W)

/-- The restriction of Milne's module to $\operatorname{Gal}(\bar K_v/K_v)$ along Mathlib's map. -/
noncomputable abbrev milneRepRes : Rep.{0} ℤ (Field.absoluteGaloisGroup Kv) :=
  Rep.res (Field.absoluteGaloisGroup.map (algebraMap K Kv) : _ →* _) (milneRep W)

instance : DiscreteTopology (fcRepRes W Kv) := ⟨rfl⟩

theorem fcRepRes_isOpen (a : fcRepRes W Kv) :
    IsOpen {g : Field.absoluteGaloisGroup Kv | (fcRepRes W Kv).ρ g a = a} :=
  (fcRep_isOpen W a).preimage (Field.absoluteGaloisGroup.map (algebraMap K Kv)).continuous

/-- The identity of $E(\bar K)$ on the restricted modules. -/
noncomputable def pointsEquivRes : fcRepRes W Kv ≃+ milneRepRes W Kv where
  toFun P := P
  invFun P := P
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Formal Conjectures' local condition on a class $x$ whose crossed homomorphism is $c$: $c \circ$
`decompHom` is principal. -/
theorem restrict_eq_zero_iff (x : continuousCohomology 1 (fcRep W)) (c : cocycles₁ (milneRep W))
    (hx : (fcEquiv W x : H1 (milneRep W)) = H1π (milneRep W) c) :
    (ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap K Kv)) (𝟙 _) 1).hom x = 0 ↔
      ∃ P : milneRep W, ∀ σ, (milneRep W).ρ (decompHom Kv σ) P - P = c (decompHom Kv σ) := by
  have key := ContH1.equiv_map (Field.absoluteGaloisGroup.map (algebraMap K Kv)) (𝟙 (fcRepRes W Kv))
    (fcRep_isOpen W) (fcRepRes_isOpen W Kv) (pointsEquiv W) (pointsEquiv_ρ W) (pointsEquivRes W Kv)
    (fun _ _ => rfl) (𝟙 (milneRepRes W Kv)) (fun _ => rfl) x
  have h3 := groupCohomology.H1π_comp_map_apply _ (𝟙 (milneRepRes W Kv)) c
  rw [fcEquiv] at hx
  rw [hx] at key
  erw [h3] at key
  rw [← (ContH1.equiv (fcRepRes W Kv) (milneRepRes W Kv) (pointsEquivRes W Kv) (fun _ _ => rfl)
    (fcRepRes_isOpen W Kv)).map_eq_zero_iff, ← ZeroMemClass.coe_eq_zero, key, H1π_eq_zero_iff,
    mem_coboundaries₁_iff']
  simp only [decompHom_apply]
  rfl

/-- **Formal Conjectures' local condition implies Milne's** at $K_v$ (functoriality along
$E(\bar K) \to E(\bar K_v)$). -/
theorem locPoints_eq_zero_of_restrict_eq_zero (x : continuousCohomology 1 (fcRep W))
    (hx : (ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap K Kv)) (𝟙 _) 1).hom x = 0) :
    locPoints Kv W (fcH1 W x) = 0 := by
  obtain ⟨c, -, hc⟩ := (mem_H1cont_iff _ _).1 (fcH1_mem W x)
  obtain ⟨P, hP⟩ := (restrict_eq_zero_iff W Kv x c hc.symm).1 hx
  rw [← hc, locPoints_H1π_eq_zero_iff]
  refine ⟨(localizePoints Kv W).hom P, fun σ => ?_⟩
  refine Eq.trans ?_ (congrArg (localizePoints Kv W).hom (hP σ))
  rw [map_sub]
  congr 1
  exact (Rep.hom_comm_apply (localizePoints Kv W) σ P).symm

/-- **Milne's local condition implies Formal Conjectures'** at $K_v$, given `LocalPointsInjectiveAt`. -/
theorem restrict_eq_zero_of_locPoints_eq_zero (hinj : LocalPointsInjectiveAt W Kv)
    (x : continuousCohomology 1 (fcRep W)) (hx : locPoints Kv W (fcH1 W x) = 0) :
    (ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap K Kv)) (𝟙 _) 1).hom x = 0 := by
  obtain ⟨c, hcont, hc⟩ := (mem_H1cont_iff _ _).1 (fcH1_mem W x)
  rw [restrict_eq_zero_iff W Kv x c hc.symm]
  rw [← hc, locPoints_H1π_eq_zero_iff] at hx
  let c' : cocycles₁ (Rep.res (decompHom Kv) (pointsRep W (AlgebraicClosure K))) :=
    ⟨fun σ => c (decompHom Kv σ), (mem_cocycles₁_iff _).2 fun σ τ => by
      rw [map_mul]
      exact (mem_cocycles₁_iff (c : _ → _)).1 c.2 _ _⟩
  have hcont' : @Continuous _ (pointsRep W (AlgebraicClosure K)) _ ⊥ c' := by
    letI : TopologicalSpace (pointsRep W (AlgebraicClosure K)) := ⊥
    have hc0 : Continuous (c : Field.absoluteGaloisGroup K → pointsRep W (AlgebraicClosure K)) := hcont
    have := hc0.comp (Field.absoluteGaloisGroup.map (algebraMap K Kv)).continuous
    refine this.congr fun σ => ?_
    exact (congrArg (fun g => c g) (decompHom_apply (K := K) Kv σ)).symm
  obtain ⟨P, hP⟩ := (mem_coboundaries₁_iff' _).1
    (hinj c' hcont' ((mem_coboundaries₁_iff' _).2 hx))
  exact ⟨P, hP⟩

end Comparison

/-! ## The Tate–Shafarevich groups -/

section Global

variable {K : Type} [Field K] [DecidableEq K] [NumberField K] (W : WeierstrassCurve K)

/-- A class in Formal Conjectures' $Ш$ goes to a class in Milne's $Ш$. -/
theorem fcEquiv_mem_tateShafarevich (x : continuousCohomology 1 (fcRep W))
    (hx : x ∈ FormalConjectures.tateShafarevich W.toAffine) :
    fcH1 W x ∈ tateShafarevich K W := by
  rw [mem_tateShafarevich_iff]
  simp only [FormalConjectures.tateShafarevich, AddSubgroup.mem_inf,
    ContinuousCohomology.mem_tateShafarevich] at hx
  exact ⟨fcH1_mem W x, fun v => locPoints_eq_zero_of_restrict_eq_zero W _ x (hx.2 v),
    fun w => locPoints_eq_zero_of_restrict_eq_zero W _ x (hx.1 w)⟩

/-- Given local injectivity at every place, a class whose image is in Milne's $Ш$ is in Formal Conjectures'. -/
theorem mem_tateShafarevich_of_fcEquiv_mem (hloc : LocalPointsInjectiveEverywhere K W)
    (x : continuousCohomology 1 (fcRep W)) (hx : fcH1 W x ∈ tateShafarevich K W) :
    x ∈ FormalConjectures.tateShafarevich W.toAffine := by
  rw [mem_tateShafarevich_iff] at hx
  simp only [FormalConjectures.tateShafarevich, AddSubgroup.mem_inf, ContinuousCohomology.mem_tateShafarevich]
  exact ⟨fun w => restrict_eq_zero_of_locPoints_eq_zero W _ (hloc.2 w) x (hx.2.2 w),
    fun v => restrict_eq_zero_of_locPoints_eq_zero W _ (hloc.1 v) x (hx.2.1 v)⟩

/-- **Formal Conjectures' $Ш(E/K)$ embeds in Milne's**, unconditionally. -/
noncomputable def shaFCToMilne :
    FormalConjectures.tateShafarevich W.toAffine →+ tateShafarevich K W where
  toFun x := ⟨fcH1 W x, fcEquiv_mem_tateShafarevich W x x.2⟩
  map_zero' := Subtype.ext (fcH1_zero W)
  map_add' x y := Subtype.ext (fcH1_add W x y)

theorem shaFCToMilne_injective : Function.Injective (shaFCToMilne W) := by
  intro x y h
  have h' : fcH1 W x = fcH1 W y :=
    congrArg (fun z : tateShafarevich K W => (z : H1 (pointsRep W (AlgebraicClosure K)))) h
  exact Subtype.ext (fcH1_injective W h')

/-- **The two Tate–Shafarevich groups are isomorphic**, given local injectivity at every place. -/
noncomputable def shaEquiv (hloc : LocalPointsInjectiveEverywhere K W) :
    FormalConjectures.tateShafarevich W.toAffine ≃+ tateShafarevich K W :=
  AddEquiv.ofBijective (shaFCToMilne W) ⟨shaFCToMilne_injective W, fun y => by
    obtain ⟨x, hx⟩ := (fcEquiv W).surjective ⟨y.1, ((mem_tateShafarevich_iff K W _).1 y.2).1⟩
    have hx' : fcH1 W x = y := congrArg Subtype.val hx
    refine ⟨⟨x, mem_tateShafarevich_of_fcEquiv_mem W hloc x (by rw [hx']; exact y.2)⟩, ?_⟩
    exact Subtype.ext hx'⟩

end Global

/-- **`ShaComparison` from local injectivity**: the named comparison of the two Tate–Shafarevich groups over
$\mathbb Q$ follows from the named local statement `LocalPointsInjective`. -/
theorem shaComparison_of_localPointsInjective (h : LocalPointsInjective) : ShaComparison := by
  refine ⟨fun E _ => ?_⟩
  exact ⟨(shaEquiv E (h.holds E)).symm⟩

/-! ## Conjecture 10.5 against `StrongBSD` -/

section BSD

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **Conjecture 10.5 (corrected normalization) is Formal Conjectures' `StrongBSD` over $\mathbb Q$** for a minimal
equation, with Mordell's theorem proved; only the local statement `LocalPointsInjective` is assumed. -/
theorem conjecture10_5Corrected_iff_strongBSD_of_localPointsInjective (hloc : LocalPointsInjective)
    (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    Conjecture10_5Corrected E ↔ FormalConjectures.StrongBSD E.toAffine :=
  conjecture10_5Corrected_iff_strongBSD_rat E (shaComparison_of_localPointsInjective hloc) hmin

/-- In rank $0$, Conjecture 10.5 as printed is `StrongBSD`, assuming only `LocalPointsInjective`. -/
theorem conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_localPointsInjective (hloc : LocalPointsInjective)
    (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    rank E = 0 → (Conjecture10_5 E ↔ FormalConjectures.StrongBSD E.toAffine) :=
  conjecture10_5_iff_strongBSD_of_rank_eq_zero_rat E (shaComparison_of_localPointsInjective hloc) hmin

/-- In positive rank, `StrongBSD` refutes Conjecture 10.5 as printed, assuming only `LocalPointsInjective`. -/
theorem not_conjecture10_5_of_strongBSD_of_localPointsInjective (hloc : LocalPointsInjective)
    (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    0 < rank E → FormalConjectures.StrongBSD E.toAffine → ¬ Conjecture10_5 E :=
  not_conjecture10_5_of_strongBSD_rat E (shaComparison_of_localPointsInjective hloc) hmin

end BSD

end NumberFieldKB.MilneEC
