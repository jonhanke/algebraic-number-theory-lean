import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Stable
import NumberFieldKB.MilneCFT.Ch3Ramified

/-!
# Milne, *Class Field Theory*, Chapter III §2: Lemmas 2.3–2.5 (open subgroups with trivial cohomology)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

* `lemma_2_3` — Lemma 2.3 (an open $G$-stable subgroup of $\mathcal O_L$ with trivial cohomology; normal basis).
* `Lemma2_4` — Lemma 2.4 (named statement: the same for $U_L$, exponential map).
* `UnitsOpenFiniteIndex` — compactness of $U_L$ in the form used (named statement).
* `lemma_2_5` — Lemma 2.5: $h(U_L) = 1$, $h(L^\times) = n$ for $L/K$ cyclic, proved from the two inputs.
* `lemma_2_6_cyclic` — Lemma 2.6 for cyclic extensions, proved from Lemma 2.5.

"Open" in $L$ is expressed through the valuation: a subgroup of $\mathcal O_L$ is open iff it contains $c\,\mathcal O_L$
for some nonzero $c \in \mathcal O_K$, and a subgroup of $U_L$ is open iff it contains $1 + c\,\mathcal O_L$ for some
nonzero $c \in \mathfrak m_K$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Some nonzero `d ∈ 𝒪[K]` makes `d • (normal basis generator)` integral over `𝒪[K]`. -/
lemma exists_integral_normalGen (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] :
    ∃ d : 𝒪[K], d ≠ 0 ∧ IsIntegral 𝒪[K] (d • (IsGalois.normalBasis K L) 1) := by
  have hx : IsIntegral K ((IsGalois.normalBasis K L) 1) := Algebra.IsIntegral.isIntegral _
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors 𝒪[K])
    (Rₘ := K) _ hx
  exact ⟨m, nonZeroDivisors.coe_ne_zero m, hm⟩

/-- The `𝒪[K]`-span of the Galois conjugates of a generator `x` is Galois-stable. -/
lemma span_conj_stable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (x : L)
    (σ : Gal(L/K)) (y : L)
    (hy : y ∈ Submodule.span 𝒪[K] (Set.range fun g : Gal(L/K) => g x)) :
    σ y ∈ Submodule.span 𝒪[K] (Set.range fun g : Gal(L/K) => g x) := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, rfl⟩ := hz
    exact Submodule.subset_span ⟨σ * g, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul a z _ hz =>
    have : σ (a • z) = a • σ z := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact AlgEquiv.commutes σ (a : K)
    rw [this]; exact Submodule.smul_mem _ _ hz

/-- Coordinates of a combination of conjugates of `d • b 1` against the normal basis `b`. -/
lemma repr_sum_conj (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] (d : 𝒪[K])
    (c : Gal(L/K) → 𝒪[K]) (h : Gal(L/K)) :
    (IsGalois.normalBasis K L).repr
      (∑ g : Gal(L/K), c g • (g (d • (IsGalois.normalBasis K L) 1))) h = ((c h : K) * d) := by
  classical
  have hg : ∀ g : Gal(L/K), g (d • (IsGalois.normalBasis K L) 1) =
      ((d : K)) • (IsGalois.normalBasis K L) g := by
    intro g
    rw [IsGalois.normalBasis_apply g]
    exact map_smul g (d : K) ((IsGalois.normalBasis K L) 1)
  simp only [hg, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  have : ∀ g : Gal(L/K), (IsGalois.normalBasis K L).repr
      (c g • ((d : K) • (IsGalois.normalBasis K L) g)) h =
      if g = h then (c g : K) * d else 0 := by
    intro g
    have e : c g • ((d : K) • (IsGalois.normalBasis K L) g) =
        ((c g : K) * d) • (IsGalois.normalBasis K L) g := by
      rw [← smul_assoc]; rfl
    rw [e, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hgh : g = h <;> simp [hgh]
  simp only [this]
  simp

/-- **Lemma 2.3** (p. 104). Let $L/K$ be finite Galois with group $G$. There is an open subgroup $V$ of
$\mathcal O_L$, stable under $G$, with $H^r(G, V) = 0$ for all $r > 0$ ("open": $V \supseteq c\,\mathcal O_L$ for
some nonzero $c \in \mathcal O_K$). Milne's proof: $V = \sum_\sigma \mathcal O_K\,\sigma x$ for a normal basis
$\{\sigma x\}$ scaled into $\mathcal O_L$; $V \simeq \operatorname{Ind}^G \mathcal O_K$ is induced (Chapter II,
Corollary 1.12), and $V$ contains $c\,\mathcal O_L$ because $\mathcal O_L$ is a finitely generated
$\mathcal O_K$-module. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.3, p. 104"]
theorem lemma_2_3 (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] :
    ∃ (V : AddSubgroup (addRep L)) (hV : ∀ (σ : Gal(L/K)), ∀ x ∈ V, (addRep L).ρ σ x ∈ V),
      (∀ x ∈ V, (x : L) ∈ integers L) ∧
      (∃ c : 𝒪[K], c ≠ 0 ∧ ∀ y ∈ integers L, algebraMap K L c * y ∈ V) ∧
      ∀ r : ℕ, 0 < r → IsZero (groupCohomology (stableRep (addRep L) V hV) r) := by
  classical
  obtain ⟨d, hd0, hdint⟩ := exists_integral_normalGen L
  set b := IsGalois.normalBasis K L with hb
  set x : L := d • b 1 with hx
  have hgx : ∀ g : Gal(L/K), g x = (d : K) • b g := by
    intro g
    rw [hb, IsGalois.normalBasis_apply g]
    exact map_smul g (d : K) ((IsGalois.normalBasis K L) 1)
  have hxint : ∀ g : Gal(L/K), IsIntegral 𝒪[K] (g x) := fun g =>
    hdint.map (g.restrictScalars 𝒪[K])
  let V : Submodule 𝒪[K] L := Submodule.span 𝒪[K] (Set.range fun g : Gal(L/K) => g x)
  have hVs : ∀ σ : Gal(L/K), ∀ y ∈ V, σ y ∈ V := fun σ y hy => span_conj_stable L x σ y hy
  have hVint : ∀ y ∈ V, y ∈ integers L := by
    intro y hy
    have : V ≤ Subalgebra.toSubmodule (integers L) :=
      Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hxint g)
    exact this hy
  have key : ∀ c c' : Gal(L/K) → 𝒪[K], ∑ g, c g • g x = ∑ g, c' g • g x → c = c' := by
    intro c c' h
    funext g
    have h1 := congrArg (fun y => b.repr y g) h
    have h2 : (c g : K) * d = (c' g : K) * d :=
      (repr_sum_conj L d c g).symm.trans (h1.trans (repr_sum_conj L d c' g))
    have hd : (d : K) ≠ 0 := by simpa using hd0
    exact Subtype.ext (mul_right_cancel₀ hd h2)
  let Vg : AddSubgroup (addRep L) := V.toAddSubgroup
  have hVg : ∀ (σ : Gal(L/K)), ∀ y ∈ Vg, (addRep L).ρ σ y ∈ Vg := fun σ y hy => hVs σ y hy
  refine ⟨Vg, hVg, fun y hy => hVint y hy, ?_, ?_⟩
  · obtain ⟨s, hs⟩ : (⊤ : Submodule 𝒪[K] (integers L)).FG :=
      Module.finite_def.1 (IsIntegralClosure.finite 𝒪[K] K L (integers L))
    obtain ⟨c0, hc0⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors 𝒪[K])
      (S := K) ((s ×ˢ (Finset.univ : Finset Gal(L/K))).image
        fun p => b.repr (p.1 : L) p.2)
    have claim : ∀ z ∈ Submodule.span 𝒪[K] (s : Set (integers L)),
        algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * (z : L) ∈ V := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        have hz' : ∀ g : Gal(L/K), ∃ a : 𝒪[K], (a : K) = (c0 : 𝒪[K]) * b.repr (z : L) g := by
          intro g
          have := hc0 (b.repr (z : L) g) (Finset.mem_image.2 ⟨(z, g), by simpa using hz, rfl⟩)
          obtain ⟨a, ha⟩ := this
          refine ⟨a, ?_⟩
          have ha' : algebraMap 𝒪[K] K a = _ := ha
          rw [Submonoid.smul_def, Algebra.smul_def] at ha'
          exact ha'
        choose a ha using hz'
        have e : algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * (z : L) =
            ∑ g, a g • g x := by
          conv_lhs => rw [← b.sum_repr (z : L)]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hgx g]
          have h3 : a g • ((d : K) • b g) = ((a g : K) * d) • b g := by
            rw [← smul_assoc]; rfl
          rw [h3, ← Algebra.smul_def, smul_smul, ha g]
          congr 1
          push_cast
          ring
        rw [e]
        exact (Submodule.mem_span_range_iff_exists_fun 𝒪[K]).2 ⟨a, rfl⟩
      | zero => simp
      | add u w _ _ hu hw =>
        have : algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * ((u + w : integers L) : L) =
            algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * (u : L) +
            algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * (w : L) := by
          push_cast; ring
        rw [this]; exact add_mem hu hw
      | smul a u _ hu =>
        have : algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * ((a • u : integers L) : L) =
            a • (algebraMap K L (((c0 : 𝒪[K]) * d : 𝒪[K]) : K) * (u : L)) := by
          rw [Subalgebra.coe_smul, mul_smul_comm]
        rw [this]; exact Submodule.smul_mem _ _ hu
    refine ⟨(c0 : 𝒪[K]) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero c0) hd0, fun y hy => ?_⟩
    have hmem : (⟨y, hy⟩ : integers L) ∈ Submodule.span 𝒪[K] (s : Set (integers L)) := by
      rw [hs]; trivial
    exact claim _ hmem
  · intro r hr
    apply cor_1_12 _ r hr
    let M := stableRep (addRep L) Vg hVg
    have hxV : ∀ a : 𝒪[K], (a • x : L) ∈ V := fun a =>
      Submodule.smul_mem _ a (Submodule.subset_span ⟨1, by simp [hx]⟩)
    let ι : 𝒪[K] →+ M := AddMonoidHom.mk' (fun a => (⟨(a • x : L), hxV a⟩ : Vg)) (fun a a' =>
      Subtype.ext (add_smul a a' x))
    let val : M →+ L := AddMonoidHom.mk' (fun v : M => ((show Vg from v).1 : L)) (fun _ _ => rfl)
    have hval : ∀ (g : Gal(L/K)) (v : M), val (M.ρ g v) = g (val v) := fun g v => rfl
    have hι : ∀ a, val (ι a) = a • x := fun a => rfl
    have hs : ∀ (f : Gal(L/K) → ι.range) (c : Gal(L/K) → 𝒪[K]), (∀ g, ι (c g) = f g) →
        val (sumMap M ι.range f) = ∑ g, c g • g x := by
      intro f c hc
      change val (∑ g, M.ρ g (f g : M)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hval, ← hc g, hι]
      exact map_smul g (c g : K) x
    refine isInduced_of_sumMap_bijective M ι.range ⟨?_, ?_⟩
    · intro f f' hff
      have hch : ∀ f : Gal(L/K) → ι.range, ∃ c : Gal(L/K) → 𝒪[K], ∀ g, ι (c g) = f g := by
        intro f
        exact ⟨fun g => (f g).2.choose, fun g => (f g).2.choose_spec⟩
      obtain ⟨c, hc⟩ := hch f
      obtain ⟨c', hc'⟩ := hch f'
      have h1 := congrArg val hff
      rw [hs f c hc, hs f' c' hc'] at h1
      have := key c c' h1
      subst this
      funext g
      exact Subtype.ext ((hc g).symm.trans (hc' g))
    · intro m
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[K]).1 (show val m ∈ V from m.2)
      refine ⟨fun g => ⟨ι (c g), ⟨c g, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      exact (hs _ c (fun g => rfl)).trans hc

variable (K Ω) in
/-- **Lemma 2.4** (named statement; Milne, p. 104). Let $L/K$ be finite Galois with group $G$. There is an open
subgroup $V$ of $U_L$, stable under $G$, with $H^r(G, V) = 0$ for all $r > 0$. "Open" is expressed as: $V$ contains
$1 + c\,\mathcal O_L$ for some nonzero $c \in \mathfrak m_K$ (these sets $U_L^{(m)}$ form a basis of neighbourhoods
of $1$). Milne proves it only for $K$ of characteristic zero, with the exponential map applied to a lattice as in
Lemma 2.3; for characteristic $p$ he refers to Serre, *Local Fields*. -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.4, p. 104 (input)"]
structure Lemma2_4 : Prop where
  exists_sub : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L],
    ∃ (V : Subgroup Lˣ) (hV : ∀ (σ : Gal(L/K)), ∀ x ∈ unitsSub L V, (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ unitsSub L V),
      V ≤ unitsL L ∧
      (∃ c : 𝒪[K], c ≠ 0 ∧ c ∈ 𝓂[K] ∧ ∀ y ∈ integers L, ∀ h : 1 + algebraMap K L c * y ≠ 0,
        Units.mk0 _ h ∈ V) ∧
      ∀ r : ℕ, 0 < r → IsZero (groupCohomology (stableRep (Rep.ofAlgebraAutOnUnits K L) (unitsSub L V) hV) r)

variable (K Ω) in
/-- **$U_L$ is compact** (named; Milne, p. 104, "because $U_L$ is compact"), in the form used: an open subgroup
$V \subseteq U_L$ (one containing $1 + c\mathcal O_L$ for some nonzero $c \in \mathfrak m_K$) has finite index. -/
@[kb "milne2020cft" "v4.03, Ch. III, proof of Lemma 2.5, U_L compact, p. 104 (input)"]
structure UnitsOpenFiniteIndex : Prop where
  finiteIndex : ∀ (L : IntermediateField K Ω) [FiniteDimensional K L] (V : Subgroup Lˣ), V ≤ unitsL L →
    (∃ c : 𝒪[K], c ≠ 0 ∧ c ∈ 𝓂[K] ∧ ∀ y ∈ integers L, ∀ h : 1 + algebraMap K L c * y ≠ 0,
        Units.mk0 _ h ∈ V) →
    (V.subgroupOf (unitsL L)).FiniteIndex

section helpers

/-- A module over a finite cyclic group with vanishing higher cohomology has Herbrand quotient $1$. -/
theorem herbrand_of_acyclic {G : Type} [Group G] [Fintype G] [IsCyclic G] (M : Rep ℤ G)
    (h : ∀ r : ℕ, 0 < r → IsZero (groupCohomology M r)) :
    HerbrandDefined M ∧ herbrandQuotient M = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  let e1 := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app M
  let e0 := periodicity g hg M 0 ≪≫ (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app M
  have s1 : Subsingleton (tateCohomology M 1) :=
    (ModuleCat.isZero_iff_subsingleton.1 ((h 1 one_pos).of_iso e1))
  have s0 : Subsingleton (tateCohomology M 0) :=
    (ModuleCat.isZero_iff_subsingleton.1 ((h 2 two_pos).of_iso e0))
  refine ⟨⟨Finite.of_subsingleton, Finite.of_subsingleton⟩, ?_⟩
  unfold herbrandQuotient
  rw [Nat.card_unique, Nat.card_unique]
  norm_num

/-- The Herbrand quotient of the trivial module $\mathbb Z$ is $|G|$. -/
theorem herbrand_trivial_int {G : Type} [Group G] [Fintype G] [IsCyclic G] :
    HerbrandDefined (trivial ℤ G ℤ) ∧ herbrandQuotient (trivial ℤ G ℤ) = Fintype.card G := by
  obtain ⟨⟨e⟩, h1⟩ := lemma_3_3b (G := G)
  let e1 := (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 1).app (trivial ℤ G ℤ)
  have s1 : Subsingleton (tateCohomology (trivial ℤ G ℤ) 1) :=
    (ModuleCat.isZero_iff_subsingleton.1 (h1.of_iso e1))
  have c0 : Nat.card (tateCohomology (trivial ℤ G ℤ) 0) = Fintype.card G := by
    rw [Nat.card_congr e.toEquiv]; simp
  have : Finite (tateCohomology (trivial ℤ G ℤ) 0) := by
    have : 0 < Nat.card (tateCohomology (trivial ℤ G ℤ) 0) := by
      rw [c0]; exact Fintype.card_pos
    exact Nat.finite_of_card_ne_zero this.ne'
  refine ⟨⟨inferInstance, Finite.of_subsingleton⟩, ?_⟩
  unfold herbrandQuotient
  rw [Nat.card_unique (α := tateCohomology (trivial ℤ G ℤ) 1), c0]
  simp

/-- The inclusion $V \to U_L$ of $G$-modules. -/
noncomputable def stableToUnits (L : IntermediateField K Ω) (V : Subgroup Lˣ) (hVU : V ≤ unitsL L)
    (hV : ∀ (σ : Gal(L/K)), ∀ x ∈ unitsSub L V, (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ unitsSub L V) :
    stableRep (Rep.ofAlgebraAutOnUnits K L) (unitsSub L V) hV ⟶ unitsRep L :=
  Rep.ofHom ⟨AddMonoidHom.toIntLinearMap
    { toFun := fun x : unitsSub L V => Additive.ofMul (⟨Additive.toMul x.1, hVU x.2⟩ : unitsL L)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }, fun σ => by
    ext x; rfl⟩

theorem stableToUnits_injective (L : IntermediateField K Ω) (V : Subgroup Lˣ) (hVU : V ≤ unitsL L)
    (hV : ∀ (σ : Gal(L/K)), ∀ x ∈ unitsSub L V, (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ unitsSub L V) :
    Function.Injective (stableToUnits L V hVU hV).hom := by
  intro a b h
  have h2 : (Additive.toMul ((stableToUnits L V hVU hV).hom a) : unitsL L) =
      Additive.toMul ((stableToUnits L V hVU hV).hom b) := congrArg Additive.toMul h
  have h3 : (Additive.toMul a.1 : Lˣ) = Additive.toMul b.1 :=
    congrArg (Subtype.val : unitsL L → Lˣ) h2
  exact Subtype.ext (Additive.toMul.injective h3)

theorem stableToUnits_coker_finite (L : IntermediateField K Ω) (V : Subgroup Lˣ) (hVU : V ≤ unitsL L)
    (hV : ∀ (σ : Gal(L/K)), ∀ x ∈ unitsSub L V, (Rep.ofAlgebraAutOnUnits K L).ρ σ x ∈ unitsSub L V)
    (hfi : (V.subgroupOf (unitsL L)).FiniteIndex) :
    Finite (unitsRep L ⧸ LinearMap.range (stableToUnits L V hVU hV).hom.toLinearMap) := by
  have : Finite (unitsL L ⧸ V.subgroupOf (unitsL L)) := Subgroup.finite_quotient_of_finiteIndex
  refine Finite.of_surjective
    (Quotient.lift (s := QuotientGroup.leftRel (V.subgroupOf (unitsL L)))
      (fun a : unitsL L => (Submodule.Quotient.mk (Additive.ofMul a) :
        unitsRep L ⧸ LinearMap.range (stableToUnits L V hVU hV).hom.toLinearMap)) ?_) ?_
  · intro a b hab
    have hab' : a⁻¹ * b ∈ V.subgroupOf (unitsL L) := QuotientGroup.leftRel_apply.1 hab
    apply (Submodule.Quotient.eq _).2
    have hab'' : (b⁻¹ * a : unitsL L) ∈ V.subgroupOf (unitsL L) := by
      have := inv_mem hab'
      rwa [mul_inv_rev, inv_inv] at this
    refine ⟨⟨Additive.ofMul (b⁻¹ * a : unitsL L).1, hab''⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    show (b⁻¹ * a : unitsL L).1 = (a * b⁻¹ : unitsL L).1
    rw [mul_comm]
  · intro q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Quotient.mk _ (Additive.toMul x), rfl⟩

end helpers

/-- The Herbrand quotients of $U_L$ and $L^\times$ (Lemma 2.5), packaged. -/
theorem lemma_2_5_aux (h24 : Lemma2_4 K Ω) (hfin : UnitsOpenFiniteIndex K Ω) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) :
    HerbrandDefined (unitsRep L) ∧ herbrandQuotient (unitsRep L) = 1 ∧
      HerbrandDefined (Rep.ofAlgebraAutOnUnits K L) ∧
      herbrandQuotient (Rep.ofAlgebraAutOnUnits K L) = Fintype.card Gal(L/K) := by
  obtain ⟨V, hV, hVU, hc, hac⟩ := h24.exists_sub L
  have hfi := hfin.finiteIndex L V hVU hc
  obtain ⟨hd, hq⟩ := herbrand_of_acyclic _ hac
  have hker : Finite (LinearMap.ker (stableToUnits L V hVU hV).hom.toLinearMap) := by
    have : Subsingleton (LinearMap.ker (stableToUnits L V hVU hV).hom.toLinearMap) := by
      refine ⟨fun x y => Subtype.ext (stableToUnits_injective L V hVU hV ?_)⟩
      have hx : (stableToUnits L V hVU hV).hom x.1 = 0 := LinearMap.mem_ker.1 x.2
      have hy : (stableToUnits L V hVU hV).hom y.1 = 0 := LinearMap.mem_ker.1 y.2
      rw [hx, hy]
    infer_instance
  have hc9 := cor_3_9 (stableToUnits L V hVU hV) hker (stableToUnits_coker_finite L V hVU hV hfi)
  have hdU : HerbrandDefined (unitsRep L) := hc9.1.1 hd
  have hqU : herbrandQuotient (unitsRep L) = 1 := by rw [← hc9.2 hd]; exact hq
  have hS := prop_3_6 (ordSeq_shortExact hv)
  obtain ⟨hZd, hZq⟩ := herbrand_trivial_int (G := Gal(L/K))
  have hZd' : HerbrandDefined (ordSeq hv).X₃ := hZd
  have hdL := hS.1.2.1 hdU hZd'
  refine ⟨hdU, hqU, hdL, ?_⟩
  have h3 : herbrandQuotient (Rep.ofAlgebraAutOnUnits K L) =
      herbrandQuotient (unitsRep L) * herbrandQuotient (trivial ℤ Gal(L/K) ℤ) := hS.2 hdU hdL hZd'
  rw [h3, hqU, one_mul]
  exact hZq

/-- **Lemma 2.5** (p. 104). Let $L/K$ be a cyclic extension of degree $n$; then $h(U_L) = 1$ and $h(L^\times) = n$
(both Herbrand quotients are defined). Milne's proof: $h(U_L) = h(V) = 1$ for the open subgroup $V$ of Lemma 2.4
($U_L/V$ is finite since $U_L$ is compact; Chapter II, Corollary 3.9), and $h(L^\times) = h(U_L)\,h(\mathbb Z) = n$
from $0 \to U_L \to L^\times \xrightarrow{\mathrm{ord}_L} \mathbb Z \to 0$ ($v = \mathrm{ord}_L$). -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.5, p. 104"]
theorem lemma_2_5 (h24 : Lemma2_4 K Ω) (hfin : UnitsOpenFiniteIndex K Ω) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) :
    HerbrandDefined (unitsRep L) ∧ herbrandQuotient (unitsRep L) = 1 ∧
      HerbrandDefined (Rep.ofAlgebraAutOnUnits K L) ∧
      herbrandQuotient (Rep.ofAlgebraAutOnUnits K L) = Module.finrank K L := by
  obtain ⟨a, b, c, d⟩ := lemma_2_5_aux h24 hfin L hv
  refine ⟨a, b, c, ?_⟩
  rw [d, ← IsGalois.card_aut_eq_finrank K L, Nat.card_eq_fintype_card]

/-- **Lemma 2.6**, cyclic case (p. 105: "it equals $n$ when $L/K$ is cyclic"): $|H^2(L/K)| = [L:K]$, from
$h(L^\times) = n$ (Lemma 2.5), $H^1(G, L^\times) = 0$ (Hilbert's Theorem 90) and periodicity. (The general case is
`lemma_2_6`, from the system of invariant maps.) -/
@[kb "milne2020cft" "v4.03, Ch. III, Lemma 2.6 (cyclic case), p. 105"]
theorem lemma_2_6_cyclic (h24 : Lemma2_4 K Ω) (hfin : UnitsOpenFiniteIndex K Ω) (L : IntermediateField K Ω)
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] {v : Additive Lˣ →+ ℤ} (hv : IsNormalizedOrd L v) :
    Nat.card (H2 L) = Module.finrank K L := by
  obtain ⟨a, b, c, d⟩ := lemma_2_5 h24 hfin L hv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let M := Rep.ofAlgebraAutOnUnits K L
  let e1 : tateCohomology M 1 ≅ groupCohomology M 1 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L/K)) 1).app M
  let e0 : tateCohomology M 0 ≅ groupCohomology M 2 :=
    periodicity g hg M 0 ≪≫ (TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L/K)) 2).app M
  have h1 : Nat.card (tateCohomology M 1) = 1 := by
    have : Subsingleton (groupCohomology M 1) :=
      ModuleCat.isZero_iff_subsingleton.1 (ModuleCat.isZero_of_subsingleton _)
    rw [Nat.card_congr e1.toLinearEquiv.toEquiv]; exact Nat.card_unique
  have c0 : Nat.card (tateCohomology M 0) = Nat.card (groupCohomology M 2) :=
    Nat.card_congr e0.toLinearEquiv.toEquiv
  unfold herbrandQuotient at d
  rw [h1, c0] at d
  have hpos : 0 < Nat.card (groupCohomology M 2) := by
    have : Finite (tateCohomology M 0) := c.1
    rw [← c0]; exact Nat.card_pos
  have : (Nat.card (groupCohomology M 2) : ℚ) = Module.finrank K L := by simpa using d
  exact_mod_cast this

end NumberFieldKB.MilneCFT.Ch3
