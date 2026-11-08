import NumberFieldKB.MilneCFT.Ch5Artin

/-!
# The main theorems in terms of ideals (Milne, *Class Field Theory*, Chapter V, §3, pp. 157–160)

* `AdmitsModulus` (p. 157) and `admitsModulus_iff_factors` ("admits a modulus iff it factors through some
  $C_\mathfrak m$");
* **Theorem 3.5** (the reciprocity law): the named statement `ReciprocityLaw`, with `IsDefiningModulus` (p. 158);
* `IsCongruenceSubgroupMod` (p. 158) and **Theorem 3.6** (the existence theorem): the named statement
  `ExistenceTheorem`, as Milne states it;
* the note after Theorem 3.6 (the Artin map induces $I^{S(\mathfrak m)}/H \cong \mathrm{Gal}(L/K)$; ray class
  fields). As stated it is false (see `Erratum` below); its corrected form is the named statement
  `ExistenceTheoremArtin`, the existence theorem with the Artin isomorphism. Consequences: `ExistenceTheorem` and the
  ray class field `exists_rayClassField`, the residue degree formula `inertiaDeg_eq_orderOf` (p. 160), and the
  comparison with the Introduction: `ReciprocityLaw` gives the Introduction's `ArtinReciprocity`
  (`artinReciprocity_of_reciprocityLaw`).

**Erratum (the note after Theorem 3.6).** Milne: "for $H$ and $L$ as in the theorem, the Artin map induces an
isomorphism $I^{S(\mathfrak m)}/H \to \mathrm{Gal}(L/K)$". Theorem 3.6 only asks $L$ to be unramified outside
$\mathfrak m$ with $H = i(K_{\mathfrak m,1})\cdot\mathrm{Nm}(I_L^{\mathfrak m})$, and that does not determine $L$: for
$K = \mathbb Q$, $\mathfrak m = (3)$, $H = I^{S(\mathfrak m)}$ (so $C_\mathfrak m/H$ is trivial, as
$C_{(3)} \cong (\mathbb Z/3)^\times/\{\pm1\} = 1$), both $L = \mathbb Q$ and the real cubic field
$L = \mathbb Q(\zeta_9)^+$ (unramified outside $3$, real) satisfy the conclusion, but $\mathrm{Gal}(L/\mathbb Q)$ has
order $3$ for the second. The note holds for the class field of $H$, the $L$ whose Artin kernel is $H$
(equivalently, with $[L:K] = (I^{S(\mathfrak m)} : H)$).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-! ## Admitting a modulus (p. 157) -/

/-- **A homomorphism admits a modulus** (Milne, *CFT*, V, §3, p. 157): $\varphi : I^S \to G$ admits a modulus if there is
a modulus $\mathfrak m$ with $S(\mathfrak m) \subseteq S$ such that $\varphi(i(K_{\mathfrak m,1})) = 1$. Here $S$ is a set
of finite primes and $T$ a set of real places (Milne's $S$ may contain infinite primes: they are $T$); the condition is
on the $a \in K_{\mathfrak m,1}$ with $(a) \in I^S$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 157 (a homomorphism admits a modulus)"]
def AdmitsModulus {G : Type*} [Group G] (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (InfinitePlace K))
    (φ : sIdeals S →* G) : Prop :=
  ∃ m : Modulus K, m.finiteSupport ⊆ S ∧ m.infinite ⊆ T ∧
    ∀ a : Kˣ, a ∈ congruenceSubgroup m → ∀ h : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S, φ ⟨_, h⟩ = 1

/-- The inclusion $I^S \hookrightarrow I^{S(\mathfrak m)}$ for $S(\mathfrak m) \subseteq S$, followed by
$I^{S(\mathfrak m)} \to C_\mathfrak m$. -/
def sIdealsToRay (m : Modulus K) (S : Set (HeightOneSpectrum (𝓞 K))) (h : m.finiteSupport ⊆ S) :
    sIdeals S →* RayClassGroup m :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion (fun _ hI v hv => hI v (h hv)))

/-- The modulus $\mathfrak m$ with the primes of a finite set $S$ adjoined to its finite part: the finite part is
$\mathfrak m_0\prod_{\mathfrak p\in S}\mathfrak p$ and the infinite part is unchanged. -/
def Modulus.adjoin (m : Modulus K) (S : Finset (HeightOneSpectrum (𝓞 K))) : Modulus K where
  finite := m.finite * ∏ v ∈ S, v.asIdeal
  finite_ne_bot := mul_ne_zero m.finite_ne_bot (Finset.prod_ne_zero_iff.2 fun v _ => v.ne_bot)
  infinite := m.infinite
  isReal_of_mem := m.isReal_of_mem

/-- A prime divides the finite part of `m.adjoin S` iff it divides that of `m` or lies in `S`. -/
theorem Modulus.mem_finiteSupport_adjoin (m : Modulus K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ (m.adjoin S).finiteSupport ↔ v ∈ m.finiteSupport ∨ v ∈ S := by
  show v.asIdeal ∣ m.finite * ∏ w ∈ S, w.asIdeal ↔ v.asIdeal ∣ m.finite ∨ v ∈ S
  rw [v.prime.dvd_mul, v.prime.dvd_finsetProd_iff]
  refine or_congr Iff.rfl ⟨fun ⟨w, hw, h⟩ => ?_, fun h => ⟨v, h, dvd_rfl⟩⟩
  have : v = w :=
    HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 h)).symm
  exact this ▸ hw

/-- Adjoining primes to the finite part of a modulus shrinks the congruence subgroup. -/
theorem congruenceSubgroup_adjoin_le (m : Modulus K) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    congruenceSubgroup (m.adjoin S) ≤ congruenceSubgroup m := by
  rintro a ⟨h1, h2⟩
  refine ⟨h1, fun v hv => ?_⟩
  have hdvd : m.finite ∣ (m.adjoin S).finite := dvd_mul_right _ _
  refine (h2 v (hv.trans hdvd)).trans ?_
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le]
  unfold Modulus.ord
  refine Associates.count_le_count_of_le ?_ (Associates.irreducible_mk.2 v.irreducible) ?_
  · exact (Associates.mk_ne_zero.2 (m.adjoin S).finite_ne_bot)
  · exact Associates.mk_le_mk_iff_dvd.2 hdvd

/-- "$\varphi$ admits a modulus iff it factors through $C_\mathfrak m$ for some $\mathfrak m$ with
$S(\mathfrak m) \subseteq S$" (Milne, *CFT*, V, §3, p. 157), for $S$ finite. -/
@[kb "milne2020cft" "Ch. V, §3, p. 157 (admits a modulus iff it factors through some C_m)"]
theorem admitsModulus_iff_factors {G : Type*} [Group G] (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (T : Set (InfinitePlace K)) (φ : sIdeals S →* G) :
    AdmitsModulus S T φ ↔ ∃ (m : Modulus K) (h : m.finiteSupport ⊆ S), m.infinite ⊆ T ∧
      ∃ ψ : RayClassGroup m →* G, φ = ψ.comp (sIdealsToRay m S h) := by
  constructor
  · rintro ⟨m, hmS, hmT, hφ⟩
    classical
    set m' := m.adjoin hS.toFinset with hm'
    have hsupp : m'.finiteSupport = S := by
      ext v
      rw [hm', Modulus.mem_finiteSupport_adjoin]
      simp only [Set.Finite.mem_toFinset]
      exact ⟨fun h => h.elim (fun h => hmS h) id, Or.inr⟩
    have hsub : m'.finiteSupport ⊆ S := hsupp.le
    refine ⟨m', hsub, hmT, ?_⟩
    have hsurj : Function.Surjective (sIdealsToRay m' S hsub) := by
      intro c
      induction c using QuotientGroup.induction_on with | H x => ?_
      exact ⟨⟨x, fun v hv => x.2 v (show v ∈ m'.finiteSupport from hsupp ▸ hv)⟩, rfl⟩
    have hker : (sIdealsToRay m' S hsub).ker ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker]
      simp only [sIdealsToRay, MonoidHom.comp_apply, QuotientGroup.mk'_apply] at hx
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
      have hx' := hx
      obtain ⟨a, ha, hax⟩ := hx'
      have h2 : toPrincipalIdeal (𝓞 K) K a ∈ sIdeals S := by
        rw [show toPrincipalIdeal (𝓞 K) K a = (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) from hax]
        exact x.2
      exact (congrArg φ (Subtype.ext hax.symm)).trans
        (hφ a (congruenceSubgroup_adjoin_le m _ ha) h2)
    exact ⟨(sIdealsToRay m' S hsub).liftOfSurjective hsurj ⟨φ, hker⟩,
      (MonoidHom.liftOfRightInverse_comp (sIdealsToRay m' S hsub) _ (Function.rightInverse_surjInv hsurj)
        ⟨φ, hker⟩).symm⟩
  · rintro ⟨m, h, hT, ψ, rfl⟩
    refine ⟨m, h, hT, fun a ha ha' => ?_⟩
    have : sIdealsToRay m S h ⟨_, ha'⟩ = 1 := by
      show (QuotientGroup.mk _ : RayClassGroup m) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact ⟨a, ha, rfl⟩
    rw [MonoidHom.comp_apply, this, map_one]

/-! ## Theorem 3.5: the reciprocity law -/

section FrobeniusHelpers

variable {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The order of the Frobenius element at an unramified prime is the residue degree. -/
theorem orderOf_frobAt_eq [IsGalois K L] (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ unramifiedPrimes K L)
    (Q : v.asIdeal.primesOver (𝓞 L)) : orderOf (frobAt K L v Q) = Q.1.inertiaDeg (𝓞 K) := by
  have := Q.2.1
  have := Q.2.2
  have : Finite (𝓞 L ⧸ Q.1) :=
    finite_quotient_of_ne_bot Q.1 (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1)
  have : Algebra.IsUnramifiedAt (𝓞 K) Q.1 := hv Q.1 Q.2.1 Q.2.2
  exact orderOf_arithFrobAt_nf Q.1

/-- The Artin map sends the prime $\mathfrak p \nmid \mathfrak m_0$ (as an element of $I^{S(\mathfrak m)}$) to its
Frobenius element. -/
theorem artinMap_coprimePrime [IsAbelianGalois K L] (m : Modulus K) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ m.finite) :
    artinMap L m.finiteSupport (coprimePrime m v hv) = artinFrob L v :=
  artinMap_prime L m.finiteSupport v (coprimePrime m v hv) rfl

end FrobeniusHelpers

section Reciprocity

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- **A defining modulus** of a finite abelian extension $L/K$ (Milne, *CFT*, V, §3, p. 158, after Theorem 3.5): a
modulus $\mathfrak m$ whose support $S(\mathfrak m)$ is the set of primes (finite and real) ramified in $L$, such that
the Artin map $\psi_{L/K} : I^{S(\mathfrak m)} \to \mathrm{Gal}(L/K)$ admits $\mathfrak m$ and induces an isomorphism
$I^{S(\mathfrak m)}/i(K_{\mathfrak m,1})\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)}) \cong \mathrm{Gal}(L/K)$: it is onto, with
kernel $i(K_{\mathfrak m,1})\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 158 (defining modulus)"]
structure IsDefiningModulus (m : Modulus K) : Prop where
  finiteSupport_eq : m.finiteSupport = (unramifiedPrimes K L)ᶜ
  infinite_iff : ∀ w : InfinitePlace K, w ∈ m.infinite ↔ InfinitePlace.RamifiesIn L w
  surjective : Function.Surjective (artinMap L m.finiteSupport)
  ker_eq : (artinMap L m.finiteSupport).ker =
    (rayPrincipal m ⊔ normIdeals K L m.finiteSupport).subgroupOf (sIdeals m.finiteSupport)

variable (K) in
/-- **Theorem 3.5, the reciprocity law** (named statement; Milne, *CFT*, V, Theorem 3.5, p. 158; proved in Chapter VII
from the idelic form, Theorem 5.3): for every finite abelian extension $L/K$, with $S$ the set of primes of $K$
ramifying in $L$, the Artin map $\psi_{L/K} : I^S \to \mathrm{Gal}(L/K)$ admits a modulus $\mathfrak m$ with
$S(\mathfrak m) = S$, and defines an isomorphism
$I^{S(\mathfrak m)}/i(K_{\mathfrak m,1})\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)}) \cong \mathrm{Gal}(L/K)$: every finite
abelian extension has a defining modulus. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.5 (input)"]
structure ReciprocityLaw : Prop where
  exists_definingModulus : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L],
    ∃ m : Modulus K, IsDefiningModulus L m

/-- A defining modulus is admitted by the Artin map: $\psi_{L/K}(i(K_{\mathfrak m,1})) = 1$. -/
theorem IsDefiningModulus.admits {m : Modulus K} (h : IsDefiningModulus L m) :
    AdmitsModulus m.finiteSupport m.infinite (artinMap L m.finiteSupport) := by
  refine ⟨m, subset_rfl, subset_rfl, fun a ha ha' => ?_⟩
  have : (⟨_, ha'⟩ : sIdeals m.finiteSupport) ∈ (artinMap L m.finiteSupport).ker := by
    rw [h.ker_eq, Subgroup.mem_subgroupOf]
    exact (le_sup_left : rayPrincipal m ≤ _) ⟨a, ha, rfl⟩
  exact this

/-- **Theorem 3.5 gives the Introduction's Theorem 0.8** (`ArtinReciprocity`): the Artin map factors through
$C_\mathfrak m$, sends $[\mathfrak p]$ to $\mathrm{Frob}_\mathfrak P$, is onto, and its kernel is generated by the classes
of the norms $\mathfrak p^{f(\mathfrak P/\mathfrak p)}$ of the primes of $L$ not above $\mathfrak m_0$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.5 (gives Introduction, Theorem 0.8)"]
theorem artinReciprocity_of_reciprocityLaw (h : ReciprocityLaw K) : ArtinReciprocity K := by
  refine ⟨fun L _ _ _ _ hab => ?_⟩
  have : IsAbelianGalois K L := { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨hab⟩⟩ }
  obtain ⟨m, hm⟩ := h.exists_definingModulus L
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite → v ∈ unramifiedPrimes K L :=
    fun v hv => by
      by_contra hc
      exact hv (show v ∈ m.finiteSupport by rw [hm.finiteSupport_eq]; exact hc)
  refine ⟨m, fun v => ?_, hm.infinite_iff, ?_⟩
  · constructor
    · intro hd hu
      have : v ∈ m.finiteSupport := hd
      rw [hm.finiteSupport_eq] at this
      exact this hu
    · intro hu
      by_contra hd
      exact hu (hunr v hd)
  have hle : (rayPrincipal m).subgroupOf (coprimeIdeals m) ≤ (artinMap L m.finiteSupport).ker := by
    intro x hx
    have : (⟨(x : (FractionalIdeal (𝓞 K)⁰ K)ˣ), x.2⟩ : sIdeals m.finiteSupport) ∈
        (artinMap L m.finiteSupport).ker := by
      rw [hm.ker_eq, Subgroup.mem_subgroupOf]
      exact (le_sup_left : rayPrincipal m ≤ _) (Subgroup.mem_subgroupOf.1 hx)
    exact this
  let ψ : RayClassGroup m →* Gal(L/K) := QuotientGroup.lift _ (artinMap L m.finiteSupport) hle
  have hψ : ∀ x : coprimeIdeals m, ψ (QuotientGroup.mk x) = artinMap L m.finiteSupport x :=
    fun x => rfl
  have hFrob : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite)
      (Q : v.asIdeal.primesOver (𝓞 L)), ψ (rayClass m v hv) = frobAt K L v Q := by
    intro v hv Q
    rw [← artinFrob_eq L v (hunr v hv) Q]
    exact artinMap_coprimePrime m v hv
  refine ⟨ψ, ?_, hFrob, ?_⟩
  · intro σ
    obtain ⟨x, hx⟩ := hm.surjective σ
    exact ⟨QuotientGroup.mk x, hx⟩
  apply le_antisymm
  · -- the kernel is generated by the classes of the norms of primes of `L`
    intro c hc
    induction c using QuotientGroup.induction_on with | H x => ?_
    have hx0 : (⟨(x : (FractionalIdeal (𝓞 K)⁰ K)ˣ), x.2⟩ : sIdeals m.finiteSupport) ∈
        (artinMap L m.finiteSupport).ker := hc
    rw [hm.ker_eq, Subgroup.mem_subgroupOf] at hx0
    have hx : (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ rayPrincipal m ⊔ normIdeals K L m.finiteSupport := hx0
    obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup.1 hx
    set M := Subgroup.closure {c | ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite)
          (Q : v.asIdeal.primesOver (𝓞 L)), c = rayClass m v hv ^ Q.1.inertiaDeg (𝓞 K)} with hM
    set E' := (M.comap (QuotientGroup.mk' ((rayPrincipal m).subgroupOf (coprimeIdeals m)))).map
      (coprimeIdeals m).subtype with hE'
    have hN : normIdeals K L m.finiteSupport ≤ E' := by
      unfold normIdeals
      rw [Subgroup.map_le_iff_le_comap, sIdeals_eq_closure, Subgroup.closure_le]
      rintro _ ⟨w, hw, rfl⟩
      have hv : ¬ (primeBelow K L w).asIdeal ∣ m.finite := hw
      let Q : (primeBelow K L w).asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, ⟨rfl⟩⟩
      refine ⟨(coprimePrime m (primeBelow K L w) hv) ^ w.asIdeal.inertiaDeg (𝓞 K), ?_, ?_⟩
      · exact Subgroup.subset_closure ⟨primeBelow K L w, hv, Q, (map_pow _ _ _)⟩
      · rw [idealNorm_primeUnitIdeal]
        rfl
    obtain ⟨y, hy, hyn⟩ := hN hn
    have hyx : (QuotientGroup.mk y : RayClassGroup m) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((y⁻¹ * x : coprimeIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = p := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        have hy' : ((y : coprimeIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = n := hyn
        rw [hy', ← hpn, mul_comm p n, inv_mul_cancel_left]
      rw [this]
      exact hp
    rw [← hyx]
    exact hy
  · rw [Subgroup.closure_le]
    rintro _ ⟨v, hv, Q, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow, hFrob v hv Q,
      ← orderOf_frobAt_eq v (hunr v hv) Q]
    exact pow_orderOf_eq_one _

end Reciprocity

/-! ## Theorem 3.6: the existence theorem -/

/-- **A congruence subgroup modulo $\mathfrak m$** (Milne, *CFT*, V, §3, p. 158): a subgroup $H$ with
$I^{S(\mathfrak m)} \supseteq H \supseteq i(K_{\mathfrak m,1})$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 158 (congruence subgroup modulo m)"]
def IsCongruenceSubgroupMod (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop :=
  rayPrincipal m ≤ H ∧ H ≤ coprimeIdeals m

/-- $L/K$ is unramified at every prime (finite or real) not dividing $\mathfrak m$. -/
def UnramifiedOutside (L : Type) [Field L] [NumberField L] [Algebra K L] (m : Modulus K) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 K), v ∉ m.finiteSupport → Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal) ∧
    ∀ w : InfinitePlace K, w ∉ m.infinite → ¬ InfinitePlace.RamifiesIn L w

variable (K) in
/-- **Theorem 3.6, the existence theorem** (named statement; Milne, *CFT*, V, Theorem 3.6, p. 158, as stated; proved
in Chapter VII from the idelic form, Theorem 5.5): for every congruence subgroup $H$ modulo $\mathfrak m$ there is a
finite abelian extension $L/K$, unramified at the primes not dividing $\mathfrak m$, with
$H = i(K_{\mathfrak m,1})\cdot\mathrm{Nm}_{L/K}(I_L^{S(\mathfrak m)})$. -/
@[kb "milne2020cft" "Ch. V, Theorem 3.6 (input)"]
structure ExistenceTheorem : Prop where
  exists_field : ∀ (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ), IsCongruenceSubgroupMod m H →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      UnramifiedOutside L m ∧ H = rayPrincipal m ⊔ normIdeals K L m.finiteSupport

/-- **The class field of a congruence subgroup** (Milne, *CFT*, V, §3, p. 160, "the field $L$ corresponding to a
congruence subgroup $H$ is called the class field of $H$"; see the erratum in the module docstring for why it is
defined through the Artin map): a finite abelian extension $L/K$, unramified outside $\mathfrak m$, such that the
Artin map $I^{S(\mathfrak m)} \to \mathrm{Gal}(L/K)$ is onto with kernel $H$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 160 (class field of a congruence subgroup)"]
structure IsClassFieldOf (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L] (m : Modulus K)
    (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Prop where
  unramifiedOutside : UnramifiedOutside L m
  surjective : Function.Surjective (artinMap L m.finiteSupport)
  ker_eq : (artinMap L m.finiteSupport).ker = H.subgroupOf (sIdeals m.finiteSupport)

variable (K) in
/-- **Theorem 3.6 with the note after it, corrected** (named statement; Milne, *CFT*, V, Theorem 3.6 and p. 158; see
the erratum in the module docstring): for every congruence subgroup $H$ modulo $\mathfrak m$ there is a finite abelian
extension $L/K$, unramified outside $\mathfrak m$, with $H = i(K_{\mathfrak m,1})\cdot\mathrm{Nm}(I_L^{S(\mathfrak m)})$,
such that the Artin map induces $I^{S(\mathfrak m)}/H \cong \mathrm{Gal}(L/K)$ ($L$ is the class field of $H$). -/
@[kb "milne2020cft" "Ch. V, Theorem 3.6 and the note after it (corrected; input)"]
structure ExistenceTheoremArtin : Prop where
  exists_field : ∀ (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ), IsCongruenceSubgroupMod m H →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L),
      IsClassFieldOf L m H ∧ H = rayPrincipal m ⊔ normIdeals K L m.finiteSupport

/-- The corrected existence theorem gives Theorem 3.6 as stated. -/
theorem existenceTheorem_of_artin (h : ExistenceTheoremArtin K) : ExistenceTheorem K :=
  ⟨fun m H hH => by
    obtain ⟨L, _, _, _, _, hL, hH'⟩ := h.exists_field m H hH
    exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hL.unramifiedOutside, hH'⟩⟩

/-- **The ray class field** (Milne, *CFT*, V, §3, p. 158, from Theorem 3.6 and the note): for every modulus
$\mathfrak m$ there is a finite abelian extension $L_\mathfrak m$, unramified outside $\mathfrak m$, such that the Artin
map defines an isomorphism $C_\mathfrak m \cong \mathrm{Gal}(L_\mathfrak m/K)$, $[\mathfrak p] \mapsto
(\mathfrak p, L_\mathfrak m/K)$. -/
@[kb "milne2020cft" "Ch. V, §3, p. 158 (the ray class field L_m)"]
theorem exists_rayClassField (h : ExistenceTheoremArtin K) (m : Modulus K) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L)
      (e : RayClassGroup m ≃* Gal(L/K)), UnramifiedOutside L m ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), e (rayClass m v hv) = artinFrob L v := by
  obtain ⟨L, _, _, _, _, hL, -⟩ := h.exists_field m (rayPrincipal m) ⟨le_rfl, rayPrincipal_le m⟩
  let f : coprimeIdeals m →* Gal(L/K) := artinMap L m.finiteSupport
  have hker : (rayPrincipal m).subgroupOf (coprimeIdeals m) = f.ker := hL.ker_eq.symm
  have hf : Function.Surjective f := hL.surjective
  let e : RayClassGroup m ≃* Gal(L/K) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, e, hL.unramifiedOutside,
    fun v hv => ?_⟩
  exact artinMap_coprimePrime m v hv

/-- **The residue degree in a class field** (Milne, *CFT*, V, §3, p. 160): if $L$ is the class field of $H$, then for a
prime $\mathfrak p \nmid \mathfrak m_0$ and $\mathfrak P \mid \mathfrak p$, $f(\mathfrak P/\mathfrak p)$ is the order of
$\mathfrak p$ in $I^{S(\mathfrak m)}/H$ (the order of the Frobenius element). -/
@[kb "milne2020cft" "Ch. V, §3, p. 160 (f(P/p) is the order of p in I^m/H)"]
theorem inertiaDeg_eq_orderOf (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (m : Modulus K) (H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ) (hL : IsClassFieldOf L m H)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)) :
    Q.1.inertiaDeg (𝓞 K) =
      orderOf (QuotientGroup.mk (coprimePrime m v hv) : coprimeIdeals m ⧸ H.subgroupOf (coprimeIdeals m)) := by
  have hunr : v ∈ unramifiedPrimes K L := hL.unramifiedOutside.1 v hv
  let ψ : (coprimeIdeals m ⧸ H.subgroupOf (coprimeIdeals m)) →* Gal(L/K) :=
    QuotientGroup.lift _ (artinMap L m.finiteSupport) (le_of_eq hL.ker_eq.symm)
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    induction c using QuotientGroup.induction_on with | H x => ?_
    have hx : x ∈ (artinMap L m.finiteSupport).ker := hc
    rw [hL.ker_eq] at hx
    exact (QuotientGroup.eq_one_iff x).2 hx
  rw [← orderOf_injective ψ hinj, ← orderOf_frobAt_eq v hunr Q, ← artinFrob_eq L v hunr Q]
  exact congrArg orderOf (artinMap_coprimePrime m v hv).symm

/-- A class field of $H$ (Artin map definition) is a class field in the Introduction's sense (`IsClassField`, defined
through split primes) for the image of $H$ in $C_\mathfrak m$. -/
theorem IsClassFieldOf.isClassField {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {m : Modulus K} {H : Subgroup (FractionalIdeal (𝓞 K)⁰ K)ˣ} (hH : IsCongruenceSubgroupMod m H)
    (hL : IsClassFieldOf L m H) :
    IsClassField L m ((H.subgroupOf (coprimeIdeals m)).map (QuotientGroup.mk' _)) := by
  refine ⟨fun σ τ => ?_, fun v hv => hL.unramifiedOutside.1 v hv, fun v hv => ?_⟩
  · open scoped IsMulCommutative in exact mul_comm σ τ
  have Q : v.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  have hunr : v ∈ unramifiedPrimes K L := hL.unramifiedOutside.1 v hv
  rw [mem_splitPrimes_iff, splitsCompletelyIn_iff_frobAt_eq_one K L v hunr Q,
    ← artinFrob_eq L v hunr Q, ← artinMap_coprimePrime m v hv]
  let x : sIdeals m.finiteSupport := coprimePrime m v hv
  have hmemk : artinMap L m.finiteSupport x = 1 ↔ (x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ H := by
    rw [← MonoidHom.mem_ker, hL.ker_eq, Subgroup.mem_subgroupOf]
  refine hmemk.trans ?_
  constructor
  · intro hmem
    exact ⟨coprimePrime m v hv, Subgroup.mem_subgroupOf.2 hmem, rfl⟩
  · rintro ⟨y, hy, hyc⟩
    have h1 := QuotientGroup.eq.1 hyc
    have h2 : ((y⁻¹ * coprimePrime m v hv : coprimeIdeals m) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ H :=
      hH.1 (Subgroup.mem_subgroupOf.1 h1)
    have h3 : (y : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ H := Subgroup.mem_subgroupOf.1 hy
    have := H.mul_mem h3 h2
    simpa using this

end NumberFieldKB.MilneCFT
