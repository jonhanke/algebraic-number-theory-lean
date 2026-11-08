import NumberFieldKB.MilneCFT.Intro.RayClass
import NumberFieldKB.Chebotarev.Unconditional
import NumberFieldKB.HilbertClassField.Artin

/-!
# The main theorems of the Introduction (Milne, *Class Field Theory*, Introduction)

* **Theorem 0.1** (Frobenius): the primes splitting completely in a Galois extension $L/K$ have density $1/[L:K]$ —
  proved (`frobenius_density`), from the unconditional Chebotarev theorem of this library.
* **Theorem 0.4** (Furtwängler), **Theorem 0.5** (Takagi), **Theorem 0.8** (Artin reciprocity): named statements
  (`FurtwanglerTheorem`, `TakagiTheorem`, `ArtinReciprocity`), with consequences proved here: the primes splitting
  in an abelian extension are those in the kernel of the Artin map (`mem_splitPrimes_iff_artin`), $L$ is a class
  field for that kernel (`isClassField_of_artin`), the Hilbert class field (weak form) from Theorem 0.4
  (`hilbertClassFieldInput_of_furtwangler`), and the two named inputs of `NumberFieldKB.HilbertClassField.Artin` from
  Theorems 0.4 and 0.8, hence the Hilbert class field with its Artin isomorphism
  (`hilbertClassFieldExists_of_furtwangler_artin`).

Universe convention: extensions are number fields `L : Type` with `[Algebra K L]` (Milne fixes an algebraic closure;
uniqueness of class fields is then up to $K$-isomorphism).
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-! ## Theorem 0.1 -/

/-- **Theorem 0.1 (Frobenius)** (Milne, *CFT*, Introduction): for a finite Galois extension $L/K$ of number fields,
the set $\mathrm{Spl}(L/K)$ of primes of $K$ splitting completely in $L$ has (Dirichlet) density $1/[L:K]$. Proved:
`NumberFieldKB.Chebotarev.splitPrimes_hasDirichletDensity_unconditional`. -/
@[kb "milne2020cft" "Introduction, Theorem 0.1"]
theorem frobenius_density (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] :
    (splitPrimes K L).HasDirichletDensity (1 / Module.finrank K L) :=
  splitPrimes_hasDirichletDensity_unconditional K L

/-! ## Theorem 0.4 (Furtwängler) -/

/-- **Theorem 0.4 (Furtwängler 1907)** (named statement; Milne, *CFT*, Introduction): for every subgroup $H$ of the
class group $C$ of $K$ a class field exists; it is unique (up to $K$-isomorphism); every finite unramified abelian
extension of $K$ is the class field of some $H$; and if $L$ is the class field of $H$, then
$\mathrm{Gal}(L/K) \cong C/H$ and $f(\mathfrak P/\mathfrak p)$ is the order of the image of $[\mathfrak p]$ in $C/H$. -/
@[kb "milne2020cft" "Introduction, Theorem 0.4 (input)"]
structure FurtwanglerTheorem : Prop where
  exists_classField : ∀ H : Subgroup (ClassGroup (𝓞 K)),
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
      IsUnramifiedClassField (K := K) L H
  unique : ∀ (H : Subgroup (ClassGroup (𝓞 K))) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L'],
    IsUnramifiedClassField (K := K) L H → IsUnramifiedClassField (K := K) L' H → Nonempty (L ≃ₐ[K] L')
  isClassField_of_unramified : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) → (∀ v : HeightOneSpectrum (𝓞 K), v ∈ unramifiedPrimes K L) →
    IsUnramifiedAtInfinitePlaces K L → ∃ H, IsUnramifiedClassField (K := K) L H
  galois_equiv : ∀ (H : Subgroup (ClassGroup (𝓞 K))) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L], IsUnramifiedClassField (K := K) L H → Nonempty (Gal(L/K) ≃* ClassGroup (𝓞 K) ⧸ H)
  inertiaDeg_eq : ∀ (H : Subgroup (ClassGroup (𝓞 K))) (L : Type) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L], IsUnramifiedClassField (K := K) L H →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (Q : v.asIdeal.primesOver (𝓞 L)),
      Q.1.inertiaDeg (𝓞 K) = orderOf (QuotientGroup.mk (primeClass K v) : ClassGroup (𝓞 K) ⧸ H)

variable {K}

/-- **The Hilbert class field, weak form, from Theorem 0.4** (Milne, *CFT*, Introduction, p. 4: "the class field of the
trivial subgroup ... the prime ideals that split in it are exactly the principal ones"): there is a number field $H$
in which every nonzero prime of $\mathcal O_K$ splitting completely is principal. -/
@[kb "milne2020cft" "Introduction, p. 4 (Hilbert class field: the split primes are the principal ones)"]
theorem hilbertClassFieldInput_of_furtwangler (hF : FurtwanglerTheorem K) : HilbertClassFieldInput K := by
  obtain ⟨L, _, _, _, _, hL⟩ := hF.exists_classField ⊥
  refine ⟨⟨L, inferInstance, inferInstance, inferInstance, ?_⟩⟩
  intro p hp hne hs
  let v : HeightOneSpectrum (𝓞 K) := ⟨p, hp, hne⟩
  have h := (hL.splits_iff v).mp ((mem_splitPrimes_iff K L v).mpr hs)
  exact (primeClass_eq_one_iff K v).mp (Subgroup.mem_bot.mp h)

/-! ## Theorem 0.5 (Takagi) -/

variable (K) in
/-- **Theorem 0.5 (Takagi)** (named statement; Milne, *CFT*, Introduction): for every subgroup $H$ of a ray class
group $C_\mathfrak m$ a class field exists; it is unique (up to $K$-isomorphism); every finite abelian extension of
$K$ is the class field of a subgroup of some ray class group; and if $L$ is the class field of
$H \subseteq C_\mathfrak m$, then $\mathrm{Gal}(L/K) \cong C_\mathfrak m/H$, and the primes $\mathfrak p \nmid
\mathfrak m_0$ are unramified in $L$ (part of `IsClassField`) with $f(\mathfrak P/\mathfrak p)$ the order of the
image of $[\mathfrak p]$ in $C_\mathfrak m/H$. -/
@[kb "milne2020cft" "Introduction, Theorem 0.5 (input)"]
structure TakagiTheorem : Prop where
  exists_classField : ∀ (m : Modulus K) (H : Subgroup (RayClassGroup m)),
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L), IsClassField L m H
  unique : ∀ (m : Modulus K) (H : Subgroup (RayClassGroup m)) (L L' : Type) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L'],
    IsClassField L m H → IsClassField L' m H → Nonempty (L ≃ₐ[K] L')
  isClassField_of_abelian : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) → ∃ (m : Modulus K) (H : Subgroup (RayClassGroup m)), IsClassField L m H
  galois_equiv : ∀ (m : Modulus K) (H : Subgroup (RayClassGroup m)) (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L], IsClassField L m H → Nonempty (Gal(L/K) ≃* RayClassGroup m ⧸ H)
  inertiaDeg_eq : ∀ (m : Modulus K) (H : Subgroup (RayClassGroup m)) (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L], IsClassField L m H →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
      Q.1.inertiaDeg (𝓞 K) = orderOf (QuotientGroup.mk (rayClass m v hv) : RayClassGroup m ⧸ H)

/-! ## Theorem 0.8 (Artin reciprocity) -/

/-- A real place $v$ of $K$ **ramifies** in $L$ (Milne, *CFT*, Introduction, p. 4): some place of $L$ above it is
complex. -/
@[kb "milne2020cft" "Introduction, p. 4 (a real prime splits or ramifies)"]
def InfinitePlace.RamifiesIn (L : Type) [Field L] [Algebra K L] (v : InfinitePlace K) : Prop :=
  v.IsReal ∧ ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v ∧ w.IsComplex

variable (K) in
/-- **Theorem 0.8 (Artin 1927)** (named statement; Milne, *CFT*, Introduction): for a finite abelian extension $L/K$
with set $S$ of ramified primes, there is a modulus $\mathfrak m$ with $S(\mathfrak m) = S$ such that
$\mathfrak p \mapsto (\mathfrak p, L/K)$ factors through $C_\mathfrak m$ and defines an isomorphism
$I^{S(\mathfrak m)}/P_\mathfrak m\cdot\mathrm{Nm}(I^{S'(\mathfrak m)}) \cong \mathrm{Gal}(L/K)$. Here: a surjective
$\psi : C_\mathfrak m \to \mathrm{Gal}(L/K)$ with $\psi[\mathfrak p] = \mathrm{Frob}_\mathfrak P$ for
$\mathfrak p \nmid \mathfrak m_0$, whose kernel is generated by the classes of the norms
$\mathrm{Nm}(\mathfrak P) = \mathfrak p^{f(\mathfrak P/\mathfrak p)}$ of the primes $\mathfrak P$ of $L$ not above
$\mathfrak m_0$ (these generate $\mathrm{Nm}(I^{S'(\mathfrak m)})$). -/
@[kb "milne2020cft" "Introduction, Theorem 0.8 (input)"]
structure ArtinReciprocity : Prop where
  exists_artin : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (∀ σ τ : Gal(L/K), σ * τ = τ * σ) →
    ∃ m : Modulus K, (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.finite ↔ v ∉ unramifiedPrimes K L) ∧
      (∀ w : InfinitePlace K, w ∈ m.infinite ↔ InfinitePlace.RamifiesIn L w) ∧
      ∃ ψ : RayClassGroup m →* Gal(L/K), Function.Surjective ψ ∧
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
          ψ (rayClass m v hv) = frobAt K L v Q) ∧
        ψ.ker = Subgroup.closure {c | ∃ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite)
          (Q : v.asIdeal.primesOver (𝓞 L)), c = rayClass m v hv ^ Q.1.inertiaDeg (𝓞 K)}

section ArtinConsequences

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **Theorem 0.8, "in particular"** (Milne, *CFT*, Introduction): if $\psi : C_\mathfrak m \to \mathrm{Gal}(L/K)$
sends $[\mathfrak p]$ to $\mathrm{Frob}_\mathfrak P$ and the primes $\mathfrak p \nmid \mathfrak m_0$ are unramified,
then such a $\mathfrak p$ splits in $L$ iff $[\mathfrak p] \in \ker\psi$. -/
@[kb "milne2020cft" "Introduction, Theorem 0.8 (the split primes are those in P_m Nm(I^{S'(m)}))"]
theorem mem_splitPrimes_iff_artin (m : Modulus K) (ψ : RayClassGroup m →* Gal(L/K))
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite → v ∈ unramifiedPrimes K L)
    (hψ : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
      ψ (rayClass m v hv) = frobAt K L v Q)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) :
    v ∈ splitPrimes K L ↔ rayClass m v hv ∈ ψ.ker := by
  have Q : v.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
  rw [mem_splitPrimes_iff, splitsCompletelyIn_iff_frobAt_eq_one K L v (hunr v hv) Q, ← hψ v hv Q,
    MonoidHom.mem_ker]

/-- **An abelian extension is a class field for the kernel of its Artin map** (Milne, *CFT*, Introduction, p. 9, the
"in particular" of Theorem 0.8). -/
@[kb "milne2020cft" "Introduction, Theorem 0.8 (L is the class field of P_m Nm(I^{S'(m)}))"]
theorem isClassField_of_artin (hA : ArtinReciprocity K) (hab : ∀ σ τ : Gal(L/K), σ * τ = τ * σ) :
    ∃ (m : Modulus K) (H : Subgroup (RayClassGroup m)), IsClassField L m H := by
  obtain ⟨m, hm, -, ψ, -, hψ, -⟩ := hA.exists_artin L hab
  have hunr : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite → v ∈ unramifiedPrimes K L :=
    fun v hv => by_contra fun h => hv ((hm v).mpr h)
  exact ⟨m, ψ.ker, hab, hunr, fun v hv => mem_splitPrimes_iff_artin m ψ hunr hψ v hv⟩

end ArtinConsequences

/-! ## The Hilbert class field from Theorems 0.4 and 0.8 -/

/-- **Theorem 0.8 for unramified extensions gives the input `UnramifiedArtinReciprocityInput`** of
`NumberFieldKB.HilbertClassField.Artin`: for $L/K$ abelian and unramified at every place, the modulus of Theorem 0.8
is $(1)$ and $C_{(1)} = \mathrm{Cl}_K$. -/
@[kb "milne2020cft" "Introduction, Theorem 0.8 (unramified case)"]
theorem unramifiedArtinReciprocityInput_of_artin (hA : ArtinReciprocity K) :
    UnramifiedArtinReciprocityInput K := by
  refine ⟨fun H _ _ _ _ hab hunr hinf => ?_⟩
  obtain ⟨m, hm, hmi, ψ, -, hψ, -⟩ := hA.exists_artin H hab
  have h0 : m.finite = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal m.finite h
    have hne : p ≠ ⊥ := fun e => m.finite_ne_bot (le_bot_iff.mp (e ▸ hle))
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, hp.isPrime, hne⟩
    exact ((hm v).mp (Ideal.dvd_iff_le.mpr hle)) (hunr v)
  have hi : m.infinite = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
    obtain ⟨hr, w', hw', hc⟩ := (hmi w).mp hw
    exact (InfinitePlace.isRamified_iff.mpr ⟨hc, hw' ▸ hr⟩) (hinf.isUnramified w')
  have hnd : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite := fun v hd =>
    v.isPrime.ne_top (by rw [h0] at hd; exact top_le_iff.mp (Ideal.le_of_dvd hd))
  refine ⟨ψ.comp (rayClassGroupEquivClassGroup m h0 hi).symm.toMonoidHom, fun 𝔭 Q => ?_⟩
  have : (rayClassGroupEquivClassGroup m h0 hi).symm (primeClass K 𝔭) = rayClass m 𝔭 (hnd 𝔭) :=
    (MulEquiv.symm_apply_eq _).mpr (rayClassGroupEquivClassGroup_rayClass m h0 hi 𝔭 (hnd 𝔭)).symm
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, this]
  exact hψ 𝔭 (hnd 𝔭) Q

/-- **Theorem 0.4 gives the input `HilbertClassFieldDegreeInput`** of `NumberFieldKB.HilbertClassField.Artin`: the
class field of the trivial subgroup is abelian, unramified at every place, of degree $|C/1| = h_K$. -/
@[kb "milne2020cft" "Introduction, Theorem 0.4 (the Hilbert class field has degree h_K)"]
theorem hilbertClassFieldDegreeInput_of_furtwangler (hF : FurtwanglerTheorem K) :
    HilbertClassFieldDegreeInput K := by
  obtain ⟨L, _, _, _, _, hL⟩ := hF.exists_classField ⊥
  obtain ⟨e⟩ := hF.galois_equiv ⊥ L hL
  refine ⟨⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hL.comm, hL.unramified,
    hL.unramifiedAtInfinitePlaces, ?_⟩⟩
  have h1 : Nat.card Gal(L/K) = Nat.card (ClassGroup (𝓞 K) ⧸ (⊥ : Subgroup (ClassGroup (𝓞 K)))) :=
    Nat.card_congr e.toEquiv
  have h2 : Nat.card (ClassGroup (𝓞 K) ⧸ (⊥ : Subgroup (ClassGroup (𝓞 K)))) = Nat.card (ClassGroup (𝓞 K)) :=
    Nat.card_congr QuotientGroup.quotientBot.toEquiv
  rw [← IsGalois.card_aut_eq_finrank, h1, h2, classNumber, Nat.card_eq_fintype_card]

/-- **The Hilbert class field exists, with its Artin isomorphism** $\mathrm{Cl}_K \cong \mathrm{Gal}(H/K)$
(Milne, *CFT*, Introduction, p. 4), from Theorems 0.4 and 0.8. -/
@[kb "milne2020cft" "Introduction, p. 4 (Hilbert class field)"]
theorem hilbertClassFieldExists_of_furtwangler_artin (hF : FurtwanglerTheorem K) (hA : ArtinReciprocity K) :
    HilbertClassFieldExists K :=
  hilbertClassFieldExists_of_inputs (unramifiedArtinReciprocityInput_of_artin hA)
    (hilbertClassFieldDegreeInput_of_furtwangler hF)

end NumberFieldKB.MilneCFT
