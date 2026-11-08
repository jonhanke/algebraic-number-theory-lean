import NumberFieldKB.Chebotarev.Cyclic

/-!
# The Chebotarev density theorem
$L/K$ is a finite Galois extension of number fields with group $G = \mathrm{Gal}(L/K)$ and $C \subseteq G$ a conjugacy
class. **Chebotarev's density theorem** says that the set of primes $\mathfrak p$ of $K$, unramified in $L$, whose
Frobenius class is $C$ has Dirichlet density $|C|/|G|$ (Milne, *ANT*
Theorem 8.31 states it for natural density).

The proof follows Chebotarev's route (no class field theory), in three steps: the cyclotomic case (Step 1), the cyclic
case by field crossing (Step 2), and the general case by Deuring's descent to cyclic subgroups (Step 3). Each statement
sits next to its proof:

* §0–§1 API and density toolkit: `Basic.lean` (definitions `frobClass`, `frobSet`, `unramifiedPrimes`, `splitPrimes`,
  `dirichletRatio`) and `DensityTools.lean` (analytic inputs, the descent lemma (D), `splitPrimes_upperBound`);
* Frobenius algebra: `FrobeniusPrimes.lean` (`finite_compl_unramifiedPrimes`, `splitPrimes_eq_frobSet_one`,
  `frobClass_restrict`, `deuring_count`);
* Step 1, `cyclotomic_density`: `Cyclotomic.lean`;
* Step 2, `cyclic_lowerBound`, `cyclic_density`: `Cyclic.lean`, with the field theory in `Crossing.lean`;
* Step 3, Deuring's descent `hasDirichletDensity_frobSet_of_fixedField`: `Descent.lean`;
* the headline `chebotarev` (Milne 8.31, Dirichlet density) and `splitPrimes_hasDirichletDensity` (Milne 8.32): here.

**The one named input.** Step 1 uses the Hecke characters $\chi\circ N_{F/\mathbb Q}$, whose construction needs the
idelic norm $N_{F/\mathbb Q}$ with its local description, not in Mathlib v4.35.0. It enters as the named input
`IdelicNormInput` (`DirichletHecke.lean`), a hypothesis of `chebotarev`; it is not definitionally related to the
conclusion.

References: Milne, *Algebraic Number Theory* v3.08, Theorem 8.31 and Corollary 8.32 [unverified locator];
Lenstra–Stevenhagen, "Chebotarëv and his density theorem", Math. Intelligencer 18 (1996) [unverified locator];
Neukirch, *Algebraic Number Theory*, Ch. VII §13 [unverified locator].
-/

open NumberField IsDedekindDomain Filter Topology Set

namespace NumberFieldKB.Chebotarev

noncomputable section

set_option linter.unusedSectionVars false

section Deuring

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- Orbit-stabilizer for conjugation: $|C|\cdot|C_G(\sigma)| = |G|$ for the class $C$ of $\sigma$. -/
theorem card_conj_mul_card_centralizer (G : Type) [Group G] [Finite G] (σ : G) :
    Nat.card (ConjClasses.mk σ).carrier * Nat.card (Subgroup.centralizer ({σ} : Set G)) =
      Nat.card G := by
  classical
  have := Fintype.ofFinite G
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) σ
  have e1 : Nat.card (ConjClasses.mk σ).carrier = Fintype.card (MulAction.orbit (ConjAct G) σ) := by
    rw [← Nat.card_eq_fintype_card, ConjAct.orbit_eq_carrier_conjClasses]
  have e2 : Nat.card (Subgroup.centralizer ({σ} : Set G)) =
      Fintype.card (MulAction.stabilizer (ConjAct G) σ) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun x => ⟨ConjAct.toConjAct x.1, ?_⟩, fun y => ⟨ConjAct.ofConjAct y.1, ?_⟩,
      fun x => ?_, fun y => ?_⟩
    · exact (SetLike.ext_iff.mp (Subgroup.centralizer_eq_comap_stabilizer σ) x.1).mp x.2
    · exact (SetLike.ext_iff.mp (Subgroup.centralizer_eq_comap_stabilizer σ)
        (ConjAct.ofConjAct y.1)).mpr y.2
    · rfl
    · rfl
  have e3 : Nat.card G = Fintype.card (ConjAct G) := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.card_congr ConjAct.toConjAct.toEquiv
  rw [e1, e2, e3]
  exact h

/-- **The Chebotarev density theorem** (Milne, *ANT* Theorem 8.31, here with Dirichlet density): the
unramified primes of `K` with Frobenius class `C` have Dirichlet density $|C|/|G|$. Conditional on the named input
`IdelicNormInput` (the idelic norm, used for the Hecke characters $\chi\circ N$ of Step 1).
*Proof*: pick $\sigma \in C$; `cyclic_density` for $L/E$, $E = L^{\langle\sigma\rangle}$;
Deuring's descent `hasDirichletDensity_frobSet_of_fixedField` gives density $1/|C_G(\sigma)| = |C|/|G|$. -/
theorem chebotarev (hN : IdelicNormInput) (C : ConjClasses Gal(L/K)) :
    (frobSet K L C).HasDirichletDensity (Nat.card C.carrier / Nat.card Gal(L/K)) := by
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep C
  have hcyc : IsCyclic Gal(L/(IntermediateField.fixedField (Subgroup.zpowers σ))) := by
    have h1 : IsCyclic (IntermediateField.fixingSubgroup
        (IntermediateField.fixedField (Subgroup.zpowers σ))) := by
      rw [IntermediateField.fixingSubgroup_fixedField]; infer_instance
    exact (IntermediateField.fixingSubgroupEquiv _).isCyclic.mp h1
  have hrank : Module.finrank (IntermediateField.fixedField (Subgroup.zpowers σ)) L = orderOf σ := by
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers]
  have h := cyclic_density hN (IntermediateField.fixedField (Subgroup.zpowers σ)) L
    (toFixedFieldGal K L σ)
  rw [hrank] at h
  have h2 := hasDirichletDensity_frobSet_of_fixedField K L σ h
  have hm := card_conj_mul_card_centralizer Gal(L/K) σ
  have hc : (0 : ℝ) < Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) := by
    exact_mod_cast Nat.card_pos
  have hC : (0 : ℝ) < Nat.card (ConjClasses.mk σ).carrier := by
    have : Nonempty (ConjClasses.mk σ).carrier :=
      ⟨⟨σ, ConjClasses.mem_carrier_iff_mk_eq.2 rfl⟩⟩
    exact_mod_cast Nat.card_pos
  convert h2 using 1
  have hm' : (Nat.card (ConjClasses.mk σ).carrier : ℝ) *
      Nat.card (Subgroup.centralizer ({σ} : Set Gal(L/K))) = Nat.card Gal(L/K) := by
    exact_mod_cast hm
  rw [← hm']
  field_simp

/-- **Milne 8.32**: the primes of `K` that split completely in `L` have Dirichlet density $1/[L:K]$.
*Proved* from `chebotarev` and `splitPrimes_eq_frobSet_one` (so conditional on `IdelicNormInput`). -/
theorem splitPrimes_hasDirichletDensity (hN : IdelicNormInput) :
    (splitPrimes K L).HasDirichletDensity (1 / Module.finrank K L) := by
  have h1 : Nat.card (ConjClasses.mk (1 : Gal(L/K))).carrier = 1 := by
    have : (ConjClasses.mk (1 : Gal(L/K))).carrier = {1} := by
      ext g
      simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    rw [this, Nat.card_unique]
  have h2 := chebotarev K L hN (ConjClasses.mk 1)
  rw [h1, IsGalois.card_aut_eq_finrank, Nat.cast_one] at h2
  rw [splitPrimes_eq_frobSet_one]
  exact h2

end Deuring

end

end NumberFieldKB.Chebotarev
