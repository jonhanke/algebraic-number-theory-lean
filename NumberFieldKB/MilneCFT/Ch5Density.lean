import NumberFieldKB.MilneCFT.Ch5LSeries
import NumberFieldKB.MilneCFT.Ch5IdelesChar
import NumberFieldKB.Chebotarev.PrimeDensityOrth
import NumberFieldKB.Chebotarev.PrimeDensityLog
import NumberFieldKB.Chebotarev.DensityTools

/-!
# Theorem 2.5: equidistribution of primes in ray classes (Milne, *Class Field Theory*, Chapter V, §2)

**Theorem 2.5** (`theorem_2_5`): for every class $c$ of the ray class group $C_\mathfrak m$, the primes of $K$ (prime to
$\mathfrak m_0$) whose class in $C_\mathfrak m$ is $c$ have Dirichlet density $1/h_\mathfrak m$.

*Proof* (Milne, Chapter VI, by $L$-series; here through the library's Hecke $L$-functions): $C_\mathfrak m$ is finite
(Theorem 1.7). A character $\chi \ne 1$ of $C_\mathfrak m$ gives the finite-order Hecke character $\chi\circ\varphi_\mathfrak m$
of $C_K$ (Remark 4.11, from Proposition 4.7), unramified at the primes $\mathfrak p \nmid \mathfrak m_0$ with value
$\chi([\mathfrak p])$ at a uniformizer; by the nonvanishing of Hecke $L$-functions on $\mathrm{Re}(s) = 1$
(`NumberFieldKB.NonVanishing`), $\sum_\mathfrak p\chi([\mathfrak p])N\mathfrak p^{-s}$ stays bounded as $s \downarrow 1$
(`Chebotarev.isBigO_primeSum_heckeCoeff_of_pow_eq_one`), and the orthogonality of characters
(`Chebotarev.hasDirichletDensity_fibre`) gives the density.

The Hecke character attached to a character of the ray class group is built in `exists_heckeChar`; the computation of
the ideal of an idèle supported at one prime is in `ideleToIdeal_ofAdicCompletion_unit` and
`ideleToIdeal_ofAdicCompletion_uniformizer`.
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev WithZero Filter Topology Asymptotics
open NumberFieldKB.HeckeCharacter NumberFieldKB.HeckeL NumberFieldKB.NonVanishing QuadFormsKB
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

variable {K : Type} [Field K] [NumberField K]

/-- The exponent at a finite prime $w$ of the fractional ideal of an idèle $x$ is $-\log$ of the absolute value of
the component $x_w$. -/
theorem count_ideleToIdeal (x : IdeleGroup (𝓞 K) K) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w ((ideleToIdeal K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
      = -log (Valued.v (ideleFinAt x w)) :=
  QuadFormsKB.Tamagawa.Measure.Weil.count_ideleIdeal _ _

/-- The idèle $u$ at the prime $v$ (and $1$ elsewhere) has component $u$ at $v$. -/
theorem ofAdicCompletion_finAt_self (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) :
    ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) v = u := by
  classical
  show FiniteAdeleRing.ofAdicCompletion K v (u : v.adicCompletion K) v = u
  exact Pi.mulSingle_eq_same v _

/-- The idèle $u$ at the prime $v$ (and $1$ elsewhere) has component $1$ at every other finite prime. -/
theorem ofAdicCompletion_finAt_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (u : (v.adicCompletion K)ˣ) :
    ideleFinAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) w = 1 := by
  classical
  show FiniteAdeleRing.ofAdicCompletion K v (u : v.adicCompletion K) w = 1
  exact Pi.mulSingle_eq_of_ne h _

/-- The idèle $u$ at the prime $v$ (and $1$ elsewhere) has component $1$ at every infinite place. -/
theorem ofAdicCompletion_infAt (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ) (w : InfinitePlace K) :
    ideleInfAt (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) w = 1 := rfl

/-- The ideal of the idèle which is a unit $u$ at $v$ (and $1$ elsewhere) is trivial. -/
theorem ideleToIdeal_ofAdicCompletion_unit (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    ideleToIdeal K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = 1 := by
  refine (item_4_1.2 _).mpr fun w => ?_
  by_cases h : w = v
  · subst h; rw [ofAdicCompletion_finAt_self]; exact hu
  · rw [ofAdicCompletion_finAt_ne h]; simp

/-- The ideal of the idèle which is a uniformizer $u$ at $v$ (and $1$ elsewhere) is the prime $v$. -/
theorem ideleToIdeal_ofAdicCompletion_uniformizer (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = exp (-1)) :
    ideleToIdeal K (IdeleGroup.ofAdicCompletion (𝓞 K) K v u) = primeUnitIdeal v := by
  refine QuadFormsKB.Tamagawa.Measure.Weil.fracIdeal_ext_count fun w => ?_
  rw [count_ideleToIdeal, primeUnitIdeal, FractionalIdeal.coe_mk0]
  by_cases h : w = v
  · subst h
    rw [ofAdicCompletion_finAt_self, hu, FractionalIdeal.count_self]; simp
  · rw [ofAdicCompletion_finAt_ne h, FractionalIdeal.count_maximal_coprime K w (Ne.symm h)]; simp

/-- **The Hecke character attached to a character of the ray class group**: for a character $\psi$ of $C_\mathfrak m$
the composite $\psi\circ\varphi_\mathfrak m$ (Remark 4.11) is a Hecke character $\Psi$ of finite order dividing
$|C_\mathfrak m|$, nontrivial if $\psi$ is, and for every prime $\mathfrak p \nmid \mathfrak m_0$ unramified with value
$\psi([\mathfrak p])$ on the standard uniformizer. -/
theorem exists_heckeChar (m : Modulus K) (ψ : MulChar (RayClassGroup m) ℂ) :
    ∃ Ψ : HeckeCharacter K, Ψ ^ Nat.card (RayClassGroup m) = 1 ∧
      (ψ ≠ 1 → Ψ ≠ 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite),
        Ψ.IsUnramifiedAt v ∧ (Ψ.finiteComponent v (Analysis.ϖU v) : ℂ) = ψ (rayClass m v hv) := by
  classical
  have hfin : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  obtain ⟨φ, ⟨hφc, hφK, hφI⟩, -⟩ := remark_4_11_exists m
  let _ : TopologicalSpace (RayClassGroup m) := ⊥
  have : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  let ψ' : RayClassGroup m →* ℂˣ := ψ.toUnitHom.comp (toUnits (G := RayClassGroup m)).toMonoidHom
  have hψ' : ∀ g, (ψ' g : ℂ) = ψ g := by intro g; simp [ψ']
  let Ψ0 : IdeleGroup (𝓞 K) K →* ℂˣ := ψ'.comp φ
  have hΨ0c : Continuous Ψ0 := (continuous_of_discreteTopology (f := (ψ' : RayClassGroup m → ℂˣ))).comp hφc
  let Ψ : HeckeCharacter K :=
    ⟨QuotientGroup.lift _ Ψ0 (by
        rintro _ ⟨a, rfl⟩
        exact (MonoidHom.mem_ker).mpr (by simp [Ψ0, hφK a])),
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hΨ0c⟩
  have hΨ : ∀ x : IdeleGroup (𝓞 K) K, Ψ (x : IdeleClassGroup (𝓞 K) K) = Ψ0 x := fun x => rfl
  have key : ∀ (v : HeightOneSpectrum (𝓞 K)) (u : (v.adicCompletion K)ˣ),
      Ψ.finiteComponent v u = ψ' (φ (IdeleGroup.ofAdicCompletion (𝓞 K) K v u)) := fun v u => rfl
  have hx : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite) (u : (v.adicCompletion K)ˣ),
      IdeleGroup.ofAdicCompletion (𝓞 K) K v u ∈ idelesTrivialAt m.finiteSupport := by
    intro v hv u
    refine ⟨fun w => ofAdicCompletion_infAt v u w, fun w hw => ?_⟩
    exact ofAdicCompletion_finAt_ne (fun h => hv (by rw [← h]; exact hw)) u
  have hunr : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), Ψ.IsUnramifiedAt v := by
    intro v hv u hu
    rw [key, hφI _ (hx v hv u) 1 (by
      rw [Subgroup.coe_one]; exact (ideleToIdeal_ofAdicCompletion_unit v u hu).symm)]
    show ψ' (toRayClass m (1 : coprimeIdeals m)) = 1
    rw [map_one, map_one]
  have hval : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite),
      (Ψ.finiteComponent v (Analysis.ϖU v) : ℂ) = ψ (rayClass m v hv) := by
    intro v hv
    have hϖ : Valued.v ((Analysis.ϖU v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = exp (-1) := by
      simpa using LocalZeta.valued_ϖU_zpow v 1
    rw [key, hφI _ (hx v hv _) (coprimePrime m v hv)
      (ideleToIdeal_ofAdicCompletion_uniformizer v _ hϖ).symm]
    rw [hψ']
    rfl
  refine ⟨Ψ, ?_, ?_, fun v hv => ⟨hunr v hv, hval v hv⟩⟩
  · refine ContinuousMonoidHom.ext fun c => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    rw [pow_apply_aux, hΨ]
    show (ψ' (φ x)) ^ Nat.card (RayClassGroup m) = 1
    rw [← map_pow, pow_card_eq_one', map_one]
  · intro hψ hΨ1
    apply hψ
    have h1 : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), ψ (rayClass m v hv) = 1 := by
      intro v hv
      rw [← hval v hv, hΨ1]; rfl
    let kr : Subgroup (coprimeIdeals m) := (ψ'.comp (QuotientGroup.mk' _)).ker
    have hcl : Subgroup.closure (primeUnitIdeal '' m.finiteSupportᶜ) ≤ kr.map (coprimeIdeals m).subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, hv, rfl⟩
      have hv' : ¬ v.asIdeal ∣ m.finite := hv
      refine ⟨coprimePrime m v hv', ?_, rfl⟩
      show coprimePrime m v hv' ∈ kr
      rw [MonoidHom.mem_ker]
      apply Units.ext
      show (ψ' (rayClass m v hv') : ℂ) = 1
      rw [hψ', h1 v hv']
    refine MulChar.ext' fun g => ?_
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
    have hb : (b : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ sIdeals m.finiteSupport := b.2
    rw [sIdeals_eq_closure] at hb
    obtain ⟨b', hb', hbb⟩ := hcl hb
    have : b' = b := Subtype.ext hbb
    subst this
    have := congrArg (fun z : ℂˣ => (z : ℂ)) (MonoidHom.mem_ker.mp hb')
    rw [MulChar.one_apply (Group.isUnit _)]; simpa [hψ'] using this

/-- **Theorem 2.5** (Milne, *CFT*, V, Theorem 2.5, p. 156): for every ideal $\mathfrak a$ prime to $\mathfrak m_0$ (every
class $c$ of $C_\mathfrak m$ is the class of such an $\mathfrak a$, Proposition 1.6), the prime ideals of $\mathcal O_K$
whose class in $C_\mathfrak m$ is $c$ have Dirichlet density $1/h_\mathfrak m$. -/
@[kb "milne2020cft" "Ch. V, Theorem 2.5"]
theorem theorem_2_5 (m : Modulus K) (c : RayClassGroup m) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ hv : ¬ v.asIdeal ∣ m.finite, rayClass m v hv = c}.HasDirichletDensity
      (1 / Nat.card (RayClassGroup m)) := by
  classical
  have : Finite (RayClassGroup m) := (theorem_1_7_card m).1
  have hS : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ m.finite}.Finite :=
    Ideal.finite_factors m.finite_ne_bot
  obtain ⟨f, hf⟩ : ∃ f : HeightOneSpectrum (𝓞 K) → RayClassGroup m,
      ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ m.finite), f v = rayClass m v hv :=
    ⟨fun v => if hv : ¬ v.asIdeal ∣ m.finite then rayClass m v hv else (1 : RayClassGroup m),
      fun v hv => by simp [hv]⟩
  have hψ : ∀ ψ : MulChar (RayClassGroup m) ℂ, ψ ≠ 1 →
      (fun s : ℝ => primeSum (F := K) (fun v => ψ (f v)) s) =O[𝓝[>] 1] (fun _ => (1 : ℂ)) := by
    intro ψ hψ1
    obtain ⟨Ψ, hpow, hne, hloc⟩ := exists_heckeChar m ψ
    have hn : Nat.card (RayClassGroup m) ≠ 0 := Nat.card_pos.ne'
    have h1 := isBigO_primeSum_heckeCoeff_of_pow_eq_one hn hpow (hne hψ1)
    have hU := isUnitary_of_pow_eq_one hn hpow
    have ha : ∀ v, ‖ψ (f v)‖ ≤ 1 := fun v => by
      refine (Complex.norm_eq_one_of_pow_eq_one (n := Nat.card (RayClassGroup m)) ?_ hn).le
      have := pow_card_eq_one' (G := RayClassGroup m) (x := f v)
      calc ψ (f v) ^ Nat.card (RayClassGroup m) = ψ (f v ^ Nat.card (RayClassGroup m)) := (map_pow ψ _ _).symm
        _ = 1 := by rw [this, map_one]
    have hdiff := isBigO_primeSum_sub_of_finite (a := fun v => ψ (f v)) (b := heckeCoeff Ψ) ha
      (norm_heckeCoeff_le hU) (hS.subset fun v hv => by
        by_contra hv'
        apply hv
        obtain ⟨hu, hval⟩ := hloc v hv'
        rw [hf v hv', heckeCoeff]; simp only [hu, ite_true]; exact hval.symm)
    refine (hdiff.add h1).congr_left fun s => ?_
    simp
  have hd := hasDirichletDensity_fibre f hψ c
  refine HasDirichletDensity.congr_finite hd (hS.subset fun v hv => ?_)
  by_contra hv'
  have hv'' : ¬ v.asIdeal ∣ m.finite := hv'
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 ⟨hv'', by rw [← hf v hv'']; exact h1⟩
  · obtain ⟨_, hh⟩ := h1
    exact h2 (by rw [Set.mem_ofPred_eq, hf v hv'']; exact hh)

end NumberFieldKB.MilneCFT
