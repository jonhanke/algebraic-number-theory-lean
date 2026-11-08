import NumberFieldKB.MilneCFT.Ch7.GaloisAdeles
import NumberFieldKB.MilneCFT.Ch7.TateZero

/-!
# Milne, *Class Field Theory*, Chapter VII §§2–5: cohomology of ideles, units and idele classes

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

$L/K$ is a finite Galois extension of number fields, $G = \mathrm{Gal}(L/K)$, acting on $\mathbb I_L$ and $C_L$
(`GaloisAdeles.lean`). Cohomology and Tate cohomology are Mathlib's `groupCohomology` and `tateCohomology`; the
Herbrand quotient is Chapter II's `herbrandQuotient` (`HerbrandDefined`).

* **Proposition 2.2** (`Prop2_2`, named statement): $\prod_{w\mid v}L_w^\times\cong\mathrm{Ind}_{G_{w_0}}^G L_{w_0}^\times$
  (finite $v$), in the explicit form of Milne's proof (the map $\alpha\mapsto f_\alpha$, $f_\alpha(\tau) =
  (\tau\alpha)_{w_0}$).
* **Corollary 2.6** (`Cor2_6`, named statement): $H^1(G,\mathbb I_L) = 0$ and
  $H^2(G,\mathbb I_L)\cong\bigoplus_v\frac1{n_v}\mathbb Z/\mathbb Z$.
* Lemma 3.4 is in `Lemma34.lean`, Lemma 4.2 in `Lemma42.lean`, Lemma 4.1 and Proposition 2.5 (a) in `TateZero.lean`.
* **Theorem 4.3** (`Theorem4_3`, named statement): $h(C_L) = [L:K]$ for $L/K$ cyclic.
* **Corollary 4.4** (`cor_4_4`, the first inequality): $(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L))\ge n$, proved
  from Theorem 4.3 and the identification $H^0_T(G, C_L) = C_K/\mathrm{Nm}(C_L)$ (`card_tateZero_ideleClassRep`).
* **Theorem 5.1** (`Theorem5_1`, named statement): the second inequality, $H^1(G, C_L) = 0$, $|H^2(G,C_L)|$ divides
  $[L:K]$. **Lemma 5.2** (`lemma_5_2`): for $G$ cyclic the three statements are equivalent.
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField CategoryTheory
open CategoryTheory.Limits
open scoped Classical
open scoped Pointwise

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

/-! ## Proposition 2.2 -/

/-- The component $\alpha_w\in L_w^\times$ of an idele $\alpha\in\mathbb I_L$ at a finite prime $w$. -/
def ideleComponent (w : HeightOneSpectrum (𝓞 L)) : IdeleGroup (𝓞 L) L →* (w.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun a : AdeleRing (𝓞 L) L => a.2 w
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- The prime of $K$ below a prime of $L$. -/
def primeBelow (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 K) :=
  ⟨w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)), Ideal.IsPrime.comap _, fun h =>
    w.ne_bot (Ideal.eq_bot_of_under_eq_bot (R := 𝓞 K) h)⟩

/-- $\prod_{w\mid v}L_w^\times\subseteq\mathbb I_L$: the ideles with component $1$ at every place not above $v$. -/
def idelesAbove (v : HeightOneSpectrum (𝓞 K)) : Subgroup (IdeleGroup (𝓞 L) L) where
  carrier := {α | (∀ w : InfinitePlace L, (α : AdeleRing (𝓞 L) L).1 w = 1) ∧
    ∀ w : HeightOneSpectrum (𝓞 L), primeBelow K L w ≠ v → (α : AdeleRing (𝓞 L) L).2 w = 1}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · change (x : AdeleRing (𝓞 L) L).1 w * (y : AdeleRing (𝓞 L) L).1 w = 1
      rw [hx1 w, hy1 w, mul_one]
    · change (x : AdeleRing (𝓞 L) L).2 w * (y : AdeleRing (𝓞 L) L).2 w = 1
      rw [hx2 w hw, hy2 w hw, mul_one]
  one_mem' := ⟨fun _ => rfl, fun _ _ => rfl⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    have key : ∀ (y : AdeleRing (𝓞 L) L) (z : AdeleRing (𝓞 L) L), y * z = 1 → ∀ w, y.1 w * z.1 w = 1 :=
      fun y z h w => congrArg (fun a : AdeleRing (𝓞 L) L => a.1 w) h
    have key2 : ∀ (y : AdeleRing (𝓞 L) L) (z : AdeleRing (𝓞 L) L), y * z = 1 → ∀ w, y.2 w * z.2 w = 1 :=
      fun y z h w => congrArg (fun a : AdeleRing (𝓞 L) L => a.2 w) h
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · have := key _ _ x.mul_inv w
      rwa [hx1 w, one_mul] at this
    · have := key2 _ _ x.mul_inv w
      rwa [hx2 w hw, one_mul] at this

variable [IsGalois K L]

/-- The derived action of $\sigma\in G_{w_0}$ on $L_{w_0}^\times$: $\sigma\cdot y = (\sigma\,\iota_{w_0}(y))_{w_0}$. -/
def localSMul (w₀ : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K)) (y : (w₀.adicCompletion L)ˣ) :
    (w₀.adicCompletion L)ˣ :=
  ideleComponent L w₀ (σ • IdeleGroup.ofAdicCompletion (𝓞 L) L w₀ y)

/-- **Proposition 2.2** (named statement; Milne, *CFT*, Chapter VII, p. 204), for a finite prime $v$: let $w_0\mid v$
with decomposition group $G_{w_0}$ (the stabilizer of $w_0$). Then $G_{w_0}$ preserves the ideles supported at $w_0$
(so $L_{w_0}^\times$ is a $G_{w_0}$-module, `localSMul`), and $\alpha\mapsto f_\alpha$,
$f_\alpha(\tau) = (\tau\alpha)_{w_0}$ is a bijection from $\prod_{w\mid v}L_w^\times$ onto
$\mathrm{Ind}_{G_{w_0}}^G(L_{w_0}^\times) = \{f : G\to L_{w_0}^\times \mid f(\sigma\tau) = \sigma f(\tau),\
\sigma\in G_{w_0}\}$; it is a $G$-map for $(\gamma f)(\tau) = f(\tau\gamma)$ (automatic:
$f_{\gamma\alpha}(\tau) = f_\alpha(\tau\gamma)$). Milne also states the versions for $L_w$ and $U_w$; the unit
version is `units`. -/
@[kb "milne2020cft" "Ch. VII, Prop. 2.2 (input)"]
structure Prop2_2 : Prop where
  stable : ∀ (w₀ : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K)), σ • w₀.asIdeal = w₀.asIdeal →
    ∀ y : (w₀.adicCompletion L)ˣ, σ • IdeleGroup.ofAdicCompletion (𝓞 L) L w₀ y =
      IdeleGroup.ofAdicCompletion (𝓞 L) L w₀ (localSMul K L w₀ σ y)
  bijective : ∀ w₀ : HeightOneSpectrum (𝓞 L),
    Set.BijOn (fun (α : IdeleGroup (𝓞 L) L) (τ : Gal(L/K)) => ideleComponent L w₀ (τ • α))
      (idelesAbove K L (primeBelow K L w₀))
      {f | ∀ σ τ : Gal(L/K), σ • w₀.asIdeal = w₀.asIdeal → f (σ * τ) = localSMul K L w₀ σ (f τ)}
  units : ∀ w₀ : HeightOneSpectrum (𝓞 L),
    Set.BijOn (fun (α : IdeleGroup (𝓞 L) L) (τ : Gal(L/K)) => ideleComponent L w₀ (τ • α))
      {α | α ∈ idelesAbove K L (primeBelow K L w₀) ∧ ∀ w, Valued.v ((α : AdeleRing (𝓞 L) L).2 w) = 1}
      {f | (∀ τ, Valued.v ((f τ : (w₀.adicCompletion L)ˣ) : w₀.adicCompletion L) = 1) ∧
        ∀ σ τ : Gal(L/K), σ • w₀.asIdeal = w₀.asIdeal → f (σ * τ) = localSMul K L w₀ σ (f τ)}

/-! ## Corollary 2.6 -/

/-- The local degree $n_v = [L_w:K_v]$: $e(w/v)f(w/v)$ at a finite prime, $2$ or $1$ at an infinite prime according as
$v$ is real and ramifies in $L$ or not. -/
def localDegree : InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K) → ℕ
  | .inl v => if InfinitePlace.RamifiesIn L v then 2 else 1
  | .inr v => (Classical.arbitrary (v.asIdeal.primesOver (𝓞 L))).1.ramificationIdx (𝓞 K) *
      (Classical.arbitrary (v.asIdeal.primesOver (𝓞 L))).1.inertiaDeg (𝓞 K)

/-- **Corollary 2.6** (named statement; Milne, *CFT*, Chapter VII, p. 206): (a) $H^1(G,\mathbb I_L) = 0$;
(b) $H^2(G,\mathbb I_L)\cong\bigoplus_v\frac1{n_v}\mathbb Z/\mathbb Z$ ($\cong\bigoplus_v\mathbb Z/n_v\mathbb Z$), the sum over
all places of $K$. (Proved in Milne from Proposition 2.5, Hilbert 90 and the local invariant maps of Chapter III.) -/
@[kb "milne2020cft" "Ch. VII, Cor. 2.6 (input)"]
structure Cor2_6 : Prop where
  h1 : IsZero (groupCohomology (ideleRep K L) 1)
  h2 : Nonempty (groupCohomology (ideleRep K L) 2 ≃+
    DirectSum (InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)) (fun v => ZMod (localDegree K L v)))

/-! ## Theorem 4.3 and Corollary 4.4 -/

/-- **Theorem 4.3** (named statement; Milne, *CFT*, Chapter VII, p. 211): for every finite cyclic extension $L/K$ of
number fields, the Herbrand quotient $h(C_L)$ is defined and equals $[L:K]$. -/
@[kb "milne2020cft" "Ch. VII, Thm. 4.3 (input)"]
structure Theorem4_3 : Prop where
  herbrand : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L], IsCyclic Gal(L/K) →
    HerbrandDefined (ideleClassRep K L) ∧ herbrandQuotient (ideleClassRep K L) = Module.finrank K L

/-- For cyclic $L/K$ of degree $n$ (given Theorem 4.3): $H^1$ and $H^2$ of $C_L$ are finite, $|H^1|>0$,
$|H^2| = (\mathbb I_K : K^\times\mathrm{Nm}\,\mathbb I_L) = n\,|H^1|$. -/
theorem herbrand_data (h43 : Theorem4_3 K) (hc : IsCyclic Gal(L/K)) :
    Finite (groupCohomology (ideleClassRep K L) 1) ∧ Finite (groupCohomology (ideleClassRep K L) 2) ∧
    0 < Nat.card (groupCohomology (ideleClassRep K L) 1) ∧
    Nat.card (groupCohomology (ideleClassRep K L) 2) = (principalNormIdeles K L).index ∧
    (principalNormIdeles K L).index = Module.finrank K L * Nat.card (groupCohomology (ideleClassRep K L) 1) := by
  obtain ⟨⟨f0, f1⟩, hq⟩ := h43.herbrand L hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e1 := (TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L/K)) 1).app (ideleClassRep K L)
  let e0 := periodicity g hg (ideleClassRep K L) 0 ≪≫
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(L/K)) 2).app (ideleClassRep K L)
  have c1 : Nat.card (tateCohomology (ideleClassRep K L) 1) = Nat.card (groupCohomology (ideleClassRep K L) 1) :=
    Nat.card_congr e1.toLinearEquiv.toEquiv
  have c0 : Nat.card (tateCohomology (ideleClassRep K L) 0) = Nat.card (groupCohomology (ideleClassRep K L) 2) :=
    Nat.card_congr e0.toLinearEquiv.toEquiv
  have fin1 : Finite (groupCohomology (ideleClassRep K L) 1) := Finite.of_equiv _ e1.toLinearEquiv.toEquiv
  have fin2 : Finite (groupCohomology (ideleClassRep K L) 2) := Finite.of_equiv _ e0.toLinearEquiv.toEquiv
  have pos : 0 < Nat.card (tateCohomology (ideleClassRep K L) 1) := Nat.card_pos
  have hidx := card_tateZero_ideleClassRep K L
  unfold herbrandQuotient at hq
  have hq' : (Nat.card (tateCohomology (ideleClassRep K L) 0) : ℚ) =
      Module.finrank K L * Nat.card (tateCohomology (ideleClassRep K L) 1) := by
    have : (Nat.card (tateCohomology (ideleClassRep K L) 1) : ℚ) ≠ 0 := by positivity
    field_simp at hq
    rw [hq, mul_comm]
  have hq'' : Nat.card (tateCohomology (ideleClassRep K L) 0) =
      Module.finrank K L * Nat.card (tateCohomology (ideleClassRep K L) 1) := by exact_mod_cast hq'
  refine ⟨fin1, fin2, c1 ▸ pos, c0.symm.trans hidx, ?_⟩
  rw [← hidx, hq'', c1]

/-- **Corollary 4.4** (the first inequality; Milne, *CFT*, Chapter VII, p. 211; conditional on Theorem 4.3): if $L/K$
is cyclic of degree $n$, then $(\mathbb I_K : K^\times\cdot\mathrm{Nm}(\mathbb I_L))\ge n$ (and the index is finite).
(Milne's proof: $h(C_L) = n$, so its numerator $|H^0_T(G,C_L)|$ is at least $n$.) -/
@[kb "milne2020cft" "Ch. VII, Cor. 4.4"]
theorem cor_4_4 (h43 : Theorem4_3 K) (hc : IsCyclic Gal(L/K)) :
    (principalNormIdeles K L).FiniteIndex ∧ Module.finrank K L ≤ (principalNormIdeles K L).index := by
  obtain ⟨_, _, hpos, _, hidx⟩ := herbrand_data K L h43 hc
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hne : (principalNormIdeles K L).index ≠ 0 := by
    rw [hidx]; positivity
  refine ⟨⟨hne⟩, ?_⟩
  rw [hidx]
  exact Nat.le_mul_of_pos_right _ hpos

/-! ## Theorem 5.1 and Lemma 5.2 -/

/-- **Theorem 5.1** (named statement; Milne, *CFT*, Chapter VII, p. 212): for every Galois extension $L/K$ of number
fields, (a) (second inequality) the index $(\mathbb I_K : K^\times\cdot\mathrm{Nm}(\mathbb I_L))$ is finite and divides
$[L:K]$; (b) $H^1(G, C_L) = 0$; (c) $H^2(G, C_L)$ is finite of order dividing $[L:K]$. -/
@[kb "milne2020cft" "Ch. VII, Thm. 5.1 (input)"]
structure Theorem5_1 : Prop where
  index_dvd : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ Module.finrank K L
  h1 : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    IsZero (groupCohomology (ideleClassRep K L) 1)
  h2 : ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L],
    Finite (groupCohomology (ideleClassRep K L) 2) ∧
      Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ Module.finrank K L

/-- **Lemma 5.2** (Milne, *CFT*, Chapter VII, p. 212; uses Theorem 4.3): if $G$ is cyclic, the statements (a), (b),
(c) of Theorem 5.1 for $L/K$ are equivalent, and then
$(\mathbb I_K : K^\times\mathrm{Nm}(\mathbb I_L)) = |H^2(G, C_L)| = [L:K]$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 5.2"]
theorem lemma_5_2 (h43 : Theorem4_3 K) (hc : IsCyclic Gal(L/K)) :
    let a := (principalNormIdeles K L).FiniteIndex ∧ (principalNormIdeles K L).index ∣ Module.finrank K L
    let b := IsZero (groupCohomology (ideleClassRep K L) 1)
    let c := Finite (groupCohomology (ideleClassRep K L) 2) ∧
      Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ Module.finrank K L
    (a ↔ b) ∧ (b ↔ c) ∧ (a → (principalNormIdeles K L).index = Module.finrank K L ∧
      Nat.card (groupCohomology (ideleClassRep K L) 2) = Module.finrank K L) := by
  obtain ⟨fin1, fin2, hpos, h2, hidx⟩ := herbrand_data K L h43 hc
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hfi : (principalNormIdeles K L).FiniteIndex := ⟨by rw [hidx]; positivity⟩
  have key : (principalNormIdeles K L).index ∣ Module.finrank K L ↔
      Nat.card (groupCohomology (ideleClassRep K L) 1) = 1 := by
    rw [hidx]
    constructor
    · intro h
      have := Nat.le_of_dvd hn h
      have h1 : Module.finrank K L * Nat.card (groupCohomology (ideleClassRep K L) 1) ≤
          Module.finrank K L * 1 := by omega
      have := Nat.le_of_mul_le_mul_left h1 hn
      omega
    · intro h; rw [h]; simp
  have hb : IsZero (groupCohomology (ideleClassRep K L) 1) ↔
      Nat.card (groupCohomology (ideleClassRep K L) 1) = 1 := by
    rw [ModuleCat.isZero_iff_subsingleton, Nat.card_eq_one_iff_unique]
    constructor
    · intro h; exact ⟨h, inferInstance⟩
    · intro h; exact h.1
  have h2' : Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ Module.finrank K L ↔
      (principalNormIdeles K L).index ∣ Module.finrank K L := by rw [h2]
  refine ⟨⟨fun h => hb.2 (key.1 h.2), fun h => ⟨hfi, key.2 (hb.1 h)⟩⟩,
    ⟨fun h => ⟨fin2, h2'.2 (key.2 (hb.1 h))⟩, fun h => hb.2 (key.1 (h2'.1 h.2))⟩, ?_⟩
  intro h
  have h1 := key.1 h.2
  rw [h1, mul_one] at hidx
  exact ⟨hidx, h2.trans hidx⟩

end NumberFieldKB.MilneCFT.Ch7
