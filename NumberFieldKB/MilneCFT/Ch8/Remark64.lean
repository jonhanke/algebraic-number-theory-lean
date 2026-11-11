import NumberFieldKB.MilneCFT.Ch8.GaloisDescentForms
import QuadFormsKB.Tamagawa.FormClassNF
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Milne, *Class Field Theory*, VIII, Remark 6.4: Hasse–Minkowski as injectivity of $H^1(K,O) \to \prod_v H^1(K_v,O)$

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §6,
Remark 6.4 (pdf p. 261, printed p. 252): "Let $(V,Q)$ be a quadratic space over a field $k$, and let $O$ be its group
of isometries. Theorem 6.3 says that $H^1(K, O) \to \prod_v H^1(K_v, O)$ is injective."

## What is formalized (finite level)

Milne's $H^1(K, O)$ is the union over finite Galois $L/K$ of $H^1(\operatorname{Gal}(L/K), O_Q(L))$ (inflation is
injective), and $H^1(K_v, O)$ likewise over the completions $L_w$, with the localization map given by restriction to
the decomposition group $D_w \cong \operatorname{Gal}(L_w/K_v)$ and $L \hookrightarrow L_w$. We work at a fixed finite
Galois level $L/K$, with the local data abstracted:

* `LocalGaloisDatum K L F`: a field $E \supseteq F$ (think $L_w \supseteq K_v$), an embedding $L \to E$ compatible
  with $K \to F$, a subgroup $D \le \operatorname{Gal}(L/K)$ acting on $E$ by $F$-automorphisms compatibly with
  $L \to E$, with fixed field exactly $F$ (`fixed`). For finite places this is Weil's Cor. 4 of III.§4
  (`NumberFieldKB.WeilBNT.weil_III_4_cor4_galois`).
* `LocCohomologous d Q a a'`: the images of $a, a'$ in $H^1(D, O_Q(E))$ agree.
* **`remark_6_4_of_data`**: for a number field $K$, a finite Galois $L/K$, a nondegenerate $Q$ over $K$, and a
  local datum at every place (infinite and finite) of $K$, two $O_Q(L)$-valued cocycles that are locally cohomologous at
  every place are cohomologous: the localization map
  $H^1(\operatorname{Gal}(L/K), O_Q(L)) \to \prod_v H^1(D_v, O_Q(E_v))$ is injective.

*Proof* (Milne's reading). By Galois descent (`galois_descent_exists`) the two classes are the twists $Q_1, Q_2$ of
$Q$; local cohomology at $v$ gives $g = P_1^{-1} c P_2 \in \mathrm{GL}_n(E)$ fixed by $D$, hence in $\mathrm{GL}_n(F)$,
with $g^{\mathsf T} H_1 g = H_2$: $Q_1 \cong Q_2$ over $K_v$ (`isometricIn_of_locCohomologous`). Hasse–Minkowski
(QuadFormsKB `isometricIn_of_everywhere_nf`, Theorem 6.3) gives $Q_1 \cong Q_2$ over $K$, and descent
(`galois_descent_cohomologous_iff`) turns this back into cohomologous cocycles.
-/

open Matrix QuadFormsKB QuadFormsKB.Lattices NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {n : ℕ}

/-- **Local Galois data at a place** (abstracting $L_w \supseteq K_v$ with $D_w \cong \operatorname{Gal}(L_w/K_v)$):
a field `E` over `F`, an embedding `emb : L → E` restricting to $K \to F \to E$, a subgroup `D` of
$\operatorname{Gal}(L/K)$ and an action `act` of `D` on `E` by $F$-algebra automorphisms with
`act σ (emb x) = emb (σ x)`, whose fixed field is exactly $F$ (`fixed`). -/
structure LocalGaloisDatum (K L : Type) [Field K] [Field L] [Algebra K L] (F : Type) [Field F] [Algebra K F] where
  /-- The local field $E$ (e.g. $L_w$). -/
  E : Type
  [instField : Field E]
  [instAlg : Algebra F E]
  /-- The embedding $L \to E$. -/
  emb : L →+* E
  emb_algebraMap : ∀ x : K, emb (algebraMap K L x) = algebraMap F E (algebraMap K F x)
  /-- The decomposition group. -/
  D : Subgroup (L ≃ₐ[K] L)
  /-- The action of the decomposition group on $E$. -/
  act : D →* (E ≃ₐ[F] E)
  act_emb : ∀ (σ : D) (x : L), act σ (emb x) = emb ((σ : L ≃ₐ[K] L) x)
  fixed : ∀ y : E, (∀ σ : D, act σ y = y) → y ∈ Set.range (algebraMap F E)

attribute [instance] LocalGaloisDatum.instField LocalGaloisDatum.instAlg

variable {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L] [FiniteDimensional K L]

namespace LocalGaloisDatum

variable {F : Type} [Field F] [Algebra K F] (d : LocalGaloisDatum K L F)

/-- The structure map $K \to E$ (through $F$). -/
def κ : K →+* d.E := (algebraMap F d.E).comp (algebraMap K F)

/-- The image of a cocycle in $\mathrm{GL}_n(E)$, restricted to $D$. -/
def locCocycle (a : (L ≃ₐ[K] L) → GL (Fin n) L) (σ : d.D) : GL (Fin n) d.E :=
  Matrix.GeneralLinearGroup.map d.emb (a σ)

end LocalGaloisDatum

/-- **Equal local classes**: the restrictions of $a, a'$ to $D$, pushed to $\mathrm{GL}_n(E)$, are cohomologous in
$O_Q(E) = \{c : c^{\mathsf T} H c = H\}$ ($H$ the Hessian of $Q$ in $E$). -/
def LocCohomologous {F : Type} [Field F] [Algebra K F] (d : LocalGaloisDatum K L F) (Q : QuadForm K n)
    (a a' : (L ≃ₐ[K] L) → GL (Fin n) L) : Prop :=
  ∃ c : GL (Fin n) d.E, cong c (Q.hessian.map d.κ) = Q.hessian.map d.κ ∧
    ∀ σ : d.D, d.locCocycle a' σ = c⁻¹ * d.locCocycle a σ * Matrix.GeneralLinearGroup.map (d.act σ : d.E →+* d.E) c

theorem map_emb_hessian {F : Type} [Field F] [Algebra K F] (d : LocalGaloisDatum K L F) (Q : QuadForm K n) :
    (Q.hessian.map (algebraMap K L)).map d.emb = Q.hessian.map d.κ := by
  ext i j
  simp [d.emb_algebraMap, LocalGaloisDatum.κ]

/-- **Local step**: twists of $Q$ whose cocycles have the same local class at a datum over $F$ are isometric over
$F$. -/
theorem isometricIn_of_locCohomologous {F : Type} [Field F] [Algebra K F] (d : LocalGaloisDatum K L F)
    {Q Q₁ Q₂ : QuadForm K n} {P₁ P₂ : GL (Fin n) L} (h₁ : IsTwist Q Q₁ P₁) (h₂ : IsTwist Q Q₂ P₂)
    (hloc : LocCohomologous d Q (twistCocycle (K := K) P₁) (twistCocycle P₂)) : Q₁.IsometricIn F Q₂ := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  obtain ⟨c, hc, hcoh⟩ := hloc
  set ε := Matrix.GeneralLinearGroup.map (n := Fin n) d.emb
  set S := Q.hessian.map d.κ
  have hP : ∀ {Q' : QuadForm K n} {P : GL (Fin n) L}, IsTwist Q Q' P → cong (ε P) S = Q'.hessian.map d.κ := by
    intro Q' P h
    have h' : cong P (Q.hessian.map (algebraMap K L)) = Q'.hessian.map (algebraMap K L) := h
    rw [← map_emb_hessian d Q', ← h', cong_map, map_emb_hessian]
  set g : GL (Fin n) d.E := (ε P₁)⁻¹ * c * ε P₂
  have hεσ : ∀ (σ : d.D) (P : GL (Fin n) L),
      Matrix.GeneralLinearGroup.map (d.act σ : d.E →+* d.E) (ε P) = ε (galGL (σ : L ≃ₐ[K] L) P) := by
    intro σ P
    ext i j
    exact d.act_emb σ _
  have hgfix : ∀ σ : d.D, (g : Matrix (Fin n) (Fin n) d.E).map (d.act σ) = g := by
    intro σ
    have e := hcoh σ
    simp only [LocalGaloisDatum.locCocycle, twistCocycle, map_mul, map_inv] at e
    have hy : Matrix.GeneralLinearGroup.map (d.act σ : d.E →+* d.E) c =
        ε (galGL (σ : L ≃ₐ[K] L) P₁) * (ε P₁)⁻¹ * c * (ε P₂ * (ε (galGL (σ : L ≃ₐ[K] L) P₂))⁻¹) := by
      rw [show ε = Matrix.GeneralLinearGroup.map d.emb from rfl, e]; group
    have : Matrix.GeneralLinearGroup.map (d.act σ : d.E →+* d.E) g = g := by
      simp only [g, map_mul, map_inv, hεσ]
      rw [hy]; group
    exact congrArg Units.val this
  -- `g` has entries in `F`
  have hent : ∀ i j, ∃ x : F, algebraMap F d.E x = (g : Matrix (Fin n) (Fin n) d.E) i j := by
    intro i j
    obtain ⟨x, hx⟩ := d.fixed _ fun σ => congrFun (congrFun (hgfix σ) i) j
    exact ⟨x, hx⟩
  choose N hN using hent
  have hNmap : (Matrix.of N).map (algebraMap F d.E) = g := by ext i j; exact hN i j
  have hdet : IsUnit (Matrix.of N).det := by
    have : algebraMap F d.E (Matrix.of N).det = (g : Matrix (Fin n) (Fin n) d.E).det := by
      rw [← hNmap, RingHom.map_det]; rfl
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, map_zero] at this
    exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit |>.ne_zero this.symm
  rw [isometricIn_iff_hessian]
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hdet).unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply Matrix.map_injective (algebraMap F d.E).injective
  change ((Matrix.of N)ᵀ * Q₁.hessian.map (algebraMap K F) * Matrix.of N).map (algebraMap F d.E) = _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hNmap, Matrix.map_map]
  show _ = (Q₂.hessian.map (algebraMap K F)).map (algebraMap F d.E)
  rw [Matrix.map_map]
  change cong g (Q₁.hessian.map d.κ) = Q₂.hessian.map d.κ
  rw [← hP h₁, ← hP h₂]
  rw [← cong_mul, show ε P₁ * g = c * ε P₂ by simp only [g]; group, cong_mul, hc]

/-- A twist of a nondegenerate form is nondegenerate. -/
theorem IsTwist.nondegenerate {Q Q' : QuadForm K n} {P : GL (Fin n) L} (h : IsTwist Q Q' P)
    (hQ : Q.Nondegenerate) : Q'.Nondegenerate := by
  intro h0
  have hd := congrArg Matrix.det h
  have e1 : (Q.hessian.map (algebraMap K L)).det = algebraMap K L Q.hessian.det := (RingHom.map_det _ _).symm
  have e2 : (Q'.hessian.map (algebraMap K L)).det = algebraMap K L Q'.hessian.det :=
    (RingHom.map_det _ _).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e1, e2, h0, map_zero] at hd
  have hP : (P : Matrix (Fin n) (Fin n) L).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit).ne_zero
  have hQ' : algebraMap K L Q.hessian.det ≠ 0 := (map_ne_zero _).mpr hQ
  exact mul_ne_zero (mul_ne_zero hP hQ') hP hd

/-- **Milne, *CFT*, VIII, Remark 6.4** (finite Galois level, p. 252): for a number field $K$, a finite Galois
extension $L/K$, a nondegenerate form $Q$ over $K$ and local Galois data at all places of $K$ (infinite: over
$K_w$ = `w.Completion`; finite: over $K_\mathfrak p$ = `v.adicCompletion K`), the localization map
$H^1(\operatorname{Gal}(L/K), O_Q(L)) \to \prod_v H^1(D_v, O_Q(E_v))$ is injective: two $O_Q(L)$-valued cocycles
with the same local classes everywhere are cohomologous. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Remark 6.4, p. 252 (finite level, abstract local data)"]
theorem remark_6_4_of_data [IsGalois K L] {Q : QuadForm K n} (hQ : Q.Nondegenerate)
    (dInf : ∀ w : InfinitePlace K, LocalGaloisDatum K L w.Completion)
    (dFin : ∀ v : HeightOneSpectrum (𝓞 K), LocalGaloisDatum K L (v.adicCompletion K))
    {a a' : (L ≃ₐ[K] L) → GL (Fin n) L} (ha : IsOrthCocycle Q a) (ha' : IsOrthCocycle Q a')
    (hInf : ∀ w, LocCohomologous (dInf w) Q a a') (hFin : ∀ v, LocCohomologous (dFin v) Q a a') :
    OrthCohomologous Q a a' := by
  obtain ⟨Q₁, P₁, h₁, rfl⟩ := galois_descent_exists Q ha
  obtain ⟨Q₂, P₂, h₂, rfl⟩ := galois_descent_exists Q ha'
  rw [galois_descent_cohomologous_iff h₁ h₂]
  refine Tamagawa.FormClassNF.isometricIn_of_everywhere_nf Q₁ Q₂ (h₁.nondegenerate hQ) (h₂.nondegenerate hQ) ?_
  rintro (w | v)
  · exact isometricIn_of_locCohomologous (dInf w) h₁ h₂ (hInf w)
  · exact isometricIn_of_locCohomologous (dFin v) h₁ h₂ (hFin v)

end NumberFieldKB.MilneCFT.Ch8
