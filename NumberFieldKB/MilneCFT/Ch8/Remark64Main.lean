import NumberFieldKB.MilneCFT.Ch8.Remark64Finite
import NumberFieldKB.MilneCFT.Ch8.Remark64Infinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Milne, *Class Field Theory*, VIII, Remark 6.4 (finite Galois level, unconditional)

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §6,
Remark 6.4 (pdf p. 261, printed p. 252): Theorem 6.3 (Hasse–Minkowski) says that
$H^1(K, O) \to \prod_v H^1(K_v, O)$ is injective, $O$ the isometry group of a quadratic space over $K$.

**`remark_6_4`**: let $L/K$ be a finite Galois extension of number fields and $Q$ a nondegenerate form over $K$
(`Q : QuadForm K n`, QuadFormsKB). At every place $v$ of $K$ choose a place $w \mid v$ of $L$; the decomposition
group $D_w$ acts on $L_w$ (finite places: $E_v = L_w$, `finiteDatum`, Weil III.§4 Cor. 4; infinite places:
`exists_infiniteDatum`, $E_v = K_v$ or $\mathbb C$). Then the localization map
$$H^1(\operatorname{Gal}(L/K), O_Q(L)) \longrightarrow \prod_v H^1(D_w, O_Q(E_v))$$
is injective: two $O_Q(L)$-valued cocycles that are cohomologous in $O_Q(E_v)$ after restriction to $D_w$, at every
place, are cohomologous. Since $H^1(K, O) = \varinjlim_L H^1(\operatorname{Gal}(L/K), O_Q(L))$ with injective
transition maps, this is Milne's statement at each finite level. Proof: `remark_6_4_of_data` (Galois descent and
Hasse–Minkowski). No hypothesis beyond the setting: unconditional.
-/

open NumberField IsDedekindDomain QuadFormsKB QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

variable {n : ℕ} {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Milne, *CFT*, VIII, Remark 6.4** (p. 252), at a finite Galois level $L/K$ of number fields: there are local
Galois data at all places — at a finite $v$ the completion $L_w$ ($w \mid v$) with the decomposition group
$D_w = \{\sigma : \sigma w = w\}$, at an infinite $v$ a datum whose group is the stabilizer of a place $w \mid v$ —
for which the localization map $H^1(\operatorname{Gal}(L/K), O_Q(L)) \to \prod_v H^1(D_w, O_Q(E_v))$ is injective,
for every nondegenerate form $Q$ over $K$. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Remark 6.4, p. 252"]
theorem remark_6_4 [IsGalois K L] :
    ∃ (dInf : ∀ v : InfinitePlace K, LocalGaloisDatum K L v.Completion)
      (dFin : ∀ v : HeightOneSpectrum (𝓞 K), LocalGaloisDatum K L (v.adicCompletion K)),
      (∀ v, ∃ w : InfinitePlace L, w.comap (algebraMap K L) = v ∧
        (dInf v).D = MulAction.stabilizer (L ≃ₐ[K] L) w) ∧
      (∀ v, ∃ (w : HeightOneSpectrum (𝓞 L)) (hw : underPlace (k := K) w = v),
        dFin v = finiteDatum v w hw ∧ (dFin v).D = decompGroup w) ∧
      ∀ {Q : QuadForm K n}, Q.Nondegenerate → ∀ {a a' : (L ≃ₐ[K] L) → GL (Fin n) L},
        IsOrthCocycle Q a → IsOrthCocycle Q a' →
        (∀ v, LocCohomologous (dInf v) Q a a') → (∀ v, LocCohomologous (dFin v) Q a a') →
        OrthCohomologous Q a a' := by
  choose dInf w hw hD using fun v : InfinitePlace K => exists_infiniteDatum K L v
  choose wf hwf using fun v : HeightOneSpectrum (𝓞 K) => exists_place_above (L := L) v
  refine ⟨dInf, fun v => finiteDatum v (wf v) (hwf v), fun v => ⟨w v, hw v, hD v⟩,
    fun v => ⟨wf v, hwf v, rfl, finiteDatum_D _ _ _⟩, ?_⟩
  intro Q hQ a a' ha ha' hInf hFin
  exact remark_6_4_of_data hQ dInf _ ha ha' hInf hFin

end NumberFieldKB.MilneCFT.Ch8
