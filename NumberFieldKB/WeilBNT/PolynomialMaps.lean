import NumberFieldKB.WeilBNT.KLattices

/-!
# Weil, *Basic Number Theory*, IV.§1, text p. 61: polynomial maps extend to the adeles

$k$ is a number field (`K`) and $k_{\mathbb A}$ = `AdeleRing (𝓞 K) K`. With $E=k^n$, $E'=k^m$ and $E_{\mathbb A}=k_{\mathbb A}^n$
(Weil's $E_{\mathbb A}$ in coordinates), a polynomial map $f:E\to E'$, $f=(p_1,\dots,p_m)$ with $p_j\in k[X_1,\dots,X_n]$,
extends to the map $f_{\mathbb A}:E_{\mathbb A}\to E'_{\mathbb A}$ given by the same polynomials (`polyMapA`), which is
continuous and agrees with $f$ on $E$ (`weil_IV_1_text61`): each coordinate is a polynomial, and $k_{\mathbb A}$ is a
topological ring.
-/

open IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K : Type} [Field K] [NumberField K]

/-- A polynomial over $k$ in $n$ variables defines a continuous function on $k_{\mathbb A}^n$. -/
theorem continuous_aeval_adele {n : ℕ} (p : MvPolynomial (Fin n) K) :
    Continuous fun x : Fin n → AdeleRing (𝓞 K) K => MvPolynomial.aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C]; exact continuous_const
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (continuous_apply i)

/-- The extension $f_{\mathbb A}$ of the polynomial map $f=(p_j)_j:k^n\to k^m$. -/
def polyMapA {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) K) (x : Fin n → AdeleRing (𝓞 K) K) :
    Fin m → AdeleRing (𝓞 K) K :=
  fun j => MvPolynomial.aeval x (p j)

/-- **Weil, IV.§1, text p. 61**: a polynomial map $f:k^n\to k^m$ extends to a continuous map
$k_{\mathbb A}^n\to k_{\mathbb A}^m$, given by the same polynomials. -/
@[kb "weil1973bnt" "Ch. IV, §1, text p. 61 (polynomial maps extend continuously), number field case, E = k^n"]
theorem weil_IV_1_text61 {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) K) :
    Continuous (polyMapA p) ∧
      ∀ ξ : Fin n → K, polyMapA p (fun i => algebraMap K (AdeleRing (𝓞 K) K) (ξ i)) =
        fun j => algebraMap K (AdeleRing (𝓞 K) K) (MvPolynomial.eval ξ (p j)) := by
  refine ⟨continuous_pi fun j => continuous_aeval_adele (p j), fun ξ => funext fun j => ?_⟩
  show MvPolynomial.aeval (algebraMap K (AdeleRing (𝓞 K) K) ∘ ξ) (p j) = _
  rw [MvPolynomial.aeval_algebraMap_apply]
  rfl

end NumberFieldKB.WeilBNT
