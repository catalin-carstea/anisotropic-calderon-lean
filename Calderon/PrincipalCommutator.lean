import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.PrincipalCommutator
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

lemma smooth_deriv {f : ℝ → 𝔄} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

lemma smooth_deriv_real {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

lemma deriv_mul_smooth (f g : ℝ → 𝔄) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    deriv (fun y => f y * g y) x = deriv f x * g x + f x * deriv g x :=
  deriv_mul ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x)

/-- An actual variable-coefficient first base derivative with noncommuting coefficients. -/
def firstBase (K u : ℝ → 𝔄) : ℝ → 𝔄 := fun x => K x * deriv u x

/-- The actual angular-independent real scalar second base term. -/
def secondBase (a : ℝ → ℝ) (u : ℝ → 𝔄) : ℝ → 𝔄 :=
  fun x => a x • deriv (deriv u) x

lemma deriv_secondBase (a : ℝ → ℝ) (u : ℝ → 𝔄)
    (ha : ContDiff ℝ ∞ a) (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    deriv (secondBase a u) x =
      deriv a x • deriv (deriv u) x + a x • deriv (deriv (deriv u)) x := by
  unfold secondBase
  rw [deriv_fun_smul]
  · abel
  · exact (ha.differentiable (by simp)) x
  · exact ((smooth_deriv (smooth_deriv hu)).differentiable (by simp)) x

lemma deriv_firstBase (K u : ℝ → 𝔄) (hK : ContDiff ℝ ∞ K)
    (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    deriv (firstBase K u) x = deriv K x * deriv u x + K x * deriv (deriv u) x := by
  exact deriv_mul_smooth K (deriv u) hK (smooth_deriv hu) x

lemma deriv_deriv_firstBase (K u : ℝ → 𝔄) (hK : ContDiff ℝ ∞ K)
    (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    deriv (deriv (firstBase K u)) x =
      deriv (deriv K) x * deriv u x + deriv K x * deriv (deriv u) x +
        (deriv K x * deriv (deriv u) x + K x * deriv (deriv (deriv u)) x) := by
  have hformula : deriv (firstBase K u) =
      fun y => deriv K y * deriv u y + K y * deriv (deriv u) y :=
    funext fun y => deriv_firstBase K u hK hu y
  rw [hformula]
  rw [deriv_fun_add]
  · rw [deriv_mul_smooth (deriv K) (deriv u) (smooth_deriv hK) (smooth_deriv hu),
      deriv_mul_smooth K (deriv (deriv u)) hK (smooth_deriv (smooth_deriv hu))]
  · exact (((smooth_deriv hK).differentiable (by simp)) x).mul
      (((smooth_deriv hu).differentiable (by simp)) x)
  · exact ((hK.differentiable (by simp)) x).mul
      (((smooth_deriv (smooth_deriv hu)).differentiable (by simp)) x)

/-- Exact third-base cancellation for actual derivative operators. No third
 derivative of `u` occurs in the result, even for noncommuting angular coefficients. -/
theorem first_secondBase_commutator (a : ℝ → ℝ) (K u : ℝ → 𝔄)
    (ha : ContDiff ℝ ∞ a) (hK : ContDiff ℝ ∞ K) (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    firstBase K (secondBase a u) x - secondBase a (firstBase K u) x =
      deriv a x • (K x * deriv (deriv u) x) -
        (2 * a x) • (deriv K x * deriv (deriv u) x) -
        a x • (deriv (deriv K) x * deriv u x) := by
  simp only [firstBase, secondBase, deriv_secondBase a u ha hu,
    deriv_deriv_firstBase K u hK hu, mul_add, mul_smul_comm, smul_add]
  module

end OAI.AnisotropicCalderon.PrincipalCommutator
#print axioms OAI.AnisotropicCalderon.PrincipalCommutator.first_secondBase_commutator
