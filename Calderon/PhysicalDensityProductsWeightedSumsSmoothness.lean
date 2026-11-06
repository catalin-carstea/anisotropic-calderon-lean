import Calderon.FiniteOperatorProductsSmoothness
import Calderon.SphereSobolevCompletion

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)

lemma contDiffOn_fin_three_weighted_operator_products
    (U : Set R3) (w : R3 → ℝ) (coeff : Fin 3 → Fin 3 → R3 → ℝ)
    (Fh Fbh : Fin 3 → R3 → Hi →L[ℝ] Hi)
    (Fl Fbl : Fin 3 → R3 → Half →L[ℝ] Half)
    (Eh Eb : Fin 3 → R3 → Hi →L[ℝ] Half)
    (hw : ContDiffOn ℝ ∞ w U)
    (hQ : ∀ i j : Fin 3, ContDiffOn ℝ ∞ (coeff i j) U)
    (hFh : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fh i) U)
    (hFbh : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fbh i) U)
    (hFl : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fl i) U)
    (hFbl : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Fbl i) U)
    (hEh : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Eh i) U)
    (hEb : ∀ i : Fin 3, ContDiffOn ℝ ∞ (Eb i) U) :
    ContDiffOn ℝ ∞ (fun x : R3 => w x •
      (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Fl i x).comp (Eh j x)+(Eh i x).comp (Fh j x)))) U ∧
    ContDiffOn ℝ ∞ (fun x : R3 => w x •
      (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Eb j x).comp (Fbh i x)+(Fbl j x).comp (Eb i x)))) U := by
  let : IsBoundedSMul ℝ (Hi →L[ℝ] Half) :=
    @NormedSpace.toIsBoundedSMul ℝ
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
      (ContinuousLinearMap.toSeminormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ))
  have hProducts :
      ContDiffOn ℝ ∞ (fun x : R3 => ∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Fl i x).comp (Eh j x)+(Eh i x).comp (Fh j x))) U ∧
      ContDiffOn ℝ ∞ (fun x : R3 => w x •
        (∑ i : Fin 3, ∑ j : Fin 3,
          coeff i j x • ((Eb j x).comp (Fbh i x)+(Fbl j x).comp (Eb i x)))) U :=
    contDiffOn_fin_three_operator_products
      R3 Hi Half U w coeff Fh Fbh Fl Fbl Eh Eb
      hw hQ hFh hFbh hFl hFbl hEh hEb
  have hDirect : ContDiffOn ℝ ∞ (fun x : R3 => w x •
      (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Fl i x).comp (Eh j x)+(Eh i x).comp (Fh j x)))) U :=
    hw.smul hProducts.1
  have hDag : ContDiffOn ℝ ∞ (fun x : R3 => w x •
      (∑ i : Fin 3, ∑ j : Fin 3,
        coeff i j x • ((Eb j x).comp (Fbh i x)+(Fbl j x).comp (Eb i x)))) U :=
    hProducts.2
  exact ⟨hDirect, hDag⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
