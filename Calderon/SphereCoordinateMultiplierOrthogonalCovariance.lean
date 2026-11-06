import Calderon.NativeSphereL2OrthogonalPullback
import Calderon.NativeValueRadialTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open OrthogonalSphereMeasure DirichletFamily

/-! Expansion: EXPANSION-native-H2-outward-trace-orthogonal-joint-v001.md, steps 1–2. -/
lemma orthogonal_forward_coordinate_eq_sum (e : R3 ≃ₗᵢ[ℝ] R3) (x : R3) (i : Fin 3) :
    (e x) i = ∑ j : Fin 3, (e (EuclideanSpace.single j 1)) i * x j := by
  have hx : (∑ j : Fin 3, x j • EuclideanSpace.single j 1) = x := by
    apply PiLp.ext
    intro l
    change (EuclideanSpace.proj l) (∑ j : Fin 3, x j • EuclideanSpace.single j 1) = x l
    simp [map_sum,map_smul,EuclideanSpace.coe_proj,EuclideanSpace.single_apply]
  calc
    (e x) i = (EuclideanSpace.proj i) (e (∑ j : Fin 3, x j • EuclideanSpace.single j 1)) :=
      congrArg (fun z : R3 => (e z) i) hx.symm
    _ = ∑ j : Fin 3, (e (EuclideanSpace.single j 1)) i * x j := by
      simp only [map_sum,map_smul,EuclideanSpace.coe_proj,smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j hj
      exact mul_comm _ _

lemma sphereCoordinateMulL_value_ae (i : Fin 3) (u : SphereL2) :
    sphereCoordinateMulL i u =ᵐ[sphereProbability]
      (fun x : UnitSphere => x.val i * u x) :=
  sphereCoordinateMul_value_ae i u

lemma sphereL2OrthogonalPullback_coordinateMul
    (e : R3 ≃ₗᵢ[ℝ] R3) (i : Fin 3) (u : SphereL2) :
    sphereL2OrthogonalPullback e (sphereCoordinateMulL i u) =
      ∑ j : Fin 3, (e (EuclideanSpace.single j 1)) i •
        sphereCoordinateMulL j (sphereL2OrthogonalPullback e u) := by
  let c : Fin 3 → ℝ := fun j => (e (EuclideanSpace.single j 1)) i
  have hLeft := Lp.coeFn_compMeasurePreserving (sphereCoordinateMulL i u)
    (orthogonalSphereHomeomorph_sphereProbability_preserving e)
  have hLeftMul := (orthogonalSphereHomeomorph_sphereProbability_preserving e).quasiMeasurePreserving.ae_eq_comp
    (sphereCoordinateMulL_value_ae i u)
  have hRot := Lp.coeFn_compMeasurePreserving u
    (orthogonalSphereHomeomorph_sphereProbability_preserving e)
  have hTerm (j : Fin 3) : c j • sphereCoordinateMulL j (sphereL2OrthogonalPullback e u)
      =ᵐ[sphereProbability] (fun x : UnitSphere => c j * (x.val j * sphereL2OrthogonalPullback e u x)) := by
    filter_upwards [Lp.coeFn_smul (c j) (sphereCoordinateMulL j (sphereL2OrthogonalPullback e u)),
      sphereCoordinateMulL_value_ae j (sphereL2OrthogonalPullback e u)] with x hs hm
    exact hs.trans (congrArg (c j * ·) hm)
  have hSum : (∑ j : Fin 3, c j • sphereCoordinateMulL j (sphereL2OrthogonalPullback e u))
      =ᵐ[sphereProbability] (fun x : UnitSphere =>
        ∑ j : Fin 3, c j * (x.val j * sphereL2OrthogonalPullback e u x)) := by
    exact (Lp.coeFn_finsetSum Finset.univ (fun j =>
      c j • sphereCoordinateMulL j (sphereL2OrthogonalPullback e u))).trans
      (eventuallyEq_sum fun j _ => hTerm j)
  apply Lp.ext
  filter_upwards [hLeft,hLeftMul,hRot,hSum] with x hL hM hR hS
  change sphereL2OrthogonalPullback e (sphereCoordinateMulL i u) x =
    (∑ j : Fin 3, c j • sphereCoordinateMulL j (sphereL2OrthogonalPullback e u)) x
  change sphereL2OrthogonalPullback e (sphereCoordinateMulL i u) x =
    sphereCoordinateMulL i u (orthogonalSphereHomeomorph e x) at hL
  change sphereL2OrthogonalPullback e u x = u (orthogonalSphereHomeomorph e x) at hR
  change sphereCoordinateMulL i u (orthogonalSphereHomeomorph e x) =
    (orthogonalSphereHomeomorph e x).val i * u (orthogonalSphereHomeomorph e x) at hM
  rw [hL,hM,hS,hR]
  change (e x.val) i * u (orthogonalSphereHomeomorph e x) =
    ∑ j : Fin 3, c j * (x.val j * u (orthogonalSphereHomeomorph e x))
  rw [orthogonal_forward_coordinate_eq_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_assoc _ _ _

end OAI.AnisotropicCalderon.SphereHarmonic
