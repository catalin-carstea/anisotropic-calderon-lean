import Calderon.PhysicalDegreeCasimirScalarFunctionals
import Calderon.SmoothSphereRotationProjection
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
open SphereHarmonic SmoothSphereRotationProjection
/-! Exact original mathematical blocks partitioned in EXPANSION-PARTITION-v002.json. -/

def degreeFiniteCasimirScalarL
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ncut mcut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) :
    PhysicalDegreeCasimirData →L[ℝ] ℝ :=
  (∑ m ∈ Finset.range mcut, ∑ n ∈ Finset.range ncut,
    (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) • degreeSharpBlockScalarL m n (u n) (v m))) -
  (1/2:ℝ) • (∑ ij : Fin 3 × Fin 3, (
    degreePrimalPhysicalScalarL hO hD ij
      (∑ n ∈ Finset.range ncut, sphereSobolevSingleL 1 n (u n))
      (∑ m ∈ Finset.range mcut, (harmonicSphereRotation m ij.1 ij.2 (v m) : SphereL2)) -
    degreePrimalPhysicalScalarL hO hD ij
      (∑ n ∈ Finset.range ncut,
        sphereSobolevSingleL 1 n (harmonicSphereRotation n ij.1 ij.2 (u n)))
      (∑ m ∈ Finset.range mcut, (v m : SphereL2))))

lemma degreeFiniteCasimirScalarL_apply
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (ncut mcut : ℕ) (u v : ∀ k, harmonicSphereSubspace k) (x : PhysicalDegreeCasimirData) :
    degreeFiniteCasimirScalarL hO hD ncut mcut u v x =
    (∑ m ∈ Finset.range mcut, ∑ n ∈ Finset.range ncut,
      (((m:ℝ)*((m:ℝ)+1)-(n:ℝ)*((n:ℝ)+1)) *
        ⟪sphereSobolevCoefficientL (1/2:ℝ) m
          (x.1.2 (sphereSobolevSingleL (3/2:ℝ) n (u n))),v m⟫_ℝ)) -
    (1/2:ℝ) * (∑ ij : Fin 3 × Fin 3, (
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (x.2.1 ij (∑ n ∈ Finset.range ncut, sphereSobolevSingleL 1 n (u n))),
        (∑ m ∈ Finset.range mcut, (harmonicSphereRotation m ij.1 ij.2 (v m) : SphereL2))⟫_ℝ -
      ⟪(sphereSobolevZeroEquiv hO hD).symm
          (x.2.1 ij (∑ n ∈ Finset.range ncut,
            sphereSobolevSingleL 1 n (harmonicSphereRotation n ij.1 ij.2 (u n)))),
        (∑ m ∈ Finset.range mcut, (v m : SphereL2))⟫_ℝ)) := by
  simp only [degreeFiniteCasimirScalarL, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    degreeSharpBlockScalarL_apply, degreePrimalPhysicalScalarL_apply, smul_eq_mul]


#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeFiniteCasimirScalarL
#print axioms OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility.degreeFiniteCasimirScalarL_apply
end OAI.AnisotropicCalderon.PhysicalDegreeCasimirCompatibility
