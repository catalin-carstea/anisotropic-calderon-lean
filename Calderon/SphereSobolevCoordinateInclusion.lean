import Calderon.SphereSobolevCoordinateMultiplier
import Calderon.SphereSobolevInclusion

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal Classical
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevInclusionL_linearCoordinateMul_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts
      (sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s k a)) =
        sphereSobolevLinearCoordinateMulL hF hO hD t d
          (sphereSobolevInclusionL s t hts (sphereSobolevSingleL s k a)) := by
  let I : SphereSobolev s →L[ℝ] SphereSobolev t := sphereSobolevInclusionL s t hts
  have hr := congrArg (sphereSobolevLinearCoordinateMulL hF hO hD t d)
    (sphereSobolevInclusionL_single s t hts k a)
  cases k with
  | zero =>
    have hs := sphereSobolevLinearCoordinateMulL_constant hF hO hD s d a
    have ht := sphereSobolevLinearCoordinateMulL_constant hF hO hD t d a
    have hI := sphereSobolevInclusionL_single s t hts 1 (radialDriftAdjointBlockL hF d 0 a)
    have hleft : I (sphereSobolevLinearCoordinateMulL hF hO hD s d (sphereSobolevSingleL s 0 a)) =
        -sphereSobolevSingleL t 1 (radialDriftAdjointBlockL hF d 0 a) := by
      calc
        _ = I (-sphereSobolevSingleL s 1 (radialDriftAdjointBlockL hF d 0 a)) := congrArg I hs
        _ = -(I (sphereSobolevSingleL s 1 (radialDriftAdjointBlockL hF d 0 a))) := map_neg I _
        _ = _ := congrArg (fun x : SphereSobolev t => -x) hI
    exact hleft.trans (ht.symm.trans hr.symm)
  | succ k =>
    have hs := sphereSobolevLinearCoordinateMulL_single_succ hF hO hD s d k a
    have ht := sphereSobolevLinearCoordinateMulL_single_succ hF hO hD t d k a
    have h0 := sphereSobolevInclusionL_single s t hts k (radialDriftBlockL hF d k a)
    have h2 := sphereSobolevInclusionL_single s t hts (k+2) (radialDriftAdjointBlockL hF d (k+1) a)
    have hleft : I (sphereSobolevLinearCoordinateMulL hF hO hD s d
        (sphereSobolevSingleL s (k+1) a)) =
          -sphereSobolevSingleL t k (radialDriftBlockL hF d k a) -
            sphereSobolevSingleL t (k+2) (radialDriftAdjointBlockL hF d (k+1) a) := by
      calc
        _ = I (-sphereSobolevSingleL s k (radialDriftBlockL hF d k a) -
              sphereSobolevSingleL s (k+2) (radialDriftAdjointBlockL hF d (k+1) a)) :=
          congrArg I hs
        _ = I (-sphereSobolevSingleL s k (radialDriftBlockL hF d k a)) -
              I (sphereSobolevSingleL s (k+2) (radialDriftAdjointBlockL hF d (k+1) a)) := map_sub I _ _
        _ = -(I (sphereSobolevSingleL s k (radialDriftBlockL hF d k a))) -
              I (sphereSobolevSingleL s (k+2) (radialDriftAdjointBlockL hF d (k+1) a)) :=
          congrArg (fun x : SphereSobolev t => x -
            I (sphereSobolevSingleL s (k+2) (radialDriftAdjointBlockL hF d (k+1) a)))
              (map_neg I _)
        _ = _ := congrArg₂ (fun x y : SphereSobolev t => -x-y) h0 h2
    exact hleft.trans (ht.symm.trans hr.symm)

lemma sphereSobolevInclusionL_linearCoordinateMul
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (sphereSobolevLinearCoordinateMulL hF hO hD s d u) =
      sphereSobolevLinearCoordinateMulL hF hO hD t d (sphereSobolevInclusionL s t hts u) := by
  let A : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevInclusionL s t hts).comp (sphereSobolevLinearCoordinateMulL hF hO hD s d)
  let B : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevLinearCoordinateMulL hF hO hD t d).comp (sphereSobolevInclusionL s t hts)
  have hn (n : ℕ) : A (sphereSobolevPartialSum s n u) = B (sphereSobolevPartialSum s n u) := by
    unfold sphereSobolevPartialSum
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact sphereSobolevInclusionL_linearCoordinateMul_single hF hO hD s t hts d k
      (sphereSobolevCoefficientL s k u)
  have hA : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  have hB : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (B u)) := by
    simp_rw [hn]
    exact (B.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  exact tendsto_nhds_unique hA hB

lemma sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (hs : 0 ≤ s) (d : R3) (u : SphereSobolev s) (v : SphereL2)
    (hu : sphereSobolevInclusionL s 0 hs u = sphereSobolevZeroEquiv hO hD v) :
    sphereSobolevInclusionL s 0 hs (sphereSobolevLinearCoordinateMulL hF hO hD s d u) =
      sphereSobolevZeroEquiv hO hD (sphereLinearCoordinateMulL d v) := by
  rw [sphereSobolevInclusionL_linearCoordinateMul,hu,
    sphereSobolevLinearCoordinateMulL_zeroEquiv]

lemma sphereLinearCoordinateMulL_single (i : Fin 3) :
    sphereLinearCoordinateMulL (EuclideanSpace.single i 1) =
      DirichletFamily.sphereCoordinateMulL i := by
  have hterm (j : Fin 3) :
      (EuclideanSpace.single i (1 : ℝ)) j • DirichletFamily.sphereCoordinateMulL j =
        if j=i then DirichletFamily.sphereCoordinateMulL i else 0 := by
    rw [EuclideanSpace.single_apply]
    by_cases hji : j=i
    · subst j
      simp only [ite_true,one_smul]
    · simp only [hji,ite_false]
      exact _root_.zero_smul ℝ (DirichletFamily.sphereCoordinateMulL j)
  unfold sphereLinearCoordinateMulL
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_linearCoordinateMul_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_linearCoordinateMul
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_linearCoordinateMul_zeroEquiv
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereLinearCoordinateMulL_single
