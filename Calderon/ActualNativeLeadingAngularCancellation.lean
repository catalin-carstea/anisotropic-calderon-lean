import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.ActualReferenceParallelRaising
import Calderon.ActualHorizontalSobolevConnection

/-! Upfront: actual-physical-leading-cancellation-author-oct16-v001/EXPANSION-v001.md.
Three concrete native leading identities; no physical/quartic conclusion assumed. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic HarmonicDerivativeOperator ActualReferenceParallelRaising
  SmoothMetricFrame MovingFrameConnection HarmonicCoordinateCompatibility SphereDerivativeAdjoint SmoothSphereRotationProjection

attribute [local irreducible] sphereSobolevAngularCoordinateTransposeL
  sphereSobolevRotationL sphereSobolevShiftedDegreeL sphereSobolevInclusionL
  referenceMetricGramFrame referenceFrameConnectionCoefficient

lemma referenceHorizontalAngular_angularTranspose_commutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L0 q : ℝ) (y : R3)
    (i j : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    referenceLowerHorizontalAngularL g L0 q y i
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u) -
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j
        (referenceHighHorizontalAngularL g L0 q y i u) =
    ∑ k : Fin 3,
      referenceFrameConnectionCoefficient g L0 q y (referenceMetricGramFrame g L0 (q,y) i) k j •
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
          (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) k u) := by
  let X := referenceMetricGramFrame g L0 (q,y) i
  let L : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (referenceLowerHorizontalAngularL g L0 q y i).comp
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j) -
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j).comp
      (referenceHighHorizontalAngularL g L0 q y i)
  let R : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    ∑ a : Fin 3, referenceFrameConnectionCoefficient g L0 q y X a j •
      (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) a)
  have hAH (a : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) a
        (sphereSobolevSingleL (3/2 : ℝ) k v) =
      sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) a k v
    have hIndex : sphereSobolevSingleL ((3/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k a v) =
        sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k a v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact h.trans hIndex
  have hAL (a : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) a
        (sphereSobolevSingleL (1/2 : ℝ) k v) =
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2 : ℝ) a k v
    have hIndex : sphereSobolevSingleL ((1/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k a v) =
        sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k a v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact h.trans hIndex
  have hOH (k : ℕ) (v : harmonicSphereSubspace k) :
      referenceHighHorizontalAngularL g L0 q y i (sphereSobolevSingleL (3/2 : ℝ) k v) =
      sphereSobolevSingleL (1/2 : ℝ) k
        (harmonicReferenceAngularConnection g L0 q k y X v) := by
    have hBase : referenceHighHorizontalAngularL g L0 q y i (sphereSobolevSingleL (3/2 : ℝ) k v) =
        sphereSobolevSingleL ((3/2 : ℝ)-1) k
          (harmonicReferenceAngularConnection g L0 q k y X v) := by
      simp (config := { instances := true }) only
        [referenceHighHorizontalAngularL,harmonicReferenceAngularConnection,X,
          ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
          sphereSobolevRotationL_single,map_smul,map_sum]
    have hIndex : sphereSobolevSingleL ((3/2 : ℝ)-1) k (harmonicReferenceAngularConnection g L0 q k y X v) =
        sphereSobolevSingleL (1/2 : ℝ) k (harmonicReferenceAngularConnection g L0 q k y X v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t k)
        (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k (harmonicReferenceAngularConnection g L0 q k y X v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact hBase.trans hIndex
  have hOL (k : ℕ) (v : harmonicSphereSubspace k) :
      referenceLowerHorizontalAngularL g L0 q y i (sphereSobolevSingleL (1/2 : ℝ) k v) =
      sphereSobolevSingleL (-(1/2 : ℝ)) k
        (harmonicReferenceAngularConnection g L0 q k y X v) := by
    have hBase : referenceLowerHorizontalAngularL g L0 q y i (sphereSobolevSingleL (1/2 : ℝ) k v) =
        sphereSobolevSingleL ((1/2 : ℝ)-1) k
          (harmonicReferenceAngularConnection g L0 q k y X v) := by
      simp (config := { instances := true }) only
        [referenceLowerHorizontalAngularL,harmonicReferenceAngularConnection,X,
          ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
          sphereSobolevRotationL_single,map_smul,map_sum]
    have hIndex : sphereSobolevSingleL ((1/2 : ℝ)-1) k (harmonicReferenceAngularConnection g L0 q k y X v) =
        sphereSobolevSingleL (-(1/2 : ℝ)) k (harmonicReferenceAngularConnection g L0 q k y X v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t k)
        (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k (harmonicReferenceAngularConnection g L0 q k y X v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact hBase.trans hIndex
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      L (sphereSobolevSingleL (3/2 : ℝ) k v) =
        R (sphereSobolevSingleL (3/2 : ℝ) k v) := by
    have h1 := (congrArg (referenceLowerHorizontalAngularL g L0 q y i) (hAH j k v)).trans
      (hOL (k+1) (harmonicDerivativeAdjoint hF k j v))
    have h2 := (congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j)
      (hOH k v)).trans (hAL j k (harmonicReferenceAngularConnection g L0 q k y X v))
    have hLeft := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a-b) h1 h2
    have hTransport := congrArg (sphereSobolevSingleL (-(1/2 : ℝ)) (k+1))
      (harmonicReferenceAngularConnection_raising_commutator hF g hg L0 q k y X j v)
    simp (config := { instances := true }) only [map_sub,map_sum,map_smul] at hTransport
    have hRight : R (sphereSobolevSingleL (3/2 : ℝ) k v) =
        ∑ a : Fin 3, referenceFrameConnectionCoefficient g L0 q y X a j •
          sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      simp (config := { instances := true }) only
        [R,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply,hAH,sphereSobolevInclusionL_single]
    simpa (config := { instances := true }) only
      [L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply]
      using hLeft.trans (hTransport.trans hRight.symm)
  have hFinite (n : ℕ) : L (sphereSobolevPartialSum (3/2 : ℝ) n u) =
      R (sphereSobolevPartialSum (3/2 : ℝ) n u) := by
    simp (config := { instances := true }) only [sphereSobolevPartialSum,map_sum]
    exact Finset.sum_congr rfl (fun k hk => hSingle k (sphereSobolevCoefficientL (3/2 : ℝ) k u))
  have hLeft := (L.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  have hRight := (R.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  have hValue := tendsto_nhds_unique
    (hLeft.congr' (Filter.Eventually.of_forall hFinite)) hRight
  simpa (config := { instances := true }) only
    [L,R,X,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply] using hValue

lemma sphereSobolevShiftedDegree_angularTranspose_commutator
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (j : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevShiftedDegreeL (1/2 : ℝ)
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u) -
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) u) =
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j u) := by
  let L : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (sphereSobolevShiftedDegreeL (1/2 : ℝ)).comp
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j) -
    (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j).comp
      (sphereSobolevShiftedDegreeL (3/2 : ℝ))
  let R : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) j)
  have hAH (a : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) a
        (sphereSobolevSingleL (3/2 : ℝ) k v) =
      sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) a k v
    have hIndex : sphereSobolevSingleL ((3/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k a v) =
        sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k a v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact h.trans hIndex
  have hAL (a : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) a
        (sphereSobolevSingleL (1/2 : ℝ) k v) =
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2 : ℝ) a k v
    have hIndex : sphereSobolevSingleL ((1/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k a v) =
        sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k a v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact h.trans hIndex
  have hBH (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevShiftedDegreeL (3/2 : ℝ) (sphereSobolevSingleL (3/2 : ℝ) k v) =
        (k : ℝ) • sphereSobolevSingleL (1/2 : ℝ) k v := by
    have hIndex : sphereSobolevSingleL ((3/2 : ℝ)-1) k v =
        sphereSobolevSingleL (1/2 : ℝ) k v := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t k)
        (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k v) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact (sphereSobolevShiftedDegreeL_single (3/2 : ℝ) k v).trans
      (congrArg (fun z : SphereSobolev ((1/2 : ℝ)) => (k : ℝ) • z) hIndex)
  have hBL (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevShiftedDegreeL (1/2 : ℝ) (sphereSobolevSingleL (1/2 : ℝ) k v) =
        (k : ℝ) • sphereSobolevSingleL (-(1/2 : ℝ)) k v := by
    have hIndex : sphereSobolevSingleL ((1/2 : ℝ)-1) k v =
        sphereSobolevSingleL (-(1/2 : ℝ)) k v := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t k)
        (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 k v) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact (sphereSobolevShiftedDegreeL_single (1/2 : ℝ) k v).trans
      (congrArg (fun z : SphereSobolev (-(1/2 : ℝ)) => (k : ℝ) • z) hIndex)
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      L (sphereSobolevSingleL (3/2 : ℝ) k v) =
        R (sphereSobolevSingleL (3/2 : ℝ) k v) := by
    let z := sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k j v)
    have h1 := (congrArg (sphereSobolevShiftedDegreeL (1/2 : ℝ)) (hAH j k v)).trans
      (hBL (k+1) (harmonicDerivativeAdjoint hF k j v))
    have h2 : sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j
        (sphereSobolevShiftedDegreeL (3/2 : ℝ) (sphereSobolevSingleL (3/2 : ℝ) k v)) =
          (k : ℝ) • z := by
      have h := congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j) (hBH k v)
      exact h.trans (((sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) j).map_smul
        (k : ℝ) (sphereSobolevSingleL (1/2 : ℝ) k v)).trans
          (congrArg (fun w : SphereSobolev (-(1/2 : ℝ)) => (k : ℝ) • w) (hAL j k v)))
    have hLeft := congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a-b) h1 h2
    have hScalar : ((k+1 : ℕ) : ℝ) • z - (k : ℝ) • z = z := by
      push_cast
      module
    have hRight : R (sphereSobolevSingleL (3/2 : ℝ) k v) = z := by
      simp (config := { instances := true }) only
        [R,z,ContinuousLinearMap.comp_apply,hAH,sphereSobolevInclusionL_single]
    simpa (config := { instances := true }) only
      [L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,z]
      using hLeft.trans (hScalar.trans hRight.symm)
  have hFinite (n : ℕ) : L (sphereSobolevPartialSum (3/2 : ℝ) n u) =
      R (sphereSobolevPartialSum (3/2 : ℝ) n u) := by
    simp (config := { instances := true }) only [sphereSobolevPartialSum,map_sum]
    exact Finset.sum_congr rfl (fun k hk => hSingle k (sphereSobolevCoefficientL (3/2 : ℝ) k u))
  have hLeft := (L.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  have hRight := (R.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  have hValue := tendsto_nhds_unique
    (hLeft.congr' (Filter.Eventually.of_forall hFinite)) hRight
  simpa (config := { instances := true }) only
    [L,R,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply] using hValue

lemma sum_sphereSobolevAngularCoordinateTranspose_twice_eq_zero
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (u : SphereSobolev (3/2 : ℝ)) :
    (∑ i : Fin 3, sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i u)) = 0 := by
  let T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    ∑ i : Fin 3, (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i).comp
      (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i)
  have hAH (a : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) a
        (sphereSobolevSingleL (3/2 : ℝ) k v) =
      sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) a k v
    have hIndex : sphereSobolevSingleL ((3/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k a v) =
        sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k a v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact h.trans hIndex
  have hAL (a : Fin 3) (k : ℕ) (v : harmonicSphereSubspace k) :
      sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) a
        (sphereSobolevSingleL (1/2 : ℝ) k v) =
      sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
    have h := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (1/2 : ℝ) a k v
    have hIndex : sphereSobolevSingleL ((1/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k a v) =
        sphereSobolevSingleL (-(1/2 : ℝ)) (k+1) (harmonicDerivativeAdjoint hF k a v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (1/2 : ℝ)-1 = -(1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k a v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    exact h.trans hIndex
  have hHarmonic (k : ℕ) (v : harmonicSphereSubspace k) :
      (∑ i : Fin 3, harmonicDerivativeAdjoint hF (k+1) i
        (harmonicDerivativeAdjoint hF k i v)) = 0 := by
    rcases harmonicPolynomialSphereMap_surjective k v with ⟨p,rfl⟩
    have hTerm (i : Fin 3) :
        (harmonicDerivativeAdjoint hF (k+1) i
          (harmonicDerivativeAdjoint hF k i (harmonicPolynomialSphereMap k p)) : SphereL2) =
        polynomialSphereL2 (sphereDerivativeAdjoint (k+1) i (sphereDerivativeAdjoint k i p)) := by
      rw [harmonicDerivativeAdjoint_apply_image]
      change (harmonicDerivativeAdjoint hF (k+1) i
        (harmonicPolynomialSphereMap (k+1) ⟨sphereDerivativeAdjoint k i p,
          sphereDerivativeAdjoint_harmonicHomogeneous k i p p.property⟩) : SphereL2) = _
      rw [harmonicDerivativeAdjoint_apply_image]
      rfl
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_zero]
    simp_rw [hTerm]
    have h := congrArg polynomialSphereL2
      (sum_double_sphereDerivativeAdjoint_eq_zero hF k p p.property)
    simpa only [map_sum,map_zero] using h
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      T (sphereSobolevSingleL (3/2 : ℝ) k v) = 0 := by
    have hTerm (i : Fin 3) :
        sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i
          (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i
            (sphereSobolevSingleL (3/2 : ℝ) k v)) =
        sphereSobolevSingleL (-(1/2 : ℝ)) ((k+1)+1)
          (harmonicDerivativeAdjoint hF (k+1) i (harmonicDerivativeAdjoint hF k i v)) :=
      (congrArg (sphereSobolevAngularCoordinateTransposeL hF hO hD (1/2 : ℝ) i)
        (hAH i k v)).trans (hAL i (k+1) (harmonicDerivativeAdjoint hF k i v))
    have hTransport := congrArg (sphereSobolevSingleL (-(1/2 : ℝ)) ((k+1)+1)) (hHarmonic k v)
    simp (config := { instances := true }) only [map_sum,map_zero] at hTransport
    simpa (config := { instances := true }) only
      [T,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,hTerm] using hTransport
  have hFinite (n : ℕ) : T (sphereSobolevPartialSum (3/2 : ℝ) n u) = 0 := by
    simp (config := { instances := true }) only [sphereSobolevPartialSum,map_sum,hSingle,
      Finset.sum_const_zero]
  have hLimit := (T.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  have hValue : T u = 0 := tendsto_nhds_unique
    (hLimit.congr' (Filter.Eventually.of_forall hFinite)) tendsto_const_nhds
  simpa (config := { instances := true }) only
    [T,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply] using hValue

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHorizontalAngular_angularTranspose_commutator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevShiftedDegree_angularTranspose_commutator
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sum_sphereSobolevAngularCoordinateTranspose_twice_eq_zero
