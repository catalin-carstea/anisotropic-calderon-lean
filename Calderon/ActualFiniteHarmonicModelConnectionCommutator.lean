import Calderon.ActualFiniteHarmonicModelReferenceWeights
import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore AngularShiftGraph HarmonicDerivativeOperator SmoothSphereRotationProjection
  ActualReferenceParallelRaising AmbientReferenceCovariantCore MovingFrameConnection SmoothMetricFrame
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeConnectionCommutatorFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeConnectionCommutatorFunction
lemma harmonicReferenceAngularConnection_adjoint_eq_neg
    (g : MatrixField) (L lam : ℝ) (k : ℕ) (x X : R3) :
    letI : CompleteSpace (harmonicSphereSubspace k) := completeSpace_harmonicSphereSubspace k
    ContinuousLinearMap.adjoint (harmonicReferenceAngularConnection g L lam k x X) =
      -harmonicReferenceAngularConnection g L lam k x X := by
  letI : CompleteSpace (harmonicSphereSubspace k) := completeSpace_harmonicSphereSubspace k
  have hRot (i j : Fin 3) :
      ContinuousLinearMap.adjoint (harmonicSphereRotation k i j) = -harmonicSphereRotation k i j := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.neg_apply,inner_neg_left]
    have hs := inner_harmonicSphereRotation_skew k i j u v
    linarith
  have hAdScalar (r : ℝ) (T : harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) :
      ContinuousLinearMap.adjoint (r • T) = r • ContinuousLinearMap.adjoint T := by
    simpa only [starRingEnd_apply,star_trivial] using
      map_smulₛₗ (ContinuousLinearMap.adjoint :
        (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) ≃ₗᵢ⋆[ℝ]
          (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)) r T
  have hAdSum (T : Fin 3 → (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)) :
      ContinuousLinearMap.adjoint (∑ i : Fin 3, T i) = ∑ i : Fin 3, ContinuousLinearMap.adjoint (T i) := by
    let Ad : (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) →+
        (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) :=
      (ContinuousLinearMap.adjoint :
        (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k) ≃ₗᵢ⋆[ℝ]
          (harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace k)).toLinearEquiv.toLinearMap.toAddMonoidHom
    change Ad (∑ i : Fin 3, T i) = ∑ i : Fin 3, Ad (T i)
    exact map_sum Ad T Finset.univ
  unfold harmonicReferenceAngularConnection
  rw [hAdScalar,hAdSum]
  simp only [hAdSum,hAdScalar,hRot,smul_neg,Finset.sum_neg_distrib]


lemma harmonicReferenceAngularConnection_derivative_commutator
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (k : ℕ) (x X : R3) (a : Fin 3) (u : harmonicSphereSubspace (k+1)) :
    harmonicReferenceAngularConnection g L lam k x X (harmonicDerivative hF k a u) -
      harmonicDerivative hF k a (harmonicReferenceAngularConnection g L lam (k+1) x X u) =
    ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x X c a • harmonicDerivative hF k c u := by
  letI : CompleteSpace (harmonicSphereSubspace k) := completeSpace_harmonicSphereSubspace k
  letI : CompleteSpace (harmonicSphereSubspace (k+1)) := completeSpace_harmonicSphereSubspace (k+1)
  have hs (m : ℕ) (v w : harmonicSphereSubspace m) :
      ⟪harmonicReferenceAngularConnection g L lam m x X v,w⟫_ℝ =
        -⟪v,harmonicReferenceAngularConnection g L lam m x X w⟫_ℝ := by
    letI : CompleteSpace (harmonicSphereSubspace m) := completeSpace_harmonicSphereSubspace m
    have ht := ContinuousLinearMap.adjoint_inner_left (harmonicReferenceAngularConnection g L lam m x X) w v
    rw [harmonicReferenceAngularConnection_adjoint_eq_neg,
      ContinuousLinearMap.neg_apply,inner_neg_left] at ht
    linarith
  apply ext_inner_left ℝ
  intro v
  have hr := harmonicReferenceAngularConnection_raising_commutator hF g hg L lam k x X a v
  have he := congrArg (fun z : harmonicSphereSubspace (k+1) => ⟪z,u⟫_ℝ) hr
  simp only [inner_sub_left,sum_inner] at he
  rw [hs (k+1),inner_harmonicDerivativeAdjoint,inner_harmonicDerivativeAdjoint,hs k] at he
  have hterm (b : Fin 3) :
      ⟪referenceFrameConnectionCoefficient g L lam x X b a • harmonicDerivativeAdjoint hF k b v,u⟫_ℝ =
        ⟪v,referenceFrameConnectionCoefficient g L lam x X b a • harmonicDerivative hF k b u⟫_ℝ := by
    calc
      _ = referenceFrameConnectionCoefficient g L lam x X b a * ⟪harmonicDerivativeAdjoint hF k b v,u⟫_ℝ :=
        real_inner_smul_left _ _ _
      _ = referenceFrameConnectionCoefficient g L lam x X b a * ⟪v,harmonicDerivative hF k b u⟫_ℝ := by
        rw [inner_harmonicDerivativeAdjoint]
      _ = _ := (real_inner_smul_right _ _ _).symm
  have hsum : (∑ b : Fin 3, ⟪referenceFrameConnectionCoefficient g L lam x X b a •
      harmonicDerivativeAdjoint hF k b v,u⟫_ℝ) =
      ∑ b : Fin 3, ⟪v,referenceFrameConnectionCoefficient g L lam x X b a • harmonicDerivative hF k b u⟫_ℝ :=
    Finset.sum_congr rfl (fun b _ => hterm b)
  rw [hsum] at he
  simp only [inner_sub_right,inner_sum]
  linarith


lemma nativeReferenceConnection_raising_commutator
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b a : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.commutator (nativeReferenceConnectionAction hO hD g hg L lam b)
      (coreRaising hO hD hF a) F x =
    ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) b) c a • coreRaising hO hD hF c F x := by
  let A := nativeReferenceConnectionAction hO hD g hg L lam b
  let X := referenceMetricGramFrame g L (lam,x) b
  have hA (U : smoothCompactFiniteSphereCore hO hD) :
      (U x,A U x) ∈ referenceAngularConnectionGraph hO hD g L lam x X := by
    dsimp only [A,X]
    rw [nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam b U x]
    exact normalizedReferenceAngularConnection_graph hO hD g L lam x _ (U x)
      (coreWeightOperator hO hD (besselWeight 1) U x)
      (coreWeightOperator_graph hO hD (besselWeight 1) U x)
  change A (coreRaising hO hD hF a F) x - coreRaising hO hD hF a (A F) x = _
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
    (A (coreRaising hO hD hF a F) x - coreRaising hO hD hF a (A F) x) =
    sphereHarmonicCoordinate hO hD k
      (∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x X c a • coreRaising hO hD hF c F x)
  rw [map_sub,map_sum]
  simp only [map_smul]
  cases k with
  | zero =>
    rw [hA (coreRaising hO hD hF a F) 0,(coreRaising_graph hO hD hF a F x).1,
      (coreRaising_graph hO hD hF a (A F) x).1,map_zero,sub_zero]
    simp only [(coreRaising_graph hO hD hF _ F x).1,smul_zero,Finset.sum_const_zero]
  | succ m =>
    rw [hA (coreRaising hO hD hF a F) (m+1),(coreRaising_graph hO hD hF a F x).2 m,
      (coreRaising_graph hO hD hF a (A F) x).2 m,hA F m]
    simp only [(coreRaising_graph hO hD hF _ F x).2 m]
    exact harmonicReferenceAngularConnection_raising_commutator hF g hg L lam m x X a
      (sphereHarmonicCoordinate hO hD m (F x))


lemma nativeReferenceConnection_derivative_commutator
    (hF : SphereFischerInner) (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L lam : ℝ) (b a : Fin 3) (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    ActualModelCommutatorWords.commutator (nativeReferenceConnectionAction hO hD g hg L lam b)
      (coreDerivative hO hD hF a) F x =
    ∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x
      (referenceMetricGramFrame g L (lam,x) b) c a • coreDerivative hO hD hF c F x := by
  let A := nativeReferenceConnectionAction hO hD g hg L lam b
  let X := referenceMetricGramFrame g L (lam,x) b
  have hA (U : smoothCompactFiniteSphereCore hO hD) :
      (U x,A U x) ∈ referenceAngularConnectionGraph hO hD g L lam x X := by
    dsimp only [A,X]
    rw [nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam b U x]
    exact normalizedReferenceAngularConnection_graph hO hD g L lam x _ (U x)
      (coreWeightOperator hO hD (besselWeight 1) U x)
      (coreWeightOperator_graph hO hD (besselWeight 1) U x)
  change A (coreDerivative hO hD hF a F) x - coreDerivative hO hD hF a (A F) x = _
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k
    (A (coreDerivative hO hD hF a F) x - coreDerivative hO hD hF a (A F) x) =
    sphereHarmonicCoordinate hO hD k
      (∑ c : Fin 3, referenceFrameConnectionCoefficient g L lam x X c a • coreDerivative hO hD hF c F x)
  rw [map_sub,map_sum]
  simp only [map_smul]
  rw [hA (coreDerivative hO hD hF a F) k,coreDerivative_graph hO hD hF a F x k,
    coreDerivative_graph hO hD hF a (A F) x k,hA F (k+1)]
  simp only [coreDerivative_graph hO hD hF _ F x k]
  exact harmonicReferenceAngularConnection_derivative_commutator hF g hg L lam k x X a
    (sphereHarmonicCoordinate hO hD (k+1) (F x))


lemma coreDegree_nativeReferenceConnection_commute
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L lam : ℝ) (b : Fin 3) :
    Commute (coreDegree hO hD) (nativeReferenceConnectionAction hO hD g hg L lam b) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  let A := nativeReferenceConnectionAction hO hD g hg L lam b
  let X := referenceMetricGramFrame g L (lam,x) b
  have hA (U : smoothCompactFiniteSphereCore hO hD) :
      (U x,A U x) ∈ referenceAngularConnectionGraph hO hD g L lam x X := by
    dsimp only [A,X]
    rw [nativeReferenceConnectionAction_apply_eq_normalized hO hD g hg L lam b U x]
    exact normalizedReferenceAngularConnection_graph hO hD g L lam x _ (U x)
      (coreWeightOperator hO hD (besselWeight 1) U x)
      (coreWeightOperator_graph hO hD (besselWeight 1) U x)
  change coreDegree hO hD (A F) x = A (coreDegree hO hD F) x
  have hd (U : smoothCompactFiniteSphereCore hO hD) (k : ℕ) :
      sphereHarmonicCoordinate hO hD k (coreDegree hO hD U x) =
        (k : ℝ) • sphereHarmonicCoordinate hO hD k (U x) :=
    coreWeightOperator_graph hO hD (fun k => (k : ℝ)) U x k
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreDegree hO hD (A F) x) =
    sphereHarmonicCoordinate hO hD k (A (coreDegree hO hD F) x)
  rw [hd,hA F k,hA (coreDegree hO hD F) k,hd,map_smul]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
