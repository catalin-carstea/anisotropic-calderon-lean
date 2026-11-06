import Calderon.ActualFiniteHarmonicModelDerivativeRaisingCommutator

set_option autoImplicit false
noncomputable section
open Set MvPolynomial
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic SphereHilbertDecomposition SpectralCoreRegularity SpectralWeightedGraph
  ActualFiniteHarmonicCore AngularShiftGraph HarmonicDerivativeOperator SmoothSphereRotationProjection
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeRaisingCommuteFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeRaisingCommuteFunction
lemma harmonicDerivative_composition_commute
    (hF : SphereFischerInner) (m : ℕ) (a b : Fin 3)
    (u : harmonicSphereSubspace (m+1+1)) :
    harmonicDerivative hF m a (harmonicDerivative hF (m+1) b u) =
      harmonicDerivative hF m b (harmonicDerivative hF (m+1) a u) := by
  rcases harmonicPolynomialSphereMap_surjective (m+1+1) u with ⟨p,rfl⟩
  have hd (i : Fin 3) :
      harmonicDerivative hF (m+1) i (harmonicPolynomialSphereMap (m+1+1) p) =
        harmonicPolynomialSphereMap (m+1)
          ⟨pderiv i (p : MvPolynomial (Fin 3) ℝ),pderiv_harmonicHomogeneous_succ (m+1) i p p.property⟩ := by
    rw [harmonicDerivative_apply_image]
    rfl
  rw [hd b,hd a,harmonicDerivative_apply_image,harmonicDerivative_apply_image]
  apply Subtype.ext
  change polynomialSphereL2 (pderiv a (pderiv b (p : MvPolynomial (Fin 3) ℝ))) =
    polynomialSphereL2 (pderiv b (pderiv a (p : MvPolynomial (Fin 3) ℝ)))
  rw [AngularPolynomial.pderiv_pderiv_comm a b]


lemma harmonicDerivativeAdjoint_composition_commute
    (hF : SphereFischerInner) (m : ℕ) (a b : Fin 3)
    (u : harmonicSphereSubspace m) :
    harmonicDerivativeAdjoint hF (m+1) a (harmonicDerivativeAdjoint hF m b u) =
      harmonicDerivativeAdjoint hF (m+1) b (harmonicDerivativeAdjoint hF m a u) := by
  letI : CompleteSpace (harmonicSphereSubspace m) := completeSpace_harmonicSphereSubspace m
  letI : CompleteSpace (harmonicSphereSubspace (m+1)) := completeSpace_harmonicSphereSubspace (m+1)
  letI : CompleteSpace (harmonicSphereSubspace (m+1+1)) := completeSpace_harmonicSphereSubspace (m+1+1)
  have hd : (harmonicDerivative hF m a).comp (harmonicDerivative hF (m+1) b) =
      (harmonicDerivative hF m b).comp (harmonicDerivative hF (m+1) a) := by
    apply ContinuousLinearMap.ext
    intro v
    exact harmonicDerivative_composition_commute hF m a b v
  have ha := congrArg ContinuousLinearMap.adjoint hd
  simp only [ContinuousLinearMap.adjoint_comp,← harmonicDerivativeAdjoint_eq_adjoint] at ha
  have he := congrArg (fun T => T u) ha.symm
  exact he


lemma coreRaising_commute
    (hF : SphereFischerInner) (a b : Fin 3) :
    Commute (coreRaising hO hD hF a) (coreRaising hO hD hF b) := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  change coreRaising hO hD hF a (coreRaising hO hD hF b F) x =
    coreRaising hO hD hF b (coreRaising hO hD hF a F) x
  apply (sphereHarmonicDecomposition hO hD).injective
  apply lp.ext
  funext k
  change sphereHarmonicCoordinate hO hD k (coreRaising hO hD hF a (coreRaising hO hD hF b F) x) =
    sphereHarmonicCoordinate hO hD k (coreRaising hO hD hF b (coreRaising hO hD hF a F) x)
  cases k with
  | zero =>
    rw [(coreRaising_graph hO hD hF a (coreRaising hO hD hF b F) x).1,
      (coreRaising_graph hO hD hF b (coreRaising hO hD hF a F) x).1]
  | succ k =>
    rw [(coreRaising_graph hO hD hF a (coreRaising hO hD hF b F) x).2 k,
      (coreRaising_graph hO hD hF b (coreRaising hO hD hF a F) x).2 k]
    cases k with
    | zero =>
      rw [(coreRaising_graph hO hD hF b F x).1,(coreRaising_graph hO hD hF a F x).1]
      simp only [map_zero]
    | succ m =>
      rw [(coreRaising_graph hO hD hF b F x).2 m,(coreRaising_graph hO hD hF a F x).2 m]
      exact harmonicDerivativeAdjoint_composition_commute hF m a b (sphereHarmonicCoordinate hO hD m (F x))

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
