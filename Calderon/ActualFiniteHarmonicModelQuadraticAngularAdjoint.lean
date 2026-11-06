import Calderon.ActualFiniteHarmonicModelGeneratorScalarExpansions

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev quadraticAdjointFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) := ⟨fun F => F.val⟩
attribute [local instance] quadraticAdjointFunction

lemma hasCoreScalarExpansionBound_generatorAdjoint (hF : SphereFischerInner)
    (i : CoreAngularGeneratorIndex) (x : R3) :
    HasCoreScalarExpansionBound hO hD (coreAngularGenerator hO hD hF)
      (coreAngularGeneratorAdjoint hO hD hF i) x 1 := by
  rcases i with a | (a | (ab | b))
  · exact hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inl a)) x
  · exact hasCoreScalarExpansionBound_generator hO hD hF (Sum.inl a) x
  · exact hasCoreScalarExpansionBound_neg hO hD _ _ x 1
      (hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inl ab))) x)
  · cases b
    · exact hasCoreScalarExpansionBound_identity hO hD hF x
    · exact hasCoreScalarExpansionBound_generator hO hD hF (Sum.inr (Sum.inr (Sum.inr true))) x

lemma exists_pointwise_adjoint_of_quadratic_expansion
    (hF : SphereFischerInner) (A : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (x : R3) (C : ℝ)
    (hA : HasCoreScalarExpansionBound hO hD
      (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
        coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2) A x C) :
    ∃ Astar : Module.End ℝ (smoothCompactFiniteSphereCore hO hD),
      (∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ y : R3,
        ⟪A F y,G y⟫_ℝ=⟪F y,Astar G y⟫_ℝ) ∧
      HasCoreScalarExpansionBound hO hD
        (fun ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
          coreAngularGenerator hO hD hF ij.1*coreAngularGenerator hO hD hF ij.2) Astar x C := by
  obtain ⟨c,hc,he,hm⟩ := hA
  let S (ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex) :=
    coreAngularGeneratorAdjoint hO hD hF ij.2*coreAngularGeneratorAdjoint hO hD hF ij.1
  let Astar := coreScalarCombination hO hD S c hc
  have hs (ij : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex) :
      HasCoreScalarExpansionBound hO hD
        (fun kl : CoreAngularGeneratorIndex × CoreAngularGeneratorIndex =>
          coreAngularGenerator hO hD hF kl.1*coreAngularGenerator hO hD hF kl.2) (S ij) x 1 := by
    simpa only [one_mul] using hasCoreScalarExpansionBound_product hO hD
      (coreAngularGenerator hO hD hF) (coreAngularGenerator hO hD hF)
      (scalarCentral_coreAngularGenerator hO hD hF) _ _ x 1 1
      (hasCoreScalarExpansionBound_generatorAdjoint hO hD hF ij.2 x)
      (hasCoreScalarExpansionBound_generatorAdjoint hO hD hF ij.1 x)
  refine ⟨Astar,?_,?_⟩
  · intro F G y
    rw [he]
    dsimp only [Astar,coreScalarCombination]
    simp only [LinearMap.sum_apply,Module.End.mul_apply,coreScalar,LinearMap.coe_mk,AddHom.coe_mk,
      Submodule.coe_mk,Submodule.coe_sum,Finset.sum_apply,sum_inner,inner_sum,
      real_inner_smul_left,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro ij _
    congr 1
    exact coreAngular_product_inner_adjoint hO hD _ _ _ _ _ _ y
      (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF ij.1 y)
      (hasCoreAngularFirstOrderBounds_coreAngularGenerator hO hD hF ij.2 y) F G
  · apply hasCoreScalarExpansionBound_mono hO hD _ _ x _ C _ hm
    dsimp only [Astar,coreScalarCombination]
    apply hasCoreScalarExpansionBound_sum hO hD
    intro ij _
    simpa only [mul_one] using hasCoreScalarExpansionBound_scalar_mul hO hD _ (S ij) x 1 (hs ij) (c ij) (hc ij)

lemma coreEnd_eq_of_pointwise_inner_eq
    (A B : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (h : ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ x : R3,
      ⟪A F x,G x⟫_ℝ=⟪B F x,G x⟫_ℝ) : A=B := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext x
  have he := h F (A F-B F) x
  have hzero : ⟪A F x-B F x,A F x-B F x⟫_ℝ=0 := by
    rw [inner_sub_left]
    exact sub_eq_zero.mpr he
  exact sub_eq_zero.mp ((inner_self_eq_zero).mp hzero)

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
