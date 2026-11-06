import Calderon.ActualLowerUSAdjointZeroSphereAdjoint

/-!
Pointwise witnesses are NOT assembled into a smooth x-indexed CLM family.
The fixed finite adjoint is identified before pairing arbitrary SphereL2 outputs.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

/-- Two genuine global finite sphere adjoints coincide as finite-core operators. -/
lemma pointwise_adjoint_unique
    (A S T : Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hS : ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ x : R3,
      ⟪(A F).val x,G.val x⟫_ℝ = ⟪F.val x,(S G).val x⟫_ℝ)
    (hT : ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ x : R3,
      ⟪(A F).val x,G.val x⟫_ℝ = ⟪F.val x,(T G).val x⟫_ℝ) : S = T := by
  apply coreEnd_eq_of_pointwise_inner_eq hO hD
  intro F G x
  calc
    _ = ⟪G.val x,(S F).val x⟫_ℝ := real_inner_comm _ _
    _ = ⟪(A G).val x,F.val x⟫_ℝ := (hS G F x).symm
    _ = ⟪G.val x,(T F).val x⟫_ℝ := hT G F x
    _ = _ := real_inner_comm _ _

/-- A smooth scalar combination has the corresponding scalar combination of
true angular adjoints. This identity is global even for a witness chosen at x. -/
lemma coreScalarCombination_inner_adjoint
    {ι : Type*} [Fintype ι]
    (T S : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hAdj : ∀ i, ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ y : R3,
      ⟪(T i F).val y,G.val y⟫_ℝ = ⟪F.val y,(S i G).val y⟫_ℝ)
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (F G : smoothCompactFiniteSphereCore hO hD) (y : R3) :
    ⟪(coreScalarCombination hO hD T c hc F).val y,G.val y⟫_ℝ =
      ⟪F.val y,(coreScalarCombination hO hD S c hc G).val y⟫_ℝ := by
  simp only [coreScalarCombination,LinearMap.sum_apply,Module.End.mul_apply,
    coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_sum,Finset.sum_apply,sum_inner,inner_sum,
    real_inner_smul_left,real_inner_smul_right]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t : ℝ => c i y*t) (hAdj i F G y))

variable (hF : SphereFischerInner) (g g2 : MatrixField)
  (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2)
  (L q dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar)
local notation "J" => nativeULowerAdjointZeroCoefficient hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
local notation "Js" => nativeULowerAdjointZeroSphereAdjointCore hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr

/-- Any actual globally smooth presentation of J determines the already fixed
Js. Its coefficients may have been chosen using the mass bound at one point. -/
theorem nativeJs_eq_of_presentation
    {ι : Type*} [Fintype ι]
    (T S : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hAdj : ∀ i, ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ y : R3,
      ⟪(T i F).val y,G.val y⟫_ℝ = ⟪F.val y,(S i G).val y⟫_ℝ)
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (hJ : J = coreScalarCombination hO hD T c hc) :
    Js = coreScalarCombination hO hD S c hc := by
  apply pointwise_adjoint_unique hO hD J
  · exact nativeULowerAdjointZeroSphereAdjointCore_inner hO hD hF g g2 hg hg2
      L q dr Ar p hdr hAr
  · intro F G y
    rw [hJ]
    exact coreScalarCombination_inner_adjoint hO hD T S hAdj c hc F G y

/-- Crucially, v need not be finite, smooth, or the value of a finite core.
The true finite Js was identified before this SphereL2 pairing. -/
theorem nativeJs_inner_eq_presentation_sum
    {ι : Type*} [Fintype ι]
    (T S : ι → Module.End ℝ (smoothCompactFiniteSphereCore hO hD))
    (hAdj : ∀ i, ∀ F G : smoothCompactFiniteSphereCore hO hD, ∀ y : R3,
      ⟪(T i F).val y,G.val y⟫_ℝ = ⟪F.val y,(S i G).val y⟫_ℝ)
    (c : ι → R3 → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (hJ : J = coreScalarCombination hO hD T c hc)
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) (v : SphereL2) :
    ⟪(Js F).val x,v⟫_ℝ = ∑ i, c i x * ⟪(S i F).val x,v⟫_ℝ := by
  rw [nativeJs_eq_of_presentation hO hD hF g g2 hg hg2 L q dr Ar p hdr hAr
    T S hAdj c hc hJ]
  simp only [coreScalarCombination,LinearMap.sum_apply,Module.End.mul_apply,
    coreScalar,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_mk,
    Submodule.coe_sum,Finset.sum_apply,sum_inner,real_inner_smul_left]

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel.ActualLowerUSAdjointPresentation
