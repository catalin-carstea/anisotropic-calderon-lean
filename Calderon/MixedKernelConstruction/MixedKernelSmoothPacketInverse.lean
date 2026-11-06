import Calderon.MixedKernelConstruction.MixedKernelNativePacketInverse
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff Topology

/-- A genuine fixed OPEN smooth inverse room, using global smoothness and actual open invertibility. -/
theorem exists_open_smooth_local_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : E → E) (hf : ContDiff ℝ ∞ F) (x0 : E)
    (hD : (fderiv ℝ F x0).IsInvertible) :
    ∃ G : E → E, ∃ V : Set E, IsOpen V ∧ F x0 ∈ V ∧
      ContDiffOn ℝ ∞ G V ∧ G (F x0) = x0 ∧
      (∀ y ∈ V, F (G y) = y) ∧ ∀ᶠ x in 𝓝 x0, G (F x) = x := by
  have hD_saved := hD
  obtain ⟨D,hDeq⟩ := hD
  have hdf : HasFDerivAt F (D : E →L[ℝ] E) x0 := by
    rw [hDeq]
    exact (hf.differentiable (by simp) x0).hasFDerivAt
  let e := hf.contDiffAt.toOpenPartialHomeomorph F hdf (by simp)
  let A : Set E := {x | (fderiv ℝ F x).IsInvertible}
  have hA : IsOpen A := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    (hf.continuous_fderiv (by simp))
  have hsource : x0 ∈ e.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hdf (by simp)
  have htarget : F x0 ∈ e.target := hf.contDiffAt.image_mem_toOpenPartialHomeomorph_target hdf (by simp)
  have hbase : e.symm (F x0) = x0 := e.left_inv hsource
  let V : Set E := e.target ∩ e.symm ⁻¹' A
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hA
  have hbaseV : F x0 ∈ V := ⟨htarget,by change (fderiv ℝ F (e.symm (F x0))).IsInvertible;rw [hbase];exact hD_saved⟩
  have hsmooth : ContDiffOn ℝ ∞ e.symm V := by
    intro y hy
    obtain ⟨Dy,hDyeq⟩ := hy.2
    have hd : HasFDerivAt e (Dy : E →L[ℝ] E) (e.symm y) := by
      change HasFDerivAt F (Dy : E →L[ℝ] E) (e.symm y)
      rw [hDyeq]
      exact (hf.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy.1 hd hf.contDiffAt).contDiffWithinAt
  refine ⟨e.symm,V,hV,hbaseV,hsmooth,hbase,fun y hy => e.right_inv hy.1,?_⟩
  filter_upwards [e.open_source.mem_nhds hsource] with x hx
  exact e.left_inv hx

local instance : CompleteSpace R3 := FiniteDimensional.complete ℝ R3
local instance : CompleteSpace ReferenceNormalParameters := FiniteDimensional.complete ℝ ReferenceNormalParameters

private theorem normalProduct_isInvertible_of_injective
    (A : (ReferenceNormalParameters × R3) →L[ℝ] (ReferenceNormalParameters × R3))
    (hA : Function.Injective A) : A.IsInvertible := by
  have hb : Function.Bijective A.toLinearMap := ⟨hA,A.toLinearMap.surjective_of_injective hA⟩
  refine ⟨(LinearEquiv.ofBijective A.toLinearMap hb).toContinuousLinearEquiv,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The actual triangular parameter map supplies one open smooth joint inverse, not only a base-point germ. -/
theorem exists_open_smooth_parameter_inverse
    (f : ReferenceNormalParameters × R3 → R3) (hf : ContDiff ℝ ∞ f)
    (p : ReferenceNormalParameters) (z : R3)
    (hB : ((fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)).IsInvertible) :
    ∃ psi : ReferenceNormalParameters × R3 → R3, ∃ V : Set (ReferenceNormalParameters × R3),
      IsOpen V ∧ (p,f (p,z)) ∈ V ∧ ContDiffOn ℝ ∞ psi V ∧ psi (p,f (p,z)) = z ∧
      (∀ b ∈ V, f (b.1,psi b) = b.2) ∧
      ∀ᶠ a in 𝓝 (p,z), psi (a.1,f a) = a.2 := by
  let T : (ReferenceNormalParameters × R3) → (ReferenceNormalParameters × R3) := fun a => (a.1,f a)
  let A := fderiv ℝ f (p,z)
  let B := A.comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)
  let DT := (ContinuousLinearMap.fst ℝ ReferenceNormalParameters R3).prod A
  have hTf : ContDiff ℝ ∞ T := contDiff_fst.prodMk hf
  have hdT : HasFDerivAt T DT (p,z) :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,z))).prodMk (hf.differentiable (by simp) (p,z)).hasFDerivAt
  have hSplit (a : ReferenceNormalParameters × R3) :
      A a = (A.comp (ContinuousLinearMap.inl ℝ ReferenceNormalParameters R3)) a.1 + B a.2 :=
    (A.comp_inl_add_comp_inr a).symm
  have hBI (v : R3) : ContinuousLinearMap.inverse B (B v) = v := by
    have hh := congrArg (fun C : R3 →L[ℝ] R3 => C v) hB.inverse_comp_self
    simpa only [B,A,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  have hDT : DT.IsInvertible := by
    apply normalProduct_isInvertible_of_injective
    intro a b hab
    change (a.1,A a) = (b.1,A b) at hab
    have hp := congrArg (fun t : ReferenceNormalParameters × R3 => t.1) hab
    change a.1 = b.1 at hp
    have hAeq : A a = A b := congrArg Prod.snd hab
    rw [hSplit a,hSplit b,hp] at hAeq
    have hBeq : B a.2 = B b.2 := add_left_cancel hAeq
    have hv := congrArg (ContinuousLinearMap.inverse B) hBeq
    rw [hBI,hBI] at hv
    exact Prod.ext hp hv
  have hInv : (fderiv ℝ T (p,z)).IsInvertible := by rw [hdT.fderiv];exact hDT
  obtain ⟨G,V,hV,hbaseV,hG,hbase,hRight,hLeft⟩ := exists_open_smooth_local_inverse T hTf (p,z) hInv
  let psi : ReferenceNormalParameters × R3 → R3 := fun b => (G b).2
  refine ⟨psi,V,hV,hbaseV,hG.snd,congrArg Prod.snd hbase,?_,?_⟩
  · intro b hb
    have hh := hRight b hb
    change ((G b).1,f (G b)) = b at hh
    have hp := congrArg (fun t : ReferenceNormalParameters × R3 => t.1) hh
    change (G b).1 = b.1 at hp
    have hs : f (G b) = b.2 := congrArg Prod.snd hh
    have hGb : G b = (b.1,psi b) := Prod.ext hp rfl
    rw [hGb] at hs
    exact hs
  · filter_upwards [hLeft] with a ha
    exact congrArg Prod.snd ha

/-- A single OPEN jointly smooth inverse for the SAME actual native packet normalization. -/
theorem exists_packet_open_smooth_normalizedEndpoint_inverse
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) (y : R3) (hy : y ∈ P.centers)
    (r : ℝ) (hr : |r| ≤ 4*P.rho) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    ∃ psi : ReferenceNormalParameters × R3 → R3, ∃ V : Set (ReferenceNormalParameters × R3),
      IsOpen V ∧ ((lam,(y,r)),referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))) ∈ V ∧
      ContDiffOn ℝ ∞ psi V ∧
      psi ((lam,(y,r)),referenceFramedNormalizedEndpointIntegral S.g1 L P.Phi (lam,((y,r),z))) = z ∧
      (∀ b ∈ V, referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi (b.1,psi b) = b.2) ∧
      ∀ᶠ a in 𝓝 ((lam,(y,r)),z),
        psi (a.1,referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi a) = a.2 := by
  let f := referenceFramedNormalizedEndpointIntegralJoint S.g1 L P.Phi
  let p : ReferenceNormalParameters := (lam,(y,r))
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ f :=
    contDiff_referenceFramedNormalizedEndpointIntegralJoint S.g1 S.g1_admissible L P.Phi hTheta
  have hs := hasFDerivAt_referenceFramedNormalizedEndpointIntegral_on_domain S.g1 S.g1_admissible L
    P.y0 P.Phi P.B hEnd (lam,((y,r),z)) ⟨hlam,(P.centers_room y hy).2⟩
  have hp : HasFDerivAt (fun w => f (p,w))
      ((fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)) z :=
    (hf.differentiable (by simp) (p,z)).hasFDerivAt.comp z (hasFDerivAt_prodMk_right p z)
  have heq : ((fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)) =
      referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((y,r),z)) := hp.unique hs
  have hInv : ((fderiv ℝ f (p,z)).comp (ContinuousLinearMap.inr ℝ ReferenceNormalParameters R3)).IsInvertible := by
    rw [heq]
    exact packet_normalizedJacobian_isInvertible S L P lam hlam y hy r hr z hz
  simpa only [f,p,referenceFramedNormalizedEndpointIntegralJoint] using
    exists_open_smooth_parameter_inverse f hf p z hInv

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
