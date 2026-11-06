import Calderon.FullSobolevCoefficientOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

/-- Correct a full native Sobolev extension by the actual zero-boundary inverse. -/
def strongHarmonicProjectionL (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) :
    BallSobolev (s+2) →L[ℝ] BallSobolev (s+2) :=
  ContinuousLinearMap.id ℝ _ - (strongDirichletSubmodule s).toSubmodule.subtypeL.comp
    (((A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse).comp A)

theorem strongHarmonicProjectionL_apply (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) (u : BallSobolev (s+2)) :
    strongHarmonicProjectionL s A u = u -
      ((A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse (A u) :
        BallSobolev (s+2)) := rfl

theorem strongHarmonicProjectionL_equation (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s)
    (hi : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible)
    (u : BallSobolev (s+2)) : A (strongHarmonicProjectionL s A u) = 0 := by
  rw [strongHarmonicProjectionL_apply,map_sub]
  have h := hi.self_apply_inverse (A u)
  change A ((A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse (A u) :
    BallSobolev (s+2)) = A u at h
  rw [h,sub_self]

theorem sub_strongHarmonicProjectionL_mem (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) (u : BallSobolev (s+2)) :
    u - strongHarmonicProjectionL s A u ∈ strongDirichletSubmodule s := by
  rw [strongHarmonicProjectionL_apply,sub_sub_cancel]
  exact ((A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse (A u)).property

theorem strongHarmonicProjectionL_subtype (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s)
    (hi : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible)
    (u : StrongDirichletSpace s) :
    strongHarmonicProjectionL s A (u : BallSobolev (s+2)) = 0 := by
  rw [strongHarmonicProjectionL_apply]
  have h := hi.inverse_apply_self u
  change (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse
    (A (u : BallSobolev (s+2))) = u at h
  rw [h,sub_self]

theorem strongHarmonicProjectionL_eq_self (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) (u : BallSobolev (s+2))
    (hu : A u = 0) : strongHarmonicProjectionL s A u = u := by
  rw [strongHarmonicProjectionL_apply,hu,map_zero]
  change u - (0 : BallSobolev (s+2)) = u
  exact sub_zero u

theorem strongHarmonicProjectionL_idempotent (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s)
    (hi : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible)
    (u : BallSobolev (s+2)) :
    strongHarmonicProjectionL s A (strongHarmonicProjectionL s A u) =
      strongHarmonicProjectionL s A u :=
  strongHarmonicProjectionL_eq_self s A _ (strongHarmonicProjectionL_equation s A hi u)

theorem strongHarmonicProjectionL_add_subtype (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s)
    (hi : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible)
    (u : BallSobolev (s+2)) (v : StrongDirichletSpace s) :
    strongHarmonicProjectionL s A (u + (v : BallSobolev (s+2))) =
      strongHarmonicProjectionL s A u := by
  rw [map_add,strongHarmonicProjectionL_subtype s A hi v,add_zero]

theorem eq_of_strong_harmonic_sub_mem (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s)
    (hi : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible)
    (u v : BallSobolev (s+2)) (hu : A u = 0) (hv : A v = 0)
    (hm : u-v ∈ strongDirichletSubmodule s) : u = v := by
  let z : StrongDirichletSpace s := ⟨u-v,hm⟩
  have hz : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL) z = 0 := by
    change A (u-v) = 0
    rw [map_sub,hu,hv,sub_self]
  have he : z = 0 := hi.injective (hz.trans (map_zero _).symm)
  have he' := congrArg (fun w : StrongDirichletSpace s => (w : BallSobolev (s+2))) he
  exact sub_eq_zero.mp he'

theorem strongHarmonicProjectionL_eq_of_sub_mem (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s)
    (hi : (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible)
    (u v : BallSobolev (s+2)) (hv : A v = 0)
    (hm : u-v ∈ strongDirichletSubmodule s) : strongHarmonicProjectionL s A u = v := by
  apply eq_of_strong_harmonic_sub_mem s A hi _ v
    (strongHarmonicProjectionL_equation s A hi u) hv
  have he : strongHarmonicProjectionL s A u - v =
      (u-v) - (u-strongHarmonicProjectionL s A u) := by abel
  rw [he]
  exact (strongDirichletSubmodule s).sub_mem hm (sub_strongHarmonicProjectionL_mem s A u)

theorem norm_sub_strongHarmonicProjectionL_le (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) (u : BallSobolev (s+2)) :
    ‖u - strongHarmonicProjectionL s A u‖ ≤
      ‖(A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse‖ * ‖A u‖ := by
  rw [strongHarmonicProjectionL_apply,sub_sub_cancel]
  exact ((A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse).le_opNorm (A u)

theorem norm_strongHarmonicProjectionL_apply_le (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) (u : BallSobolev (s+2)) :
    ‖strongHarmonicProjectionL s A u‖ ≤
      (1 + ‖(A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse‖ * ‖A‖) * ‖u‖ := by
  rw [strongHarmonicProjectionL_apply]
  calc
    _ ≤ ‖u‖ + ‖(A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse (A u)‖ :=
      norm_sub_le _ _
    _ ≤ ‖u‖ + ‖(A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse‖ * ‖A u‖ :=
      add_le_add (le_refl ‖u‖)
        (((A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse).le_opNorm (A u))
    _ ≤ ‖u‖ + ‖(A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse‖ * (‖A‖ * ‖u‖) :=
      add_le_add (le_refl ‖u‖) (mul_le_mul_of_nonneg_left (A.le_opNorm u)
        (norm_nonneg (A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse))
    _ = _ := by ring

theorem norm_strongHarmonicProjectionL_le (s : ℕ)
    (A : BallSobolev (s+2) →L[ℝ] BallSobolev s) :
    ‖strongHarmonicProjectionL s A‖ ≤
      1 + ‖(A.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).inverse‖ * ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_strongHarmonicProjectionL_apply_le s A

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem contDiffOn_strongHarmonicProjectionL {n : WithTop ℕ∞} (s : ℕ)
    (A : H → BallSobolev (s+2) →L[ℝ] BallSobolev s) (q : Set H)
    (hA : ContDiffOn ℝ n A q)
    (hi : ∀ p ∈ q, (A p |>.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible) :
    ContDiffOn ℝ n (fun p => strongHarmonicProjectionL s (A p)) q := by
  have hR : ContDiffOn ℝ n (fun p => (A p).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL) q := hA.clm_comp contDiffOn_const
  letI : CompleteSpace (StrongDirichletSpace s) := instCompleteSpaceStrongDirichletSpace s
  have hI := contDiffOn_banachInverseFamily (X := StrongDirichletSpace s) _ q hR hi
  unfold strongHarmonicProjectionL
  exact contDiffOn_const.sub (contDiffOn_const.clm_comp (hI.clm_comp hA))

theorem exists_uniform_strongHarmonicProjectionL_bound (s : ℕ)
    (A : H → BallSobolev (s+2) →L[ℝ] BallSobolev s) (q : Set H) (hq : IsCompact q)
    (hA : ContDiffOn ℝ ∞ A q)
    (hi : ∀ p ∈ q, (A p |>.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q, ∀ u : BallSobolev (s+2),
      ‖strongHarmonicProjectionL s (A p) u‖ ≤ C * ‖u‖ := by
  have hP := contDiffOn_strongHarmonicProjectionL s A q hA hi
  obtain ⟨B,hB⟩ := hq.exists_bound_of_continuousOn hP.continuousOn
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro p hp u
  exact ((strongHarmonicProjectionL s (A p)).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right ((hB p hp).trans (le_max_left _ _)) (norm_nonneg u))

theorem exists_commonSupport_smallRadius_strongHarmonicProjection
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
    (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
    (K : Set R3) (hK : IsCompact K)
    (hza : ∀ p z, z ∉ K → a (p,z)=0) (hzw : ∀ p z, z ∉ K → w (p,z)=0)
    (L : ℝ) (q : Set R3) (hq : IsCompact q) (lam Lam : R3 → ℝ)
    (hUE : ∀ y ∈ q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (fun z => a ((y,0),z)) (lam y) (Lam y)) (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ eta ∧
      (∀ p ∈ q ×ˢ Icc (-delta) delta, ∀ u : BallSobolev (s+2),
        fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p
          (strongHarmonicProjectionL s
            (fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p) u) = 0 ∧
        u - strongHarmonicProjectionL s
          (fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p) u
            ∈ strongDirichletSubmodule s) ∧
      ContDiffOn ℝ ∞ (fun p => strongHarmonicProjectionL s
        (fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p))
          (q ×ˢ Icc (-delta) delta) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ q ×ˢ Icc (-delta) delta, ∀ u : BallSobolev (s+2),
        ‖strongHarmonicProjectionL s
          (fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p) u‖ ≤ C*‖u‖ := by
  obtain ⟨delta,hdelta,hdeltaeta,hi,hInv,hBound,hJets,hSol,hSolJets⟩ :=
    exists_commonSupport_smallRadius_strongDrift_inverse hcalc hreg s a ha w hw b hb K hK hza hzw L q hq lam Lam hUE eta heta
  let A := fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L
  let Q := q ×ˢ Icc (-delta) delta
  have hA : ContDiffOn ℝ ∞ A Q :=
    (contDiff_fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L).contDiffOn
  have hi' : ∀ p ∈ Q, (A p |>.comp (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible := by
    intro p hp
    change ((fullCommonSupportStrongDriftFamily hcalc s a ha w hw b hb K hK hza hzw L p).comp
      (strongDirichletSubmodule s).toSubmodule.subtypeL).IsInvertible
    rw [fullCommonSupportStrongDriftFamily_comp_subtype]
    exact hi p hp
  refine ⟨delta,hdelta,hdeltaeta,?_,?_,?_⟩
  · intro p hp u
    exact ⟨strongHarmonicProjectionL_equation s (A p) (hi' p hp) u,
      sub_strongHarmonicProjectionL_mem s (A p) u⟩
  · exact contDiffOn_strongHarmonicProjectionL s A Q hA hi'
  · exact exists_uniform_strongHarmonicProjectionL_bound s A Q (hq.prod isCompact_Icc) hA hi'

end OAI.AnisotropicCalderon.DirichletFamily
