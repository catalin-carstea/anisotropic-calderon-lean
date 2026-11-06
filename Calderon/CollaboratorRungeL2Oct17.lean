import Calderon.CollaboratorInteriorSmoothOct17
import Calderon.CollaboratorRungeL2DualOct17

/-! Runge approximation in `L²` for a fixed source set, from weak unique continuation
(Lassas–Liimatainen–Salo Prop. A.6, `L²` version; helper for tasks 07–09). -/

noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped ContDiff Matrix.Norms.Elementwise Distributions Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.Regularity
open TauCeti TauCeti.PDE _root_.OAI.AnisotropicCalderon.Affine

/-- Let `M = ball c R`, `A` smooth positive definite, `W ⊆ M` open (sources), and `K` the
Dirichlet solution map on `M` for smooth sources in `W`. Let `U` be open with closure inside an
open `U' ⊆ M`, `closure U` disjoint from `W`, and `M \ closure U` connected. Then every weak
solution `u0` of `div(A ∇u0) = 0` on `U'` is an `L²(U)` limit of the solutions `K f`. -/
theorem l2_runge (hUCP : UniqueContinuation) (c : R3) {R : ℝ} (hR : 0 < R)
    {A : R3 → Matrix (Fin 3) (Fin 3) ℝ} (hA : ContDiff ℝ ∞ A) (hpos : ∀ x, (A x).PosDef)
    {W : Opens R3} (hWne : (W : Set R3).Nonempty) (hW : (W : Set R3) ⊆ ball c R)
    (K : 𝓓(W, ℝ) → W1p (volume : Measure R3) (ballO c R) 2)
    (hK0 : ∀ f, K f ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2)
    (hK : ∀ f (φ : W1p (volume : Measure R3) (ballO c R) 2),
      φ ∈ w1p0Submodule (volume : Measure R3) (ballO c R) 2 →
      ∫ x in ball c R, matrixBilinearForm (A x) (W1p.gradient φ x) (W1p.gradient (K f) x) =
        ∫ x in ball c R, (f : R3 → ℝ) x * W1p.value φ x)
    {U U' : Set R3} (hU : IsOpen U) (hU' : IsOpen U') (hUU' : closure U ⊆ U')
    (hU'M : U' ⊆ ball c R) (hWU : Disjoint (W : Set R3) (closure U))
    (hconn : IsConnected (ball c R \ closure U))
    (u0 : W1p (volume : Measure R3) ⟨U', hU'⟩ 2)
    (hu0 : ∀ φ : 𝓓((⟨U', hU'⟩ : Opens R3), ℝ), ∫ x in U',
      matrixBilinearForm (A x) (gradient (φ : R3 → ℝ) x) (W1p.gradient u0 x) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : 𝓓(W, ℝ), ∫ x in U, (W1p.value (K f) x - W1p.value u0 x) ^ 2 < ε := by
  have hUM : U ⊆ ball c R := subset_closure.trans (hUU'.trans hU'M)
  have hm1 : (volume : Measure R3).restrict U ≤
      (volume : Measure R3).restrict ((ballO c R : Opens R3) : Set R3) :=
    Measure.restrict_mono hUM le_rfl
  have hm2 : (volume : Measure R3).restrict U ≤
      (volume : Measure R3).restrict (((⟨U', hU'⟩ : Opens R3)) : Set R3) :=
    Measure.restrict_mono (subset_closure.trans hUU') le_rfl
  let T : 𝓓(W, ℝ) → Lp ℝ 2 ((volume : Measure R3).restrict U) := fun f =>
    ((Lp.memLp (W1p.value (K f))).mono_measure hm1).toLp _
  let v : Lp ℝ 2 ((volume : Measure R3).restrict U) :=
    ((Lp.memLp (W1p.value u0)).mono_measure hm2).toLp _
  have hTae : ∀ f, (T f : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] W1p.value (K f) :=
    fun f => MemLp.coeFn_toLp _
  have hvae : (v : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict U] W1p.value u0 :=
    MemLp.coeFn_toLp _
  have hT : ∀ (a : ℝ) (f g : 𝓓(W, ℝ)), T (a • f + g) = a • T f + T g := by
    intro a f g
    have hKv : W1p.value (K (a • f + g)) = a • W1p.value (K f) + W1p.value (K g) := by
      rw [RungeAux.K_add_smul c hR hA.continuous hpos K hK0 hK a f g, w1_value_add,
        w1_value_smul]
    have h1 := ae_mono hm1 (Lp.coeFn_add (a • W1p.value (K f)) (W1p.value (K g)))
    have h2 := ae_mono hm1 (Lp.coeFn_smul a (W1p.value (K f)))
    apply Lp.ext
    filter_upwards [hTae (a • f + g), Lp.coeFn_add (a • T f) (T g), Lp.coeFn_smul a (T f),
      hTae f, hTae g, h1, h2] with x e1 e2 e3 e4 e5 e6 e7
    rw [e2, Pi.add_apply, e3, Pi.smul_apply, e1, hKv, e6, Pi.add_apply, e7, Pi.smul_apply, e4,
      e5]
  have horth : ∀ h : Lp ℝ 2 ((volume : Measure R3).restrict U),
      (∀ f, ⟪T f, h⟫_ℝ = 0) → ⟪v, h⟫_ℝ = 0 := by
    intro h hh
    have hcore := RungeAux.orth_core hUCP c hR hA hpos
      (fun hO _ hw => exists_smooth_of_weak hO hA hpos hw) hWne hW K hK0 hK hU hU' hUU' hU'M
      hWU hconn u0 hu0 h (fun f => by
        have := hh f
        rw [L2.inner_def] at this
        rw [← this]
        refine integral_congr_ae ?_
        filter_upwards [hTae f] with x hx
        simp [hx])
    rw [L2.inner_def, ← hcore]
    refine integral_congr_ae ?_
    filter_upwards [hvae] with x hx
    simp [hx]
  obtain ⟨f, hf⟩ := RungeAux.approx_of_orth T hT v horth (Real.sqrt_pos.2 hε)
  refine ⟨f, ?_⟩
  have hn : ‖T f - v‖ ^ 2 < ε := (Real.lt_sqrt (norm_nonneg _)).1 hf
  rw [← real_inner_self_eq_norm_sq, L2.inner_def] at hn
  refine lt_of_eq_of_lt (integral_congr_ae ?_) hn
  filter_upwards [Lp.coeFn_sub (T f) v, hTae f, hvae] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2, h3]
  simp [sq]

end OAI.AnisotropicCalderon.Regularity
