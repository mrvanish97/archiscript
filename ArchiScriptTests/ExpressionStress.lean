import ArchiScriptExamples.ReservationController

namespace ArchiScriptTests.PresentationStress

open ArchiScript
open ArchiScriptExamples.ReservationController

#guard controllerPresentationFamily.presentations.length == 5
#guard controllerPresentationFamily.targets.length == 5

example :
    Presentation.denote controllerPlanPresentation =
      planControllerMutation := rfl

example :
    Presentation.denote controllerWritePresentation =
      persistMutation.comp planControllerMutation := rfl

example :
    Presentation.Rewrite
      (.comp
        (.atom nextReservationState)
        (.comp
          (.copair
            planUserMutationPresentation
            planPaymentMutationPresentation)
          (.coproductInl userContextPartition paymentContextPartition)))
      (.comp (.atom nextReservationState) planUserMutationPresentation) :=
  userSelectedStateNormalization

example :
    userPaymentFactoringCertificate.targetIso.toOperation.comp
        (Presentation.denote userPaymentPlanPresentation) =
      (Presentation.denote userPaymentFactoredPlanPresentation).comp
        userPaymentFactoringCertificate.sourceIso.toOperation :=
  userPaymentFactoringCertificate.commutes

example :
    controllerFactoringCertificate.targetIso.toOperation.comp
        (Presentation.denote controllerPlanPresentation) =
      (Presentation.denote controllerFactoredPlanPresentation).comp
        controllerFactoringCertificate.sourceIso.toOperation :=
  controllerFactoringCertificate.commutes

#guard controllerSourceFactoringIso.memberIndex.toFun
    (.inl (.inl ((.reserve, .available), .empty))) ==
  (.inl (.inl (.reserve, .available)), .empty)

#guard controllerSourceFactoringIso.memberIndex.toFun
    (.inl (.inr (.authorized, .held))) ==
  (.inl (.inr .authorized), .held)

#guard controllerSourceFactoringIso.memberIndex.toFun
    (.inr (.fired, .held)) ==
  (.inr .fired, .held)

example :
    projectedControllerStateOperation =
      nextReservationState.comp planControllerMutation := rfl

end ArchiScriptTests.PresentationStress
