namespace ArchiScript

/-- A review address names a model object, not a page in a rendered pack. -/
inductive ReviewSubjectKind where
  | carrier | partition | member | operation | branch | effectContract | implementationBinding
  deriving DecidableEq, BEq, Repr

structure ReviewSubject where
  kind : ReviewSubjectKind
  canonicalId : String
  deriving BEq, Repr

inductive FindingDisposition where
  | open | addressed | accepted
  deriving DecidableEq, BEq, Repr

/-- A human concern stays attached to its canonical model subject. -/
structure ReviewFinding where
  id : String
  subject : ReviewSubject
  reviewer : String
  concern : String
  requestedChange : String
  disposition : FindingDisposition := .open
  deriving Repr

/-- Approval is explicitly attributed to a reviewer and a model revision. -/
inductive ReviewDecision where
  | draft
  | readyForReview
  | changesRequested
  | approved (reviewer : String) (revision : String)
  | superseded
  deriving BEq, Repr

structure ReviewRecord where
  modelRevision : String
  decision : ReviewDecision := .draft
  findings : List ReviewFinding := []
  deriving Repr

/-- Workflow gate, not a claim that a reviewer identity has been authenticated. -/
def ReviewRecord.implementationAllowed (record : ReviewRecord) : Bool :=
  match record.decision with
  | .approved reviewer revision =>
    !reviewer.isEmpty && !revision.isEmpty && revision == record.modelRevision &&
      !(record.findings.any fun finding => finding.disposition == .open)
  | _ => false

end ArchiScript
