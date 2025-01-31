module mongoTxModel

enum TxState { Active, Committed, Aborted }

sig Document {
  docID: Int
}

sig Tx {
  state: TxState,
  updates: set Document
}

fact isolation {
  all t1, t2: Tx |
    (t1 != t2 and some (t1.updates & t2.updates)) =>
      not (t1.state = Committed and t2.state = Committed)
}

assert noDoubleCommit {
  no disj t1, t2: Tx |
    (some (t1.updates & t2.updates))
    and t1.state = Committed
    and t2.state = Committed
}

check noDoubleCommit for 5

assert atomicCommit {
  all t: Tx |
    (t.state = Committed) implies (some t.updates)
}

check atomicCommit for 5