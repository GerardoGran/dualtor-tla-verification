----------------------------- MODULE dualtor_stats ----------------------------
EXTENDS CSV, TLC, TLCExt, IOUtils, FiniteSets, Sequences, Integers, dualtor

ASSUME
    \* The data collection below only works with TLC running in generation mode.
    /\ TLCGet("config").mode = "generate"
    \* The algorithm terminates. Thus, do not check for deadlocks.
    /\ TLCGet("config").deadlock = FALSE
    \* Require a recent versions of TLC with support for the operators appearing here.
    /\ TLCGet("revision").timestamp >= 1663720820 

CSVFile ==
    "dualtor_stats.csv"

Reset ==
    /\ TLCSet(1, 0)
    /\ TLCSet(2, 0)
    /\ TLCSet(3, 0)
    /\ TLCSet(4, 0)
    /\ TLCSet(5, 0)

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("torA,torB,one,both,none,states", <<>>, CSVFile)
    /\ Reset

CollectStats ==
    /\ IF torA \in ActiveTor THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF torB \in ActiveTor THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE
    /\ IF Cardinality(ActiveToRs) = 1 THEN TLCSet(3, TLCGet(3) + 1) ELSE TRUE
    /\ IF Cardinality(ActiveToRs) = 2 THEN TLCSet(4, TLCGet(4) + 1) ELSE TRUE
    /\ IF Cardinality(ActiveToRs) = 0 THEN TLCSet(5, TLCGet(5) + 1) ELSE TRUE

WriteToCSV ==
    \* Cfg: CONSTRAINT WriteToCSV
    /\ TLCGet("level") = TLCGet("config").depth =>
        /\ CSVWrite("%1$s,%2$s,%3$s,%4$s,%5$s,%6$s", 
            <<TLCGet(1), TLCGet(2), TLCGet(3), TLCGet(4), TLCGet(5), TLCGet("level")>>, CSVFile)
        /\ Reset
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "dualtor_stats.R", CSVFile>>).exitValue = 0

PostCondition ==
    \* +1 because of header in csv file.
    /\ Assert(TLCGet("config").traces + 1 = CSVRecords(CSVFile), <<"Fewer samples than expected:", CSVRecords(CSVFile)>>)
    /\ IOExec(<<"/usr/bin/env", "Rscript", "dualtor_stats.R", CSVFile>>).exitValue = 0

===============================================================================

$ rm *.csv *.svg ; tlc dualtor_stats -note -generate num=1000 -depth 10000