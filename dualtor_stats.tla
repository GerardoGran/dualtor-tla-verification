----------------------------- MODULE dualtor_stats ----------------------------
EXTENDS CSV, TLC, TLCExt, IOUtils, FiniteSetsExt, Sequences, Integers, dualtor

Flags ==
    {{"TH"}, {"FL"}, {"FT"}, {"CX"}, {"FM"}, {"FH"}, {"OT"}}

VARIABLE flag, failures, active
simVars == <<flag, failures, active>>

SimInit ==
    /\ failures = 0
    /\ active = <<0, 0, 0>>
    \* Single feature flags.
    \* All subsets of feature flags.
    \* /\ flag \in SUBSET UNION Flags
    /\ flag \in {{}} \union Flags

    /\  mux \in {f \in [ active: T, next: T, serving: T \union {"-"} ]: f.active = f.next /\ f.serving = "-"}
    /\  torB \in InitialTor("torA", IF "OT" \in flag THEN {FALSE} ELSE {TRUE})
    /\  torA \in InitialTor("torB", {TRUE})

SimEnvironment == 
    /\ failures' = failures + 1
    /\  \* TLC will pick (an enabled) sub-action uniformly at random.
        \/ /\ "FM" \in flag
           /\ FailMux
        \/ /\ "FH" \in flag
           /\ FailHeartbeat
        \/ /\ "CX" \in flag
           /\ \/  CrashXCVRD(torA, torB)
              \/  CrashXCVRD(torB, torA)
        \/ /\ "FT" \in flag
           /\ \/ FailTor(torA, torB)
              \* Failing both ToRs has the unsurprising effect that 
              \* from that point onwards, none of them is active.
              \* With both tors dead, the behavior will deadlock.
              \*   \/ FailTor(torB, torA)
        \/ /\ "TH" \in flag
           /\ \/ TimeoutHeartbeat(torA, torB)
              \/ TimeoutHeartbeat(torB, torA)
        \/ /\ "FL" \in flag
           /\ \/ FailLinkState(torA, torB)
              \/ FailLinkState(torB, torA)
        \/ /\ "OT" \in flag
           /\ UNCHANGED vars

SimNext ==
    /\ UNCHANGED flag
    \* With a 1% chance, some part of the system may fail.
    /\ IF flag # {} /\ RandomElement(1..100) = 1
       THEN SimEnvironment
       ELSE System /\ UNCHANGED failures
    /\ active' = [ active EXCEPT ![Quantify({torA', torB'}, LAMBDA t: t \in ActiveTor) + 1] = @ + 1 ]

SimSpec ==
    /\ SimInit
    /\ [][SimNext]_<<vars, simVars>>

-------------------------------------------------------------------------------

ASSUME
    \* The data collection below only works with TLC running in generation mode.
    /\ TLCGet("config").mode = "generate"
    \* The algorithm does *not* terminate => Check for deadlocks.
    /\ TLCGet("config").deadlock = TRUE
    \* Require a recent versions of TLC with support for the operators appearing here.
    /\ TLCGet("revision").timestamp >= 1663720820 

CSVFile ==
    "dualtor_stats.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("torA#torB#none#one#both#states#flags#failures", <<>>, CSVFile)

WriteToCSV ==
    \* Cfg: CONSTRAINT WriteToCSV
    /\ TLCGet("level") = TLCGet("config").depth =>
        /\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s", 
            <<0, 0, active[1], active[2], active[3], TLCGet("level"), flag, failures>>, CSVFile)
        /\ TLCGet("stats").traces % 1000 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "dualtor_stats.R", CSVFile>>).exitValue = 0

PostCondition ==
    \* +1 because of header in csv file.
    \* /\ Assert(TLCGet("config").traces + 1 = CSVRecords(CSVFile), <<"Fewer or more samples than expected:", CSVRecords(CSVFile)>>)
    /\ IOExec(<<"/usr/bin/env", "Rscript", "dualtor_stats.R", CSVFile>>).exitValue = 0

===============================================================================

$ rm -rf states/ ; rm *.csv ; rm *.svg ; tlc dualtor_stats -note -generate num=1000 -depth 10000