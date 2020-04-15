# madl-dvt
MaDL Design &amp; Verification Tools

A quick installation guide.
1. Clone the repo.
2. Install the latest stack by executing either "curl -sSL https://get.haskellstack.org/ | sh" or "wget -qO- https://get.haskellstack.org/ | sh"
3. Execute "stack build" from the project folder.

### Executables

The main executable is the deadlock detection tool.

### To reproduce the experiments with idle and block equations for xMAS FSMs

1. Make sure that the folder with dlockdetect is in the system path.
2. Execute "python3 dac_experiments.py [output_file]". You can find fmcad_experiments.py and the corresponding experimental xMAS models in madl-dvt/examples/.  

