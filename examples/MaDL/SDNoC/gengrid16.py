import sys
import math

# Grid definition
#  R0 = R1 * R2 = R3
#  ||   ||   ||   ||
#  R4 = R5 - R6 = R7
#  *    |    *    | 
#  R8 = R9 - R10=R11
#  ||   ||   ||   ||
#  R12=R13 * R14=R15

# Grid width/height
width = 4
height = 4
numRouters = width * height

# Define local rings, the first ID is the entry point
rings = [
	[5,4,0,1],
	[7,6,2,3],
	[13,12,8,9],
	[15,14,10,11],
]

DIR_N = 0
DIR_E = 1
DIR_S = 2
DIR_W = 3

CONN_NONE = 0
CONN_LOCAL = 1
CONN_GLOBAL = 2
CONN_BOTH = 3

#Description of the grid
# One router per line, inputs in the order N, E, S, W
outputs = [
	[CONN_NONE, 	CONN_LOCAL, 	CONN_NONE,		CONN_NONE], 	#Router 0
	[CONN_NONE, 	CONN_NONE, 		CONN_LOCAL, 	CONN_NONE], 	#Router 1
	[CONN_NONE, 	CONN_LOCAL, 	CONN_NONE, 		CONN_NONE],		#Router 2
	[CONN_NONE, 	CONN_NONE, 		CONN_LOCAL, 	CONN_NONE], 	#Router 3
	[CONN_LOCAL,	CONN_NONE, 		CONN_NONE,		CONN_NONE], 	#Router 4
	[CONN_NONE,		CONN_GLOBAL,	CONN_GLOBAL,	CONN_LOCAL],	#Router 5
	[CONN_LOCAL,	CONN_GLOBAL,	CONN_NONE,		CONN_GLOBAL],	#Router 6
	[CONN_NONE, 	CONN_NONE, 		CONN_GLOBAL, 	CONN_BOTH],		#Router 7
	[CONN_NONE, 	CONN_LOCAL, 	CONN_NONE,		CONN_NONE],		#Router 8
	[CONN_GLOBAL, 	CONN_NONE, 		CONN_BOTH, 		CONN_NONE],		#Router 9
	[CONN_NONE, 	CONN_LOCAL, 	CONN_NONE, 		CONN_NONE],		#Router 10
	[CONN_GLOBAL,	CONN_NONE,		CONN_BOTH,		CONN_NONE],		#Router 11
	[CONN_LOCAL,	CONN_NONE,		CONN_NONE,		CONN_NONE],		#Router 12
	[CONN_GLOBAL,	CONN_GLOBAL,	CONN_NONE,		CONN_LOCAL],	#Router 13
	[CONN_LOCAL,	CONN_GLOBAL,	CONN_NONE,		CONN_GLOBAL],	#Router 14
	[CONN_GLOBAL,	CONN_NONE,		CONN_NONE,		CONN_BOTH],		#Router 15
]

#Size of buffers
rBufSize = 2 # Ring buffer
sBufSize = 2 # Intermediate buffer (ejection)

def routerC(id, chan):
	return "R" + str(id) + "_" + str(chan)

def isRingEntry(id):
	for ring in rings:
		if ring[0] == id:
			return True
	return False

def getRing(id):
	for ring in rings:
		for router in ring:
			if router == id:
				return ring

def hasOutputDir(id, dir):
	return outputs[id][dir] > CONN_NONE

def hasRingVertical(id):
	ring = getRing(id)
	return id == ring[1] or id == ring[3]

def hasRingHorizontal(id):
	ring = getRing(id)
	return id == ring[0] or id == ring[2]

def hasRingDir(id, dir):
	return outputs[id][dir] & CONN_LOCAL > 0

def predInRing(id):
	for ring in rings:
		for r in ring:
			if r == id:
				return "(" + "||".join(map(lambda x: "p.dst==" + str(x), ring)) + ")"

def makePredN(id):
	pred = str.format("pred pred{0}N (p: package) {{p.dst!={0}&&(",id)

	if hasOutputDir(id, DIR_N):
		#True
		pred = pred + "1==1"
	else:
		#False
		pred = pred + "2==1"
	pred = pred + ")};"
	return pred

def makePredE(id):
	pred = str.format("pred pred{0}E (p: package) {{p.dst!={0}&&(",id)

	if hasOutputDir(id, DIR_E):
		# Eject if in local ring, continue otherwise
		if hasRingVertical(id):
			pred = pred + "(!" + predInRing(id) + ")"
		else:
			pred = pred + predInRing(id)
	else:
		# False
		pred = pred + "2==1"
	pred = pred + ")};"
	return pred

def makePredS(id):
	pred = str.format("pred pred{0}S (p: package) {{p.dst!={0}&&(",id)

	if hasOutputDir(id, DIR_S):
		# Can we eject to the west at all
		if outputs[id][DIR_W]:
			# Eject if in local ring, so continue if not in local ring
			pred = pred + "(!" + predInRing(id) + ")"
		else:
			# Can't eject, just continue
			pred = pred + "1==1"
	else:
		# False
		pred = pred + "2==1"
	pred = pred + ")};"
	return pred

def makePredW(id):
	pred = str.format("pred pred{0}W (p: package) {{p.dst!={0}&&(",id)

	if hasOutputDir(id, DIR_W):
		# Check if this router is main ring entry point
		if hasRingVertical(id):
			pred = pred + "(!" + predInRing(id) + ")"
		else:
			pred = pred + predInRing(id)
	else:
		#False
		pred = pred + "2==1"
	pred = pred + ")};"
	return pred

def makeInjPred(id):
	#Check if it is possible to output in horizontal direction
	if hasOutputDir(id, DIR_W) or hasOutputDir(id, DIR_E):
		# Check if it is possible on output in vertical direction
		if hasOutputDir(id, DIR_N) or hasOutputDir(id, DIR_S):
			#If in local ring and ring entry, inject Horizontal
			if hasRingHorizontal(id):
				return predInRing(id)
			else:
				return "(!" + predInRing(id) + ")"
		else:
			#Otherwise always inject in horizontal direction
			return "1==1"
	else:
		#Otherwise always inject in vertical direction
		return "1==2"

def makeX2YPred(id):
	if hasOutputDir(id, DIR_N):
		if hasOutputDir(id, DIR_S):
			if outputs[id][DIR_N] == CONN_LOCAL:
				return predInRing(id)
			else:
				if outputs[id][DIR_S] == CONN_LOCAL:
					return "(!" + predInRing(id) + ")"
				else:
					return str.format("p.dst < {}", id)
		else:
			return "1==1"
	else:
		return "1==2"

def makeY2XPred(id):
	if hasOutputDir(id, DIR_W):
		if hasOutputDir(id, DIR_E):
			if outputs[id][DIR_W] == CONN_LOCAL:
				return predInRing(id)
			else:
				if outputs[id][DIR_E] == CONN_LOCAL:
					return "(!" + predInRing(id) + ")"
				else:
					return str.format("p.dst % {0} < {1} % {0}", width, id)
		else:
			return "1==1"
	else:
		return "1==2"


# Make a ring stop definition
def makeRingStop(id, dirOut, dirIn):
	switch = str.format("chan R{0}_RS_{1}_CONT, R{0}_RS_{1}_EJCT := Switch(R{0}_RS_{2}_IN, pred{0}{1}, otherwise);", id, dirOut, dirIn)
	ringBuffer = str.format("chan R{0}_RS_{1}_RBuf := Queue({2}, R{0}_RS_{1}_CONT)[RS_{1}_RingBuf];", id, dirOut, rBufSize)
	interBuffer = str.format("chan R{0}_RS_{1}_SBuf := Queue({2}, R{0}_RS_{1}_EJCT)[RS_{1}_IntermBuf];", id, dirOut, sBufSize)
	merge = str.format("chan R{0}_RS_{1}_OUT := Merge(R{0}_RS_{1}_RBuf, R{0}_RS_{1}_INJ);", id, dirOut)

	return switch + ringBuffer + interBuffer + merge

# Make a router definition
def makeRouter(id):
	predN = makePredN(id)
	predE = makePredE(id)
	predS = makePredS(id)
	predW = makePredW(id)

	ringStopN = makeRingStop(id, "N", "S")
	ringStopE = makeRingStop(id, "E", "W")
	ringStopS = makeRingStop(id, "S", "N")
	ringStopW = makeRingStop(id, "W", "E")

	#Filter out packages with current router as destination, or destinations not in the network
	nic_filter_pred = str.format("pred NICPred(p:package) {{p.dst == {0}||p.dst >= {1}}};", id, numRouters);
	nic_filter = "chan " + routerC(id, "NIC_filter_drop") + "," + routerC(id, "NIC_IN") + ":= Switch(Source(package),NICPred, otherwise);"
	nic_sink = "Sink(" + routerC(id, "NIC_filter_drop") + ");"

	# Choose where to inject
	injPred = "pred injPred(p:package) {" + makeInjPred(id) + "};"
	inj_sw = "chan inj_X, inj_Y := Switch(" + routerC(id, "NIC_IN") + ", injPred, otherwise);"

	# X (W/E) to Y(N/S) switch
	x2y = str.format("chan R{0}_X2Y_OUT := XYSwitch({0}, inj_Y, R{0}_RS_W_SBuf, R{0}_RS_E_SBuf);", id)
	x2ypred = "pred x2ypred(p:package) {" + makeX2YPred(id) + "};"
	x2ySwitch = str.format("chan R{0}_RS_N_INJ, R{0}_RS_S_INJ := Switch(R{0}_X2Y_OUT, x2ypred, otherwise);", id)

	# Y (N/S) to X(W/E) switch
	y2x = str.format("chan R{0}_Y2X_OUT := XYSwitch({0}, inj_X, R{0}_RS_N_SBuf, R{0}_RS_S_SBuf);", id)
	y2xpred = "pred y2xpred(p:package) {" + makeY2XPred(id) + "};"
	y2xSwitch = str.format("chan R{0}_RS_W_INJ, R{0}_RS_E_INJ := Switch(R{0}_Y2X_OUT, y2xpred, otherwise);", id)

	# Set inputs of macro to inputs of ring stations
	inN = str.format("chan R{0}_RS_N_IN := Vars(R{0}_IN_N);", id)
	inE = str.format("chan R{0}_RS_E_IN := Vars(R{0}_IN_E);", id)
	inS = str.format("chan R{0}_RS_S_IN := Vars(R{0}_IN_S);", id)
	inW = str.format("chan R{0}_RS_W_IN := Vars(R{0}_IN_W);", id)

	# Set outputs of macro to outputs of ring stations
	outN = str.format("let R{0}_OUT_N := Vars(R{0}_RS_N_OUT);", id)
	outE = str.format("let R{0}_OUT_E := Vars(R{0}_RS_E_OUT);", id)
	outS = str.format("let R{0}_OUT_S := Vars(R{0}_RS_S_OUT);", id)
	outW = str.format("let R{0}_OUT_W := Vars(R{0}_RS_W_OUT);", id)

	routerNetwork = predN + predE + predS + predW
	routerNetwork = routerNetwork + ringStopN + ringStopE + ringStopS + ringStopW
	routerNetwork = routerNetwork + nic_filter_pred + nic_filter + nic_sink + injPred + inj_sw
	routerNetwork = routerNetwork + x2y + x2ypred + x2ySwitch + y2x + y2xpred + y2xSwitch
	routerNetwork = routerNetwork + inN + inE + inS + inW + outN + outE + outS + outW

	inputs = str.format("chan R{0}_IN_N, chan R{0}_IN_E, chan R{0}_IN_S, chan R{0}_IN_W", id)
	outputs = str.format("chan R{0}_OUT_N, chan R{0}_OUT_E, chan R{0}_OUT_S, chan R{0}_OUT_W", id)

	return "macro GridRouter" + str(id) + "(" + inputs + ") => " + outputs + " {" + routerNetwork + "};\n"

# Return the channel connections of a router in the grid
def connectRouter(id):
	# Calculate column/row of router
	col = id % width
	row = int(id / width)

	# Calculate inputs
	in_n = routerC(id, "OUT_N") if row == 0 else routerC(id - width, "OUT_S")
	in_e = routerC(id, "OUT_E") if col == width - 1 else routerC(id + 1, "OUT_W")
	in_s = routerC(id, "OUT_S") if row == height - 1 else routerC(id + width, "OUT_N")
	in_w = routerC(id, "OUT_W") if col == 0 else routerC(id - 1, "OUT_E")

	channels = str.format("chan R{0}_OUT_N, R{0}_OUT_E, R{0}_OUT_S, R{0}_OUT_W", id)
	inputs = in_n + "," + in_e + "," + in_s + "," + in_w
	return channels + " := GridRouter" + str(id) + "(" + inputs + "); \n"

def gen():
	# Calculate number of routers and destination field size
	numRouters = width * height
	dstSize = math.ceil(math.log(numRouters, 2))

	# File header
	lines = []
	lines.append("struct package { dst: [" + str(dstSize - 1) + ":0]; };\n")
	lines.append("param int WIDTH = " + str(width) + ";")
	lines.append("param int HEIGHT = " + str(height) + ";\n")
	lines.append("uses XYSwitch;")
	lines.append("\n")

	# Calculate routers
	for i in range(0, numRouters):
		lines.append(makeRouter(i))

	lines.append("\n")

	# Connect routers
	for i in range(0, numRouters):
		lines.append(connectRouter(i))

	# Save
	with open("gen/grid.madl", "w") as madlFile:
		madlFile.writelines(lines)

# Call top level method
gen()