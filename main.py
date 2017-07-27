
# ------------------------------  ------------------------------
# predefined in the config file:
# 
# - the valid variables (=column/header field)
# - the valid values for that variable
# - the relationships between varaibles
# ------------------------------  ------------------------------
# what the script file does:
# 
# - interpret command line args like:
# 	+ path to config file (mandatory, a JSON-file)
# 	+ path to input file (mandatory, a csv-fiel)
# 	+ path to output file (optional, 
# 		defaults to input file name with '.xbif' suffix)
# 	+ a custom csv field-separator (optional, default = \t)
# - read the config file
#	+ check for syntax errors
#	+ check for the following information
# 		* path to input csv file
# 		* the csv delimiter
# 		* path to output directory 
# 		* name of output xbiv file
# 		* variable definitions (name & list of valid values)
# 		* connection definition (A -> B)
# - check for problems like:
#	+ there is no wrapping dictionary at all
# 	+ there is no preferences variable defined
# 	+ there is no nodes variable defined
# 	+ there is no edges variable defined
# 	+ the nodes variable is empty
#   + duplicate variable names
#   + duplicate values for variables
#   + duplicate relationships
#   + circular relationships (including direct loop edges)
# - calculate node-positions
# - calculate NCPDs for the root nodes.
# - calculate CPDs for the inner nodes.
# - write the xbif data

# LX_OPTIONS: -v --lines -o ./ --fog_prefix "------------------------- FNC :: "
# LX_OPTIONS: -v -tc -o ./ --short_output --fog_prefix "------------------------- FNC :: "


# ? -p : print incompatible nodes
# ? -c : config file (JSON)
# ? -i : input file (CSV)
# ? -o : output file (XBIF)
# LX_ARGUMENTS: -c coinToss_config.json -i coinToss_input.csv -o cointoss.xbif -d '\t'
# LX_ARGUMENTS: -c config.json -i Access_DB_Daten_TSV.csv -o output.xbif
# LX_SWITCHES: -loops

# ============================== IMPORTS ==============================
import os
import sys
import cProfile;
import json
from json_tricks.nonp import load as loadIgnoringComments
import csv
from lxml import etree
import collections
import re
import itertools
import copy
import time
from decimal import *
from functools import reduce
import operator
# ============================== CONSTANTS ==============================
# ------------------------------ misc ------------------------------
# ? floating point numbers can have rounding errors. The rounding Errors have to  
MIN_DECIMAL_ROUNDING_ERROR = Decimal('0.0000000000000001');
SAMIAM_PRECISION = 16;
# ------------------------------ options ------------------------------
OPTION__CONFIG_JSON_FILE = "-c";
OPTION__INPUT_CSV_FILE = "-i";
OPTION__OUTPUT_XBIF_FILE = "-o";
OPTION__CSV_DELIMITER = "-d";
OPTION__PRINT_INCOMPATIBLE_NODES = "-p";
OPTION__PRINT_COMPATIBLE_NODES = "-P";
# ------------------------------ regex ------------------------------
REGEX__CSV_DELIMITER = "^(?:\t| |,|;)$";
REGEX__VALUE_STRING_FORMAT = "^.+$";
# ? in samiam, nodes have to begin with a letter and can only contain letters, numbers and underscores.
REGEX__NODE_NAME_FORMAT = "^[a-zA-Z][0-9a-zA-Z_]*$";
REGEX__NODE_POSITION = "^\s*\(\s*(?P<row>[1-9][0-9]*)\s*(?:/|,)\s*(?P<column>[1-9][0-9]*)\s*\)\s*$";
REGEX__EDGE = "^\s*(?P<source>[^\s]+)\s*(?:->|=>)\s*(?P<target>[^\s]+)\s*$";
# ------------------------------ defaults ------------------------------
DEFAULT__CSV_DELIMITER = '\t';
DEFAULT__GRID_SIZE_X = 50;
DEFAULT__GRID_SIZE_Y = 100;
DEFAULT__DATA_THRESHOLD = 0;
# ------------------------------ xbif document definition ------------------------------
XML_DTD_XBIF = """\
<?xml version="1.0" encoding="US-ASCII"?>

<!--
	Bayesian network in XMLBIF v0.3 (BayesNet Interchange Format)
-->

<!-- DTD for the XMLBIF 0.3 format -->
<!DOCTYPE BIF [
	<!ELEMENT BIF ( NETWORK )*>
	      <!ATTLIST BIF VERSION CDATA #REQUIRED>
	<!ELEMENT NETWORK ( NAME, ( PROPERTY | VARIABLE | DEFINITION )* )>
	<!ELEMENT NAME (#PCDATA)>
	<!ELEMENT VARIABLE ( NAME, ( OUTCOME |  PROPERTY )* ) >
	      <!ATTLIST VARIABLE TYPE (nature|decision|utility) "nature">
	<!ELEMENT OUTCOME (#PCDATA)>
	<!ELEMENT DEFINITION ( FOR | GIVEN | TABLE | PROPERTY )* >
	<!ELEMENT FOR (#PCDATA)>
	<!ELEMENT GIVEN (#PCDATA)>
	<!ELEMENT TABLE (#PCDATA)>
	<!ELEMENT PROPERTY (#PCDATA)>
]>
"""
# ============================== VARIABLES ==============================
# ------------------------------ paths ------------------------------
# path variables
pathToConfigJsonFile = None;
pathToInputCsvFile = None;
pathToOutputXbifFile = None;
# ------------------------------ config ------------------------------
# delimiter used to parse the csv file
csvDelimiter = None;
gridSizeX = DEFAULT__GRID_SIZE_X;
gridSizeY = DEFAULT__GRID_SIZE_Y;
dataThreshold = DEFAULT__DATA_THRESHOLD;
# ------------------------------ flags ------------------------------
flag_printIncompatibleNodes = False;
flag_printCompatibleNodes = False;
# ------------------------------ global data ------------------------------
# datastructure representing the network
network = {};
dict_csvNamesToNodeNames = {};
dict_nodeComplexities = {};
numberOfCalculatedPDs = 0;
numberOfPDsWithLittleData = 0;
numberOfSingleParentPDsWithLittleData = 0;
# ============================== FUNCTIONS ==============================
def errorAndExit(message, exception=None):
	errorString = "ERROR: "+message;
	if exception is not None:
		errorString = errorString+": "+str(exception);
	print(errorString, file=sys.stderr);
	exit();
# (I>)
def parseCommandLineArguments():
	global pathToConfigJsonFile, pathToInputCsvFile, pathToOutputXbifFile;
	global csvDelimiter, flag_printIncompatibleNodes;
	# (F)
	expectedArgument = "OPTION";
	# 
	for i in range(1,len(sys.argv)):
		argument = sys.argv[i];
		# > process this {{argument}}..
		if (expectedArgument == "OPTION") and (argument == OPTION__CONFIG_JSON_FILE):
			# > expect the config file path as the next argument (L)
			expectedArgument = "CONFIG_JSON_FILE";
		elif (expectedArgument == "CONFIG_JSON_FILE"):
			# ! argument should be the config file path (L)
			# > write it to a global variable (L)
			pathToConfigJsonFile = argument;
			expectedArgument = "OPTION";
		elif (expectedArgument == "OPTION") and (argument == OPTION__PRINT_INCOMPATIBLE_NODES):
			# > set the flag to print incompatible nodes. (L)
			flag_printIncompatibleNodes = True;
		elif (expectedArgument == "OPTION") and (argument == OPTION__PRINT_COMPATIBLE_NODES):
			# > set the flag to print compatible nodes. (L)
			flag_printCompatibleNodes = True;
		elif (expectedArgument == "OPTION") and (argument == OPTION__INPUT_CSV_FILE):
			# > expect the input file path as the next argument (L)
			expectedArgument = "INPUT_CSV_FILE";
		elif (expectedArgument == "INPUT_CSV_FILE"):
			# ! argument should be the input file path (L)
			# > write it to a global variable (L)
			pathToInputCsvFile = argument;
			expectedArgument = "OPTION";
		elif (expectedArgument == "OPTION") and (argument == OPTION__OUTPUT_XBIF_FILE):
			# > expect the output file as the next argument (L)
			expectedArgument = "OUTPUT_XBIF_FILE";
		elif (expectedArgument == "OUTPUT_XBIF_FILE"):
			# ! argument should be the output file path (L)
			# > write it to a global variable (L)
			pathToOutputXbifFile = argument;
			expectedArgument = "OPTION";
		elif (expectedArgument == "OPTION") and (argument == OPTION__CSV_DELIMITER):
			# > expect the csv delimiter as the next argument (L)
			expectedArgument = "CSV_DELIMITER"
		elif (expectedArgument == "CSV_DELIMITER"):
			# ! argument should be the csv delimiter (L)
			if (csvDelimiter is not None):
				errorAndExit("bad argument: assigning csv delimiter twice!");
			else:
				# > write it to a global variable. (L)
				# ? bytes..decode.. is to keep escape characters intact ('\t' etc)
				csvDelimiter = bytes(argument, "utf-8").decode("unicode_escape");
		else:
			errorAndExit("bad argument: "+argument);
	# ! all arguments are parsed.
	if pathToConfigJsonFile is None: 
		errorAndExit("bad arguments: please provied a config file path (option: -i <path>)!");
# (<I>) ------------------------------ CONFIG JSON ------------------------------ 
def parseConfigJsonFile():
	try:
		with open(pathToConfigJsonFile, 'r', newline='') as configJsonFile:
			# > read the json object from the file.
			configJsonObject = loadIgnoringComments(configJsonFile);
			# print(json.dumps(configJsonObject))
			if type(configJsonObject) is not collections.OrderedDict:
				errorAndExit("bad config file: outermost json entity is not a dict");
			#
			parseConfigJsonFile_preferences(configJsonObject);
			parseConfigJsonFile_nodes(configJsonObject);
			parseConfigJsonFile_edges(configJsonObject);
			# 
			checkNetworkForLoops()
	except IOError as e:
		errorAndExit("could not open the config file: "+pathToConfigJsonFile,e);
	except json.JSONDecodeError as e:
		errorAndExit("the json file has syntax errors: "+pathToConfigJsonFile,e);
# 
def parseConfigJsonFile_preferences(configJsonObject):
	# (F)
	try:
		preferences = configJsonObject["preferences"];
	except:
		errorAndExit("the config file is incomplete: could not find the field 'preferences'");
	# ------------------------------ csv delimiter ------------------------------
	global csvDelimiter;
	if (csvDelimiter is None) and ("csv_delimiter" in preferences):
		# ! the csv delimiter was NOT set by command line arguments and it IS provided in the config file. (L)
		csvDelimiter = preferences['csv_delimiter'];
		# > make sure the csv delimiter is valid.
		delimiterIsValid = re.match(REGEX__CSV_DELIMITER, csvDelimiter);
		if not delimiterIsValid:
			errorAndExit("bad config file: the specified csv delimiter is not valid");
	# ------------------------------ grid size X ------------------------------
	if "grid_size_x" in preferences:
		global gridSizeX;
		gridSizeX = preferences['grid_size_x'];
		if type(gridSizeX) is not int:
			errorAndExit("bad config file: the preferences field 'grid_size_x' must be of type 'int'");
		if gridSizeX < 0:
			errorAndExit("bad config file: 'grid_size_x' cannot be negative");
	# ------------------------------ grid size Y ------------------------------
	if "grid_size_y" in preferences:
		global gridSizeY;
		gridSizeY = preferences['grid_size_y'];
		if type(gridSizeY) is not int:
			errorAndExit("bad config file: the preferences field 'grid_size_y' must be of type 'int'");
		if gridSizeY < 0:
			errorAndExit("bad config file: 'grid_size_y' cannot be negative");
	# ------------------------------ data shreshold ------------------------------
	if "data_threshold" in preferences:
		global dataThreshold;
		dataThreshold = preferences['data_threshold'];
		if type(dataThreshold) is not int:
			errorAndExit("bad config file: the preferences field 'data_threshold' must be of type 'int'");
		if gridSizeY < 0:
			errorAndExit("bad config file: 'dataThreshold' cannot be negative");
# (<I>)
def parseConfigJsonFile_nodes(configJsonObject):
	# > get the 'nodes' field from the json object
	try:
		nodes = configJsonObject["nodes"];
	except:
		errorAndExit("the config file is incomplete: could not find the field 'nodes'")
	# > make sure 'nodes' is an array
	if type(nodes) is not list:
		errorAndExit("bad config file: the field 'nodes' must be of type 'array'");
	# > make sure the array is not empty
	if (len(nodes) == 0):
		errorAndExit("bad config file: the array 'nodes' is empty");
	# > loop over the nodes...
	global network;
	for i in range(0,len(nodes)):
		node = nodes[i];
		if type(node) is not collections.OrderedDict:
			errorAndExit("bad config file: node at index "+str(i)+": node must be of type 'dict'")
		# > get the name of the node
		try: nodeName = node["name"];
		except: errorAndExit("bad config file: node at index "+str(i)+": missing field: 'name'");
		# > make sure the 'name' is of type 'string'
		if type(nodeName) is not str:
			errorAndExit("bad config file: node at index "+str(i)+": field 'name' must be of type 'string'");
		# > make sure the name is valid
		if not re.match(REGEX__NODE_NAME_FORMAT,nodeName):
			errorAndExit("bad config file: node at index "+str(i)+": invalid name format: "+nodeName);
		# > make sure the name does not already exist
		if nodeName in network:
			errorAndExit("bad config file: node at index "+str(i)+": name '"+nodeName+"' already exists");
		# > get the csv-name, if specified
		csvName = nodeName;
		if "csv_name" in node:
			# ! this node DOES have a csv-name specified.
			csvName = node['csv_name']
			if type(csvName) is not str:
				errorAndExit("bad config file: node at index "+str(i)+": field 'csv_name' must be of type 'string'")
		# > make sure the csv name is not used twice
		if csvName in dict_csvNamesToNodeNames:
			errorAndExit("bad config file: node at index "+str(i)+": csv name"+csvName+" already exists");
		dict_csvNamesToNodeNames[csvName] = nodeName;
		# > add the node to the global 'network' variable
		network[nodeName] = {'name':nodeName,'csvName':csvName,'values':[],'parents':[],'children':[]};
		# > get the values of the node
		try: values = node["values"];
		except: errorAndExit("bad config file: node at index "+str(i)+": missing field: 'values'");
		# > make sure 'values' is an array
		if type(values) is not list:
			errorAndExit("bad config file: node at index "+str(i)+": the field 'values' must be of type 'array'");
		# > make sure at least one value is defined
		if (len(nodes) == 0):
			errorAndExit("bad config file: node at index "+str(i)+": the array 'values' is empty");
		# > loop over the values...
		for j in range(0,len(values)):
			value = values[j];
			# > make sure the value is of type 'string'
			if type(value) is not str:
				errorAndExit("bad config file: node at index "+str(i)+": value at index "+str(j)+": type must be 'string'");
			# > make sure the value string is valid.
			if not re.match(REGEX__VALUE_STRING_FORMAT,value):
				errorAndExit("bad config file: node at index "+str(i)+": invalid value format");
			# > make sure the value name does not already exist
			for k in range(0,j):
				if (values[k] == value):
					errorAndExit("bad config file: node at index "+str(i)+": value at index "+str(j)+": identical to value at index "+str(k));
			# > write the value to the coresponding network node.
			network[nodeName]['values'].append(value);
		# > try to get the position 
		try: positionString = node["position"];
		except: errorAndExit("bad config file: node at index "+str(i)+": missing field: 'position'");
		# > make sure the 'position' is of type 'string'
		if type(positionString) is not str:
			errorAndExit("bad config file: node at index "+str(i)+": the field 'position' must be of type 'string'");
		# > make sure the 'position' string has the right format
		positionMatch = re.search(REGEX__NODE_POSITION, positionString);
		if positionMatch is None:
			errorAndExit("bad config file: node at index "+str(i)+": field 'position' has invalid format");
		# > extract 'row' and 'column' and write them to the coresponding network node
		network[nodeName]['row'] = int(positionMatch.group('row'));
		network[nodeName]['column'] = int(positionMatch.group('column'));
# (<I>)
def parseConfigJsonFile_edges(configJsonObject):
	try:
		edges = configJsonObject["edges"];
	except:
		errorAndExit("the config file is incomplete: could not find the field 'edges'")
	# > make sure 'edges' is of type 'array'
	if type(edges) is not list:
		errorAndExit("bad config file: the field 'edges' must be of type 'array'");
	# > loop over the edges...
	for i in range(0,len(edges)):
		edgeString = edges[i];
		if type(edgeString) is not str:
			errorAndExit("bad config file: edge at index "+str(i)+": edge must be of type 'string'")
		# > match the edge string against the regex
		edgeMatch = re.search(REGEX__EDGE, edgeString);
		if edgeMatch is None:
			errorAndExit("bad config file: edge at index "+str(i)+": has invalid format");
		# > extract the names of source and target nodes from the match
		sourceNodeName = edgeMatch.group('source');
		targetNodeName = edgeMatch.group('target');
		# > make sure the edge's source and target nodes exist
		try: sourceNode = network[sourceNodeName];
		except: errorAndExit("bad config file: edge at index "+str(i)+": source node does not exist: "+sourceNodeName);
		try: targetNode = network[targetNodeName];
		except: errorAndExit("bad config file: edge at index "+str(i)+": target node does not exist: "+targetNodeName);
		# > connect the parent/child nodes with each other 
		sourceNode['children'].append(targetNode);
		targetNode['parents'].append(sourceNode);
# (<I>)
def checkNetworkForLoops():
	# (F)
	checkedNodes = [];
	loopingPath = None;
	def loopFinder(node,visitedNodes=None):
		nonlocal checkedNodes, loopingPath;
		if visitedNodes is None: 
			# ! this the initial call, NOT a recursive call. (L::loops)
			# > initialize 'visitedNodes'
			visitedNodes = [];
		# > get the node name.
		nodeName = node['name'];
		# > check if we already visited this node (=> we made a loop) (L::loops) {{nodeName}}
		if nodeName in visitedNodes:
			# ! we already visited this node => this is a loop. (L::loops)
			# > declare the visited nodes to be a looping path.
			loopingPath = visitedNodes;
			return True;
		# > check if the node is already confirmed as non-looping (L::loops) 
		if nodeName in checkedNodes:
			# ! this node's subtree is a non-looping area of the graph (L::loops)
			return False;
		# ! this is not a loop yet 
		# > remember visiting this node
		visitedNodes.append(nodeName);
		# > check if this is a leaf node
		children = node['children'];
		if len(children) == 0:
			# ! this is a leaf node => no loop (L::loops)
			# > mark the visited nodes as checked 
			checkedNodes.extend(visitedNodes)
			return False;
		# > check children for loops (L::loops)
		# ? for things to work out, every recursive call needs to get its own (independent)
		# list of visited nodes. So every child gets a copy except the last child, which gets the original.
		for i in range(0,len(children)):
			child = children[i];
			if i == (len(children)-1):
				# ! this is the last child.
				# > use the original list of visited nodes.
				hasLoop = loopFinder(child,visitedNodes);
			else:
				# ! this is not the last child.
				# > use a copy of the visited nodes.
				hasLoop = loopFinder(child,copy.copy(visitedNodes))
			# 
			if hasLoop: return True;
		# ! no loops found;
		return False;
	# ------------------------- 
	# > loop over network nodes and make sure none of them is part of a loop...
	for (_,node) in network.items(): 
		hasLoop = loopFinder(node);
		if hasLoop:
			errorAndExit("bad config file: network contains loop:\n"+" -> ".join(loopingPath))
# (<I>) ------------------------------ INPUT CSV ------------------------------
def parseInputCsvFile():
	# (F)
	global csvDelimiter;
	if csvDelimiter is None:
		# ! no csv delimiter was assigned > use the default (L)
		csvDelimiter = DEFAULT__CSV_DELIMITER;
	# 
	try:
		with open(pathToInputCsvFile, 'r', newline='') as inputCsvFile:
			# ? a DictReader is a sequence of (ordered) dictionaries, each representing a
			# row and the fields are indexed by the coldumn headers (as found in the first 
			# line of the file).
			# > get the DictReader and pull it into memory by converting it into a list.
			csvFileAsList = list(csv.DictReader(inputCsvFile,delimiter=csvDelimiter));
			# > make sure the input csv file is not empty
			if len(csvFileAsList) == 0:
				errorAndExit("bad input file: the csv file is empty: "+pathToInputCsvFile);
			# > get the header names (L)
			headerNames = csvFileAsList[0].keys(); 
			# > make sure all the defined nodes (config file) exist in the csv file.
			for csvName,_ in dict_csvNamesToNodeNames.items():
				if csvName not in headerNames:
					errorAndExit("bad csv file: cannot find name as defined in the config file: "+csvName)
			# > check if all table entries are valid.
			for row in csvFileAsList:
				for columnName,value in row.items():
					# > is this a relevant column?
					if columnName in dict_csvNamesToNodeNames:
						# ! this is a relevant column.
						# > make sure the field contains a valid value 
						allowedValues = network[dict_csvNamesToNodeNames[columnName]]['values'];
						if (value is not None) and (value not in allowedValues):
							# > the {{value}} is not allowed (L) {{allowedValues}}
							errorAndExit("bad input file: the value '"+value+"' is not allowed in column '"+columnName+"'"+"\n\nContent of the row:\n"+csvDelimiter.join([str(v) for v in row.values()]) );

			if flag_printIncompatibleNodes == True or flag_printCompatibleNodes == True:
				# ! the user decided (via command line option) to print the list of incompatible nodes instead of normal execution.
				printIncompatibleNodes(csvFileAsList);
				exit();
			else:
				# > calculate the CPDs for every node in the network.
				calculateCPDs(csvFileAsList);
	except IOError:
		errorAndExit("could not open the input csv file!");
	except Exception as e:
		print("--------- unknown error within parseInputCsvFile()", file = sys.stderr);
		raise;
# (<I>) ------------------------------ CALCULATE CPDs ------------------------------
def calculateCPDs(csvFileAsList):
	# (F)
	global numberOfCalculatedPDs, numberOfPDsWithLittleData, dict_nodeComplexities;
	# > loop over the network nodes and calculate a cpd for each... (L)
	for nodeName,node in network.items():
		# ? CPDs are represented as they are in xbif xbif file format:
		# a column for every value of the current variable
		# a row for every condition (i.e. every combination of values in the parent variables)
		cpd = []
		# ? the 'conditions' for a node are all possible value-combinations of the parent-nodes.
		# - the number of conditions is the number of rows in the child-cpd.
		# - if there is only one parent with n possible values, then there will be n conditions for the cpd of the child node.
		# - if there are two parents with n and m possible values, then there will be n*m conditions for the cpd of the child node.
		conditions = generateConditions(node);
		numberOfConditions = dict_nodeComplexities[nodeName];
		# if numberOfConditions > 10000:
			# ! the number of conditions is very high (L) (B) {{numberOfConditions}} (I)
		# > get this node's column name in the csv data base.
		columnName = node['csvName'];
		# # ------------------------------ >>> ------------------------------
		# counter = 0;
		# for condition in conditions:
		# 	counter += 1;
		# # {{columnName}} {{counter}}
		# continue;
		# # ------------------------------ <<< ------------------------------
		# > loop over the generated conditions... (L) {{columnName}}
		counter = 0;
		secondCounter = 0
		for condition in conditions:
			counter += 1;
			if counter % 1000 == 0:
				secondCounter += 1;
				# {{columnName}}
				print("\n\n----------- condition: "+str(counter)+"/"+str(numberOfConditions)+" -----------n\n");
				sys.stdout.flush()
				# time.sleep(0.5);
				# (B:this takes too long!) (I)__ secondCounter%100==0 __ 
			# > create new cpd row
			# ? a row represents the variable's propbability distribution for this condition. It has to sum to 1.
			cpdRow = [];
			# > calculate the number of csv rows that match this condition
			numberOfRowsThatMatchCondition = getRowCount(csvFileAsList, columnName, condition=condition);
			# > make sure there is enough data for this condition.
			if numberOfRowsThatMatchCondition > dataThreshold:
				# ! this condition DOES fit enough database entries to calculate a cpd.
				# > calculate the cpd row.
				for value in node['values']:
					# > get the number of rows that match this condition and this value.
					numberOfRowsThatMatchConditionAndValue = getRowCount(csvFileAsList, columnName, value, condition); 
					# > calculate the propbability for this value under the given condition. 
					# print("%r / %r" % (numberOfRowsThatMatchConditionAndValue,numberOfRowsThatMatchCondition))
					conditionalProbability = roundForSamiam( Decimal(numberOfRowsThatMatchConditionAndValue) / Decimal(numberOfRowsThatMatchCondition) );
					# > add the {{conditionalProbability}} to the cad. (L)
					cpdRow.append(conditionalProbability);
				# ! the cpdRow is now calculated. > remove possible rounding errors. (L)
				removeRoundingErrors(cpdRow);
			else:
				# ! this condition does NOT fit enough database entries to calculate a cpd. (L)
				# => normal calculation would create a non stochastic cpd row of [0 0 0...] (L)
				# > calculate the cpd row in a different way. (L)
				cpdRow = approximateCpdRowForDataShortage(csvFileAsList, columnName, node['values'], condition);
				# > count this for the statistics
				numberOfPDsWithLittleData += 1;
			assert(sum(cpdRow) == 1), " + ".join(map(lambda p: str(p), cpdRow)) + " = " + str(sum(cpdRow));
			cpd.append(cpdRow);
			# > count for the statistics
			numberOfCalculatedPDs += 1;
		# ! the whole cpd (every row) is now calculated. (L)
		# > write the cpd to the network node. (L)
		node['cpd'] = cpd;
		

	#
# (<I>)
def approximateCpdRowForDataShortage(csvFileAsList, columnName, nodeValues, condition):
	global numberOfSingleParentPDsWithLittleData;
	# ! the condition not matched by enough rows. (L) (F) {{columnName}} {{condition}} {{nodeValues}}
	# ? how do we solve this? Since there is not enough data for this condition, we try to reduce the
	# the condition by looking at each parent separately (instead of the strict value combination of all of them).
	# The cpd row is generated for each parent and all of them are summed up & normalized to calculate the final cpd row that is returned by the function: cpdRow = cpdRowForParent1 + cpdRowForParent2 + ... / numberOfParents
	# If there isn't even enough data to calculate the cpd row for one of the parents, then the uniform distribution is used ([1/n,...,1/n], with n=#values) since that is the choice with the maximum entropy (=> represents the highest uncertainty).
	# ------------------------- 
	numberOfParents = len(condition);
	numberOfValues = len(nodeValues);
	# > calcualte the uniform distribution (L)
	uniformDistribution = [1/Decimal(numberOfValues)]*numberOfValues;
	# > initialize the cpd row with zeros. (L) 
	unnormalizedCpdRow = [0]*numberOfValues;
	for (parentName,parentValue) in condition: 
		# loop: {{parentName}} {{parentValue}} (L)
		cpdRowForThisParent = [];
		# > create a reduced condition that only takes this specific parent into account.
		reducedCondition = [(parentName,parentValue)];
		numberOfRowsThatMatchCondition = getRowCount(csvFileAsList, columnName, condition=reducedCondition);
		# 
		if numberOfRowsThatMatchCondition <= dataThreshold:
			# ! this parent's column does not contain this value at all!
			# > use the uniform distribution.
			cpdRowForThisParent = uniformDistribution;
			# > count this for the statistics.
			numberOfSingleParentPDsWithLittleData += 1;
		else:
			# ! there ARE enough rows that matched the reduced condition to generate the partial cpd row (L)
			for value in nodeValues:
				numberOfRowsThatMatchConditionAndValue = getRowCount(csvFileAsList,columnName,value,reducedCondition);
				# > calculate the propbability for this value under the given condition. 
				# print("%r / %r = %r" % (numberOfRowsThatMatchConditionAndValue,numberOfRowsThatMatchCondition,
					# numberOfRowsThatMatchConditionAndValue/numberOfRowsThatMatchCondition));
				# > calculate the conditional propbability.
				conditionalProbability = Decimal(numberOfRowsThatMatchConditionAndValue) / Decimal(numberOfRowsThatMatchCondition);
				assert type(conditionalProbability) == type(Decimal()),"wrong type!: "+str(type(conditionalProbability));
				# > add the conditional propbability to the cad.
				cpdRowForThisParent.append(conditionalProbability);
		# ! the partial cpd row has been generated. (L) {{cpdRowForThisParent}} {{sum(cpdRowForThisParent)}}
		# > add it tho the sum.
		for i in range(0,len(unnormalizedCpdRow)):
			unnormalizedCpdRow[i] += cpdRowForThisParent[i];
			assert type(unnormalizedCpdRow[i]) == type(Decimal()),"wrong type!: "+str(type(unnormalizedCpdRow[i]));
	# ! all patial cpd rows are calculated and summed up.
	# > normalize the row: devide the sum by the number of summands. (L) {{unnormalizedCpdRow}} {{sum(unnormalizedCpdRow)}} {{numberOfParents}}
	cpdRow = [roundForSamiam(Decimal(propbability)/Decimal(numberOfParents)) for propbability in unnormalizedCpdRow];
	# remove possible rounding errors. (L)
	removeRoundingErrors(cpdRow);
	# > return the cpd row.
	return(cpdRow);
# (<I>)
def estimateComplexity():
	# (F)
	global dict_nodeComplexities;
	dict_nodeComplexities = {};
	for nodeName,node in network.items():
		numberOfConditions = reduce(operator.mul, [len(parent['values']) for parent in node['parents']], 1); 
		#
		dict_nodeComplexities[nodeName] = numberOfConditions;
	# {{dict_nodeComplexities}}
# (<I>)
def roundForSamiam(edgyDecimal):
	# (F+)
	roundedDecimal = edgyDecimal.quantize(Decimal(10)**-SAMIAM_PRECISION, rounding = ROUND_FLOOR);
	return(roundedDecimal);
# (<I>)
def removeRoundingErrors(cpdRow):
	# (F+)
	theSum = Decimal(sum(cpdRow));
	missingTotal = Decimal(1.0) - theSum;
	# {{missingTotal}}
	missingIncrements = missingTotal/MIN_DECIMAL_ROUNDING_ERROR;
	# {{theSum}} {{missingTotal}} {{missingIncrements}} 
	# now distribute the missing increments over the array.
	while missingIncrements > 0:
		# ! there are still some increments to distribute (L)
		for i in range(0,len(cpdRow)):
			# > stop as soon as all the missing increments are distributed.
			if missingIncrements == 0: 
				# ! missing increments are distributed > break (L)
				break;
			# > do not distribute over 'impossible' cases (propbability == 0).
			if cpdRow[i] == 0: continue;
			# > distribute one increment over this entry. (L) {{cpdRow[i]}}
			cpdRow[i] += MIN_DECIMAL_ROUNDING_ERROR; # {{cpdRow[i]}}
			# > there is now one less increment to distribute.
			missingIncrements -= 1;
	theSum = sum(cpdRow);
	# {{str(type(theSum))}} {{theSum}} {{cpdRow}} {{getcontext().prec}}
	assert sum(cpdRow) == 1, "rounding error was not removed: sum(cpdRow) = "+ str(sum(cpdRow));
	return(cpdRow);
# (<I>)
def generateConditions(node):
	nameValuePairsOfAllParents = []
	for parent in node['parents']:
		# a list of tuples (<parentColumnName>,<value>)
		nameValuePairsOfThisParent = [ (parent['csvName'],value) for value in parent['values'] ];
		nameValuePairsOfAllParents.append(nameValuePairsOfThisParent);
	# > calculate the conditions (L)
	# ? the nameValuePairsOfAllParents is a list of lists of tuples:
	# [ [(name1,value1),(name1,value2),...], [(name2,value1),(name2,value2),...], ...] 
	# ? itertools.product(list1, list2, list3, ..) makes a cartesian product of all the lists.
	conditions = itertools.product(*nameValuePairsOfAllParents);
	return conditions;
# (<I>)
dict_indicesForNodeAndValue = None;
def getRowCount_prepareDataStructure(csvFileAsList):
	global dict_indicesForNodeAndValue;
	# (F)
	# ? idea: to make row counting easier, we generate a datastructure that
	# contains the set of data-entry-indices (line numbers) for every combination 
	# of columnName and value (for values that are allowed in that column).
	# This way the question of #(lines that match N1(a)&N2(b)&N3(c) can be calculated as an indersection of three sets);
	# ------------------------- 
	# > initiate the datastructure as an empty dictionary
	dict_indicesForNodeAndValue = {};
	# > get a list of the column names (those in the csv file)
	columnNames = [node['csvName'] for node in network.values()];
	# > further initiate the datastructure by
	# 1) filling the dictionary with empty dirctionaries: one for each network node
	# 2) filling each of those dirctionaries with empty sets: one for each possible value of that node
	# => Any specific set can then be accessed via dict_indicesForNodeAndValue[<nodeName>][<value>]
	for _,node in network.items():
		dict_indicesForValue = {}
		for value in node['values']:
			# > create an empty set (to be populated with indices later)
			indices = set()
			# > add that set to the (value:indices)-dictionary
			dict_indicesForValue[value] = indices;
		# > add the (value:indices)-dict to the (nodeName:(value:indices))-dict
		dict_indicesForNodeAndValue[node['csvName']] = dict_indicesForValue;
	# ------------------------- 
	# > populate the empty datastructure using the data from the csv file..
	# loop over the rows in the csv file..
	for index,row in enumerate(csvFileAsList):
		# for each column name..
		for columnName in columnNames:
			# > get the value of the column from this row
			value = row[columnName];
			# > make sure there is a value
			if value is not None:
				# > add the index of this row to the datastructure, associated with the column and value.
				dict_indicesForNodeAndValue[columnName][value].add(index);
	# -------------------------

def getRowCount(csvFileAsList, columnName, value=None, condition=[]):
	# (F) {{columnName}} {{value}}{{condition}}
	# ? The condition is just a list of (columnName,value) tuples, that have to be matched in addition to the columnName and value that are provided as separate arguments. Providing them separately has mainly sematic reasons on the side of the caller.
	# ? idea: We calculate the number of columns that match the condition by using the support-datastructure dict_indicesForNodeAndValue: We calculate the number of columns that have certain fields (=columnName-value-pairs) by getting the rowindex-sets for each of those fields from the support-datastructure and intersecting all of them.
	# ------------------------- 
	# > make sure the support-datastructure is set up.
	if dict_indicesForNodeAndValue is None:
		# ! there is no data structure yet > set it up (L)
		getRowCount_prepareDataStructure(csvFileAsList);
	# ------------------------- handle trivial case efficiently
	if value is None and len(condition) == 0:
		# > return the number of nonempty rows for this column.
		return sum([len(indexSet) for indexSet in dict_indicesForNodeAndValue[columnName].values()]);
	# ------------------------- handle non-trivial cases...
	# > initiate the working variable.
	matchingRows = None;
	# ------------------------- do value
	if value is None:
		# no values specified => all values match (L)
		# > get the index-sets for all values in this column
		indexSetsForAllValues = dict_indicesForNodeAndValue[columnName].values()
		# > calcualte the union 
		nonemptyRowsForThisColumn = reduce(set.union, indexSetsForAllValues);
		#
		matchingRows = nonemptyRowsForThisColumn;
	else:
		# ! there is a value specified (L)
		# > get the index-set for the value (L)
		indicesThatMatchTheValue = dict_indicesForNodeAndValue[columnName][value];
		# 
		matchingRows = indicesThatMatchTheValue;
	# ------------------------- do conditions
	if len(condition) > 0:
		# ! there is a condition. (L)
		# > get the index-sets for the condition. (L)
		indexSets = [dict_indicesForNodeAndValue[n][v] for (n,v) in condition];
		# > intersect the indexsets to filter out those who dont match the whole condition.
		rowsThatMatchCondition = reduce(set.intersection, indexSets);
		# > reduce the matching rows to only those who also match the condition.
		matchingRows = matchingRows.intersection(rowsThatMatchCondition);
	# ------------------------- done
	# > return the length of the list (= the number or matching rows);
	return len(matchingRows)
# (<I)

# ------------------------------ OUTPUT XBIF ------------------------------
def writeOutputXbifFile():
	# (F)
	xmlNetwork = createXmlFromNetwork()
	xmlNetworkAsString = "\n\n"+str(etree.tostring(xmlNetwork, pretty_print=True),encoding='utf-8');
	try:
		#
		with open(pathToOutputXbifFile, 'w', newline='') as outputXbifFile:
			outputXbifFile.write(XML_DTD_XBIF)
			outputXbifFile.write(xmlNetworkAsString)
	except IOError as e:
		errorAndExit("could not write to output file: "+pathToOutputXbifFile,e);
	except Exception as e:
		print("unknown error!");
		raise;
# 
def createXmlFromNetwork():
	# ? more info on xbif format: http://www.cs.cmu.edu/~fgcozman/Research/InterchangeFormat/
	bifTag = etree.Element("BIF", VERSION="0.3");
	networkTag = etree.SubElement(bifTag, "NETWORK");
	etree.SubElement(networkTag, "NAME").text = "TEST_NAME";
	# 
	for nodeName,node in network.items():
		# ------------------------------ VARIABLE ------------------------------
		variableTag = etree.SubElement(networkTag, "VARIABLE", TYPE = "nature");
		etree.SubElement(variableTag, "NAME").text = nodeName;
		for value in node['values']:
			etree.SubElement(variableTag, "OUTCOME").text = value;
		# 
		etree.SubElement(variableTag, "PROPERTY").text = "position = ("+str(node['column']*gridSizeX)+","+str(node['row']*gridSizeY)+")";
		# ------------------------------ DEFINITION ------------------------------
		# > create the definition tag (which defines the edges and the CPD);
		definitionTag = etree.SubElement(networkTag, "DEFINITION");
		# > add the FOR-tag as a reference to the node/variable.
		etree.SubElement(definitionTag, "FOR").text = nodeName;
		# > loop over the parents...
		for parent in node['parents']:
			# > add the parents name as a reference to the parent.
			etree.SubElement(definitionTag, "GIVEN").text = dict_csvNamesToNodeNames[parent['csvName']];
		# > get the cpd from the node and convert it into a pretty string.
		cpdAsString = "\n".join([" ".join(map(lambda p: str(p),cpdRow)) for cpdRow in node['cpd']]);
		# > add the cpd between TABLE-tags.
		etree.SubElement(definitionTag, "TABLE").text = cpdAsString;
	# 
	return bifTag;

def printIncompatibleNodes(csvFileAsList):
	networkAsList = list(network.items());
	incompatibleNodes = [];
	compatibleNodes = [];
	for i in range(0,len(networkAsList)):
		(nodeName1,node1) = networkAsList[i];
		columnName1 = node1['csvName'];
		values1 = node1['values'];
		# 
		for j in range(i+1,len(networkAsList)):
			(nodeName2,node2) = networkAsList[j];
			columnName2 = node2['csvName'];
			values2 = node2['values'];
			# 
			valuePairs = [ (v1,v2) for v1 in values1 for v2 in values2 ];
			for k in range(0,len(valuePairs)):
				(value1, value2) = valuePairs[k];
				numberOfRowsThatMatchCondition = getRowCount(csvFileAsList,columnName1, value=value1, condition = [(columnName2, value2)]);
				if numberOfRowsThatMatchCondition == 0:
					incompatibleNodes.append((nodeName1,value1,nodeName2,value2));
					break;
				if k == len(valuePairs)-1:
					compatibleNodes.append((nodeName1,value1,nodeName2,value2));
			# 
		# 
	# 
	print("-------------------------")
	print("LIST OF INCOMPATIBLE NODES:")
	if len(incompatibleNodes) == 0:
		print("<none>");
	else:
		for (nodeName1,value1,nodeName2,value2) in incompatibleNodes:
			print("\n"+nodeName1+" = "+value1);
			print(nodeName2+" = "+value2);
			# print("\nnode '"+nodeName1+"' and node '"+nodeName2+"' in values '"+value1+"' and '"+value2+"'");



# ============================== EXECUTION ==============================
# > set the decimal precision to fit samiam.
# getcontext().prec = SAMIAM_PRECISION;
# > only round down, so rounding errors can be measured 
# getcontext().rounding = ROUND_FLOOR;
# ------------------------- 
parseCommandLineArguments()
parseConfigJsonFile()
estimateComplexity();
# cProfile.run('parseInputCsvFile()'); # (B:done)
parseInputCsvFile()
writeOutputXbifFile()
# > give feedback
print("\n\n");
print("-- Output written to {outfile}.".format(outfile=pathToOutputXbifFile))
print("-- There was data shortage for {0} out of {1} calculated PDs ({2:.{digits}f}%)".format(
	numberOfPDsWithLittleData,
	numberOfCalculatedPDs,
	(numberOfPDsWithLittleData/numberOfCalculatedPDs)*100,digits=2))
# -------------------------  
# END OF FILE (L)

