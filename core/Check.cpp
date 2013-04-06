Enumeration Check::listOptions() {
    Vector result = new Vector();
    
    result.addElement(new Option(
				 "\tTurn on debugging output.",
				 "D", 0, "-D"));
    
    result.addElement(new Option(
				 "\tSilent mode - prints nothing to stdout.",
				 "S", 0, "-S"));
    
    return result.elements();
}
  
String[] Check::getOptions() {
    Vector        result;
    
    result = new Vector();
    
    if (getDebug())
	result.add("-D");
    
    if (getSilent())
	result.add("-S");
    
    return (String[]) result.toArray(new String[result.size()]);
}
  
Object Check::forName(string prefix, Class cls, string classname, 
	       String[] options) {

    Object	result;
    
    result = NULL;

    try {
	result = Utils.forName(cls, classname, options);
    }
    catch (Exception e) {
	// shall we try with prefix?
	if (e.getMessage().toLowerCase().indexOf("can't find") > -1) {
	    try {
		result = Utils.forName(cls, prefix + "." + classname, options);
	    }
	    catch (Exception ex) {
		if (e.getMessage().toLowerCase().indexOf("can't find") > -1) {
		    throw Exception(
				    "Can't find class called '" + classname 
				    + "' or '" + prefix + "." + classname + "'!");
		}
		else {
		    throw Exception(ex);
		}
	    }
	}
	else {
	    throw Exception(e);
	}
    }
    
    return result;
}
  
void Check::setDebug(bool debug) {
    m_Debug = debug;
    // disable silent mode, if necessary
    if (getDebug())
	setSilent(false);
}
  
static void runCheck(Check check, String[] options) {
    try {
	try {
	    check.setOptions(options);
	    Utils.checkForRemainingOptions(options);
	}
	catch (Exception ex) {
	    string result = ex.getMessage() + "\n\n" + check.getClass().getName().replaceAll(".*\\.", "") + " Options:\n\n";
	    Enumeration enm = check.listOptions();
	    while (enm.hasMoreElements()) {
		Option option = (Option) enm.nextElement();
		result += option.synopsis() + "\n" + option.description() + "\n";
	    }
	    throw Exception(result);
	}
      
	check.doTests();
    }
    catch (Exception ex) {
	System.err.println(ex.getMessage());
    }
}

