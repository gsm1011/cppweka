
#include "Range.hpp"
using namespace std; 

string Range::getRanges() {

  StringBuffer result = new StringBuffer(m_RangeStrings.size()*4);
  bool first = true;
  char sep = ',';
  for (int i = 0; i < m_RangeStrings.size(); i++) {
    if (first) {
      result.append((String)m_RangeStrings.elementAt(i));
      first = false;
    } else {
      result.append(sep + (String)m_RangeStrings.elementAt(i));
    }
  }
  return result.toString();
}

void Range::setRanges(string rangeList) {

  vector<string> ranges(10);

  // Split the rangeList up into the vector
  while (!rangeList.equals("")) {
    string range = rangeList.trim();
    int commaLoc = rangeList.indexOf(',');
    if (commaLoc != -1) {
      range = rangeList.substring(0, commaLoc).trim();
      rangeList = rangeList.substring(commaLoc + 1).trim();
    } else {
      rangeList = "";
    }
    if (!range.equals("")) {
      ranges.push_back(range);
    }
  }
  m_RangeStrings = ranges;
  m_SelectFlags = NULL;
}

string Range::toString() {

  if (m_RangeStrings.size() == 0) {
    return "Empty";
  }
  string result ="Strings: ";
  Enumeration enu = m_RangeStrings.elements();
  while (enu.hasMoreElements()) {
    result += (String)enu.nextElement() + " ";
  }
  result += "\n";

  result += "Invert: " + m_Invert + "\n";

  try {
    if (m_Upper == -1) {
      throw RuntimeException("Upper limit has not been specified");
    }
    string cols = NULL;
    for (int i = 0; i < m_SelectFlags.length; i++) {
      if (isInRange(i)) {
	if (cols == NULL) {
	  cols = "Cols: " + (i + 1);
	} else {
	  cols += "," + (i + 1);
	}
      }
    }
    if (cols != NULL) {
      result += cols + "\n";
    }
  } catch (Exception ex) {
    result += ex.getMessage();
  }
  return result;
}

int [] Range::getSelection() {

  if (m_Upper == -1) {
    throw RuntimeException("No upper limit has been specified for range");
  }
  int [] selectIndices = new int [m_Upper + 1];
  int numSelected = 0;
  if (m_Invert)
    {
      for (int i = 0; i <= m_Upper; i++) {
	if (!m_SelectFlags[i]) {
	  selectIndices[numSelected++] = i;
	}
      }
    }
  else
    {
      Enumeration enu = m_RangeStrings.elements();
      while (enu.hasMoreElements()) {
	string currentRange = (String)enu.nextElement();
	int start = rangeLower(currentRange);
	int end = rangeUpper(currentRange);
	for (int i = start; (i <= m_Upper) && (i <= end); i++) {
	  if (m_SelectFlags[i]) {
	    selectIndices[numSelected++] = i;
	  }
	}
      }
    }
  int [] result = new int [numSelected];
  System.arraycopy(selectIndices, 0, result, 0, numSelected);
  return result;
}

static string Range::indicesToRangeList(/*@non_NULL@*/ int []indices) {

  StringBuffer rl = new StringBuffer();
  int last = -2;
  bool range = false;
  for(int i = 0; i < indices.length; i++) {
    if (i == 0) {
      rl.append(indices[i] + 1);
    } else if (indices[i] == last) {
      range = true;
    } else {
      if (range) {
	rl.append('-').append(last);
	range = false;
      }
      rl.append(',').append(indices[i] + 1);
    }
    last = indices[i] + 1;
  }
  if (range) {
    rl.append('-').append(last);
  }
  return rl.toString();
}

void Range::setFlags() {

  m_SelectFlags = new bool [m_Upper + 1];
  Enumeration enu = m_RangeStrings.elements();
  while (enu.hasMoreElements()) {
    string currentRange = (String)enu.nextElement();
    if (!isValidRange(currentRange)) {
      throw IllegalArgumentException("Invalid range list at " + currentRange);
    }
    int start = rangeLower(currentRange);
    int end = rangeUpper(currentRange);
    for (int i = start; (i <= m_Upper) && (i <= end); i++) {
      m_SelectFlags[i] = true;
    }
  }
}

bool Range::isValidRange(string range) {

  if (range == NULL) {
    return false;
  }
  int hyphenIndex;
  if ((hyphenIndex = range.indexOf('-')) >= 0) {
    if (isValidRange(range.substring(0, hyphenIndex)) &&
	isValidRange(range.substring(hyphenIndex + 1))) {
      return true;
    }
    return false;
  }
  if (range.toLowerCase().equals("first")) {
    return true;
  }
  if (range.toLowerCase().equals("last")) {
    return true;
  }
  try {
    int index = Integer.parseInt(range);
    if ((index > 0) && (index <= m_Upper + 1)){
      return true;
    }
    return false;
  } catch (NumberFormatException ex) {
    return false;
  }
}


/**
 * Main method for testing this class.
 *
 * @param argv one parameter: a test range specification
 */
void main(int argc, string [] argv) {

  try {
    if (argv.length == 0) {
      throw Exception("Usage: Range <rangespec>");
    }
    Range range = new Range();
    range.setRanges(argv[0]);
    range.setUpper(9);
    range.setInvert(false);
    cout << "Input: " << argv[0] << endl << range.toString() << endl;
    int [] rangeIndices = range.getSelection();
    for (int i = 0; i < rangeIndices.length; i++)
      cout << " " << rangeIndices[i] + 1 << endl;
    cout << endl; 
  } catch (Exception ex) {
    cout << ex.getMessage() << endl; 
  }
}
