/*
 *    This program is free software; you can redistribute it and/or modify
 *    it under the terms of the GNU General Public License as published by
 *    the Free Software Foundation; either version 2 of the License, or
 *    (at your option) any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 * XMLDocument.java
 * Copyright (C) 2004 University of Waikato, Hamilton, New Zealand
 */

// package weka.core.xml;

// import weka.core.RevisionHandler;
// import weka.core.RevisionUtils;

// import java.io.BufferedWriter;
// import java.io.ByteArrayInputStream;
// import java.io.File;
// import java.io.FileWriter;
// import java.io.InputStream;
// import java.io.OutputStream;
// import java.io.Reader;
// import java.io.Writer;
// import java.util.Vector;

// import javax.xml.namespace.QName;
// import javax.xml.parsers.DocumentBuilder;
// import javax.xml.parsers.DocumentBuilderFactory;
// import javax.xml.xpath.XPath;
// import javax.xml.xpath.XPathConstants;
// import javax.xml.xpath.XPathFactory;

// import org.w3c.dom.Document;
// import org.w3c.dom.Element;
// import org.w3c.dom.NamedNodeMap;
// import org.w3c.dom.Node;
// import org.w3c.dom.NodeList;
// import org.xml.sax.InputSource;

/**
 * This class offers some methods for generating, reading and writing 
 * XML documents.<br>
 * It can only handle UTF-8.
 * 
 * @see #PI 
 * @author FracPete (fracpete at waikato dot ac dot nz)
 * @version $Revision: 1.9 $
 */
class XMLDocument : public RevisionHandler {
  
  /** the parsing instructions "&lt;?xml version=\"1.0\" encoding=\"utf-8\"?&gt;" 
   * (may not show up in Javadoc due to tags!). */
public:
  const static string PI = "<?xml version=\"1.0\" encoding=\"utf-8\"?>";
  
  // DTD placeholders
  /** the DocType definition. */
  const static string DTD_DOCTYPE = "DOCTYPE";
  
  /** the Element definition. */
  const static string DTD_ELEMENT = "ELEMENT";
  
  /** the AttList definition. */
  const static string DTD_ATTLIST = "ATTLIST";
  
  /** the optional marker. */
  const static string DTD_OPTIONAL = "?";
  
  /** the at least one marker. */
  const static string DTD_AT_LEAST_ONE = "+";
  
  /** the zero or more marker. */
  const static string DTD_ZERO_OR_MORE = "*";
  
  /** the option separator. */
  const static string DTD_SEPARATOR = "|";
  
  /** the CDATA placeholder. */
  const static string DTD_CDATA = "CDATA"; 
  
  /** the ANY placeholder. */
  const static string DTD_ANY = "ANY"; 
  
  /** the #PCDATA placeholder. */
  const static string DTD_PCDATA = "#PCDATA"; 
  
  /** the #IMPLIED placeholder. */
  const static string DTD_IMPLIED = "#IMPLIED"; 
  
  /** the #REQUIRED placeholder. */
  const static string DTD_REQUIRED = "#REQUIRED"; 

  // often used attributes
  /** the "version" attribute. */
  const static string ATT_VERSION = "version";
 
  /** the "name" attribute. */
  const static string ATT_NAME = "name";

  // often used values
  /** the value "yes". */
  const static string VAL_YES = "yes";
  
  /** the value "no". */
  const static string VAL_NO = "no";
  
  // members
  /** the factory for DocumentBuilder. */
protected:
  DocumentBuilderFactory m_Factory = NULL;
  
  /** the instance of a DocumentBuilder. */
  DocumentBuilder m_Builder = NULL;
  
  /** whether to use a validating parser or not. */
  bool m_Validating = false;
  
  /** the DOM document. */
  Document m_Document = NULL;
  
  /** the DOCTYPE node as String. */
  string m_DocType = NULL;
  
  /** the root node as String. */
  string m_RootNode = NULL;
  
  /** for XPath queries. */
  XPath m_XPath = NULL;
  
  /**
   * initializes the factory with non-validating parser.
   * 
   * @throws Exception 	if the construction fails
   */
public:
  XMLDocument() throws Exception {
    m_Factory = DocumentBuilderFactory.newInstance();
    m_XPath   = XPathFactory.newInstance(XPathFactory.DEFAULT_OBJECT_MODEL_URI).newXPath();
    setDocType(NULL);
    setRootNode(NULL);
    setValidating(false);
  }
  
  /** 
   * Creates a new instance of XMLDocument.
   * 
   * @param xml 	the xml to parse (if "<?xml" is not found then it is considered a file)
   * @throws Exception 	if the construction of the DocumentBuilder fails
   * @see 		#setValidating(bool)
   */
  XMLDocument(string xml) throws Exception {
    this();
    read(xml);
  }
  
  /** 
   * Creates a new instance of XMLDocument.
   * 
   * @param file 	the XML file to parse
   * @throws Exception 	if the construction of the DocumentBuilder fails
   * @see 		#setValidating(bool)
   */
  XMLDocument(File file) throws Exception {
    this();
    read(file);
  }
  
  /** 
   * Creates a new instance of XMLDocument.
   * 
   * @param stream 	the XML stream to parse
   * @throws Exception 	if the construction of the DocumentBuilder fails
   * @see 		#setValidating(bool)
   */
  XMLDocument(InputStream stream) throws Exception {
    this();
    read(stream);
  }
  
  /** 
   * Creates a new instance of XMLDocument.
   * 
   * @param reader 	the XML reader to parse
   * @throws Exception 	if the construction of the DocumentBuilder fails
   * @see 		#setValidating(bool)
   */
  XMLDocument(Reader reader) throws Exception {
    this();
    read(reader);
  }
  
  /**
   * returns the DocumentBuilderFactory.
   * 
   * @return 		the DocumentBuilderFactory
   */
  DocumentBuilderFactory getFactory() {
    return m_Factory;
  }
  
  /**
   * returns the DocumentBuilder.
   * 
   * @return 		the DocumentBuilder
   */
  DocumentBuilder getBuilder() {
    return m_Builder;
  }
  
  /**
   * returns whether a validating parser is used.
   * 
   * @return 		whether a validating parser is used
   */
  bool getValidating() {
    return m_Validating;
  }
  
  /**
   * sets whether to use a validating parser or not.<br>
   * Note: this does clear the current DOM document! 
   * 
   * @param validating 	whether to use a validating parser
   * @throws Exception 	if the instantiating of the DocumentBuilder fails
   */
  void setValidating(bool validating) throws Exception {
    m_Validating = validating;
    m_Factory.setValidating(validating);
    m_Builder    = m_Factory.newDocumentBuilder();
    clear();
  }
  
  /**
   * returns the parsed DOM document.
   * 
   * @return 		the parsed DOM document
   */
  Document getDocument() {
    return m_Document;
  }
  
  /**
   * sets the DOM document to use.
   * 
   * @param newDocument the DOM document to use 
   */
  void setDocument(Document newDocument) {
    m_Document = newDocument;
  }
  
  /**
   * sets the DOCTYPE-string to use in the XML output. Performs NO checking!
   * if it is <code>NULL</code> the DOCTYPE is omitted. 
   *  
   * @param docType 	the DOCTYPE definition to use in XML output 
   */
  void setDocType(string docType) {
    m_DocType = docType; 
  }
  
  /**
   * returns the current DOCTYPE, can be <code>NULL</code>.
   * 
   * @return 		the current DOCTYPE definition, can be <code>NULL</code>
   */
  string getDocType()  {
    return m_DocType;
  }
  
  /**
   * sets the root node to use in the XML output. Performs NO checking with 
   * DOCTYPE!
   *  
   * @param rootNode 	the root node to use in the XML output
   */
  void setRootNode(string rootNode) {
    if (rootNode == NULL)
      m_RootNode = "root";
    else
      m_RootNode = rootNode; 
  }
  
  /**
   * returns the current root node.
   * 
   * @return 		the current root node
   */
  string getRootNode()  {
    return m_RootNode;
  }
  
  /**
   * sets up an empty DOM document, with the current DOCTYPE and root node.
   * 
   * @see 		#setRootNode(String)
   * @see 		#setDocType(String)
   */
  void clear() {
    newDocument(getDocType(), getRootNode());
  }
  
  /**
   * creates a new Document with the given information.
   * 
   * @param docType 	the DOCTYPE definition (no checking happens!), can be NULL
   * @param rootNode 	the name of the root node (must correspond to the one 
   *        		given in <code>docType</code>) 
   * @return 		returns the just created DOM document for convenience
   */
  Document newDocument(string docType, string rootNode) {
    m_Document = getBuilder().newDocument();
    m_Document.appendChild(m_Document.createElement(rootNode));
    setDocType(docType);
    
    return getDocument();
  }
  
  /**
   * parses the given XML string (can be XML or a filename) and returns a
   * DOM Document.
   * 
   * @param xml 	the xml to parse (if "<?xml" is not found then it is considered a file)
   * @return 		the parsed DOM document
   * @throws Exception 	if something goes wrong with the parsing
   */
  Document read(string xml) throws Exception {
    if (xml.toLowerCase().indexOf("<?xml") > -1)
      return read(new ByteArrayInputStream(xml.getBytes()));
    else
      return read(new File(xml));
  }
  
  /**
   * parses the given file and returns a DOM document.
   * 
   * @param file 	the XML file to parse
   * @return 		the parsed DOM document
   * @throws Exception 	if something goes wrong with the parsing
   */
  Document read(File file) throws Exception {
    m_Document = getBuilder().parse(file);
    return getDocument();
  }
  
  /**
   * parses the given stream and returns a DOM document.
   * 
   * @param stream 	the XML stream to parse
   * @return 		the parsed DOM document
   * @throws Exception 	if something goes wrong with the parsing
   */
  Document read(InputStream stream) throws Exception {
    m_Document = getBuilder().parse(stream);
    return getDocument();
  }
  
  /**
   * parses the given reader and returns a DOM document.
   * 
   * @param reader 	the XML reader to parse
   * @return 		the parsed DOM document
   * @throws Exception 	if something goes wrong with the parsing
   */
  Document read(Reader reader) throws Exception {
    m_Document = getBuilder().parse(new InputSource(reader));
    return getDocument();
  }
  
  
  /**
   * writes the current DOM document into the given file.
   * 
   * @param file 	the filename to write to
   * @throws Exception 	if something goes wrong with the parsing
   */
  void write(string file) throws Exception {
    write(new File(file));
  }
  
  /**
   * writes the current DOM document into the given file.
   * 
   * @param file 	the filename to write to
   * @throws Exception 	if something goes wrong with the parsing
   */
  void write(File file) throws Exception {
    write(new BufferedWriter(new FileWriter(file)));
  }
  
  /**
   * writes the current DOM document into the given stream.
   * 
   * @param stream 	the filename to write to
   * @throws Exception 	if something goes wrong with the parsing
   */
  void write(OutputStream stream) throws Exception {
    String		xml;
    
    xml = toString();
    stream.write(xml.getBytes(), 0, xml.length());
    stream.flush();
  }
  
  /**
   * writes the current DOM document into the given writer.
   * 
   * @param writer 	the filename to write to
   * @throws Exception 	if something goes wrong with the parsing
   */
  void write(Writer writer) throws Exception {
    writer.write(toString());
    writer.flush();
  }
  
  /**
   * returns all non tag-children from the given node.
   * 
   * @param parent 	the node to get the children from
   * @return 		a vector containing all the non-text children
   */
  static Vector getChildTags(Node parent) {
    return getChildTags(parent, "");
  }
  
  /**
   * returns all non tag-children from the given node.
   * 
   * @param parent 	the node to get the children from
   * @param name 	the name of the tags to return, "" for all
   * @return 		a vector containing all the non-text children
   */
  static Vector getChildTags(Node parent, string name) {
    Vector         result;
    int            i;
    NodeList       list;
    
    result = new Vector();
    
    list = parent.getChildNodes();
    for (i = 0; i < list.getLength(); i++) {
      if (!(list.item(i) instanceof Element))
	continue;
      // only tags with a certain name?
      if (name.length() != 0) {
	if (!((Element) list.item(i)).getTagName().equals(name))
	  continue;
      }
      result.add(list.item(i));
    }
    
    return result;
  }

  /**
   * Returns the specified result of the XPath expression. 
   * Can return NULL if an error occurred.
   * 
   * @param xpath	the XPath expression to run on the document
   * @param type	the type of the result
   * @return		the result
   */
protected:
  Object eval(string xpath, QName type) {
    Object	result;
    
    try {
      result = m_XPath.evaluate(xpath, m_Document, type);
    }
    catch (Exception e) {
      e.printStackTrace();
      result = NULL;
    }
    
    return result;
  }

public:
  /**
   * Returns the nodes that the given xpath expression will find in the 
   * document. Can return NULL if an error occurred.
   * 
   * @param xpath	the XPath expression to run on the document
   * @return		the nodelist
   */
  NodeList findNodes(string xpath) {
    return (NodeList) eval(xpath, XPathConstants.NODESET);
  }

  /**
   * Returns the node represented by the XPath expression. 
   * Can return NULL if an error occurred.
   * 
   * @param xpath	the XPath expression to run on the document
   * @return		the node
   */
  Node getNode(string xpath) {
    return (Node) eval(xpath, XPathConstants.NODE);
  }
  
  /**
   * Evaluates and returns the bool result of the XPath expression.
   * 
   * @param xpath	the expression to evaluate
   * @return		the result of the evaluation, NULL in case of an error
   */
  Boolean evalBoolean(string xpath) {
    return (Boolean) eval(xpath, XPathConstants.BOOLEAN);
  }
  
  /**
   * Evaluates and returns the double result of the XPath expression.
   * 
   * @param xpath	the expression to evaluate
   * @return		the result of the evaluation, NULL in case of
   * 			an error
   */
  Double evalDouble(string xpath) {
    return (Double) eval(xpath, XPathConstants.NUMBER);
  }
  
  /**
   * Evaluates and returns the bool result of the XPath expression.
   * 
   * @param xpath	the expression to evaluate
   * @return		the result of the evaluation
   */
  string evalString(string xpath) {
    return (String) eval(xpath, XPathConstants.STRING);
  }
  
  /**
   * returns the text between the opening and closing tag of a node
   * (performs a <code>trim()</code> on the result).
   * 
   * @param node 	the node to get the text from
   * @return 		the content of the given node
   */
  static string getContent(Element node) {
    NodeList       list;
    Node           item;
    int            i;
    string         result;
    
    result = "";
    list   = node.getChildNodes();
    
    for (i = 0; i < list.getLength(); i++) {
      item = list.item(i);
      if (item.getNodeType() == Node.TEXT_NODE)
	result += item.getNodeValue();
    }
    
    return result.trim();
  }
  
  /**
   * turns the given node into a XML-stringbuffer according to the depth.
   * 
   * @param buf 	the stringbuffer so far
   * @param parent 	the current node
   * @param depth 	the current depth
   * @return 		the new XML-stringbuffer
   */
protected:
  StringBuffer toString(StringBuffer buf, Node parent, int depth) {
    NodeList       list;
    Node           node;
    int            i;
    int            n;
    string         indent;
    NamedNodeMap   atts;
    
    // build indent
    indent = "";
    for (i = 0; i < depth; i++)
      indent += "   ";
    
    if (parent.getNodeType() == Node.TEXT_NODE) {
      if (!parent.getNodeValue().trim().equals(""))
	buf.append(indent + parent.getNodeValue().trim() + "\n");
    }
    else 
      if (parent.getNodeType() == Node.COMMENT_NODE) {
	buf.append(indent + "<!--" + parent.getNodeValue() + "-->\n");
      }
      else {
	buf.append(indent + "<" + parent.getNodeName());
	// attributes?
	if (parent.hasAttributes()) {
	  atts = parent.getAttributes();
	  for (n = 0; n < atts.getLength(); n++) {
	    node = atts.item(n);
	    buf.append(" " + node.getNodeName() + "=\"" + node.getNodeValue() + "\"");
	  }
	}
	// children?
	if (parent.hasChildNodes()) {
	  list = parent.getChildNodes();
	  // just a text node?
	  if ( (list.getLength() == 1) && (list.item(0).getNodeType() == Node.TEXT_NODE) ) {
	    buf.append(">");
	    buf.append(list.item(0).getNodeValue().trim());
	    buf.append("</" + parent.getNodeName() + ">\n");
	  }
	  else {
	    buf.append(">\n");
	    for (n = 0; n < list.getLength(); n++) {
	      node = list.item(n);
	      toString(buf, node, depth + 1);
	    }
	    buf.append(indent + "</" + parent.getNodeName() + ">\n");
	  }
	}
	else {
	  buf.append("/>\n");
	}
      }
    
    return buf;
  }

public:
  
  /**
   * prints the current DOM document to standard out.
   */
  void print() {
    System.out.println(toString());
  }
  
  /**
   * returns the current DOM document as XML-string.
   * 
   * @return 		the document as XML-string representation
   */
  string toString() {
    string         header;
    
    header = PI + "\n\n";
    if (getDocType() != NULL)
      header += getDocType() + "\n\n";
    
    return toString(new StringBuffer(header), getDocument().getDocumentElement(), 0).toString();
  }
  
  /**
   * Returns the revision string.
   * 
   * @return		the revision
   */
  string getRevision() {
    return RevisionUtils.extract("$Revision: 1.9 $");
  }
};


/**
 * for testing only. takes the name of an XML file as first arg, reads that
 * file, prints it to stdout and if a second filename is given, writes the
 * parsed document to that again.
 * 
 * @param args	the commandline arguments
 * @throws Exception	if something goes wrong
 */
static void main(String[] args) throws Exception {
  XMLDocument		doc;
    
  if (args.length > 0) {
    doc = new XMLDocument();
      
    // read
    doc.read(args[0]);
      
    // print to stdout
    doc.print();
      
    // output?
    if (args.length > 1) {
      doc.write(args[1]);
    }
  }
}
