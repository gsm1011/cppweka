AUTOMAKE_OPTIONS = foreign
SUBDIRS = #logging autom4te.cache converters matrix \
neighboursearch neighboursearch/kdtrees \
neighboursearch/balltrees neighboursearch/covertrees \
tokenizers pmml stemmers mathematicalexpression xml

# what flags you want to pass to the C compiler & linker
CFLAGS = --pedantic -Wall -std=c99 -O2
LDFLAGS =

# this lists the binaries to produce, the (non-PHONY, binary) targets in
# the previous manual Makefile
bin_PROGRAMS = cppweka
cppweka_SOURCES = AbstractStringDistanceFunction.cpp ContingencyTables.cpp Jython.cpp Queue.cpp Tag.cpp \
AdditionalMeasureProducer.cpp Copyable.cpp JythonObject.cpp Randomizable.cpp \
TechnicalInformation.cpp AlgVector.cpp Copyright.cpp JythonSerializableObject.cpp RandomVariates.cpp \
TechnicalInformationHandler.cpp \
AllJavadoc.cpp Debug.cpp ListOptions.cpp Range.cpp TechnicalInformationHandlerJavadoc.cpp\
Attribute.cpp ManhattanDistance.cpp RelationalLocator.cpp Tee.cpp \
AttributeExpression.cpp Drawable.cpp Matchable.cpp RevisionHandler.cpp TestInstances.cpp \
AttributeLocator.cpp dummy.cpp MathematicalExpression.cpp RevisionUtils.cpp Trie.cpp \
AttributeStats.cpp EditDistance.cpp Matrix.cpp SelectedTag.cpp UnassignedClassException.cpp \
BinarySparseInstance.cpp Environment.cpp Memory.cpp SerializationHelper.cpp\
UnassignedDatasetException.cpp \
Capabilities.cpp EnvironmentHandler.cpp MultiInstanceCapabilitiesHandler.cpp SerializedObject.cpp Undoable.cpp\
CapabilitiesHandler.cpp EuclideanDistance.cpp NormalizableDistance.cpp SingleIndex.cpp UnsupportedAttributeTypeException.cpp\
ChebyshevDistance.cpp FastVector.cpp NoSupportForMissingValuesException.cpp SparseInstance.cpp UnsupportedClassTypeException.cpp\
Check.cpp FindWithCapabilities.cpp Optimization.cpp SpecialFunctions.cpp Utils.cpp\
CheckGOE.cpp GlobalInfoJavadoc.cpp Option.cpp Statistics.cpp Version.cpp\
CheckOptionHandler.cpp InstanceComparator.cpp OptionHandler.cpp Stopwords.cpp WeightedInstancesHandler.cpp\
CheckScheme.cpp Instance.cpp OptionHandlerJavadoc.cpp StringLocator.cpp WekaException.cpp\
ClassDiscovery.cpp Instances.cpp PropertyPath.cpp Summarizable.cpp \
ClassloaderUtil.cpp Javadoc.cpp ProtectedProperties.cpp 
