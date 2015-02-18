#include "external/ConstraintAdditionInterface.hpp"
#include "space/Remapper.hpp"
#include "external/Translator.hpp"

using namespace std;
using namespace MinisatID;

ExternalConstraintVisitor::ExternalConstraintVisitor(const SolverOption& options, const std::string& name) :
		ConstraintVisitor(name), basicoptions(options), remapper(new Remapper()), _translator(new PlainTranslator()) {
	_origremapper = remapper;
	_origtranslator = _translator;
}
ExternalConstraintVisitor::ExternalConstraintVisitor(Remapper* remapper, Translator *translator, const SolverOption& options, const std::string& name) :
		ConstraintVisitor(name), basicoptions(options), remapper(remapper), _origremapper(NULL), _translator(translator), _origtranslator(NULL) {
}

ExternalConstraintVisitor::~ExternalConstraintVisitor() {
	if(_origremapper!=NULL){
		delete (_origremapper);
	}
	if(_origtranslator!=NULL){
		delete (_origtranslator);
	}
}
void ExternalConstraintVisitor::notifyFinishParsing() {
	getTranslator()->finish();
}

std::string ExternalConstraintVisitor::toString(VarID id) const {
	std::stringstream ss;
	if (getRemapper()->wasInput(id.id)) {
		auto origid = VarID{getRemapper()->getOrigID(id.id)};
		if (getTranslator()->hasTranslation(origid)) {
			ss << getTranslator()->toString(origid);
			return ss.str();
		}
	}
	ss << "internvar_" << id.id;
	return ss.str();
}
void ExternalConstraintVisitor::setString(const Atom& atom, const std::string& name){
	atom2string[atom]=name;
}
bool ExternalConstraintVisitor::isTseitin(const Atom& atom) const {
	if(getRemapper()->wasInput(atom)){
		return getTranslator()->isTseitin(getRemapper()->getLiteral(mkPosLit(atom)).getAtom());
	}else{
		return true;
	}
}
std::string ExternalConstraintVisitor::toString(const Lit& l) const {
	auto overriddenit = atom2string.find(l.getAtom());
	if(overriddenit!=atom2string.cend()){
		return sign(l)?"~"+overriddenit->second:overriddenit->second;
	}
	std::stringstream ss;
	if (getRemapper()->wasInput(l)) {
		auto lit = getRemapper()->getLiteral(l);
		if (getTranslator()->hasTranslation(lit)) {
			ss << getTranslator()->toString(lit);
			return ss.str();
		}
	}
	ss << (sign(l) ? "~" : "") << "i_" << var(l) + 1; // NOTE: do not call <<l, this will cause an infinite loop (as that calls this method!)
	return ss.str();
}
std::string ExternalConstraintVisitor::toString(const litlist& literals) const {
	std::stringstream ss;
	bool begin = true;
	for (auto i = literals.cbegin(); i < literals.cend(); ++i) {
		if (not begin) {
			ss << " | ";
		}
		begin = false;
		ss << toString(*i);
	}
	return ss.str();
}
