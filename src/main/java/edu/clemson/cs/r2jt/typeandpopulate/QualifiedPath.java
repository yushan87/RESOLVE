package edu.clemson.cs.r2jt.typeandpopulate;

import edu.clemson.cs.r2jt.data.PosSymbol;
import edu.clemson.cs.r2jt.typeandpopulate.MathSymbolTable.FacilityStrategy;
import edu.clemson.cs.r2jt.typeandpopulate.entry.FacilityEntry;
import edu.clemson.cs.r2jt.typeandpopulate.entry.SymbolTableEntry;
import edu.clemson.cs.r2jt.typeandpopulate.query.UnqualifiedNameQuery;
import edu.clemson.cs.r2jt.typeandpopulate.searchers.TableSearcher;
import edu.clemson.cs.r2jt.typeandpopulate.searchers.TableSearcher.SearchContext;
import edu.clemson.cs.r2jt.utilities.SourceErrorException;
import java.util.List;

/**
 * <p>Defines the search path when a symbol is fully qualified.  Namely:</p>
 * 
 * <ul>
 * 		<li>If the qualifier matches a facility defined in the same module as
 *          the source scope, open the corresponding module and search for the
 *          symbol there.</li>
 *      <li>Otherwise, look for a module with that name and search there.</li>
 * </ul>
 * 
 * <p>Instances of this class can be parameterized to determine how generics are
 * handled if the qualifier refers to a facility.</p>
 */
public class QualifiedPath implements ScopeSearchPath {

    private final FacilityStrategy myFacilityStrategy;
    private final PosSymbol myQualifier;

    /**
     * 
     * @param qualifier
     * @param facilityStrategy The FACILITY_IGNORE strategy is not permitted.
     */
    public QualifiedPath(PosSymbol qualifier, FacilityStrategy facilityStrategy) {

        if (facilityStrategy == FacilityStrategy.FACILITY_IGNORE) {
            throw new IllegalArgumentException("Can't use FACILITY_IGNORE");
        }

        myQualifier = qualifier;
        myFacilityStrategy = facilityStrategy;
    }

    @Override
    public <E extends SymbolTableEntry> List<E> searchFromContext(
            TableSearcher<E> searcher, Scope source, ScopeRepository repo)
            throws DuplicateSymbolException {

        List<E> result;

        try {
            //Note that this will throw the appropriate SourceErrorException if
            //the returned symbol identifies anything other than a facility
            FacilityEntry facility =
                    source.queryForOne(
                            new UnqualifiedNameQuery(myQualifier.getName()))
                            .toFacilityEntry(myQualifier.getLocation());

            Scope facilityScope =
                    facility
                            .getFacility()
                            .getSpecification()
                            .getScope(
                                    myFacilityStrategy == FacilityStrategy.FACILITY_INSTANTIATE);

            result =
                    facilityScope.getMatches(searcher, SearchContext.FACILITY);
        }
        catch (NoSuchSymbolException nsse) {
            //There's nothing by that name in local scope, so it must be the
            //name of a module
            try {
                ModuleScope moduleScope =
                        repo.getModuleScope(new ModuleIdentifier(myQualifier
                                .getName()));

                result =
                        moduleScope.getMatches(searcher, SearchContext.IMPORT);
            }
            catch (NoSuchSymbolException nsse2) {
                throw new SourceErrorException("No such facility or a module.",
                        myQualifier.getLocation());
            }
        }
        catch (DuplicateSymbolException dse) {
            //Not possible--UnqualifiedNameQuery can't throw this
            throw new RuntimeException(dse);
        }

        return result;
    }

}
