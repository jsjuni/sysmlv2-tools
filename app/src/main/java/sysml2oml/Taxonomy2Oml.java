package sysml2oml;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.xpath.XPath;
import javax.xml.xpath.XPathConstants;
import javax.xml.xpath.XPathExpression;
import javax.xml.xpath.XPathExpressionException;
import javax.xml.xpath.XPathFactory;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.emf.ecore.resource.impl.ResourceSetImpl;
import org.eclipse.emf.ecore.util.ECrossReferenceAdapter;
import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedAcyclicGraph;
import org.jgrapht.graph.SimpleDirectedGraph;
import org.slf4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.w3c.dom.Element;

import com.google.common.base.Joiner;
import com.google.common.collect.Sets;
import com.opencsv.CSVReaderHeaderAware;
import com.opencsv.CSVWriter;
import com.opencsv.exceptions.CsvValidationException;

import io.github.novacrypto.base58.Base58;
import io.opencaesar.oml.Concept;
import io.opencaesar.oml.Import;
import io.opencaesar.oml.ImportKind;
import io.opencaesar.oml.Literal;
import io.opencaesar.oml.OmlFactory;
import io.opencaesar.oml.Vocabulary;
import io.opencaesar.oml.VocabularyBundle;
import io.opencaesar.oml.dsl.OmlStandaloneSetup;
import io.opencaesar.oml.resource.OmlJsonResourceFactory;
import io.opencaesar.oml.resource.OmlXMIResourceFactory;
import io.opencaesar.oml.util.OmlBuilder;
import io.opencaesar.oml.util.OmlConstants;
import io.opencaesar.oml.util.OmlRead;

public class Taxonomy2Oml {
	
	protected final static String catalogStem = "catalog.xml";
	protected final Logger logger;
	protected final List<String> inputPaths;
	protected final String coreVocabsPath;
	protected final String bundleStem;
	protected final String outputPath;
	protected final Set<String> metaclasses;
	protected final String mapFile;
	protected final String catalogPath;
	protected final String edgelistPath;
	protected final String pairsStem;
	
	protected final Map<String, URI> iriByDeclName = new HashMap<>();
	protected final Map<URI, String> outputFn = new HashMap<>();
	protected final Map<URI, Node> packages = new HashMap<>();
	protected final Map<URI, Vocabulary> vocabularies = new HashMap<>();
	protected final Map<String, Concept> concepts = new HashMap<>();
	protected final Map<String, String> catalogMap = new HashMap<>();
	
	protected final Map<String, Map<String, String>> sbcById = new HashMap<>();
	protected final Map<String, String> idByDn = new HashMap<>();
	protected final Map<String, String> idByName = new HashMap<>();
	protected final Map<Concept, String> dnByConcept = new HashMap<>();
	
	protected final DirectedAcyclicGraph<String, DefaultEdge> sbcSuper = new DirectedAcyclicGraph<String, DefaultEdge>(DefaultEdge.class);
	protected final SimpleDirectedGraph<String, DefaultEdge> djClass = new SimpleDirectedGraph<String, DefaultEdge>(DefaultEdge.class);
	protected final SimpleDirectedGraph<String, DefaultEdge> sbcImplicit = new SimpleDirectedGraph<String, DefaultEdge>(DefaultEdge.class);
	
	/**
	 * Constructs a new instance
	 * 
	 */
	public Taxonomy2Oml(Logger logger, List<String> inputPaths, String coreVocabsPath, String bundleStem, String outputPath, Set<String> metaclasses, String mapFile,
			String catalogPath, String edgelistPath, String pairsStem) {
		this.logger = logger;
		this.inputPaths = inputPaths;
		this.coreVocabsPath = coreVocabsPath;
		this.bundleStem = bundleStem;
		this.outputPath = outputPath;
		this.metaclasses = metaclasses;
		this.mapFile = mapFile;
		this.catalogPath = catalogPath;
		this.edgelistPath = edgelistPath;
		this.pairsStem = pairsStem;
	}
	
	public void run() throws CsvValidationException, FileNotFoundException, IOException, ParserConfigurationException, XPathExpressionException {
		
		/*
		 * Compile xpath expressions for later use.
		 */
		
		XPath xPath = XPathFactory.newInstance().newXPath();
		XPathExpression topPackageXPath = xPath.compile("Namespace/ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement[@type='sysml:LibraryPackage']");
		XPathExpression ownedRelationshipXPath = xPath.compile("ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement");
		XPathExpression subclassificationXPath = xPath.compile(
				"ownedRelationship[@type='sysml:Subclassification']/superclassifier[@href]/@href" +
						" | ownedRelationship[@type='sysml:Subclassification']/@superclassifier"
				);
		XPathExpression disjoiningXPath = xPath.compile(
				"ownedRelationship[@type='sysml:Disjoining']/disjoiningType[@href]/@href" +
						" | ownedRelationship[@type='sysml:Disjoining']/@disjoiningType"
				);

		/*
		 * Load implicit supertypes map.
		 */
		
		final CSVReaderHeaderAware csvReader = new CSVReaderHeaderAware(new FileReader(mapFile));
		final Map<String, String> stMap = new HashMap<>();
		Map <String, String> tm = new HashMap<>();
		while ((tm = csvReader.readMap()) != null) {
			final String key = "sysml:" + tm.get("Abstract syntax");
			final String val = tm.get("Implicit subclassification to superclassifier").replaceAll("::", ":");
			stMap.put(key, val);
		}
		csvReader.close();
		
		/*
		 * Open optional output edgelist.
		 */
		final CSVWriter edgelistWriter = (edgelistPath != null) ? 
			new CSVWriter(new FileWriter(edgelistPath)) : null;
		
		/*
		 * Find all XMI files in path and parse.
		 */
		
		final Pattern pattern = Pattern.compile(".*\\.(kermlx|sysmlx)");
		final DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();

		logger.info("load documents");
		inputPaths.forEach(pathString -> {
			try {
				final Path inputPath = Paths.get(pathString);
				Files.walk(inputPath)
				.filter(Files::isRegularFile)
                .filter(p -> pattern.matcher(p.getFileName().toString()).matches())
				.forEach(filePath -> {
					
					logger.info("document file path " + filePath.toString());
					String dirName = filePath.getParent().toString();

					/*
					 * Parse XMI document.
					 */
					
					Document doc = null;
					try {
						doc = builder.parse(new FileInputStream(filePath.toString()));
						doc.getDocumentElement().normalize();
					} catch (SAXException | IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
					try {
						
						/*
						 * Find Library Package.
						 */
						
						final NodeList topNodes = (NodeList) topPackageXPath.evaluate(doc, XPathConstants.NODESET);
						if (topNodes.getLength() == 0) {
							logger.error("no library package found for " + filePath);
							throw(new RuntimeException());
						}
						final Node topPackage = topNodes.item(0);
						final NamedNodeMap topPackageAttributes = topPackage.getAttributes();
						
						/*
						 * Construct vocabulary IRI and cache it.
						 */
						
						final String declaredName = topPackageAttributes.getNamedItem("declaredName").getNodeValue();
						final URI iri = makeIri(dirName, declaredName);
						iriByDeclName.put(declaredName, iri);
						logger.info("  document iri " + iri);
						
						/*
						 * Construct output filename and cache it.
						 */
						
						final String fn = makeOutputFn(outputPath, inputPath, filePath);
						logger.info("  output file path " + fn);
						outputFn.put(iri, fn);
						
						/*
						 * Cache document by IRI.
						 */
						
						packages.put(iri, topPackage);
						
						/*
						 * Create catalog entry for this document.
						 */
						
						catalogMap.put(makeCatalogStartString(inputPath, filePath), makeCatalogRewritePrefix(inputPath, filePath));
						
					} catch (XPathExpressionException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				});
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		});
		logger.info(String.format("loaded %d documents", packages.size()));
		
		/*
		 * Add catalog rule for bundle (optional).
		 */
		
		if (bundleStem != null) {
		}
		
		/*
		 * Add default catalog rule and write catalog.
		 */
		
		catalogMap.put("http://",  "src/oml");
		if (catalogPath != null) createOutputCatalog(catalogPath, catalogMap);
		
		OmlStandaloneSetup.doSetup();
		OmlXMIResourceFactory.register();
		OmlJsonResourceFactory.register();
		
		final ResourceSet outputResourceSet = new ResourceSetImpl();
		outputResourceSet.getLoadOptions().put(OmlConstants.RESOLVE_IRI_USING_RESOURCE_SET, true);
		outputResourceSet.eAdapters().add(new ECrossReferenceAdapter());
		
		logger.info("create oml factory");
		OmlFactory oml = OmlFactory.eINSTANCE;
		
		logger.info("create builder");
		OmlBuilder omlBuilder = new OmlBuilder(outputResourceSet);
		
		logger.info("start builder");
		omlBuilder.start();
		
		/*
		 * Load core vocabularies.
		 */
		
		final Pattern omlPattern = Pattern.compile(".*\\.oml");
		try {
			final Path vocabsPath = Paths.get(coreVocabsPath);
			Files.walk(vocabsPath)
			.filter(Files::isRegularFile)
            .filter(p -> omlPattern.matcher(p.getFileName().toString()).matches())
			.forEach(filePath -> {
				logger.info("core vocabulary file path " + filePath.toString());
				final URI ontologyUri = URI.createFileURI(filePath.toAbsolutePath().toString());
				OmlRead.getOntology(outputResourceSet.getResource(ontologyUri, true));
			});
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

				
		/*
		 * Process packages.
		 */
		
		logger.info("process packages");
		packages.forEach((iri, pkg) -> {
			final Node packageNameNode = pkg.getAttributes().getNamedItem("declaredName");
			final String packageName = packageNameNode.getNodeValue();
			
			/*
			 * Find elements that will become concepts.
			 */
			
			NodeList sbcs = null;
			try {
				sbcs = (NodeList) ownedRelationshipXPath.evaluate(pkg, XPathConstants.NODESET);
			} catch (XPathExpressionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			for (int i = 0; i < sbcs.getLength(); i++) {
				final Node sbc = sbcs.item(i);
				final NamedNodeMap sbcAttributes = sbc.getAttributes();
				
				final Node dnNode = sbcAttributes.getNamedItem("declaredName");
				if (dnNode == null) continue;
				String dn = dnNode.getNodeValue();
				
				final Node tpNode = sbcAttributes.getNamedItem("xsi:type");
				final String tp = tpNode.getNodeValue();
				if (!metaclasses.contains(tp)) continue;
				
				final Node idNode = sbcAttributes.getNamedItem("elementId");
				final String id = idNode.getNodeValue();
				final String qName = packageName + ":" + dn;
				final Map<String, String> m = new HashMap<>();
				m.put("name", dn);
				m.put("iri", iri.toString());
				sbcById.put(id, m);
				idByDn.put(dn, id);
				idByName.put(qName, id);
				sbcSuper.addVertex(id);
				djClass.addVertex(id);
				logger.info("candidate " + dn + " type " + tp + " vocab-iri " + iri + " id " + id);

				/*
				 * Find  superclass relations.
				 */
				
				NodeList supc = null;
				try {
					supc = (NodeList) subclassificationXPath.evaluate(sbc, XPathConstants.NODESET);
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < supc.getLength(); j++) {
					final String supId = supc.item(j).getTextContent().replaceAll("\\A.*#", "");
					sbcSuper.addVertex(supId);
					sbcSuper.addEdge(id, supId);
					logger.info("specialization " + id + " :> " + supId);
				}
				
				/*
				 * Add implicit superclass relations.
				 */

				if (sbcSuper.outDegreeOf(id) == 0) {
					logger.info("tp " + tp);
					final String spcType = stMap.get(tp);
					if (spcType != null) {
			            logger.info("implicit edge " + qName + " :> " + spcType);
			            sbcImplicit.addVertex(qName);
			            sbcImplicit.addVertex(spcType);
						sbcImplicit.addEdge(qName, spcType);
					}
				}
				
				/*
				 * Find  disjoining relations.
				 */
				
				NodeList djc = null;
				try {
					djc = (NodeList) disjoiningXPath.evaluate(sbc, XPathConstants.NODESET);
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < djc.getLength(); j++) {
					final String djId = djc.item(j).getTextContent().replaceAll("\\A.*#", "");
					djClass.addVertex(djId);
					djClass.addEdge(id, djId);
					logger.info("disjoining " + id + " " + djId);
				}

			}
			
		});
		
		/*
		 * Create vocabularies.
		 */
		
		logger.info("create vocabularies");		
		final Set<URI> outputResourceUris = new HashSet<>();
		packages.forEach((iri, pkg) -> {
			final URI uri = URI.createFileURI(outputFn.get(iri));
			outputResourceUris.add(uri);
			final String namespace = iri.toString() + "#";
			final Vocabulary v = omlBuilder.createVocabulary(uri, namespace, Paths.get(iri.toString()).getFileName().toString().toLowerCase());
			vocabularies.put(iri, v);
			
			final Import rdfsImport = oml.createImport();
			rdfsImport.setKind(ImportKind.EXTENSION);
			rdfsImport.setNamespace("http://www.w3.org/2000/01/rdf-schema#");
			rdfsImport.setPrefix("rdfs");
			rdfsImport.setOwningOntology(vocabularies.get(iri));
		});
		
		/*
		 * Add concept definitions.
		 */
	
		sbcById.forEach((id, c) -> {
			final Vocabulary v = vocabularies.get(URI.createURI(c.get("iri")));
			final String cName = cleanIdentifier(c.get("name"));
			final Literal cLiteral = omlBuilder.createLiteral(c.get("name"));
			final Concept concept = omlBuilder.addConcept(v, cName);
			concepts.put(id, concept);
			logger.info("concept " + cName + " label " + cLiteral.getLexicalValue() + " id " + id);
			omlBuilder.addAnnotation(v, concept.getIri(), "http://www.w3.org/2000/01/rdf-schema#label", cLiteral);
			dnByConcept.put(concept, c.get("name"));
		});
			
		/*
		 * Merge implicit concept specialization axioms with explicit.
		 */

		sbcImplicit.edgeSet().forEach(e -> {
			final String es = idByName.get(sbcImplicit.getEdgeSource(e));
			final String et = idByName.get(sbcImplicit.getEdgeTarget(e));
			sbcSuper.addEdge(es, et);
		});
			  			
		/*
		 * Add explicit concept specialization axioms and extension axioms.
		 */

		Map<Vocabulary, Set<Vocabulary>> imported = new HashMap<>();

		sbcSuper.edgeSet().forEach(e -> {
			final String es = sbcSuper.getEdgeSource(e);
			final String et = sbcSuper.getEdgeTarget(e);
			addSpecialization(concepts, es, et, omlBuilder, dnByConcept, logger, imported, false, edgelistWriter);
		});
			  			
		if (edgelistWriter != null) edgelistWriter.close();

		/*
		 * Add annotations for disjointness.
		 */

		djClass.edgeSet().forEach(e -> {
			final String es = djClass.getEdgeSource(e);
			final String et = djClass.getEdgeTarget(e);
			final Concept dj1 = concepts.get(es);
			final Concept dj2 = concepts.get(et);
			if (dj2 != null) {
				final Vocabulary dj1Vocab = dj1.getOwningVocabulary();
				final String dj1Prefix = dj1Vocab.getPrefix();
				final Vocabulary dj2Vocab = dj2.getOwningVocabulary();
				final String dj2Prefix = dj2Vocab.getPrefix();
				
				logger.info("concept " + dj1Prefix + ":" + dj1.getName() + " disjoint from " + dj2Prefix + ":" + dj2.getName());

				final String dj2Name = (dj1Prefix == dj2Prefix ? "" : dj2Prefix + ":") + dnByConcept.get(dj2);
				omlBuilder.addAnnotation(dj1Vocab, dj1.getIri(), "http://www.w3.org/2000/01/rdf-schema#comment",
						omlBuilder.createLiteral("disjoint from " + dj2Name));				
			}
		});
		
		/*
		 * Create optional vocabulary bundle.
		 */
		
		if (bundleStem != null) {
			final String core = outputPath + "/" + "omg.org/SysML-v2" + "/" + bundleStem;
			final String bundlePath = core + ".omlxmi";
			final URI bundleUri = URI.createFileURI(bundlePath);
			final String bundleNamespace = "http:/" + ("/" + core.replaceAll(outputPath, "")).replaceAll("\\/+", "/") + "#";
			final VocabularyBundle vocabBundle = omlBuilder.createVocabularyBundle(bundleUri, bundleNamespace, bundleStem);
			outputResourceUris.add(bundleUri);
			
			vocabularies.forEach((iri, vocab) -> {
				final Import vocabImport = oml.createImport();
				vocabImport.setKind(ImportKind.INCLUSION);
				vocabImport.setNamespace(vocab.getNamespace());
				vocabImport.setOwningOntology(vocabBundle);
			});
		
			/*
			 * Crate optional vocabulary of all pairwise intersections.
			 */
			
			if (pairsStem != null) {
				final String pairsCore = outputPath + "/" + "omg.org/SysML-v2" + "/" + pairsStem;
				final String pairsPath = pairsCore + ".omlxmi";
				final URI pairsUri = URI.createFileURI(pairsPath);
				final String pairsNamespace = "http:/" + ("/" + pairsCore.replaceAll(outputPath, "")).replaceAll("\\/+", "/") + "#";
				final Vocabulary pairsVocab = omlBuilder.createVocabulary(pairsUri, pairsNamespace, pairsStem);
				outputResourceUris.add(pairsUri);

				final Import rdfsImport = oml.createImport();
				rdfsImport.setKind(ImportKind.EXTENSION);
				rdfsImport.setNamespace("http://www.w3.org/2000/01/rdf-schema#");
				rdfsImport.setPrefix("rdfs");
				rdfsImport.setOwningOntology(pairsVocab);

				vocabularies.forEach((iri, vocab) -> {
					final Import vocabImport = oml.createImport();
					vocabImport.setKind(ImportKind.EXTENSION);
					vocabImport.setNamespace(vocab.getNamespace());
					vocabImport.setPrefix(vocab.getPrefix());
					vocabImport.setOwningOntology(pairsVocab);
					
				});
				
				final Set<String> vs = sbcSuper.vertexSet();
				final Set<DefaultEdge> es = sbcSuper.edgeSet();
				final Set<Set<String>> cn = Sets.combinations(vs, 2);

				logger.info(vs.size() + " pairs vertices");
				logger.info(es.size() + " pairs edges");
				logger.info(cn.size() + " vertex combinations");
				
				final Map<String, Set<String>> anc = new HashMap<>();
				final Map<Set<String>, Boolean> dj = new HashMap<>();
				
				vs.forEach(v -> {
					final Set<String> sc = sbcSuper.getAncestors(v);		// self + subclasses
					sc.add(v);
					anc.put(v, sc);
				});
					
				cn.forEach(pair -> {
					final Object[] pairArray = pair.toArray();
					dj.put(pair, Sets.intersection(anc.get(pairArray[0]), anc.get(pairArray[1])).isEmpty());
				});
				logger.info(dj.values().stream().filter(v -> v).toList().size() + " unsats");
				
				cn.stream().limit(100000).collect(Collectors.toSet()).forEach(pair -> {
					final String pairSubclassName = Joiner.on("_")
							.join(pair.stream()
									.map(iri -> concepts.get(iri))
									.flatMap(c -> Stream.of(c.getOwningVocabulary().getPrefix(), c.getName()))
									.toArray());
					final Concept pairSubclass = omlBuilder.addConcept(pairsVocab, pairSubclassName);
					pair.forEach(supC -> {
						final Concept sc = concepts.get(supC);
						omlBuilder.addSpecializationAxiom(pairsVocab, pairSubclass.getIri(), sc.getIri());
						omlBuilder.addAnnotation(pairsVocab, pairSubclass.getIri(), "http://www.w3.org/2000/01/rdf-schema#comment",
								omlBuilder.createLiteral("specializes " + sc.getOwningVocabulary().getPrefix() + ":" + dnByConcept.get(sc)));
					});
					
					omlBuilder.addAnnotation(pairsVocab, pairSubclass.getIri(), "http://www.w3.org/2000/01/rdf-schema#comment",
							omlBuilder.createLiteral(dj.get(pair) ? "unsatisfiable" : "satisfiable"));	
				});
			}
			
		}

		/*
		 * Write output OML files.
		 */
		
		logger.info("finish builder");
		omlBuilder.finish();
		
		logger.info("save resources");
		outputResourceUris.forEach(outputResourceUri -> {
			logger.info("save " + outputResourceUri.toString());
			final Resource outputResource = outputResourceSet.getResource(outputResourceUri, false);
			try {
				outputResource.save(Collections.EMPTY_MAP);
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		});
		
		logger.info("done");
	}
	
	private static Path trail(Path fp, Path sp) {
		return Paths.get(fp.toString().replace(sp.toString(), ""));
	}
	
	private static URI makeIri(String path, String stem) {
		final String p = path.replaceAll("\\A.*/sysml.library.xmi", "http://omg.org/SysML-v2");
		return URI.createURI((p + "/" + stem).replaceAll("\\s+", "-"));
	}
	
	private static String makeOutputFn(String op, Path sp, Path fp) {
		final Path trail = trail(fp, sp);
		final String path = op + "/omg.org/SysML-v2/" + trail.getParent().toString();
		final String stem = trail.getFileName().toString().replaceAll("\\..*$", ".omlxmi");
		return (path + "/" + stem).replaceAll("\\/+", "/").replaceAll("\\s+", "-");
	}
	
	private static String makeCatalogStartString(Path sp, Path fp) {
		final Path trail = trail(fp, sp);
		return "http://omg.org/SysML-v2" + trail.getParent().toString().replaceAll("\\s+", "-").replaceAll("\\/+", "/");
	}

	private static String makeCatalogRewritePrefix(Path sp, Path fp) {
		final Path trail = trail(fp, sp);
		return "omg.org/SysML-v2" + trail.getParent().toString().replaceAll("\\s+", "-").replaceAll("\\/+", "/");
	}
	
	private static void createOutputCatalog(String path, Map<String, String> map) {
		(new File(path)).mkdirs();
		
		final String fn = path + "/" + catalogStem;
		FileWriter writer = null;
		try {
			writer = new FileWriter(fn);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		final DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		try {
			builder = factory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		final Document doc = builder.newDocument();
		final DOMSource source = new DOMSource(doc);
		final Element cat = (Element) doc.createElement("catalog");
		cat.setAttribute("xmlns", "urn:oasis:names:tc:entity:xmlns:xml:catalog");
		cat.setAttribute("prefer", "public");
		doc.appendChild(cat);
		
		map.forEach((ss, rp) -> {
			final Element srw = doc.createElement("rewriteURI");
			srw.setAttribute("uriStartString", ss);
			srw.setAttribute("rewritePrefix", rp);
			cat.appendChild(srw);
		});
		
		final TransformerFactory transformerFactory = TransformerFactory.newInstance();
		Transformer transformer = null;
		try {
			transformer = transformerFactory.newTransformer();
		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		transformer.setOutputProperty(OutputKeys.INDENT, "yes");
		transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
		final StreamResult result = new StreamResult(writer);
		try {
			transformer.transform(source, result);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		try {
			writer.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private static String cleanIdentifier(String id) {
		return "Concept_" + Base58.base58Encode(id.getBytes());
	}
	
	private static void addSpecialization(Map<String, Concept> concepts, String es, String et, OmlBuilder omlBuilder,
			Map<Concept, String> dnByConcept, Logger logger, Map<Vocabulary, Set<Vocabulary>> imported, boolean implicit,
			CSVWriter edgelistWriter) {
		final Concept subC = concepts.get(es);
		final Concept supC = concepts.get(et);
		if (supC != null) {
			final Vocabulary subVocab = subC.getOwningVocabulary();
			final String subPrefix = subVocab.getPrefix();
			final Vocabulary supVocab = supC.getOwningVocabulary();
			final String supPrefix = supVocab.getPrefix();
			final String subQName = subPrefix + ":" + dnByConcept.get(subC);
			final String supQName = supPrefix + ":" + dnByConcept.get(supC);

			omlBuilder.addSpecializationAxiom(subVocab, subC.getIri(), supC.getIri());

			final String superName = (subPrefix == supPrefix ? "" : supPrefix + ":") + dnByConcept.get(supC);
			omlBuilder.addAnnotation(subVocab, subC.getIri(), "http://www.w3.org/2000/01/rdf-schema#comment",
					omlBuilder.createLiteral("specializes " + (implicit ? "(implicit) " : "") + superName));

			if (edgelistWriter != null) {
				final String[] row = { supQName, subQName };
				edgelistWriter.writeNext(row);
			}
			
			logger.info("concept " + subQName + " :> " + supQName);

			if (!imported.containsKey(subVocab)) imported.put(subVocab, new HashSet<Vocabulary>());
			if (subVocab != supVocab && !imported.get(subVocab).contains(supVocab)) {
				omlBuilder.addImport(subVocab, ImportKind.EXTENSION, supVocab.getIri() + "#", supPrefix);
				imported.get(subVocab).add(supVocab);
			}
		}
	}
}
