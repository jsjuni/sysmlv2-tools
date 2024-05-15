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
import org.jgrapht.graph.SimpleDirectedGraph;
import org.slf4j.Logger;
import org.w3c.dom.Document;
import org.w3c.dom.NamedNodeMap;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import org.w3c.dom.Element;

import com.opencsv.CSVReaderHeaderAware;
import com.opencsv.exceptions.CsvValidationException;

import io.github.novacrypto.base58.Base58;
import io.opencaesar.oml.Concept;
import io.opencaesar.oml.Import;
import io.opencaesar.oml.ImportKind;
import io.opencaesar.oml.Literal;
import io.opencaesar.oml.OmlFactory;
import io.opencaesar.oml.Vocabulary;
import io.opencaesar.oml.dsl.OmlStandaloneSetup;
import io.opencaesar.oml.util.OmlBuilder;
import io.opencaesar.oml.util.OmlConstants;
import io.opencaesar.oml.util.OmlRead;

public class Taxonomy2Oml {
	
	protected final static String catalogStem = "catalog.xml";
	protected final Logger logger;
	protected final List<String> inputPaths;
	protected final String coreVocabsPath;
	protected final String bundle;
	protected final String outputPath;
	protected final Set<String> metaclasses;
	protected final String mapFile;
	protected final String catalogPath;
	
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
	
	protected final SimpleDirectedGraph<String, DefaultEdge> sbcSuper = new SimpleDirectedGraph<String, DefaultEdge>(DefaultEdge.class);
	protected final SimpleDirectedGraph<String, DefaultEdge> djClass = new SimpleDirectedGraph<String, DefaultEdge>(DefaultEdge.class);
	
	/**
	 * Constructs a new instance
	 * 
	 */
	public Taxonomy2Oml(Logger logger, List<String> inputPaths, String coreVocabsPath, String bundle, String outputPath, Set<String> metaclasses, String mapFile, String catalogPath) {
		this.logger = logger;
		this.inputPaths = inputPaths;
		this.coreVocabsPath = coreVocabsPath;
		this.bundle = bundle;
		this.outputPath = outputPath;
		this.metaclasses = metaclasses;
		this.mapFile = mapFile;
		this.catalogPath = catalogPath;
	}
	
	public void run() throws CsvValidationException, FileNotFoundException, IOException, ParserConfigurationException, XPathExpressionException {
		
		/*
		 * Load implicit supertypes map.
		 */
		
		@SuppressWarnings("resource")
		Map<String, String> values = new CSVReaderHeaderAware(new FileReader(mapFile)).readMap();
		Map<String, String> st_map = new HashMap<>();
		values.forEach((v1, v2) -> {
			st_map.put(v1, v2);
		});
		
		/*
		 * Find all XMI files in path and parse.
		 */
		
		Pattern pattern = Pattern.compile(".*\\.(kermlx|sysmlx)");
		DocumentBuilder builder = DocumentBuilderFactory.newInstance().newDocumentBuilder();
		XPath xPath = XPathFactory.newInstance().newXPath();
		String topPackageString = "Namespace/ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement[@type='sysml:LibraryPackage']";
		XPathExpression topPackageXPath = xPath.compile(topPackageString);

		logger.info("load documents");
		inputPaths.forEach(pathString -> {
			try {
				Path inputPath = Paths.get(pathString);
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
						
						NodeList topNodes = (NodeList) topPackageXPath.evaluate(doc, XPathConstants.NODESET);
						if (topNodes.getLength() == 0) {
							logger.error("no library package found for " + filePath);
							throw(new RuntimeException());
						}
						Node topPackage = topNodes.item(0);
						NamedNodeMap topPackageAttributes = topPackage.getAttributes();
						
						/*
						 * Construct vocabulary IRI and cache it.
						 */
						
						String declaredName = topPackageAttributes.getNamedItem("declaredName").getNodeValue();
						URI iri = makeIri(dirName, declaredName);
						iriByDeclName.put(declaredName, iri);
						logger.info("  document iri " + iri);
						
						/*
						 * Construct output filename and cache it.
						 */
						
						String fn = makeOutputFn(outputPath, inputPath, filePath);
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
		 * Add default catalog rule and write catalog.
		 */
		
		catalogMap.put("http://",  "src/oml");
		if (catalogPath != null) createOutputCatalog(catalogPath, catalogMap);
		
		OmlStandaloneSetup.doSetup();
		
		ResourceSet outputResourceSet = new ResourceSetImpl();
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
		
		Pattern omlPattern = Pattern.compile(".*\\.oml");
		try {
			Path vocabsPath = Paths.get(coreVocabsPath);
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
		 * Create vocabularies.
		 */
		
		logger.info("create vocabularies");		
		Set<URI> outputResourceUris = new HashSet<>();
		packages.forEach((iri, pkg) -> {
			Node packageNameNode = pkg.getAttributes().getNamedItem("declaredName");
			String packageName = packageNameNode.getNodeValue();
			
			/*
			 * Find elements that will become concepts.
			 */
			
			XPathExpression ownedRelationshipXPath = null;
			try {
				ownedRelationshipXPath = xPath.compile("ownedRelationship[@type='sysml:OwningMembership']/ownedRelatedElement");
			} catch (XPathExpressionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			NodeList sbcs = null;
			try {
				sbcs = (NodeList) ownedRelationshipXPath.evaluate(pkg, XPathConstants.NODESET);
			} catch (XPathExpressionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			for (int i = 0; i < sbcs.getLength(); i++) {
				Node sbc = sbcs.item(i);
				NamedNodeMap sbcAttributes = sbc.getAttributes();
				
				Node dnNode = sbcAttributes.getNamedItem("declaredName");
				if (dnNode == null) continue;
				String dn = dnNode.getNodeValue();
				
				Node tpNode = sbcAttributes.getNamedItem("xsi:type");
				String tp = tpNode.getNodeValue();
				if (!metaclasses.contains(tp)) continue;
				
				Node idNode = sbcAttributes.getNamedItem("elementId");
				String id = idNode.getNodeValue();
				Map<String, String> m = new HashMap<>();
				m.put("name", dn);
				m.put("iri", iri.toString());
				sbcById.put(id, m);
				idByDn.put(dn, id);
				idByName.put(packageName, id);
				sbcSuper.addVertex(id);
				djClass.addVertex(id);
				logger.info("candidate " + dn + " type " + tp + " vocab-iri " + iri + " id " + id);

				/*
				 * Find  superclass relations.
				 */
				
				XPathExpression subclassification1XPath = null;
				try {
					subclassification1XPath = xPath.compile("ownedRelationship[@type='sysml:Subclassification']/superclassifier[@href]/@href");
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				NodeList supc1 = null;
				try {
					supc1 = (NodeList) subclassification1XPath.evaluate(sbc, XPathConstants.NODESET);
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < supc1.getLength(); j++) {
					String supId = supc1.item(j).getTextContent().replaceAll("\\A.*#", "");
					sbcSuper.addVertex(supId);
					sbcSuper.addEdge(id, supId);
					logger.info("specialization " + id + " :> " + supId);
				}
				XPathExpression subclassification2XPath = null;
				try {
					subclassification2XPath = xPath.compile("ownedRelationship[@type='sysml:Subclassification' and @superclassifier]/@superclassifier");
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				NodeList supc2 = null;
				try {
					supc2 = (NodeList) subclassification2XPath.evaluate(sbc, XPathConstants.NODESET);
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < supc2.getLength(); j++) {
					String supId = supc2.item(j).getTextContent().replaceAll("\\A.*#", "");
					sbcSuper.addVertex(supId);
					sbcSuper.addEdge(id, supId);
					logger.info("specialization " + id + " :> " + supId);
				}

				/*
				 * Find  disjoining relations.
				 */
				
				XPathExpression disjoining1XPath = null;
				try {
					disjoining1XPath = xPath.compile("ownedRelationship[@type='sysml:Disjoining']/disjoiningType[@href]/@href");
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				NodeList djc1 = null;
				try {
					djc1 = (NodeList) disjoining1XPath.evaluate(sbc, XPathConstants.NODESET);
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < djc1.getLength(); j++) {
					String djId = djc1.item(j).getTextContent().replaceAll("\\A.*#", "");
					djClass.addVertex(djId);
					djClass.addEdge(id, djId);
					logger.info("disjoining " + id + " " + djId);
				}
				XPathExpression disjoining2XPath = null;
				try {
					disjoining2XPath = xPath.compile("ownedRelationship[@type='sysml:Disjoining' and @disjoiningType]/@disjoiningType");
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				NodeList djc2 = null;
				try {
					djc2 = (NodeList) disjoining2XPath.evaluate(sbc, XPathConstants.NODESET);
				} catch (XPathExpressionException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				for (int j = 0; j < djc2.getLength(); j++) {
					String djId = djc2.item(j).getTextContent().replaceAll("\\A.*#", "");
					djClass.addVertex(djId);
					djClass.addEdge(id, djId);
					logger.info("disjoining " + id + " " + djId);
				}

			}
			
		});
		
		packages.forEach((iri, pkg) -> {
			URI uri = URI.createFileURI(outputFn.get(iri));
			outputResourceUris.add(uri);
			String namespace = iri.toString() + "#";
			Vocabulary v = omlBuilder.createVocabulary(uri, namespace, Paths.get(iri.toString()).getFileName().toString());
			vocabularies.put(iri,v);
			
			Import rdfsImport = oml.createImport();
			rdfsImport.setKind(ImportKind.EXTENSION);
			rdfsImport.setNamespace("http://www.w3.org/2000/01/rdf-schema#");
			rdfsImport.setPrefix("rdfs");
			rdfsImport.setOwningOntology(vocabularies.get(iri));
		});
		
		/*
		 * Add concept definitions.
		 */
	
		sbcById.forEach((id, c) -> {
			Vocabulary v = vocabularies.get(URI.createURI(c.get("iri")));
			String cName = cleanIdentifier(c.get("name"));
			Literal cLiteral = omlBuilder.createLiteral(c.get("name"));
			Concept concept = omlBuilder.addConcept(v, cName);
			concepts.put(id, concept);
			logger.info("concept " + cName + " label " + cLiteral.getLexicalValue() + " id " + id);
			omlBuilder.addAnnotation(v, concept, "http://www.w3.org/2000/01/rdf-schema#label", cLiteral, null);
			dnByConcept.put(concept, c.get("name"));
		});
			
		/*
		 * Add concept specialization axioms and extension axioms.
		 */

		Map<Vocabulary, Set<Vocabulary>> imported = new HashMap<>();

		sbcSuper.edgeSet().forEach(e -> {
			String es = sbcSuper.getEdgeSource(e);
			String et = sbcSuper.getEdgeTarget(e);
			Concept subC = concepts.get(es);
			Concept supC = concepts.get(et);
			if (supC != null) {
				Vocabulary subVocab = subC.getOwningVocabulary();
				String subPrefix = subVocab.getPrefix();
				Vocabulary supVocab = supC.getOwningVocabulary();
				String supPrefix = supVocab.getPrefix();
				
				omlBuilder.addSpecializationAxiom(subVocab, subC.getIri(), supC.getIri());
				
				String superName = (subPrefix == supPrefix ? "" : supPrefix + ":") + dnByConcept.get(supC);
				omlBuilder.addAnnotation(subVocab, subC, "http://www.w3.org/2000/01/rdf-schema#comment",
						omlBuilder.createLiteral("specializes " + superName), null);
				
				logger.info("concept " + subPrefix + ":" + subC.getName() + " :> " + supPrefix + ":" + supC.getName());
				
				if (!imported.containsKey(subVocab)) imported.put(subVocab, new HashSet<Vocabulary>());
				if (subVocab != supVocab && !imported.get(subVocab).contains(supVocab)) {
					omlBuilder.addImport(subVocab, ImportKind.EXTENSION, supVocab.getIri() + "#", supPrefix);
					imported.get(subVocab).add(supVocab);
				}
			}
		});
			  			
		/*
		 * Add annotations for disjointness.
		 */

		djClass.edgeSet().forEach(e -> {
			String es = djClass.getEdgeSource(e);
			String et = djClass.getEdgeTarget(e);
			Concept dj1 = concepts.get(es);
			Concept dj2 = concepts.get(et);
			if (dj2 != null) {
				Vocabulary dj1Vocab = dj1.getOwningVocabulary();
				String dj1Prefix = dj1Vocab.getPrefix();
				Vocabulary dj2Vocab = dj2.getOwningVocabulary();
				String dj2Prefix = dj2Vocab.getPrefix();
				
				String dj2Name = (dj1Prefix == dj2Prefix ? "" : dj2Prefix + ":") + dnByConcept.get(dj2);
				omlBuilder.addAnnotation(dj1Vocab, dj1, "http://www.w3.org/2000/01/rdf-schema#comment",
						omlBuilder.createLiteral("disjoint from " + dj2Name), null);				
			}
		});
		
		/*
		 * Write output.
		 */
		
		logger.info("finish builder");
		omlBuilder.finish();
		
		logger.info("save resources");
		outputResourceUris.forEach(outputResourceUri -> {
			logger.info("save " + outputResourceUri.toString());
			Resource outputResource = outputResourceSet.getResource(outputResourceUri, false);
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
		String p = path.replaceAll("\\A.*/sysml.library.xmi", "http://omg.org/SysML-v2");
		return URI.createURI((p + "/" + stem).replaceAll("\\s+", "-"));
	}
	
	private static String makeOutputFn(String op, Path sp, Path fp) {
		Path trail = trail(fp, sp);
		String path = op + "/omg.org/SysML-v2/" + trail.getParent().toString();
		String stem = trail.getFileName().toString().replaceAll("\\..*$", ".oml");
		return (path + "/" + stem).replaceAll("\\/+", "/");
	}
	
	private static String makeCatalogStartString(Path sp, Path fp) {
		Path trail = trail(fp, sp);
		return "http://omg.org/SysML-v2" + trail.getParent().toString().replaceAll("\\s+", "-").replaceAll("\\/+", "/");
	}

	private static String makeCatalogRewritePrefix(Path sp, Path fp) {
		Path trail = trail(fp, sp);
		return "/omg.org/SysML-v2" + trail.getParent().toString().replaceAll("\\s+", "-").replaceAll("\\/+", "/");
	}
	
	private static void createOutputCatalog(String path, Map<String, String> map) {
		(new File(path)).mkdirs();
		
		String fn = path + "/" + catalogStem;
		FileWriter writer = null;
		try {
			writer = new FileWriter(fn);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
		DocumentBuilder builder = null;
		try {
			builder = factory.newDocumentBuilder();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		Document doc = builder.newDocument();
		DOMSource source = new DOMSource(doc);
		Element cat = (Element) doc.createElement("catalog");
		cat.setAttribute("xmlns", "urn:oasis:names:tc:entity:xmlns:xml:catalog");
		cat.setAttribute("prefer", "public");
		doc.appendChild(cat);
		
		map.forEach((ss, rp) -> {
			Element srw = doc.createElement("rewriteURI");
			srw.setAttribute("uriStartString", ss);
			srw.setAttribute("rewritePrefix", rp);
			cat.appendChild(srw);
		});
		
		TransformerFactory transformerFactory = TransformerFactory.newInstance();
		Transformer transformer = null;
		try {
			transformer = transformerFactory.newTransformer();
		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		transformer.setOutputProperty(OutputKeys.INDENT, "yes");
		transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "2");
		StreamResult result = new StreamResult(writer);
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
}
