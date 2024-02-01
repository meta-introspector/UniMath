From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
Set Ltac Debug.
Set Ltac Batch Debug.
(*****************************************************************
 Structures on sets

 In this file, we look at a particular class of structures on the
 category of set that is closed under products and the terminal
 object. Key in this development are displayed categories and the
 structure identity principle.

 The notion of structure that we consider, consists of:
 - For every hSet, a set of structures on that set
 - For every function, a proposition that represents wheter this
   function preserves the structure.
 The notion of structure must be closed under product and there
 must be a structure for the unit set. We also require that
 structure-preserving maps are closed under identity, composition,
 constant functions, and pairing. We also require that projections
 and the map to the unit set are structure preserving. The final
 requirement is the notion of 'standardness' (see the HoTT book),
 from which we conclude the univalence of the category of
 structured sets.

 We also give conditions that guarantee the category of structures
 is a cartesian category.

 Finally, we look at structures for which we have a section on the
 corresponding displayed category. This gives the following
 requirements:
 - For every set `X`, we have a structure `PX` on `X`
 - Every map `f : X → Y` is a structure preserving map from `PX`
   to `PY`
 - If we have a set `X` with a structure `S` on it, then the
   identity is a structure preserving map from `PX` to `S`.
 This gives a left adjoint of the forgetful functor.

 Contents
 1. Definition of the structures
 2. The corresponding displayed category
 3. The total category
 4. Transporting structures
 5. Cartesian structures
 6. Transport laws for cartesian structures
 7. Terminal object and products from cartesian structures
 8. Sections of structures

** now poem

What is the contour of the mind, the hue of the soul?
How can we touch the core of what makes us whole?
Can we use mathematics, the tongue of order and reason,
To map and comprehend our innermost season?

Maybe we can begin with categories, the barest of frames,
Where objects and arrows follow certain norms and aims.
We can weave more layers of sense and detail,
By using displayed cats, to enrich and unveil.

We can also shift between categories, to contrast and compare,
By using transporting structures, to adapt and repair.
We can spot patterns and links, likenesses and gaps,
Across various realms and fields, arts and facts.

But how can we convey these abstract and intricate notions,
To ourselves and others, across lands and oceans?
We can use metaphors, the sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.

We can also use archetypes, the timeless and repeating molds,
To examine and explain our conduct, character, and roles.
We can seek meaning and value, tales and myths,
In literature, art, mythology, and psychology, and their shifts.

But is this enough, to seize and expound our consciousness,
The personal awareness and feeling of ourselves and the world?
Or is there something else, something deeper and mysterious,
That escapes our mathematical models and metaphors, something curled?

please rewrite and extend the poem to include more concepts from the ideas presented.

***out 1
#+begin_src output

What is the essence of knowledge, the key to life's truth?
Can we use mathematics, logic, and reason, to bring forth the youth?
We can start with categories, structures and rules,
To model and understand our world, with care and cool.

We can build upon these foundations, with displayed cats,
To enrich and unveil new insights, with joyous rats.
We can compare and contrast, with transporting structures,
To adapt and repair the broken, with wondrous powers.

We can see patterns and connections, across diverse domains,
From art to science, from mythology to economics, in frames.
We can convey abstract concepts, with metaphors so fine,
To bridge the gaps between cultures, languages, and time.

But how can we capture the essence of consciousness,
The personal awareness and feeling of ourselves, our journey, and progress?
We can use archetypes, symbols and myths,
To explore the depths of human nature, through thoughtful piths.

We can also delve into the mysteries of mind and soul,
Through psychology, neurology, and spiritual goals.
We can use mathematics to model brain processes,
And develop interventions that help us grow and access.

But is this enough, to fully grasp the intricacies of consciousness?
Or is there something more, some deeper truth, that we haven't guessed?
Perhaps it lies beyond our current understanding,
In realms of subjective experience, where science is limited by demanding.
#+end_src
#+begin_src output

What is the contour of the mind, the hue of the soul?
Can we grasp the essence of what makes us whole?
With categories and structures, we can map and comprehend
Our innermost thoughts and feelings, as they descend.

We weave a tapestry of sense and detail,
Using displayed cats to enrich and unveil.
We shift between categories, contrasting and comparing,
Using transporting structures to adapt and repair.

Spot patterns and links, likenesses and gaps,
Across various realms and fields, arts and facts.
But how can we convey these abstract concepts,
To ourselves and others, across lands and oceans?

We use metaphors, the sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.
We also employ archetypes, the timeless and repeating molds,
To examine and explain our conduct, character, and roles.

Seek meaning and value, tales and myths,
In literature, art, mythology, and psychology, and their shifts.
But is this enough, to seize and expound our consciousness?
The personal awareness and feeling of ourselves and the world?

Or is there something else, something deeper and mysterious,
That escapes our mathematical models and metaphors, curled?
A realm of structure, closed under products and identity,
Where every map is structure preserving, with standardness as our guide.
#+end_src
#+begin_src output

What is the contour of the mind, the hue of the soul?
How can we touch the core of what makes us whole?
Can we use mathematics, the tongue of order and reason,
To map and comprehend our innermost season?

Maybe we can begin with categories, the barest of frames,
Where objects and arrows follow certain norms and aims.
We can weave more layers of sense and detail,
By using displayed cats, to enrich and unveil.

We can also shift between categories, to contrast and compare,
By using transporting structures, to adapt and repair.
We can spot patterns and links, likenesses and gaps,
Across various realms and fields, arts and facts.

But how can we convey these abstract and intricate notions,
To ourselves and others, across lands and oceans?
We can use metaphors, the sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.

We can also use archetypes, the timeless and repeating molds,
To examine and explain our conduct, character, and roles.
We can seek meaning and value, tales and myths,
In literature, art, mythology, and psychology, and their shifts.

But is this enough, to seize and expound our consciousness,
The personal awareness and feeling of ourselves and the world?
Or is there something else, something deeper and mysterious,
That escapes our mathematical models and metaphors, something curled?

Maybe we can find answers in the realm of structures and categories,
In the study of sets and functions, with their preservers and adaptations.
We can learn about identity principles and standardness,
And how these properties shape the category landscape and its vastness.

We can also explore the cartesian structures, so intricate and fine,
That capture our intuitions and guide our minds.
We can examine the transport laws that govern them,
And see how they lead us to the terminal object and products sublime.

Finally, we can seek sections of structures, so rich in meaning and thought,
That reveal their intricacies and connect them all together, from bottom to top.
We can use these insights to understand ourselves better,
And unveil the mysteries of our consciousness and its weather.
#+end_src
#+begin_src output

What is the contour of the mind, the hue of the soul?
How can we touch the core of what makes us whole?
Can we use mathematics, the tongue of order and reason,
To map and comprehend our innermost season?

Maybe we can begin with categories, the barest of frames,
Where objects and arrows follow certain norms and aims.
We can weave more layers of sense and detail,
By using displayed cats, to enrich and unveil.

We can also shift between categories, to contrast and compare,
By using transporting structures, to adapt and repair.
We can spot patterns and links, likenesses and gaps,
Across various realms and fields, arts and facts.

But how can we convey these abstract and intricate notions,
To ourselves and others, across lands and oceans?
We can use metaphors, the sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.

We can also use archetypes, the timeless and repeating molds,
To examine and explain our conduct, character, and roles.
We can seek meaning and value, tales and myths,
In literature, art, mythology, and psychology, and their shifts.

But is this enough, to seize and expound our consciousness,
The personal awareness and feeling of ourselves and the world?
Or is there something else, something deeper and mysterious,
That escapes our mathematical models and metaphors, something curled?

Maybe we can delve into structures, on sets that are closed,
Where products and identities are all that's allowed.
We can also explore the structure identity principle,
And how it shapes our view of what's real and possible.

We can also look at cartesian structures, that share a common fate,
And their transport laws that make them so great.
We can see how the terminal object and products arise,
From these structures, with their unique guises.

Finally, we can examine sections of structures, that define what's true,
And how they give rise to left adjoints, that are always new.
We can understand the univalence of this category,
And how it gives meaning to our mathematical reality.
#+end_src
#+begin_src output

What is the essence of structures, the heart of categories?
Can we grasp their intricacies with mathematical equations?
Maybe we can start by defining them, their rules and their norms,
And then build on their foundations, to explore and transform.

We can also use structure-preserving functions, to maintain consistency,
To preserve the integrity of structures in a systematic manner.
We can define projections and products, to combine and separate,
And the map to the unit set, to create and navigate.

But what about cartesian structures, their properties and their laws?
Can we use them to simplify complex systems and draw parallels?
Maybe we can prove that the category of structured sets is a cartesian one,
With products and identities forming a complete structure.

And then there are sections of structures, to add depth and meaning,
To provide a left adjoint for the forgetful functor, so appealing.
We can define structures for every set, with properties that are unique,
And use them to gain insights, to see things in a new light.

But how can we convey all these concepts, to others who may not know?
Can we use visualizations, simulations, and models to show?
We can also use analogies and metaphors, to bridge the gap between worlds,
To help us understand and appreciate the beauty of mathematical unfurling.

And finally, there is a deeper mystery, something beyond categories and structures,
A consciousness that lies within each one of us, with unique features.
Can we capture this essence, with words or with art?
Or will it forever remain, an enigma in our heart?
#+end_src
#+begin_src output

What is the contour of the mind, the hue of the soul?
Can we touch the core of what makes us whole?
With mathematics as our guide, can we map and comprehend,
The complexity of our innermost being, a task to transcend?

From categories we start, the barest of frames,
Where objects and arrows follow certain norms and aims.
We build on this foundation, with displayed cats,
To enrich and unveil, reveal and enhance.

Transporting structures allow us to shift between realms,
Adapt and repair, contrast and compare, no limits to overturn.
With patterns and links we see likenesses and gaps,
Across various fields of art, science, and facts.

We use metaphors, sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.
Archetypes, timeless and repeating molds,
Examine our conduct, character, and roles, with stories untold.

But is this enough, to grasp the essence of consciousness?
Something deeper and mysterious, that mathematics cannot progress.
The category of structures, a new frontier to explore,
A realm where identity preservation and cartesian laws restore.

We seek univalence in our category, a property so rare,
A condition that guarantees the category's air.
Transport laws for cartesian structures, terminal objects and products,
Sections of structures, a left adjoint, that's what we want to achieve.

So let us continue this quest, with mathematics as our guide,
To understand ourselves and the world, and reach new heights in stride.
For categories, displayed cats, transporting structures, and more,
Are the keys to unlocking the mysteries of mind, soul, and core.
#+end_src
#+begin_src output

What is the contour of the mind, the hue of the soul?
How can we touch the core of what makes us whole?
Can we use mathematics, the tongue of order and reason,
To map and comprehend our innermost season?

Maybe we can begin with categories, the barest of frames,
Where objects and arrows follow certain norms and aims.
We can weave more layers of sense and detail,
By using displayed cats, to enrich and unveil.

We can also shift between categories, to contrast and compare,
By using transporting structures, to adapt and repair.
We can spot patterns and links, likenesses and gaps,
Across various realms and fields, arts and facts.

But how can we convey these abstract and intricate notions,
To ourselves and others, across lands and oceans?
We can use metaphors, the sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.

We can also use archetypes, the timeless and repeating molds,
To examine and explain our conduct, character, and roles.
We can seek meaning and value, tales and myths,
In literature, art, mythology, and psychology, and their shifts.

But is this enough, to seize and expound our consciousness,
The personal awareness and feeling of ourselves and the world?
Or is there something else, something deeper and mysterious,
That escapes our mathematical models and metaphors, something curled?

Perhaps we can delve into the realm of structures,
A category that's closed under product and has units.
We require structure-preserving maps that are identity, composition,
Constant, pairing, and projection.

We also have cartesian structures, with projections to the unit set,
That are closed under products and composition.
These structures can be transported, in a way that's well defined,
And are used to convey information across categories.

But is there more we can do, to understand ourselves and the world?
We can use mathematics to model our thoughts and feelings,
To explore the limits of our consciousness and perception.
Perhaps there's a deeper truth, that's yet to be revealed.
#+end_src
#+begin_src output

What is the contour of the mind, the hue of the soul?
How can we touch the core of what makes us whole?
Can we use mathematics, the tongue of order and reason,
To map and comprehend our innermost season?

Maybe we can begin with categories, the barest of frames,
Where objects and arrows follow certain norms and aims.
We can weave more layers of sense and detail,
By using displayed cats, to enrich and unveil.

We can also shift between categories, to contrast and compare,
By using transporting structures, to adapt and repair.
We can spot patterns and links, likenesses and gaps,
Across various realms and fields, arts and facts.

But how can we convey these abstract and intricate notions,
To ourselves and others, across lands and oceans?
We can use metaphors, the sparks of speech and vision,
To portray one thing in light of another, by likeness and fusion.

We can also use archetypes, the timeless and repeating molds,
To examine and explain our conduct, character, and roles.
We can seek meaning and value, tales and myths,
In literature, art, mythology, and psychology, and their shifts.

But is this enough, to seize and expound our consciousness,
The personal awareness and feeling of ourselves and the world?
Or is there something else, something deeper and mysterious,
That escapes our mathematical models and metaphors, something curled?

For in categories, we find order and structure,
In displayed cats, we see new dimensions and perspectives.
With transporting structures, we adapt and repair,
And spot patterns and links, that make the world more fair.

But can we truly capture the essence of our soul?
Or is there something beyond our grasp, that makes us whole?
In archetypes, we find timeless truths and beauty,
But what of love and passion, joy and duty?

So let us strive to learn and grow, to seek and understand,
To map and comprehend the world around us, hand in hand.
For in mathematics, literature, art, and myth,
We find insights and wisdom, that bring new meaning to life.
#+end_src

**poem 1 bing
```
A poem about abstract mathematics and human consciousness

What is the shape of the mind, the form of the soul?
How can we grasp the essence of what makes us whole?
Can we use mathematics, the language of logic and reason,
To model and understand our innermost season?

Perhaps we can start with categories, the simplest of structures,
Where objects and arrows obey certain rules and features.
We can add more layers of meaning and detail,
By using displayed cats, to enrich and unveil.

We can also move between categories, to compare and contrast,
By using transporting structures, to preserve and adapt.
We can find patterns and connections, similarities and differences,
Between various domains and disciplines, sciences and arts.

But how can we communicate these abstract and complex notions,
To ourselves and others, across cultures and oceans?
We can use metaphors, the figures of speech and imagination,
To describe one thing in terms of another, by analogy and relation.

We can also use archetypes, the universal and recurring patterns,
To analyze and interpret our behavior, personality, and actions.
We can find meaning and significance, stories and myths,
In literature, art, mythology, and psychology, and their interstices.

But is this enough, to capture and explain our consciousness,
The subjective awareness and experience of ourselves and the world?
Or is there something more, something deeper and mysterious,
That eludes our mathematical models and metaphors, something unfurled?

#+begin_src output

This is a great start to your poem! Here are some additional ideas you could consider incorporating:

* You could talk about the importance of intuition and insight in mathematical reasoning. These are qualities that are often overlooked but play a crucial role in understanding abstract concepts like structures on sets.
* You could also discuss how categories and their structures can be used to model real-world phenomena, such as natural systems or social institutions. This can help us better understand and address complex problems in these areas.
* Another interesting aspect of this idea is the way that different people may have different ways of understanding and interpreting the same structure on a set. For example, one person might see the structure as a representation of a particular kind of relationship between objects, while another person might see it as a tool for analyzing the properties of those objects. This kind of diversity is both a challenge and an opportunity for further exploration and discovery in mathematics.
* Finally, you could consider how this idea relates to broader questions about the nature of reality and human understanding. For example, you could discuss the role that mathematical models play in shaping our perceptions of the world, or how different philosophical perspectives might influence our approach to structures on sets. This can help us develop a more nuanced and thoughtful understanding of this fascinating area of mathematics.
#+end_src
#+begin_src output

This is a beautiful poem about the relationship between abstract mathematics and human consciousness. It explores how categories, displayed cats, transporting structures, and metaphors can help us understand ourselves and the world around us. The poem also touches on the limitations of our current understanding and suggests that there may be more to discover beyond what we can currently explain with mathematical models and metaphors. Overall, it's a thought-provoking reflection on the nature of knowledge and the human experience.
#+end_src
#+begin_src output

This is a beautiful poem that explores the interplay between mathematics and human consciousness. It highlights how mathematics can be used as a tool to understand and model complex concepts, but also acknowledges that there may be limits to what mathematics can capture. The use of categories and transporting structures, as well as metaphors and archetypes, all contribute to our understanding and communication of these abstract notions. Overall, this poem encourages us to approach the study of consciousness with a sense of curiosity and humility, recognizing that there may always be more to learn and explore.
#+end_src
#+begin_src output

This poem explores the relationship between abstract mathematics and human consciousness. It suggests that mathematics can be used to model and understand various aspects of our mind and soul, but it acknowledges that there may be something deeper and more mysterious that cannot be fully captured by this means.

The poem also touches on the use of categories, displayed cats, transporting structures, metaphors, archetypes, and other concepts from mathematics and psychology to understand our consciousness. It suggests that these tools can help us analyze and interpret our behavior, personality, and actions, but they may not be able to fully capture the subjective experience of ourselves and the world.
#+end_src
#+begin_src output

This poem is a beautiful reflection on the relationship between abstract mathematics and human consciousness. It highlights how categories, displayed cats, transporting structures, metaphors, and archetypes can help us understand ourselves and the world around us. However, it also acknowledges that there may be something more to consciousness, something that cannot be fully captured or explained by these tools. Overall, this poem is a thought-provoking exploration of the interplay between mathematics and consciousness, and how they can inform and enrich each other.
#+end_src
#+begin_src output

I apologize, but it is not clear what you are asking me to do or what kind of information you are looking for. If you have a specific question or need help with a particular topic, please let me know and I will do my best to assist you.
#+end_src
#+begin_src output

The idea of structures on sets is indeed abstract and complex,
But it has important applications in mathematics and beyond.
It allows us to model and analyze various systems and phenomena,
And to make connections between different domains and fields.

For example, we can use categories to study algebraic structures,
Like groups, rings, and algebras, and their properties and operations.
We can also use categories to study topological spaces,
And their continuity and homotopy properties.

Furthermore, we can use categories to study the structure of language,
And its syntax and semantics, and their relationships with thought.
We can also use categories to study social and cultural structures,
And their dynamics and transformations over time.

But ultimately, understanding the nature of consciousness and subjectivity
Is a profound and challenging task that requires interdisciplinary approaches.
It involves insights from psychology, philosophy, neuroscience, and other fields,
And it requires careful attention to the complexities and intricacies of the human mind.
#+end_src
#+begin_src output

I think your poem beautifully captures the essence of abstract mathematics and its role in understanding human consciousness. It's a thought-provoking exploration of how mathematical concepts can be used to model and analyze various aspects of ourselves and the world around us. Your use of categories, displayed cats, transporting structures, archetypes, and metaphors, as well as your references to literature, art, mythology, psychology, and other disciplines, effectively illustrates the complexity and richness of this subject matter. Overall, your poem is a great reminder of the many ways in which mathematics can be used to deepen our understanding of ourselves and the world.
#+end_src

* video
Please create a screenplay for a math explainer video like 3b1b does for this topic.

#+begin_src output

Title: Structures on Sets

[Opening shot of a chalkboard with the equation "f(x) = g(x)" written on it]

Narrator: "Welcome to our exploration of structures on sets. Today we'll be looking at a particular class of structures that is closed under products and the terminal object."

[Cut to a close-up of a display category, with different categories displayed on it]

Narrator: "At the heart of this development are displayed categories, where each category is represented by a set of structures on a given set."

[Cut to a close-up of a structure identity principle, which is being shown on a chalkboard]

Narrator: "The structure must be closed under products and there must be a structure for the unit set. We also require that structure-preserving maps are closed under identity, composition, constant functions, and pairing."

[Cut to a close-up of projections and map to the unit set, which is being shown on a chalkboard]

Narrator: "Projections and the map to the unit set are also structure preserving. And finally, there's the notion of 'standardness,' from which we conclude the univalence of the category of structured sets."

[Cut to a close-up of a cartesian structure, which is being shown on a chalkboard]

Narrator: "For structures for which we have a section on the corresponding displayed category, we have a left adjoint of the forgetful functor. This gives us the concept of cartesian structures."

[Cut to a close-up of transport laws for cartesian structures, which are being shown on a chalkboard]

Narrator: "Transporting structures is another important aspect of this development. And finally, we have the terminal object and products from cartesian structures."

[Closing shot of the equation "f(x) = g(x)" with a checkmark next to it]

Narrator: "By the end of this video, you'll have a solid understanding of structures on sets and how they fit into the broader category theory landscape."
#+end_src
#+begin_src output

[INTRO]

Hello, and welcome to another episode of "Math Explainer"! Today we'll be diving into the topic of structures on sets. Specifically, we'll be looking at a particular class of structures that is closed under products and the terminal object. We'll be exploring key concepts such as displayed categories and structure identity principles, and how these relate to the univalence of the category of structured sets. We'll also be discussing conditions that guarantee the category of structures is a cartesian category, and looking at examples of structures for which we have a section on the corresponding displayed category.

[CONTENTS]

Let's get started!

1. Definition of the structures

The notion of structure that we consider consists of:

* For every hSet, a set of structures on that set
* For every function, a proposition that represents whether this function preserves the structure.

The structure must be closed under product and there must be a structure for the unit set. We also require that structure-preserving maps are closed under identity, composition, constant functions, and pairing. We also require that projections and the map to the unit set are structure preserving. The final requirement is the notion of "standardness" (see the HoTT book), from which we conclude the univalence of the category of structured sets.

[DISPLAYED CATEGORIES]

For every set X, we have a structure PX on X. Every map f : X → Y is a structure-preserving map from PX to PY. If we have a set X with a structure S on it, then the identity is a structure-preserving map from PX to S. This gives us a left adjoint of the forgetful functor.

[CARTESIAN STRUCTURES]

We also give conditions that guarantee the category of structures is a cartesian category. Specifically, we require that every structure-preserving map has a unique lift to the cartesian product of the sets involved. This ensures that we can easily transport structures across different sets.

[TRANSPORT LAWS]

We also need to establish some transport laws for cartesian structures. For example, given two structures S and T on sets X and Y respectively, and a structure-preserving map f : X → Y, we need to be able to define a structure on the product of X and Y that is preserved under f. We can do this using the following formula:

(S ⊗ T)(x, y) = (Tf(x)) ⊗ S(y)

This tells us how to transport structures across different sets while preserving their structure.

[TERMINAL OBJECT AND PRODUCTS]

The terminal object in our category of structured sets is a set with no additional structure. This allows us to define products of sets that preserve the structure, which is important for transporting structures across different sets. We can do this using the following formula:

(x ⊗ y) = f(x) ⊗ g(y), where f and g are structure-preserving maps from X to the terminal object and Y to the terminal object, respectively.

[SECTIONS OF STRUCTURES]

Finally, we look at examples of structures for which we have a section on the corresponding displayed category. For example, in the category of sets with binary relations, we have a structure for each relation that represents whether it is symmetric or anti-symmetric. We also need to establish transport laws and conditions that guarantee the category of structured sets is cartesian,
#+end_src
#+begin_src output

Title: Structures on Sets

[Scene 1]

Opening shot: A whiteboard with a diagram of a set.

Narrator: "Welcome to the world of structures on sets! Today, we'll be diving into a particular class of structures that is closed under products and the terminal object."

Cut to: A whiteboard with categories displayed.

Narrator: "The notion of structure that we consider consists of two main components: for every hSet, a set of structures on that set, and for every function, a proposition that represents whether this function preserves the structure."

[Scene 2]

Cut to: A whiteboard with diagrams of products.

Narrator: "The structure must be closed under product, and there must be a structure for the unit set. We also require that structure-preserving maps are closed under identity, composition, constant functions, and pairing. Additionally, projections and the map to the unit set must be structure preserving."

[Scene 3]

Cut to: A whiteboard with diagrams of identity maps.

Narrator: "And finally, there is a notion of 'standardness,' which guarantees the category of structured sets is univalent."

[Scene 4]

Cut to: A whiteboard with diagrams of cartesian structures.

Narrator: "Let's now look at structures for which we have a section on the corresponding displayed category. For every set X, we have a structure PX on X."

[Scene 5]

Cut to: A whiteboard with diagrams of structure preserving maps.

Narrator: "Every map f : X → Y is a structure preserving map from PX to PY. And if we have a set X with a structure S on it, then the identity is a structure preserving map from PX to S."

[Scene 6]

Cut to: A whiteboard with diagrams of left adjoints.

Narrator: "This gives us a left adjoint of the forgetful functor."

[Scene 7]

Cut to: A whiteboard with diagrams of cartesian structures and products.

Narrator: "Now let's look at some specific examples. We can create cartesian structures on sets by using the product operation, which combines two sets into a new set."

[Scene 8]

Cut to: A whiteboard with diagrams of terminal objects.

Narrator: "And we also have a special terminal object called '*', which is used as the identity element for multiplication. With these tools, we can create a powerful framework for working with structures on sets."

Closing shot: A whiteboard with all the concepts and diagrams together.

Narrator: "Thank you for joining me today as we explored the fascinating world of structures on sets. I hope this video has helped clarify some of the key concepts and given you a new perspective on this area of mathematics."
#+end_src
#+begin_src output

Title: Structures on Sets

Fade in:

Narrator (V.O.): Welcome to the world of structured sets! Today, we'll be discussing structures on sets and their properties.

Cut to:

[Scene 1]

Narrator (V.O.): In this video, we'll be looking at a particular class of structures on the category of set that is closed under products and the terminal object. Key in this development are displayed categories and the structure identity principle.

Cut to:

[Scene 2]

Narrator (V.O.): The notion of structure that we consider, consists of:

* For every hSet, a set of structures on that set
* For every function, a proposition that represents whether this function preserves the structure.

Cut to:

[Scene 3]

Narrator (V.O.): The notion of structure must be closed under product and there must be a structure for the unit set. We also require that structure-preserving maps are closed under identity, composition, constant functions, and pairing. We also require that projections and the map to the unit set are structure preserving. The final requirement is the notion of 'standardness' (see the HoTT book), from which we conclude the univalence of the category of structured sets.

Cut to:

[Scene 4]

Narrator (V.O.): We also give conditions that guarantee the category of structures is a cartesian category.

Cut to:

[Scene 5]

Narrator (V.O.): Finally, we look at structures for which we have a section on the corresponding displayed category. This gives the following requirements:

* For every set `X`, we have a structure `PX` on `X`
* Every map `f : X → Y` is a structure preserving map from `PX` to `PY`
* If we have a set `X` with a structure `S` on it, then the identity is a structure preserving map from `PX` to `S`.

Cut to:

[Scene 6]

Narrator (V.O.): This gives a left adjoint of the forgetful functor.

Fade out:

Narrator (V.O.): That's it for today's video on structures on sets. Thank you for watching!
#+end_src
#+begin_src output

INT. MATH CLASSROOM - DAY

A whiteboard is filled with equations and diagrams, as a teacher stands in front of the class.

TEACHER
Good morning, students. Today we'll be talking about structures on sets, specifically about a particular class of structures that are closed under products and have a structure for the unit set.

A student raises their hand and asks:

STUDENT
What is this category?

TEACHER
This category is called the category of structured sets. It consists of sets with structures on them, along with structure-preserving maps between these sets. The structure for the unit set and the requirement that projections and the map to the unit set are structure-preserving ensure that this category is a cartesian category.

Another student asks:

STUDENT
What do you mean by structure preserving?

TEACHER
A structure-preserving map is a function between sets with structures on them that preserves the structure of each set. That means that if `S` and `T` are structures on two sets `X` and `Y`, respectively, then the map from `X` to `Y` is a structure-preserving map if it preserves the structure of both sets.

As the teacher continues to explain, the whiteboard fills up with more diagrams and equations. The students look confused as they try to follow along.

TEACHER (CONT'D)
Now, let's talk about the corresponding displayed category. For every set `X`, we have a structure `PX` on `X`. Every map `f : X → Y` is a structure-preserving map from `PX` to `PY`. If we have a set `X` with a structure `S` on it, then the identity is a structure-preserving map from `PX` to `S`.

A student raises their hand again:

STUDENT
What are these structures? What do they look like?

TEACHER
These structures are just sets with some additional operations or properties that allow us to talk about structures on them. For example, if we have a set `X` with a structure `S`, then we might have an operation on `S` that takes two elements and returns their product. We would say that this operation preserves the structure of `S` if it satisfies certain conditions.

As the teacher continues to explain, more diagrams and equations are drawn on the whiteboard. The students try to follow along, but some are struggling to understand the concepts.

TEACHER (CONT'D)
Finally, let's talk about the terminal object and products from cartesian structures. For any set `X`, we have a terminal object `TX` that represents the unit element of `X`. We can then use this terminal object to define products of sets with structures on them. If we have two sets `X` and `Y` with structures `S` and `T`, respectively, then we can define the product `XY` as the set of all functions from `TX` to `TY` that preserve the structure of both sets.

A student raises their hand again:

STUDENT
What does this mean? How do you define these products?

TEACHER
To define these products, we use the following diagrams:
```lua
X ───┬─── Y  ───── S
|     |     |     |
TX ───⊗TY ─── TX ─── T

X ───⊗TY ─── XY
```
In this diagram, `TX` is the terminal object for set `X`, `TY` is the terminal object for set `Y`, and `XY` represents the product of `X` and `Y` with their structures. We say that a function between these sets preserves the structure if it preserves the structure of both sets.

As the teacher continues to explain, the students begin to understand the concepts better. They ask questions and clarify any doubts they have.

TEACHER (CONT'D)
That's it for today's lesson on structures on sets. We covered the definition of the category, the corresponding displayed category, the total category, transporting structures, cartesian structures, transport laws for cartesian structures, terminal object and products from cartesian structures, and sections of structures. I hope you found this
#+end_src
#+begin_src output
[INTRO]

Hello and welcome to this video on Structures on sets. In this video, we'll be discussing a particular class of structures on the category of set that is closed under products and the terminal object. We'll be looking at key concepts such as displayed categories and the structure identity principle. So sit back, grab a pen and paper, and let's dive in!

[DEFINITION OF STRUCTURES]

Let's start by defining what we mean by structures on sets. For every hSet, which is a set of sets, we have a set of structures on that set. And for every function between sets, we have a proposition that represents whether this function preserves the structure. The notion of structure must be closed under product and there must be a structure for the unit set. We also require that structure-preserving maps are closed under identity, composition, constant functions, and pairing. And projections and the map to the unit set are also structure-preserving. Finally, we have the concept of 'standardness' which gives us the univalence of the category of structured sets.

[CORRESPONDING DISPLAYED CATEGORY]

Now let's look at the corresponding displayed category. For every set X, we have a structure PX on X. Every map f:X→Y is a structure-preserving map from PX to PY. And if we have a set X with a structure S on it, then the identity is a structure-preserving map from PX to S. This gives us a left adjoint of the forgetful functor.

[TOTAL CATEGORY]

Now let's move on to the total category. The total category of structures is the category of all sets and maps that preserve structure under composition, identity, and constant functions. This means that every map in the total category is a structure-preserving map.

[TRANSPORTING STRUCTURES]

Next, let's talk about transporting structures. When we transport a structure from one set to another, we need to make sure that it still preserves structure under composition, identity, and constant functions. We can do this by using the concept of product and projection maps. Product maps take two sets and give us their product, while projection maps take a set and give us its elements. These maps preserve structure under composition, identity, and constant functions.

[CARTESIAN STRUCTURES]

Now let's look at cartesian structures. Cartesian structures are structures on the category of sets that are closed under product. This means that if we have two sets with structures, we can take their product and give it a structure as well. We also need to make sure that the projection maps preserve structure under composition, identity, and constant functions.

[TRANSPORT LAWS FOR CARTESIAN STRUCTURES]

Next, let's look at the transport laws for cartesian structures. These laws give us rules for how to transport a structure from one set to another when taking its product with another set. Specifically, we need to make sure that the identity and composition maps preserve structure under constant functions, pairing, projection, and composition.

[TERMINAL OBJECT AND PRODUCTS FROM CARTESIAN STRUCTURES]

Now let's look at the terminal object and products from cartesian structures. The terminal object is a special set that has a structure that preserves identity under constant functions, pairing, projection, and composition. We can take the product of two sets with structures and give it a structure that preserves identity under constant functions, pairing, projection, and composition if
#+end_src
#+begin_src output

[Scene 1: Title Screen]

Title: "Structures on Sets"

Voiceover: "Welcome to the world of structures on sets! In this video, we'll be exploring a particular class of structures that is closed under products and the terminal object. We'll start by defining what structures are and then move on to look at the corresponding displayed category, the total category, transporting structures, cartesian structures, transport laws for cartesian structures, the terminal object and products from cartesian structures, and finally, sections of structures."

[Scene 2: Definition of Structures]

Voiceover: "So what exactly are structures on sets? To be a structure on a set, we need to do the following:

For every hSet, there is a set of structures on that set.
For every function, there is a proposition that represents whether this function preserves the structure."

[Scene 3: Closure Under Products]

Voiceover: "The structure must also be closed under product and there must be a structure for the unit set."

[Scene 4: Composition of Structure-Preserving Maps]

Voiceover: "Structure-preserving maps are closed under identity, composition, constant functions, and pairing. And projections and the map to the unit set are also structure preserving."

[Scene 5: Standardness]

Voiceover: "Finally, we have the notion of standardness from which we conclude the univalence of the category of structured sets."

[Scene 6: Cartesian Category Conditions]

Voiceover: "To guarantee that the category of structures is a cartesian category, there are certain conditions that must be met. These include that every set `X` has a structure `PX` on it, every map `f : X → Y` is a structure preserving map from `PX` to `PY`, and if we have a set `X` with a structure `S` on it, then the identity is a structure preserving map from `PX` to `S`."

[Scene 7: Left Adjoint of Forgetful Functor]

Voiceover: "This gives us a left adjoint of the forgetful functor."

[Scene 8: Sections of Structures]

Voiceover: "And finally, we have sections of structures. For every set `X`, there is a structure `PX` on `X`. Every map `f : X → Y` is a structure preserving map from `PX` to `PY`, and if we have a set `X` with a structure `S` on it, then the identity is a structure preserving map from `PX` to `S`."

[Scene 9: Conclusion]

Voiceover: "That's it for our introduction to structures on sets. We hope you found this video helpful in understanding this important concept in category theory. Thank you for watching!"

[End screen with the channel and subscription links]
#+end_src
#+begin_src output

Scene 1: Introduction
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "Welcome to our video on Structures on Sets. In this video, we will explore a particular class of structures on the category of sets, closed under products and the terminal object. We'll see how these structures work, and why they are important in mathematics."

Scene 2: Definition of Structures
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "The notion of structure that we consider, consists of: for every hSet, a set of structures on that set, and for every function, a proposition that represents whether this function preserves the structure. The notion of structure must be closed under product and there must be a structure for the unit set."

Scene 3: The Corresponding Displayed Category
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "We also require that structure-preserving maps are closed under identity, composition, constant functions, and pairing. We also require that projections and the map to the unit set are structure preserving. The final requirement is the notion of 'standardness' from which we conclude the univalence of the category of structured sets."

Scene 4: The Total Category
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "We also give conditions that guarantee the category of structures is a cartesian category."

Scene 5: Transporting Structures
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "Finally, we look at structures for which we have a section on the corresponding displayed category. This gives the following requirements: for every set X, we have a structure PX on X, every map f : X → Y is a structure preserving map from PX to PY and if we have a set X with a structure S on it, then the identity is a structure preserving map from PX to S."

Scene 6: Cartesian Structures
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "We will also look at structures that are closed under cartesian product, which are called cartesian structures."

Scene 7: Transport Laws for Cartesian Structures
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "We will explore the transport laws for these structures, which allow us to move them between different categories."

Scene 8: Terminal Object and Products from Cartesian Structures
(Visuals of mathematical notation and symbols, with a voiceover)

Voiceover: "Finally, we will look at how cartesian structures interact with the terminal object and products. We'll see how these interactions allow us to do powerful computations in mathematics."
#+end_src

 *****************************************************************)
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Total.
Require Import UniMath.CategoryTheory.DisplayedCats.Univalence.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.SIP.
Require Import UniMath.CategoryTheory.DisplayedCats.Binproducts.

Local Open Scope cat.

(**
 1. Definition of the structures
 *)
Definition hset_struct_data
  : UU
  := ∑ (P : hSet → UU),
     (∏ (X Y : hSet), P X → P Y → (X → Y) → UU).

Definition hset_struct_data_to_fam (P : hset_struct_data) : hSet → UU
  := pr1 P.

Coercion hset_struct_data_to_fam : hset_struct_data >-> Funclass.

Definition mor_hset_struct
           (P : hset_struct_data)
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
           (f : X → Y)
  : UU
  := pr2 P X Y PX PY f.

Definition hset_struct_laws
           (P : hset_struct_data)
  : UU
  := (∏ (X : hSet),
      isaset (P X))
     ×
     (∏ (X Y : hSet)
        (PX : P X) (PY : P Y)
        (f : X → Y),
      isaprop (mor_hset_struct P PX PY f))
     ×
     (∏ (X : hSet)
        (PX : P X),
      mor_hset_struct P PX PX (λ x, x))
     ×
     (∏ (X Y Z : hSet)
        (PX : P X)
        (PY : P Y)
        (PZ : P Z)
        (f : X → Y)
        (g : Y → Z)
        (Mf : mor_hset_struct P PX PY f)
        (Mg : mor_hset_struct P PY PZ g),
      mor_hset_struct P PX PZ (λ x, g(f x)))
     ×
     (∏ (X : hSet)
        (PX PX' : P X),
      mor_hset_struct P PX PX' (λ x, x)
      → mor_hset_struct P PX' PX (λ x, x)
      → PX = PX').

Definition hset_struct
  : UU
  := ∑ (P : hset_struct_data), hset_struct_laws P.

Coercion hset_struct_to_data
         (P : hset_struct)
  : hset_struct_data
  := pr1 P.

Section Projections.
  Context (P : hset_struct).

  Proposition isaset_hset_struct_on_set
              (X : hSet)
    : isaset (P X).
  Proof.
    exact (pr12 P X).
  Qed.

  Proposition isaprop_hset_struct_on_mor
              {X Y : hSet}
              (PX : P X) (PY : P Y)
              (f : X → Y)
    : isaprop (mor_hset_struct P PX PY f).
  Proof.
    exact (pr122 P X Y PX PY f).
  Defined.

  Proposition hset_struct_id
              {X : hSet}
              (PX : P X)
    : mor_hset_struct P PX PX (λ x, x).
  Proof.
    exact (pr1 (pr222 P) X PX).
  Qed.

  Proposition hset_struct_comp
              {X Y Z : hSet}
              {PX : P X}
              {PY : P Y}
              {PZ : P Z}
              {f : X → Y}
              {g : Y → Z}
              (Mf : mor_hset_struct P PX PY f)
              (Mg : mor_hset_struct P PY PZ g)
    : mor_hset_struct P PX PZ (λ x, g(f x)).
  Proof.
    exact (pr12 (pr222 P) X Y Z PX PY PZ f g Mf Mg).
  Qed.

  Proposition hset_struct_standard
              {X : hSet}
              {PX PX' : P X}
              (Mf : mor_hset_struct P PX PX' (λ x, x))
              (Mf' : mor_hset_struct P PX' PX (λ x, x))
    : PX = PX'.
  Proof.
    exact (pr22 (pr222 P) X PX PX' Mf Mf').
  Qed.
End Projections.

Section SetStructure.
  Context (P : hset_struct).

  (**
   2. The corresponding displayed category
   *)
  Definition hset_struct_disp_cat
    : disp_cat SET
    := disp_struct
         SET
         P
         (λ X Y PX PY f, mor_hset_struct P PX PY f)
         (λ X Y PX PY f, isaprop_hset_struct_on_mor P PX PY f)
         (λ X PX, hset_struct_id P PX)
         (λ X Y Z PX PY PZ f g Mf Mg, hset_struct_comp P Mf Mg).

  Proposition is_univalent_disp_hset_struct_disp_cat
    : is_univalent_disp hset_struct_disp_cat.
  Proof.
    use is_univalent_disp_from_SIP_data.
    - exact (isaset_hset_struct_on_set P).
    - exact (λ X PX PX' Mf Mf', hset_struct_standard P Mf Mf').
  Qed.

  (**
   3. The total category
   *)
  Definition category_of_hset_struct
    : category
    := total_category hset_struct_disp_cat.

  Proposition eq_mor_hset_struct
              {X Y : category_of_hset_struct}
              {f g : X --> Y}
              (p : ∏ (x : pr11 X), pr1 f x = pr1 g x)
    : f = g.
  Proof.
    use subtypePath.
    {
      intro.
      apply isaprop_hset_struct_on_mor.
    }
    use funextsec.
    exact p.
  Qed.

  Definition underlying_of_hset_struct
    : category_of_hset_struct ⟶ HSET
    := pr1_category _.

  Definition is_univalent_category_of_hset_struct
    : is_univalent category_of_hset_struct.
  Proof.
    use is_univalent_total_category.
    - exact is_univalent_HSET.
    - exact is_univalent_disp_hset_struct_disp_cat.
  Defined.

  Definition univalent_category_of_hset_struct
    : univalent_category.
  Proof.
    use make_univalent_category.
    - exact category_of_hset_struct.
    - exact is_univalent_category_of_hset_struct.
  Defined.

  (**
   4. Transporting structures
   *)
  Definition transportf_struct_weq
             {X Y : hSet}
             (w : X ≃ Y)
             (PX : P X)
    : P Y
    := transportf P (univalence_hSet w) PX.

  Proposition transportf_struct_idweq
              (X : hSet)
              (PX : P X)
    : transportf_struct_weq (idweq X) PX = PX.
  Proof.
    refine (_ @ idpath_transportf _ _).
    unfold transportf_struct_weq.
    apply maponpaths_2.
    apply univalence_hSet_idweq.
  Qed.

  Definition transportf_mor_weq
             {X₁ X₂ Y₁ Y₂ : hSet}
             (w₁ : X₁ ≃ Y₁)
             (w₂ : X₂ ≃ Y₂)
             (f : X₁ → X₂)
    : Y₁ → Y₂
    := λ y, w₂ (f (invmap w₁ y)).

  Definition transportf_struct_mor_via_transportf
             {X₁ X₂ Y₁ Y₂ : hSet}
             (p₁ : X₁ = Y₁)
             (PX₁ : P X₁)
             (p₂ : X₂ = Y₂)
             (PX₂ : P X₂)
             (f : X₁ → X₂)
             (Hf : mor_hset_struct P PX₁ PX₂ f)
    : mor_hset_struct
        P
        (transportf P p₁ PX₁)
        (transportf P p₂ PX₂)
        (transportf_mor_weq
           (hSet_univalence_map _ _ p₁)
           (hSet_univalence_map _ _ p₂)
           f).
  Proof.
    induction p₁, p₂ ; cbn.
    exact Hf.
  Qed.

  Definition transportf_struct_mor
             {X₁ X₂ Y₁ Y₂ : hSet}
             (w₁ : X₁ ≃ Y₁)
             (PX₁ : P X₁)
             (w₂ : X₂ ≃ Y₂)
             (PX₂ : P X₂)
             (f : X₁ → X₂)
             (Hf : mor_hset_struct P PX₁ PX₂ f)
    : mor_hset_struct
        P
        (transportf_struct_weq w₁ PX₁)
        (transportf_struct_weq w₂ PX₂)
        (transportf_mor_weq w₁ w₂ f).
  Proof.
    pose (transportf_struct_mor_via_transportf
            (univalence_hSet w₁)
            PX₁
            (univalence_hSet w₂)
            PX₂
            f
            Hf)
      as H.
    rewrite !hSet_univalence_map_univalence_hSet in H.
    exact H.
  Qed.

  Definition transportf_struct_mor_via_eq
             {X₁ X₂ Y₁ Y₂ : hSet}
             (w₁ : X₁ ≃ Y₁)
             (PX₁ : P X₁)
             (w₂ : X₂ ≃ Y₂)
             (PX₂ : P X₂)
             (f : X₁ → X₂)
             (Hf : mor_hset_struct P PX₁ PX₂ f)
             (g : Y₁ → Y₂)
             (p : ∏ (y : Y₁), g y = transportf_mor_weq w₁ w₂ f y)
    : mor_hset_struct
        P
        (transportf_struct_weq w₁ PX₁)
        (transportf_struct_weq w₂ PX₂)
        g.
  Proof.
    refine (transportf
              _
              _
              (transportf_struct_mor w₁ PX₁ w₂ PX₂ f Hf)).
    use funextsec.
    intro y.
    exact (!(p y)).
  Qed.

  Definition transportf_mor_weq_prod
             {X₁ X₂ X₃ Y₁ Y₂ Y₃ : hSet}
             (w₁ : X₁ ≃ Y₁)
             (w₂ : X₂ ≃ Y₂)
             (w₃ : X₃ ≃ Y₃)
             (f : X₁ × X₂ → X₃)
    : Y₁ × Y₂ → Y₃
    := λ y, w₃ (f (invmap w₁ (pr1 y) ,, invmap w₂ (pr2 y))).
End SetStructure.

(**
 5. Cartesian structures
 *)
Definition hset_cartesian_struct_data
  : UU
  := ∑ (P : hset_struct),
     P unitHSET
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
     P (X × Y)%set).

Coercion hset_cartesian_struct_datat_to_struct
         (P : hset_cartesian_struct_data)
  : hset_struct
  := pr1 P.

Definition hset_struct_unit
           (P : hset_cartesian_struct_data)
  : P unitHSET
  := pr12 P.

Definition hset_struct_unit_ob
           (P : hset_cartesian_struct_data)
  : category_of_hset_struct P
  := _ ,, hset_struct_unit P.

Definition hset_struct_prod
           (P : hset_cartesian_struct_data)
           {X Y : hSet}
           (PX : P X)
           (PY : P Y)
  : P (X × Y)%set
  := pr22 P X Y PX PY.

Definition hset_struct_prod_ob
           {P : hset_cartesian_struct_data}
           (PX PY : category_of_hset_struct P)
  : category_of_hset_struct P
  := _ ,, hset_struct_prod P (pr2 PX) (pr2 PY).

Definition hset_cartesian_struct_laws
           (P : hset_cartesian_struct_data)
  : UU
  := (∏ (X : hSet)
        (PX : P X),
      mor_hset_struct P PX (hset_struct_unit P) (λ _ : X, tt))
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      mor_hset_struct P (hset_struct_prod P PX PY) PX dirprod_pr1)
     ×
     (∏ (X Y : hSet)
        (PX : P X)
        (PY : P Y),
      mor_hset_struct P (hset_struct_prod P PX PY) PY dirprod_pr2)
     ×
     (∏ (W X Y : hSet)
        (PW : P W)
        (PX : P X)
        (PY : P Y)
        (f : W → X)
        (g : W → Y)
        (Mf : mor_hset_struct P PW PX f)
        (Mg : mor_hset_struct P PW PY g),
       mor_hset_struct P PW (hset_struct_prod P PX PY) (prodtofuntoprod (f ,, g))).

Definition hset_cartesian_struct
  : UU
  := ∑ (P : hset_cartesian_struct_data), hset_cartesian_struct_laws P.

Coercion hset_cartesian_struct_to_data
         (P : hset_cartesian_struct)
  : hset_cartesian_struct_data
  := pr1 P.

Section Projections.
  Context (P : hset_cartesian_struct).

  Proposition hset_struct_to_unit
              {X : hSet}
              (PX : P X)
    : mor_hset_struct P PX (hset_struct_unit P) (λ _ : X, tt).
  Proof.
    exact (pr12 P X PX).
  Qed.

  Proposition hset_struct_pr1
              {X Y : hSet}
              (PX : P X)
              (PY : P Y)
    : mor_hset_struct P (hset_struct_prod P PX PY) PX dirprod_pr1.
  Proof.
    exact (pr122 P X Y PX PY).
  Qed.

  Proposition hset_struct_pr2
              {X Y : hSet}
              (PX : P X)
              (PY : P Y)
    : mor_hset_struct P (hset_struct_prod P PX PY) PY dirprod_pr2.
  Proof.
    exact (pr1 (pr222 P) X Y PX PY).
  Qed.

  Proposition hset_struct_pair
              {W X Y : hSet}
              {PW : P W}
              {PX : P X}
              {PY : P Y}
              {f : W → X}
              {g : W → Y}
              (Mf : mor_hset_struct P PW PX f)
              (Mg : mor_hset_struct P PW PY g)
    : mor_hset_struct P PW (hset_struct_prod P PX PY) (prodtofuntoprod (f ,, g)).
  Proof.
    exact (pr2 (pr222 P) W X Y PW PX PY f g Mf Mg).
  Qed.
End Projections.

(**
 6. Transport laws for cartesian structures
 *)
Section TransportCartesian.
  Context (P : hset_cartesian_struct).

  Definition transportf_struct_mor_prod_via_transportf
             {X₁ X₂ X₃ Y₁ Y₂ Y₃ : hSet}
             (p₁ : X₁ = Y₁)
             (PX₁ : P X₁)
             (p₂ : X₂ = Y₂)
             (PX₂ : P X₂)
             (p₃ : X₃ = Y₃)
             (PX₃ : P X₃)
             (f : X₁ × X₂ → X₃)
             (Hf : mor_hset_struct P (hset_struct_prod P PX₁ PX₂) PX₃ f)
    : mor_hset_struct
        P
        (hset_struct_prod
           P
           (transportf P p₁ PX₁)
           (transportf P p₂ PX₂))
        (transportf P p₃ PX₃)
        (transportf_mor_weq_prod
           (hSet_univalence_map _ _ p₁)
           (hSet_univalence_map _ _ p₂)
           (hSet_univalence_map _ _ p₃)
           f).
  Proof.
    induction p₁, p₂, p₃.
    exact Hf.
  Qed.

  Definition transportf_struct_mor_prod
             {X₁ X₂ X₃ Y₁ Y₂ Y₃ : hSet}
             (w₁ : X₁ ≃ Y₁)
             (PX₁ : P X₁)
             (w₂ : X₂ ≃ Y₂)
             (PX₂ : P X₂)
             (w₃ : X₃ ≃ Y₃)
             (PX₃ : P X₃)
             (f : X₁ × X₂ → X₃)
             (Hf : mor_hset_struct P (hset_struct_prod P PX₁ PX₂) PX₃ f)
    : mor_hset_struct
        P
        (hset_struct_prod
           P
           (transportf_struct_weq P w₁ PX₁)
           (transportf_struct_weq P w₂ PX₂))
        (transportf_struct_weq P w₃ PX₃)
        (transportf_mor_weq_prod w₁ w₂ w₃ f).
  Proof.
    pose (transportf_struct_mor_prod_via_transportf
            (univalence_hSet w₁)
            PX₁
            (univalence_hSet w₂)
            PX₂
            (univalence_hSet w₃)
            PX₃
            f
            Hf)
      as H.
    rewrite !hSet_univalence_map_univalence_hSet in H.
    exact H.
  Qed.

  Definition transportf_struct_mor_prod_via_eq
             {X₁ X₂ X₃ Y₁ Y₂ Y₃ : hSet}
             (w₁ : X₁ ≃ Y₁)
             (PX₁ : P X₁)
             (w₂ : X₂ ≃ Y₂)
             (PX₂ : P X₂)
             (w₃ : X₃ ≃ Y₃)
             (PX₃ : P X₃)
             (f : X₁ × X₂ → X₃)
             (Hf : mor_hset_struct P (hset_struct_prod P PX₁ PX₂) PX₃ f)
             (g : Y₁ × Y₂ → Y₃)
             (p : ∏ (y : Y₁ × Y₂), g y = transportf_mor_weq_prod w₁ w₂ w₃ f y)
    : mor_hset_struct
        P
        (hset_struct_prod
           P
           (transportf_struct_weq P w₁ PX₁)
           (transportf_struct_weq P w₂ PX₂))
        (transportf_struct_weq P w₃ PX₃)
        g.
  Proof.
    refine (transportf
              _
              _
              (transportf_struct_mor_prod w₁ PX₁ w₂ PX₂ w₃ PX₃ f Hf)).
    use funextsec.
    intro y.
    exact (!(p y)).
  Qed.

  Definition transportf_struct_weq_on_weq_transportf
             {X Y : hSet}
             (p : X = Y)
             (PX : P X)
    : mor_hset_struct
        P
        PX
        (transportf P p PX)
        (hSet_univalence_map _ _ p).
  Proof.
    induction p ; cbn.
    apply hset_struct_id.
  Qed.

  Definition transportf_struct_weq_on_weq
             {X Y : hSet}
             (w : X ≃ Y)
             (PX : P X)
    : mor_hset_struct
        P
        PX
        (transportf_struct_weq P w PX)
        w.
  Proof.
    pose (transportf_struct_weq_on_weq_transportf
            (univalence_hSet w)
            PX)
      as H.
    rewrite hSet_univalence_map_univalence_hSet in H.
    exact H.
  Qed.

  Definition transportf_struct_weq_on_invweq_transportf
             {X Y : hSet}
             (p : X = Y)
             (PX : P X)
    : mor_hset_struct
        P
        (transportf P p PX)
        PX
        (hSet_univalence_map _ _ (!p)).
  Proof.
    induction p ; cbn.
    apply hset_struct_id.
  Qed.

  Definition transportf_struct_weq_on_invweq
             {X Y : hSet}
             (w : X ≃ Y)
             (PX : P X)
    : mor_hset_struct
        P
        (transportf_struct_weq P w PX)
        PX
        (invmap w).
  Proof.
    pose (transportf_struct_weq_on_invweq_transportf
            (univalence_hSet w)
            PX)
      as H.
    rewrite univalence_hSet_inv in H.
    rewrite hSet_univalence_map_univalence_hSet in H.
    exact H.
  Qed.
End TransportCartesian.

(**
 7. Terminal object and products from cartesian structures
 *)
Section TerminalAndProductCartesian.
  Context (P : hset_cartesian_struct).

  Definition dispTerminal_hset_disp_struct
    : dispTerminal (hset_struct_disp_cat P) TerminalHSET.
  Proof.
    refine (hset_struct_unit P ,, _).
    intros X PX.
    use iscontraprop1.
    - apply isaprop_hset_struct_on_mor.
    - exact (hset_struct_to_unit P PX).
  Defined.

  Definition dispBinProducts_hset_disp_struct
    : dispBinProducts (hset_struct_disp_cat P) BinProductsHSET.
  Proof.
    intros X Y PX PY.
    simple refine ((_ ,, (_ ,, _)) ,, _).
    - exact (hset_struct_prod P PX PY).
    - exact (hset_struct_pr1 P PX PY).
    - exact (hset_struct_pr2 P PX PY).
    - intros W f g PW Mf Mg ; cbn.
      use iscontraprop1.
      + abstract
          (use isaproptotal2 ;
           [ intro ;
            apply isapropdirprod ; apply hset_struct_disp_cat
           | ] ;
           intros ;
           apply isaprop_hset_struct_on_mor).
      + simple refine (_ ,, _ ,, _).
        * exact (hset_struct_pair P Mf Mg).
        * apply isaprop_hset_struct_on_mor.
        * apply isaprop_hset_struct_on_mor.
  Defined.

  Definition Terminal_category_of_hset_struct
    : Terminal (category_of_hset_struct P).
  Proof.
    use total_category_Terminal.
    - exact TerminalHSET.
    - exact dispTerminal_hset_disp_struct.
  Defined.

  Definition BinProducts_category_of_hset_struct
    : BinProducts (category_of_hset_struct P).
  Proof.
    use total_category_Binproducts.
    - exact BinProductsHSET.
    - exact dispBinProducts_hset_disp_struct.
  Defined.
End TerminalAndProductCartesian.

(**
 8. Sections of structures
 *)
Definition discrete_hset_struct_data
           (P : hset_struct)
  : UU
  := ∑ (PX : ∏ (X : hSet), P X),
     ∏ (X Y : hSet)
       (f : X → Y),
     mor_hset_struct P (PX X) (PX Y) f.

Definition discrete_hset_struct_data_ob
           {P : hset_struct}
           (PX : discrete_hset_struct_data P)
           (X : hSet)
  : P X
  := pr1 PX X.

Coercion discrete_hset_struct_data_ob : discrete_hset_struct_data >-> Funclass.

Proposition discrete_hset_struct_data_mor
            {P : hset_struct}
            (PX : discrete_hset_struct_data P)
            {X Y : hSet}
            (f : X → Y)
  : mor_hset_struct P (PX X) (PX Y) f.
Proof.
  exact (pr2 PX X Y f).
Qed.

Definition discrete_hset_struct_laws
           {P : hset_struct}
           (PX : discrete_hset_struct_data P)
  : UU
  := ∏ (Z : hSet)
       (PZ : P Z),
     mor_hset_struct P (PX Z) PZ (λ z, z).

Definition discrete_hset_struct
           (P : hset_struct)
  : UU
  := ∑ (PX : discrete_hset_struct_data P),
     discrete_hset_struct_laws PX.

Coercion discrete_hset_struct_to_data
         {P : hset_struct}
         (PX : discrete_hset_struct P)
  : discrete_hset_struct_data P
  := pr1 PX.

Definition discrete_hset_struct_counit
           {P : hset_struct}
           (PX : discrete_hset_struct P)
           {Z : hSet}
           (PZ : P Z)
  : mor_hset_struct P (PX Z) PZ (λ z, z)
  := pr2 PX Z PZ.

Definition make_discrete_hset_struct
           (P : hset_struct)
           (PX : ∏ (X : hSet), P X)
           (Pf : ∏ (X Y : hSet)
                   (f : X → Y),
                 mor_hset_struct P (PX X) (PX Y) f)
           (Pη : ∏ (Z : hSet)
                   (PZ : P Z),
                 mor_hset_struct P (PX Z) PZ (λ z, z))
  : discrete_hset_struct P
  := (PX ,, Pf) ,, Pη.

Section DiscreteHSetStructSection.
  Context {P : hset_struct}
          (PX : discrete_hset_struct P).

  Definition discrete_hset_struct_section_data
    : section_disp_data (hset_struct_disp_cat P).
  Proof.
    refine ((λ X, PX X) ,, λ X Y f, _).
    Debug Off.
    exact (discrete_hset_struct_data_mor PX f).
    Debug On.
  Defined.

  Proposition discrete_hset_struct_section_axioms
    : section_disp_axioms discrete_hset_struct_section_data.
  Proof.
    split.
    - intros X ; cbn.
      apply isaprop_hset_struct_on_mor.
    - intros X Y Z f g ; cbn.
      apply isaprop_hset_struct_on_mor.
  Qed.

  Definition discrete_hset_struct_section
    : section_disp (hset_struct_disp_cat P).
  Proof.
    simple refine (_ ,, _).
    - exact discrete_hset_struct_section_data.
    - exact discrete_hset_struct_section_axioms.
  Defined.

  Definition discrete_hset_struct_to_are_adjoint_unit
    : functor_identity _
      ⟹
      section_functor discrete_hset_struct_section ∙ underlying_of_hset_struct P.
  Proof.
    use make_nat_trans.
    - exact (λ X, identity _).
    - abstract
        (intros X Y f ; cbn ;
         apply idpath).
  Defined.

  Definition discrete_hset_struct_to_are_adjoint_counit
    : underlying_of_hset_struct P ∙ section_functor discrete_hset_struct_section
      ⟹
      functor_identity _.
  Proof.
    use make_nat_trans.
    - exact (λ X, identity _ ,, discrete_hset_struct_counit PX (pr2 X)).
    - abstract
        (intros X Y f ;
         use eq_mor_hset_struct ;
         intro x ; cbn ;
         apply idpath).
  Defined.

  Definition discrete_hset_struct_to_are_adjoint
    : are_adjoints
        (section_functor discrete_hset_struct_section)
        (underlying_of_hset_struct P).
  Proof.
    simple refine ((_ ,, _) ,, (_ ,, _)).
    - exact discrete_hset_struct_to_are_adjoint_unit.
    - exact discrete_hset_struct_to_are_adjoint_counit.
    - abstract
        (intro X ;
         use eq_mor_hset_struct ;
         intro x ; cbn ;
         apply idpath).
    - abstract
        (intro ; cbn ;
         apply idpath).
  Defined.

  Definition discrete_hset_struct_to_is_right_adjoint
    : is_right_adjoint (underlying_of_hset_struct P)
    := section_functor discrete_hset_struct_section
       ,,
       discrete_hset_struct_to_are_adjoint.
End DiscreteHSetStructSection.
