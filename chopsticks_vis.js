const stage = new Stage()

/////////////////////////////////////////////////////////////////////
// Handle all states
/////////////////////////////////////////////////////////////////////

// Create a grid object that contains one cell per state
//    `instances` is an array that contains the states
const stateGridConfig = {
    grid_location :{
        x:10,
        y:10
    },
    cell_size:{
        x_size:200,
        y_size:200
    },
    grid_dimensions:{
        y_size: instances.length,
        x_size:1
    }
  }

const statesGrid = new Grid(stateGridConfig)
var Y= 100
// For every instance, place a visualization in the proper grid location
instances.forEach( (inst, idx) => {    
    const lb = idx == loopBack ? " (loopback)" : ""
    statesGrid.add({x:0, y:idx}, new TextBox(`State:${idx}${lb}`,{x:0,y:0},'black',16))
    
    stage.add(new TextBox({
        text: `${[...Array(5).keys()]}`, 
        coords: {x:300, y:Y},
        color: 'black',
        fontSize: 16}))
    Y=Y+100;
    statesGrid.add({x:0, y:idx}, visualizeStateAsText(inst, idx))    
})

/////////////////////////////////////////////////////////////////////
// Handle each individual state
/////////////////////////////////////////////////////////////////////

function visualizeStateAsText(inst, idx) {
    // The set of smiths present in this instance (which should, technically, never change)
    const handsPerTeam = inst.signature('Team').atoms()[0].join(inst.field('hands')).tuples().length
    const hands = inst.signature('Team').join(inst.field('hands')).tuples()
    const fingers = inst.signature('Hand').atoms().map(h => h.join(inst.field('fingers')).tuples()).flat()

    // const theseSmiths = inst.signature('Team').atoms()
    // The set of chopsticks present in this instance (which also should never change)
    const teams = inst.signature('Team').atoms()
    // const theseChops = inst.signature('Chopstick').atoms()
    // The value of clean, requested, etc. in this state. We must work with _ids_, not with atoms
    //   if we plan to check for membership in these arrays (and we do), since two atoms may be
    //   different *JavaScript* objects, yet represent the same "object" in the instance.
    const lastChangeIDs = inst.signature('Game').join(inst.field('lastChanged')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    const turnID = inst.signature('Game').join(inst.field('turn')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()

    // const nowCleanIDs = inst.signature('Table').join(inst.field('clean')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    // const nowRequestedIDs = inst.signature('Table').join(inst.field('requested')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    // const nowHoldingLeftIDs = inst.signature('Table').join(inst.field('holdingLeft')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()
    // const nowHoldingRightIDs = inst.signature('Table').join(inst.field('holdingRight')).tuples().map(tup => tup.atoms().map(at => at.id())).flat()

    // hands.forEach((hand, handIdx))
    const group = new Grid({
        grid_location :{
            x:10,
            y:10
        },
        cell_size:{
            x_size:80,
            y_size:80
        },
        grid_dimensions:{
            y_size: teams.length,
            x_size: 2
        }
      })

    teams.forEach((team, teamIdx) => {
        [...Array(handsPerTeam).keys()].forEach((handIdx) => {
            group.add({x: handIdx, y:teamIdx}, 
            new TextBox({
                text: `${fingers[(teamIdx * handsPerTeam) + handIdx]}`,
                color: 'black',
                fontSize: 16})
            )
        })
    })
    
    return group
}

// Finally, add the grid to the stage and render it:
stage.add(statesGrid)
stage.render(svg, document)