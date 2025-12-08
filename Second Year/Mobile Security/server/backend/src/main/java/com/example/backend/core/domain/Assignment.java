package com.example.backend.core.domain;

import java.util.Date;

import jakarta.persistence.CascadeType;
import jakarta.persistence.Entity;
import jakarta.persistence.FetchType;
import jakarta.persistence.GeneratedValue;
import jakarta.persistence.GenerationType;
import jakarta.persistence.Id;
import jakarta.persistence.OneToOne;
import jakarta.persistence.SequenceGenerator;
import jakarta.persistence.Table;

@Entity
@Table(name = "assignment")
public class Assignment {
    @Id
    @GeneratedValue(strategy = GenerationType.SEQUENCE, generator = "assignment_id_gen")
    @SequenceGenerator(name = "assignment_id_gen", sequenceName = "assignment_id_seq")
    private Long id;
    private String title;
    private String description;
    @OneToOne(cascade = CascadeType.ALL, fetch = FetchType.LAZY)
    private Course course;
    @OneToOne(fetch = FetchType.LAZY)
    private User teacher;
    private Date dueDate;

    public Assignment() {
    }

    public Assignment(String title, String description, Date dueDate, Course course, User teacher) {
        this.title = title;
        this.description = description;
        this.dueDate = dueDate;
        this.course = course;
        this.teacher = teacher;
    }

    public Long getId() {
        return id;
    }

    public void setId(Long id) {
        this.id = id;
    }

    public String getTitle() {
        return title;
    }

    public void setTitle(String title) {
        this.title = title;
    }

    public String getDescription() {
        return description;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    public Date getDueDate() {
        return dueDate;
    }

    public void setDueDate(Date dueDate) {
        this.dueDate = dueDate;
    }

}
